"""المُحمِّل (bootstrap) — هذا وحده ما يُحزم في التطبيق، لا الخوارزمية.

- إن كان السكربت الحقيقي (engine.py) موجودًا في مجلد التطبيق، يشغّله مباشرة ويبقى فيه.
- وإلا يعرض صفحة إدخال رمز الدخول، يفعّله على خادم التحكّم، ينزّل منه السكربت الحقيقي (برمز صالح فقط)، يحفظه،
  ثم يعيد تشغيل التطبيق فيشتغل السكربت. فالخوارزمية الكاملة لا تكون داخل حزمة التطبيق أبدًا.
"""

from __future__ import annotations

import base64
import errno
import hashlib
import hmac
import http.client as _http_client
import json
import os
import re
import runpy
import secrets
import socket
import ssl as _ssl
import sys
import threading
import time
import urllib.request
from pathlib import Path

from flask import Flask, jsonify, make_response, redirect, request
from werkzeug.serving import make_server

# رابط خادم التحكّم. يُحقن عند البناء من script_original.py؛ ومتغيّر البيئة يغلبه (للاختبار).
CONTROL_LINK = "__CONTROL_LINK__"

FOLDER = Path(os.environ.get("GG_FOLDER") or Path(__file__).resolve().parent)
ENGINE_FILE = FOLDER / "engine.py"
CONTENT_FILE = FOLDER / "content.py"
DATA_DIR = FOLDER / "data"
UNLOCK_PATH = DATA_DIR / "unlock.json"
DEVICE_PATH = DATA_DIR / "device.json"
# «الربط» on the first page too: the owner's move key (public), built in from script_original.py, so even a phone that
# never reached the old server follows the owner's signed move order to the new one (read from the relay). The
# server the app moved to is kept where the script keeps it (data/control.json), for the script too.
MOVE_KEY = "__MOVE_KEY__"
MOVE_RELAY = (os.environ.get("GG_RELAY") or "https://ntfy.sh").rstrip("/")
CONTROL_STATE_PATH = DATA_DIR / "control.json"
# A weak connection: each try to reach the control server may take this long, and it is tried this many times
# (only while nothing was sent yet, so a request is never made twice).
CONNECT_SECONDS = float(os.environ.get("GG_CONNECT_SECONDS") or 15)
CONNECT_TRIES = 3
CONNECT_PAUSE = float(os.environ.get("GG_CONNECT_PAUSE") or 2)
ACCESS_PATH = os.getenv("X_ACCESS_PATH", "desk")
IN_APP = os.environ.get("GG_IN_APP") == "1"
MAX_SCRIPT_BYTES = 16 * 1024 * 1024

_CONTROL_RE = re.compile(r"https://(\[[0-9A-Fa-f:]{2,39}\]|[A-Za-z0-9](?:[A-Za-z0-9.\-]{0,251}[A-Za-z0-9])?)(?::(\d{1,5}))?/([A-Za-z0-9_\-]{16,64})/?#([0-9a-fA-F]{64})")


def _control_state() -> dict:
    data = _read_json(CONTROL_STATE_PATH)
    if not isinstance(data, dict):
        return {}
    # (a build with another link in it: its link wins over one the app moved to before, as in the script)
    if data.get("link") and data.get("built") != CONTROL_LINK:
        return {"move_key": data.get("move_key") or "", "built": CONTROL_LINK}
    return data


def control_link() -> str:
    return (os.environ.get("GG_CONTROL_LINK") or str(_control_state().get("link") or "") or CONTROL_LINK or "").strip()


def _control_parse(link: str):
    match = _CONTROL_RE.fullmatch(link or "")
    if not match:
        return None
    port = int(match.group(2) or 443)
    if not 0 < port < 65536:
        return None
    return match.group(1), port, match.group(3), match.group(4).lower()


def control_configured() -> bool:
    return _control_parse(control_link()) is not None


def _read_json(path: Path) -> dict:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}


def _write_json(path: Path, data: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".new")
    temporary.write_text(json.dumps(data, ensure_ascii=False), encoding="utf-8")
    temporary.replace(path)


def device_id() -> str:
    """A stable id for this install (same one the engine uses), so the code binds to one phone."""
    got = str(_read_json(DEVICE_PATH).get("id") or "")
    if not re.fullmatch(r"[A-Za-z0-9]{16,64}", got):
        got = secrets.token_hex(16)
        _write_json(DEVICE_PATH, {"id": got})
    return got


def hardware_id() -> str:
    """This phone as Android knows it for this app (ANDROID_ID): the same after the app is deleted and installed again,
    or its data cleared (only a factory reset changes it), unlike device_id(), which is made by the install. Sent
    hashed, only so the control server gives one account and one trial balance per phone. "" outside the app."""
    try:
        from java import jclass
        try:
            context = jclass("com.chaquo.python.Python").getPlatform().getApplication()
        except Exception:
            context = jclass("android.app.ActivityThread").currentApplication()
        secure = jclass("android.provider.Settings$Secure")
        value = str(secure.getString(context.getContentResolver(), secure.ANDROID_ID) or "").strip().lower()
    except Exception:
        return ""
    if not re.fullmatch(r"[0-9a-f]{8,32}", value) or value == "9774d56d682e549c":
        return ""                                   # (none, or the one value some very old phones all share)
    return hashlib.sha256(("bot-grob-hw|" + value).encode("utf-8")).hexdigest()[:32]


class _Unreachable(RuntimeError):
    """The control server could not be reached at its link (or something else answers there): a move is worth looking
    for. Its text says why, for the page."""


_UNREACHABLE_TEXT = {
    "weak": "الإنترنت ضعيف: لم يكتمل الاتصال بخادم التحكّم. أعد المحاولة بعد قليل، أو جرّب شبكة أخرى.",
    "refused": "خادم التحكّم لا يستقبل الاتصال الآن (قد يكون متوقفًا أو يُعاد تشغيله). أعد المحاولة بعد قليل.",
    "offline": "لا يوجد اتصال بالإنترنت. تأكد من الشبكة ثم أعد المحاولة.",
    "other": "على عنوان خادم التحكّم برنامج آخر. راجع الرابط.",
    "cut": "انقطع الاتصال بخادم التحكّم أثناء فتحه. أعد المحاولة.",
}


def _connect(host: str, port: int, pin: str):
    """An open, pinned connection to the control server, tried CONNECT_TRIES times (CONNECT_SECONDS each)."""
    why = "weak"
    for attempt in range(CONNECT_TRIES):
        if attempt:
            time.sleep(CONNECT_PAUSE)
        context = _ssl.SSLContext(_ssl.PROTOCOL_TLS_CLIENT)
        context.check_hostname = False
        context.verify_mode = _ssl.CERT_NONE
        connection = _http_client.HTTPSConnection(host, port, timeout=CONNECT_SECONDS, context=context)
        try:
            connection.connect()
        except (socket.timeout, TimeoutError):
            why = "weak"
        except ConnectionRefusedError:
            why = "refused"
        except _ssl.SSLError as exc:
            why = "cut" if "EOF" in str(exc) or "reset" in str(exc).lower() else "other"
        except socket.gaierror:
            why = "offline"
        except OSError as exc:
            why = "offline" if exc.errno in (errno.ENETUNREACH, errno.EHOSTUNREACH, errno.ENETDOWN) else "cut"
        else:
            seen = hashlib.sha256(connection.sock.getpeercert(binary_form=True) or b"").hexdigest()
            if not hmac.compare_digest(seen, pin):
                connection.close()
                raise _Unreachable("شهادة خادم التحكّم لا تطابق الرابط المثبّت في التطبيق.")
            return connection
        connection.close()
        print(f"boot: لم يكتمل الاتصال بخادم التحكّم ({why})، المحاولة {attempt + 1} من {CONNECT_TRIES}", flush=True)
    raise _Unreachable(_UNREACHABLE_TEXT[why])


def _request_on(link: str, action: str, body: dict, seconds: float = 30, max_read: int = 1 << 20) -> dict:
    """Pinned POST to the control server at this link (the certificate is trusted by the fingerprint in the link)."""
    parsed = _control_parse(link)
    if not parsed:
        raise RuntimeError("خادم التحكّم غير مضبوط في هذه النسخة. راجع صاحب البرنامج.")
    host, port, secret, pin = parsed
    connection = _connect(host, port, pin)
    try:
        connection.sock.settimeout(seconds)
        sent = json.dumps(body or {}, ensure_ascii=False).encode("utf-8")
        connection.request("POST", f"/{secret}/{action}", body=sent,
                           headers={"Content-Type": "application/json; charset=utf-8", "Accept": "application/json", "Connection": "close"})
        answer = connection.getresponse()
        status, raw = answer.status, answer.read(max_read)
    except (socket.timeout, TimeoutError):
        raise RuntimeError("طال انتظار خادم التحكّم. أعد المحاولة.") from None
    except (OSError, _http_client.HTTPException):
        raise RuntimeError("انقطع الاتصال بخادم التحكّم. أعد المحاولة.") from None
    finally:
        connection.close()
    try:
        data = json.loads(raw.decode("utf-8", "replace"))
    except ValueError:
        data = None
    if not isinstance(data, dict):
        raise RuntimeError("ردّ غير مفهوم من خادم التحكّم." if status == 200 else f"ردّ خادم التحكّم برمز {status}.")
    if not data.get("ok"):
        raise RuntimeError(str(data.get("error") or "").strip() or "خطأ من خادم التحكّم.")
    return data


def _control_request(action: str, body: dict, seconds: float = 30, max_read: int = 1 << 20) -> dict:
    """The request to the control server; when it cannot be reached, a move order of the owner (when there is a
    newer one, and its server answers) is followed, and the request made there."""
    try:
        data = _request_on(control_link(), action, body, seconds, max_read)
    except _Unreachable:
        if os.environ.get("GG_CONTROL_LINK") or not follow_move():
            raise
        data = _request_on(control_link(), action, body, seconds, max_read)
    _remember_move_key(data)
    return data


# ---- «الربط»: the owner's move order, signed with the key of the panel's password (Ed25519, as in the script) ----
_ED_P = 2 ** 255 - 19
_ED_L = 2 ** 252 + 27742317777372353535851937790883648493
_ED_D = -121665 * pow(121666, _ED_P - 2, _ED_P) % _ED_P
_ED_I = pow(2, (_ED_P - 1) // 4, _ED_P)


def _ed_xrecover(y: int) -> int:
    xx = (y * y - 1) * pow(_ED_D * y * y + 1, _ED_P - 2, _ED_P)
    x = pow(xx, (_ED_P + 3) // 8, _ED_P)
    if (x * x - xx) % _ED_P:
        x = x * _ED_I % _ED_P
    return _ED_P - x if x & 1 else x


_ED_BY = 4 * pow(5, _ED_P - 2, _ED_P) % _ED_P
_ED_BX = _ed_xrecover(_ED_BY)
_ED_B = (_ED_BX, _ED_BY, 1, _ED_BX * _ED_BY % _ED_P)


def _ed_add(p, q):
    x1, y1, z1, t1 = p
    x2, y2, z2, t2 = q
    a = (y1 - x1) * (y2 - x2) % _ED_P
    b = (y1 + x1) * (y2 + x2) % _ED_P
    c = t1 * 2 * _ED_D * t2 % _ED_P
    d = z1 * 2 * z2 % _ED_P
    e, f, g, h = b - a, d - c, d + c, b + a
    return (e * f % _ED_P, g * h % _ED_P, f * g % _ED_P, e * h % _ED_P)


def _ed_mul(s: int, p):
    q = (0, 1, 1, 0)
    while s > 0:
        if s & 1:
            q = _ed_add(q, p)
        p = _ed_add(p, p)
        s >>= 1
    return q


def _ed_encode(p) -> bytes:
    x, y, z, _ = p
    zi = pow(z, _ED_P - 2, _ED_P)
    x, y = x * zi % _ED_P, y * zi % _ED_P
    return (y | ((x & 1) << 255)).to_bytes(32, "little")


def _ed_decode(s: bytes):
    y = int.from_bytes(s, "little")
    sign, y = y >> 255, y & ((1 << 255) - 1)
    if y >= _ED_P:
        raise ValueError("bad point")
    x = _ed_xrecover(y)
    if (x & 1) != sign:
        x = _ED_P - x
    if (-x * x + y * y - 1 - _ED_D * x * x * y * y) % _ED_P or (x == 0 and sign):
        raise ValueError("bad point")
    return (x, y, 1, x * y % _ED_P)


def ed_verify(public: bytes, message: bytes, signature: bytes) -> bool:
    if len(public) != 32 or len(signature) != 64:
        return False
    try:
        point_a, point_r = _ed_decode(public), _ed_decode(signature[:32])
    except ValueError:
        return False
    s = int.from_bytes(signature[32:], "little")
    if s >= _ED_L:
        return False
    k = int.from_bytes(hashlib.sha512(signature[:32] + public + message).digest(), "little") % _ED_L
    return _ed_encode(_ed_mul(s, _ED_B)) == _ed_encode(_ed_add(point_r, _ed_mul(k, point_a)))


def _move_key() -> str:
    """The owner's move key: as the control server last said it, else as built in."""
    for key in (str(_control_state().get("move_key") or ""), MOVE_KEY):
        key = key.strip().lower()
        if re.fullmatch(r"[0-9a-f]{64}", key):
            return key
    return ""


def _remember_move_key(answer: dict) -> None:
    key = str((answer or {}).get("move_key") or "").lower()
    if re.fullmatch(r"[0-9a-f]{64}", key):
        data = _control_state()
        if data.get("move_key") != key:
            data.update(move_key=key, built=CONTROL_LINK)
            _write_json(CONTROL_STATE_PATH, data)


def _move_open(public: bytes, text: str):
    """(link, time) of a move order signed with this key, or None."""
    try:
        if not text.startswith("ggmv1."):
            return None
        raw = base64.urlsafe_b64decode(text[6:].strip().encode("ascii"))
        nonce, body = raw[:16], raw[16:]
        key = hashlib.sha256(b"gg-move-enc|" + public).digest()
        stream = bytearray()
        counter = 0
        while len(stream) < len(body):
            stream += hashlib.sha256(key + nonce + counter.to_bytes(4, "big")).digest()
            counter += 1
        data = json.loads(bytes(a ^ b for a, b in zip(body, stream)).decode("utf-8"))
        link, at = str(data.get("link") or ""), int(data.get("at") or 0)
        if not ed_verify(public, f"gg-move|{link}|{at}".encode("utf-8"), bytes.fromhex(str(data.get("sig") or ""))):
            return None
        return (link, at) if _control_parse(link) else None
    except Exception:
        return None


def follow_move() -> bool:
    """The control server could not be reached: the owner's newest move order on the relay, when it names another
    server and that server answers (with the certificate the order names), becomes the link. True when moved."""
    key = _move_key()
    if not key:
        return False
    public = bytes.fromhex(key)
    topic = "gg" + hashlib.sha256(b"gg-relay|" + public).hexdigest()[:30]
    try:
        request_ = urllib.request.Request(f"{MOVE_RELAY}/{topic}/json?poll=1&since=all",
                                          headers={"User-Agent": "tg-groups-app/1.0", "Cache-Control": "no-cache"})
        with urllib.request.urlopen(request_, timeout=20) as answer:
            lines = answer.read(1 << 20).decode("utf-8", "replace").splitlines()
    except Exception:
        return False
    best = None
    for line in lines:
        try:
            event = json.loads(line)
        except ValueError:
            continue
        if not isinstance(event, dict) or event.get("event") != "message":
            continue
        found = _move_open(public, str(event.get("message") or ""))
        if found and (best is None or found[1] > best[1]):
            best = found
    state = _control_state()
    if not best or best[1] <= int(state.get("moved_at") or 0) or best[0] == control_link():
        return False
    link, at = best
    try:
        _request_on(link, "check", {"token": saved_token()}, seconds=15)
    except RuntimeError:
        return False
    data = _control_state()
    data.update(link=link, moved_at=at, built=CONTROL_LINK)
    _write_json(CONTROL_STATE_PATH, data)
    print("boot: انتقل إلى خادم التحكّم الجديد (أمر «ربط» موقَّع من صاحب البرنامج).", flush=True)
    return True


def saved_token() -> str:
    return str(_read_json(UNLOCK_PATH).get("token") or "")


def _download_and_save(token: str) -> None:
    """Download the published script and content with a valid token, check them, and save them. Raises
    RuntimeError on any problem."""
    import base64
    got = _control_request("script-download", {"token": token}, seconds=120, max_read=MAX_SCRIPT_BYTES)
    try:
        engine = base64.b64decode(str(got.get("gg") or ""), validate=True)
    except Exception:
        raise RuntimeError("وصل السكربت تالفًا. أعد المحاولة.") from None
    if not engine or len(engine) > MAX_SCRIPT_BYTES:
        raise RuntimeError("لم يصل السكربت كاملًا. أعد المحاولة.")
    try:
        compile(engine.decode("utf-8"), "engine.py", "exec")
    except (UnicodeDecodeError, SyntaxError, ValueError):
        raise RuntimeError("السكربت المنزّل غير صالح. أعد المحاولة.") from None
    content = None
    if got.get("content"):
        try:
            content = base64.b64decode(str(got.get("content")), validate=True)
            compile(content.decode("utf-8"), "content.py", "exec")
        except Exception:
            content = None
    if content is not None:
        tmp = CONTENT_FILE.with_name("content.py.new")
        tmp.write_bytes(content)
        tmp.replace(CONTENT_FILE)
    tmp = ENGINE_FILE.with_name("engine.py.new")
    tmp.write_bytes(engine)
    tmp.replace(ENGINE_FILE)


def _get_engine(data: dict, code: str = "", user: str = "") -> None:
    token = str(data.get("token") or "")
    if not token:
        raise RuntimeError("لم يصل رمز الجلسة من الخادم. أعد المحاولة.")
    _download_and_save(token)
    saved = {"token": token, "code": code}
    if user:
        saved["user"] = user
    _write_json(UNLOCK_PATH, saved)      # (saved last: the engine is now unlocked)


def fetch_engine(code: str) -> None:
    """Activate the code, then download and save the script. Raises RuntimeError with a message for the user."""
    _get_engine(_control_request("activate", {"code": code, "device": device_id(), "hw": hardware_id()}), code=code)


def fetch_engine_with_account(kind: str, name: str, password: str) -> None:
    """Sign in («login») or make a new account («register»), then download and save the script."""
    if kind not in ("login", "register"):
        raise RuntimeError("طلب غير معروف.")
    _get_engine(_control_request(kind, {"user": name, "password": password, "device": device_id(), "hw": hardware_id()}), user=name)


def resume() -> bool:
    """A device activated before (its code is saved): download the script silently, without asking again."""
    token = saved_token()
    if not token or not control_configured():
        return False
    try:
        _download_and_save(token)
        return True
    except RuntimeError:
        return False


def restart_app() -> None:
    time.sleep(1.2)
    if IN_APP:
        try:
            from java import jclass
            jclass("app.tg.groups.MainActivity").restartApp()
            return
        except Exception as exc:
            print("تعذّر إعادة التشغيل تلقائيًا:", exc, flush=True)
    # (outside the app, e.g. a test: just end so a supervisor relaunches)
    os._exit(0)


def engine_ready() -> bool:
    if not ENGINE_FILE.is_file():
        return False
    try:
        compile(ENGINE_FILE.read_text(encoding="utf-8"), "engine.py", "exec")
        return True
    except (OSError, UnicodeDecodeError, SyntaxError, ValueError):
        return False


# ---------------------------------------------------------------- the setup page (only until the script is in place)
SETUP_PAGE = """<!doctype html><html lang="ar" dir="rtl"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover"><title>الدخول</title>
<style>
*{box-sizing:border-box}
html{-webkit-text-size-adjust:100%;-webkit-tap-highlight-color:transparent}
body{margin:0;min-height:100vh;min-height:100dvh;display:grid;place-items:center;padding:16px;background:#f3f5fa;color:#101828;
font:15px/1.65 "Plex Arabic",system-ui,-apple-system,"Segoe UI",Roboto,"Noto Sans Arabic",Tahoma,sans-serif;-webkit-font-smoothing:antialiased}
.box{width:min(100%,360px);overflow:hidden;border-radius:22px;background:#fff;border:1px solid #e6e9f0;text-align:center;
box-shadow:0 24px 48px -20px rgba(16,24,40,.28),0 6px 12px -6px rgba(16,24,40,.08);animation:rise .45s cubic-bezier(.2,.8,.2,1) both}
.hero{position:relative;isolation:isolate;padding:26px 20px 22px;color:#fff;
background:radial-gradient(120% 95% at 100% 0%,rgba(92,132,255,.5) 0%,rgba(92,132,255,0) 58%),radial-gradient(85% 90% at 0% 100%,rgba(141,98,255,.42) 0%,rgba(141,98,255,0) 62%),linear-gradient(158deg,#0c1640 0%,#13215e 52%,#1b2675 100%)}
.hero::before{content:"";position:absolute;inset:0;z-index:-1;background-image:linear-gradient(rgba(255,255,255,.055) 1px,transparent 1px),linear-gradient(90deg,rgba(255,255,255,.055) 1px,transparent 1px);background-size:20px 20px;-webkit-mask-image:linear-gradient(200deg,#000 0%,transparent 75%);mask-image:linear-gradient(200deg,#000 0%,transparent 75%)}
.mark{display:grid;place-items:center;width:52px;height:52px;margin:0 auto 12px;border-radius:16px;background:linear-gradient(135deg,#5b8cff,#7c5cff);box-shadow:0 10px 22px -8px rgba(91,140,255,.8),inset 0 1px 0 rgba(255,255,255,.4)}
.mark::before{content:"";width:24px;height:24px;background:#fff;-webkit-mask:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 24 24'%3E%3Cpath fill='%23000' d='M13.2 2.2 4.6 13.1a.8.8 0 0 0 .6 1.3h5.9l-1 7.2c-.1.8.9 1.2 1.4.6l8.6-10.9a.8.8 0 0 0-.6-1.3h-5.9l1-7.2c.1-.8-.9-1.2-1.4-.6z'/%3E%3C/svg%3E") center/contain no-repeat;mask:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 24 24'%3E%3Cpath fill='%23000' d='M13.2 2.2 4.6 13.1a.8.8 0 0 0 .6 1.3h5.9l-1 7.2c-.1.8.9 1.2 1.4.6l8.6-10.9a.8.8 0 0 0-.6-1.3h-5.9l1-7.2c.1-.8-.9-1.2-1.4-.6z'/%3E%3C/svg%3E") center/contain no-repeat}
h1{margin:0 0 4px;font-size:19px;font-weight:600}
.hero p{margin:0;color:rgba(255,255,255,.74);font-size:13px}
.body{padding:20px 20px 2px}
label{display:block;margin:0 0 8px;font-size:12.5px;font-weight:500;color:#344054;text-align:right}
input{width:100%;height:50px;padding:0 14px;border-radius:13px;border:1px solid #d5dae3;background:#f7f8fb;color:#101828;text-align:center;direction:ltr;
font:600 18px/1 ui-monospace,"SFMono-Regular",Menlo,Consolas,"Liberation Mono",monospace;letter-spacing:3px;outline:none;transition:border-color .15s,box-shadow .15s,background .15s}
input::placeholder{color:#98a2b3}
input:focus{border-color:#2f5bea;background:#fff;box-shadow:0 0 0 4px rgba(47,91,234,.16)}
#btn{display:flex;align-items:center;justify-content:center;gap:8px;width:100%;height:48px;margin-top:12px;border:1px solid rgba(36,71,200,.6);border-radius:13px;
background:linear-gradient(180deg,#4a74ff,#2f5bea);color:#fff;font:inherit;font-size:15px;font-weight:600;cursor:pointer;
box-shadow:0 10px 20px -10px rgba(47,91,234,.9),inset 0 1px 0 rgba(255,255,255,.22);transition:transform .12s}
#btn:active{transform:scale(.98)}#btn:disabled{opacity:.75}
#btn:disabled::after{content:"";width:15px;height:15px;border-radius:50%;border:2px solid #fff;border-inline-end-color:transparent;animation:spin .7s linear infinite}
.msg{min-height:22px;margin:12px 0 0;font-size:13px;color:#b42318}
.foot{display:flex;align-items:center;justify-content:center;gap:6px;margin:0;padding:10px 20px 18px;font-size:11.5px;color:#98a2b3}
.foot::before{content:"";flex:none;width:13px;height:13px;background:#98a2b3;-webkit-mask:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 24 24' fill='none' stroke='%23000' stroke-width='2' stroke-linecap='round' stroke-linejoin='round'%3E%3Cpath d='M12 22s8-3.5 8-10V5l-8-3-8 3v7c0 6.5 8 10 8 10z'/%3E%3Cpath d='m9 12 2 2 4-4'/%3E%3C/svg%3E") center/contain no-repeat;mask:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 24 24' fill='none' stroke='%23000' stroke-width='2' stroke-linecap='round' stroke-linejoin='round'%3E%3Cpath d='M12 22s8-3.5 8-10V5l-8-3-8 3v7c0 6.5 8 10 8 10z'/%3E%3Cpath d='m9 12 2 2 4-4'/%3E%3C/svg%3E") center/contain no-repeat}
@keyframes rise{from{opacity:0;transform:translateY(8px)}to{opacity:1;transform:none}}
@keyframes spin{to{transform:rotate(360deg)}}
@media (prefers-reduced-motion:reduce){*,*::before,*::after{animation:none!important;transition:none!important}}

input{width:100%;height:48px;padding:0 14px;border-radius:13px;border:1px solid #d5dae3;background:#f7f8fb;color:#101828;outline:none;
font:500 15px/1.2 "Plex Arabic",system-ui,-apple-system,"Segoe UI",Roboto,"Noto Sans Arabic",Tahoma,sans-serif;letter-spacing:0;text-align:right;direction:rtl;transition:border-color .15s,box-shadow .15s,background .15s}
input.cd{height:50px;text-align:center;direction:ltr;font:600 18px/1 ui-monospace,"SFMono-Regular",Menlo,Consolas,"Liberation Mono",monospace;letter-spacing:3px}
input[type=password]{direction:ltr;text-align:left;letter-spacing:2px}
input[type=password]::placeholder{letter-spacing:0;text-align:right}
.pane label{margin-top:12px}.pane label:first-child{margin-top:0}
.tabs{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:4px;margin:16px 16px 0;padding:4px;border-radius:13px;background:#eef1f6}
.tabs button{width:auto;height:36px;margin:0;padding:0 4px;border:0;border-radius:10px;background:transparent;color:#667085;
font:inherit;font-size:12.5px;font-weight:600;box-shadow:none;cursor:pointer;transition:background .15s,color .15s}
.tabs button:active{transform:none}
.tabs button[aria-selected=true]{background:#fff;color:#101828;box-shadow:0 1px 2px rgba(16,24,40,.1),0 0 0 1px #e6e9f0}
.hint{margin:10px 0 0;font-size:12px;line-height:1.7;color:#667085;text-align:right}
</style></head>
<body><form class="box" onsubmit="go(event)" novalidate>
<div class="hero"><span class="mark" aria-hidden="true"></span><h1>قروبات</h1><p>ادخل برمز الدخول أو بحسابك، أو أنشئ حسابًا. يُجهَّز التطبيق مرة واحدة ثم يعمل مباشرة.</p></div>
<div class="tabs" role="tablist" aria-label="طريقة الدخول"><button type="button" role="tab" data-k="code" aria-selected="true">رمز الدخول</button><button type="button" role="tab" data-k="login" aria-selected="false">تسجيل الدخول</button><button type="button" role="tab" data-k="register" aria-selected="false">حساب جديد</button></div>
<div class="body">
<div class="pane" data-p="code"><label for="code">رمز الدخول</label><input id="code" class="cd" placeholder="XXXX-XXXX-XXXX" autocomplete="off" autocapitalize="characters" spellcheck="false" autofocus></div>
<div class="pane" data-p="login" hidden><label for="lu">اسم المستخدم</label><input id="lu" class="t" dir="auto" autocomplete="username" autocapitalize="off" spellcheck="false"><label for="lp">كلمة السر</label><input id="lp" type="password" autocomplete="current-password"></div>
<div class="pane" data-p="register" hidden><label for="ru">اسم المستخدم</label><input id="ru" class="t" dir="auto" maxlength="24" autocomplete="username" autocapitalize="off" spellcheck="false" placeholder="حروف وأرقام، بلا مسافات"><label for="rp">كلمة السر</label><input id="rp" type="password" maxlength="128" autocomplete="new-password" placeholder="6 أحرف على الأقل"><label for="rp2">تأكيد كلمة السر</label><input id="rp2" type="password" maxlength="128" autocomplete="new-password"><p class="hint">يُربط حسابك بهذا الجوال. التعليقات تُكتب برصيد مسبق يضيفه لك صاحب البرنامج.</p></div>
<button id="btn" type="submit">دخول</button><div class="msg" id="msg" role="status"></div></div>
<p class="foot">رمزك أو حسابك مربوط بهذا الجوال ويعمل عليه وحده.</p></form>
<script>
var kind="code";
function el(id){return document.getElementById(id)}
function say(t,c){var m=el("msg");m.style.color=c||"#b42318";m.textContent=t}
function pick(k){kind=k;
document.querySelectorAll(".tabs button").forEach(function(t){t.setAttribute("aria-selected",String(t.dataset.k===k))});
document.querySelectorAll(".pane").forEach(function(p){p.hidden=p.dataset.p!==k});
el("btn").textContent=k==="register"?"إنشاء الحساب":"دخول";say("");
var f=document.querySelector(".pane[data-p="+k+"] input");if(f)f.focus()}
document.querySelectorAll(".tabs button").forEach(function(t){t.addEventListener("click",function(){pick(t.dataset.k)})});
async function go(e){e.preventDefault();var b=el("btn"),url,body;
if(kind==="code"){var code=el("code").value.trim();if(!code){say("أدخل الرمز.");return}url="SETUP_URL";body={code:code}}
else if(kind==="login"){var u=el("lu").value.trim(),p=el("lp").value;if(!u||!p){say("أدخل اسم المستخدم وكلمة السر.");return}url="SETUP_URL/login";body={user:u,password:p}}
else{var nu=el("ru").value.trim(),np=el("rp").value;
if(nu.length<3){say("اسم المستخدم 3 أحرف على الأقل.");return}
if(np.length<6){say("كلمة السر 6 أحرف على الأقل.");return}
if(np!==el("rp2").value){say("كلمتا السر غير متطابقتين.");return}
url="SETUP_URL/register";body={user:nu,password:np}}
b.disabled=true;say("جارٍ التحقّق والتجهيز… قد يأخذ لحظات.","#667085");
try{var r=await fetch(url,{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify(body)});var d=await r.json();
if(d.ok){say("تم التجهيز. يُعاد تشغيل التطبيق…","#067647");}else{say(d.error||"تعذّر الدخول.");b.disabled=false}}
catch(x){say("تعذّر الاتصال. أعد المحاولة.");b.disabled=false}}
</script></body></html>"""

boot_app = Flask(__name__)


@boot_app.get("/healthz")
def _healthz():
    return "ok", 200


@boot_app.get("/")
def _root():
    return redirect("/" + ACCESS_PATH, code=302)


@boot_app.get("/<path:_any>")
def _setup_page(_any):
    page = SETUP_PAGE.replace("SETUP_URL", "/" + ACCESS_PATH + "/setup")
    return make_response(page)


@boot_app.post("/<access>/setup")
def _setup(access):
    if not hmac.compare_digest(access, ACCESS_PATH):
        return jsonify(ok=False, error="رابط غير صحيح."), 404
    code = str((request.get_json(silent=True) or {}).get("code") or "").strip()
    if not code:
        return jsonify(ok=False, error="أدخل الرمز."), 200
    try:
        fetch_engine(code)
    except RuntimeError as exc:
        return jsonify(ok=False, error=str(exc)), 200
    threading.Thread(target=restart_app, name="restart", daemon=True).start()
    return jsonify(ok=True)


@boot_app.post("/<access>/setup/<kind>")
def _setup_account(access, kind):
    if not hmac.compare_digest(access, ACCESS_PATH) or kind not in ("login", "register"):
        return jsonify(ok=False, error="رابط غير صحيح."), 404
    body = request.get_json(silent=True) or {}
    name = str(body.get("user") or "").strip()
    password = str(body.get("password") or "")
    if not name or not password:
        return jsonify(ok=False, error="أدخل اسم المستخدم وكلمة السر."), 200
    try:
        fetch_engine_with_account(kind, name, password)
    except RuntimeError as exc:
        return jsonify(ok=False, error=str(exc)), 200
    threading.Thread(target=restart_app, name="restart", daemon=True).start()
    return jsonify(ok=True)


BACKUPS_DIR = DATA_DIR / "backups"


def roll_back() -> bool:
    """Put back the version an update replaced (the update keeps it in data/backups as engine-<version>.py, with
    its content-<version>.py). The backup is used up, so a version that also fails does not loop."""
    try:
        kept = sorted(BACKUPS_DIR.glob("engine-*.py"), key=lambda p: p.stat().st_mtime, reverse=True)
    except OSError:
        return False
    for backup in kept:
        try:
            body = backup.read_bytes()
            compile(body.decode("utf-8"), "engine.py", "exec")
        except Exception:
            continue
        version = backup.stem[len("engine-"):]
        content = BACKUPS_DIR / f"content-{version}.py"
        try:
            if content.is_file():
                tmp = CONTENT_FILE.with_name("content.py.new")
                tmp.write_bytes(content.read_bytes())
                tmp.replace(CONTENT_FILE)
            tmp = ENGINE_FILE.with_name("engine.py.new")
            tmp.write_bytes(body)
            tmp.replace(ENGINE_FILE)
            backup.unlink()
        except OSError:
            return False
        print(f"boot: الإصدار الجديد لم يعمل — رجعت إلى الإصدار {version}.", flush=True)
        return True
    return False


def run_engine() -> None:
    """Hand off to the real script in this same process (it serves the app from here on). If it fails to start
    (an update that does not work on this phone), go back to the version before it and restart."""
    os.chdir(str(FOLDER))
    sys.argv = [str(ENGINE_FILE)]
    try:
        runpy.run_path(str(ENGINE_FILE), run_name="__main__")
    except Exception:
        import traceback
        traceback.print_exc()
        if roll_back():
            restart_app()
            return
        raise


def main() -> None:
    if not control_configured():
        print("boot: لا يوجد رابط خادم تحكّم مضبوط.", flush=True)
    if engine_ready():
        print("boot: السكربت موجود — تشغيله.", flush=True)
        run_engine()
        return
    if resume():
        print("boot: جُهّز بالرمز المحفوظ — إعادة التشغيل.", flush=True)
        restart_app()
        return
    port = int(os.environ.get("PORT") or 5000)
    host = os.environ.get("BIND_HOST") or "127.0.0.1"
    print(f"boot: لا يوجد سكربت بعد — عرض صفحة الإعداد على {host}:{port}", flush=True)
    server = make_server(host, port, boot_app, threaded=True)
    server.serve_forever()


if __name__ == "__main__":
    main()
