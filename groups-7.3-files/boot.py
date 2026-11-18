"""المُحمِّل (bootstrap) — هذا وحده ما يُحزم في التطبيق، لا الخوارزمية.

- إن كان السكربت الحقيقي (engine.py) موجودًا في مجلد التطبيق، يشغّله مباشرة ويبقى فيه.
- وإلا يعرض صفحة إدخال رمز الدخول، يفعّله على خادم التحكّم، ينزّل منه السكربت الحقيقي (برمز صالح فقط)، يحفظه،
  ثم يعيد تشغيل التطبيق فيشتغل السكربت. فالخوارزمية الكاملة لا تكون داخل حزمة التطبيق أبدًا.
"""

from __future__ import annotations

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
ACCESS_PATH = os.getenv("X_ACCESS_PATH", "desk")
IN_APP = os.environ.get("GG_IN_APP") == "1"
MAX_SCRIPT_BYTES = 16 * 1024 * 1024

_CONTROL_RE = re.compile(r"https://(\[[0-9A-Fa-f:]{2,39}\]|[A-Za-z0-9](?:[A-Za-z0-9.\-]{0,251}[A-Za-z0-9])?)(?::(\d{1,5}))?/([A-Za-z0-9_\-]{16,64})/?#([0-9a-fA-F]{64})")


def control_link() -> str:
    return (os.environ.get("GG_CONTROL_LINK") or CONTROL_LINK or "").strip()


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


def _control_request(action: str, body: dict, seconds: float = 30, max_read: int = 1 << 20) -> dict:
    """Pinned POST to the control server (the certificate is trusted by the fingerprint in the link)."""
    parsed = _control_parse(control_link())
    if not parsed:
        raise RuntimeError("خادم التحكّم غير مضبوط في هذه النسخة. راجع صاحب البرنامج.")
    host, port, secret, pin = parsed
    context = _ssl.SSLContext(_ssl.PROTOCOL_TLS_CLIENT)
    context.check_hostname = False
    context.verify_mode = _ssl.CERT_NONE
    connection = _http_client.HTTPSConnection(host, port, timeout=8, context=context)
    try:
        try:
            connection.connect()
        except _ssl.SSLError:
            raise RuntimeError("على عنوان خادم التحكّم برنامج آخر. راجع الرابط.") from None
        except OSError:
            raise RuntimeError("تعذّر الوصول إلى خادم التحكّم. تأكد من الإنترنت ومن أن الخادم يعمل.") from None
        seen = hashlib.sha256(connection.sock.getpeercert(binary_form=True) or b"").hexdigest()
        if not hmac.compare_digest(seen, pin):
            raise RuntimeError("شهادة خادم التحكّم لا تطابق الرابط المثبّت في التطبيق.")
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


def fetch_engine(code: str) -> None:
    """Activate the code, then download and save the script. Raises RuntimeError with a message for the user."""
    data = _control_request("activate", {"code": code, "device": device_id()})
    token = str(data.get("token") or "")
    if not token:
        raise RuntimeError("لم يصل رمز الجلسة من الخادم. أعد المحاولة.")
    _download_and_save(token)
    _write_json(UNLOCK_PATH, {"token": token, "code": code})      # (saved last: the engine is now unlocked)


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
<meta name="viewport" content="width=device-width, initial-scale=1"><title>الدخول</title>
<style>body{font:16px/1.7 "IBM Plex Sans Arabic",system-ui,-apple-system,sans-serif;background:#f3f5fa;color:#101828;margin:0;display:grid;place-items:center;min-height:100vh;padding:16px;box-sizing:border-box}
.box{background:#fff;padding:28px 24px;border-radius:20px;width:min(92vw,350px);box-shadow:0 0 0 1px rgba(16,24,40,.06),0 18px 44px rgba(16,24,40,.10);text-align:center}
.box::before{content:"";display:block;width:46px;height:46px;margin:0 auto 12px;border-radius:14px;background:linear-gradient(135deg,#2f5bea,#7c5cff);box-shadow:0 8px 18px rgba(47,91,234,.3)}
h1{font-size:20px;margin:0 0 4px}p{color:#667085;font-size:14px;margin:0 0 18px}
input{width:100%;box-sizing:border-box;padding:13px;border-radius:12px;border:1px solid #e4e7ec;background:#f9fafb;color:#101828;text-align:center;font-size:18px;letter-spacing:2px}
input:focus{outline:none;border-color:#2f5bea;box-shadow:0 0 0 4px rgba(47,91,234,.14);background:#fff}
button{width:100%;padding:13px;border:0;border-radius:12px;background:linear-gradient(135deg,#2f5bea,#5b6ef5);color:#fff;font-weight:700;font-size:16px;cursor:pointer;margin-top:12px;box-shadow:0 8px 18px rgba(47,91,234,.28)}
button:disabled{opacity:.6}.msg{min-height:20px;color:#b42318;font-size:14px;margin-top:12px}</style></head>
<body><form class="box" onsubmit="go(event)"><h1>قروبات</h1><p>أدخل رمز الدخول الذي أعطاك إياه صاحب البرنامج. يُجهَّز التطبيق مرة واحدة ثم يبدأ العمل.</p>
<input id="code" placeholder="XXXX-XXXX-XXXX" autocomplete="off" autocapitalize="characters" autofocus>
<button id="btn" type="submit">دخول</button><div class="msg" id="msg"></div></form>
<script>
async function go(e){e.preventDefault();var b=document.getElementById("btn"),m=document.getElementById("msg");
var code=document.getElementById("code").value.trim();if(!code)return;b.disabled=true;m.style.color="#667085";m.textContent="جارٍ التحقّق والتجهيز… قد يأخذ لحظات.";
try{var r=await fetch("SETUP_URL",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({code:code})});
var d=await r.json();if(d.ok){m.style.color="#067647";m.textContent="تم التجهيز. يُعاد تشغيل التطبيق…";}else{m.style.color="#b42318";m.textContent=d.error||"الرمز غير صحيح.";b.disabled=false;}}
catch(x){m.style.color="#b42318";m.textContent="تعذّر الاتصال. أعد المحاولة.";b.disabled=false;}}
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


def run_engine() -> None:
    """Hand off to the real script in this same process (it serves the app from here on)."""
    os.chdir(str(FOLDER))
    sys.argv = [str(ENGINE_FILE)]
    runpy.run_path(str(ENGINE_FILE), run_name="__main__")


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
