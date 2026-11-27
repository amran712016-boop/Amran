"""Standalone control server for the «قروبات/تعليقات» app, meant to run on the owner's own hosting.

What it does, all from one page the owner opens with a master password:
  • Access codes — the owner makes a code for each user. The app does not open until the user types a code the
    server knows and the owner has not stopped. The owner can stop any code at any moment.
  • Keys — the owner puts the Gemini key and the Claude key here and picks which one writes the comments. The keys
    stay on this server (kept sealed on disk); they are never sent to the phones. The app sends the tweet's text
    (and its picture) to this server, and the server writes the reply with the owner's key and sends it back.

Nothing of the main groups/users server is touched: this is a separate service. The app reaches it the same way it
reaches the comments server today — an HTTPS link that carries the server's own certificate fingerprint, so no
certificate authority is needed and the app refuses any other certificate:

    https://<your-host>[:port]/<app-secret>#<certificate-fingerprint>

Run it:
    pip install flask
    python control_server.py                 # makes its data, certificate and secrets on first run, and prints
                                              # the owner page link and the app link.
Useful environment variables (all optional):
    CONTROL_DATA=./control-data              # where it keeps its data, certificate and secrets
    CONTROL_HOST=0.0.0.0   CONTROL_PORT=8443 # where it listens
    CONTROL_PUBLIC_HOST=example.com          # the host to print in the links (else the machine's)
    CONTROL_ADMIN_PASSWORD=...               # set/replace the owner password (else one is made and printed once)
"""
from __future__ import annotations

import base64
import io
import gzip
import hashlib
import hmac
import json
import os
import re
import secrets
import shutil
import ssl
import struct
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path
from urllib.parse import quote

from flask import Flask, jsonify, redirect, render_template_string, request, send_file, session
from werkzeug.serving import ThreadedWSGIServer

# ----------------------------------------------------------------------------- where everything lives
DATA_DIR = Path(os.environ.get("CONTROL_DATA") or (Path(__file__).resolve().parent / "control-data"))
SECRETS_PATH = DATA_DIR / "secrets.json"
CODES_PATH = DATA_DIR / "codes.json"
KEYS_PATH = DATA_DIR / "keys.json"
USAGE_PATH = DATA_DIR / "usage.json"
NOTICES_PATH = DATA_DIR / "notices.json"
ACTS_PATH = DATA_DIR / "acts.json"
SUPPORT_PATH = DATA_DIR / "support.json"
MOVE_PATH = DATA_DIR / "move.json"
FAILURES_PATH = DATA_DIR / "failures.json"
FAILURES_DIR = DATA_DIR / "failures"
SCRIPT_DIR = DATA_DIR / "script"
SUPPORT_DIR = DATA_DIR / "support"
CERT_PATH = DATA_DIR / "server.crt"
CERT_KEY_PATH = DATA_DIR / "server.key"

LISTEN_HOST = os.environ.get("CONTROL_HOST") or "0.0.0.0"
LISTEN_PORT = int(os.environ.get("CONTROL_PORT") or 8443)

TOKEN_DAYS = 30                      # how long an app stays unlocked before it must check the code again
LOCK = threading.Lock()


# ----------------------------------------------------------------------------- private files (owner-only on disk)
def read_private_json(path: Path) -> dict | None:
    try:
        loaded = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return None
    except (OSError, json.JSONDecodeError):
        return None
    return loaded if isinstance(loaded, dict) else None


def write_private_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
    try:
        os.chmod(temporary, 0o600)
    except OSError:
        pass
    temporary.replace(path)
    try:
        os.chmod(path, 0o600)
    except OSError:
        pass


# ----------------------------------------------------------------------------- the server's own secrets
def new_secret(length: int = 40) -> str:
    return secrets.token_urlsafe(length)[:length].replace("-", "x").replace("_", "y")


def hash_password(password: str, salt: str) -> str:
    return hashlib.scrypt(password.encode("utf-8"), salt=bytes.fromhex(salt), n=1 << 14, r=8, p=1, dklen=32).hex()


# ---- Ed25519 (RFC 8032), pure Python: signs and checks the «ربط» move order (no crypto package needed) ----
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


def _ed_secret(seed: bytes) -> tuple[int, bytes]:
    h = hashlib.sha512(seed).digest()
    a = int.from_bytes(h[:32], "little")
    a = (a & ((1 << 254) - 8)) | (1 << 254)
    return a, h[32:]


def ed_public(seed: bytes) -> bytes:
    return _ed_encode(_ed_mul(_ed_secret(seed)[0], _ED_B))


def ed_sign(seed: bytes, message: bytes) -> bytes:
    a, prefix = _ed_secret(seed)
    public = _ed_encode(_ed_mul(a, _ED_B))
    r = int.from_bytes(hashlib.sha512(prefix + message).digest(), "little") % _ED_L
    big_r = _ed_encode(_ed_mul(r, _ED_B))
    k = int.from_bytes(hashlib.sha512(big_r + public + message).digest(), "little") % _ED_L
    return big_r + ((r + k * a) % _ED_L).to_bytes(32, "little")


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


# ---- «الربط»: moving the apps to a new server ----
# A key pair made from the control panel's password alone (the same on any server with the same password): the
# apps keep its public half (sent with every check), and a move order signed with it is the only one they follow.
# Its private half is never kept: it is made again from the password when «ربط» is pressed.
# The order travels through a public relay (ntfy.sh), encrypted, on a topic named from the public key; apps that
# cannot reach their server read it there, check the signature, then move.
MOVE_SALT = b"groups-control-move-v1"
MOVE_RELAY = (os.environ.get("CONTROL_RELAY") or "https://ntfy.sh").rstrip("/")
MOVE_REPEAT_HOURS = 6                 # the order is sent again this often (the relay keeps messages ~12 h)
MOVE_REPEAT_DAYS = 90                 # and for this long, for phones that were off


def move_seed(password: str) -> bytes:
    return hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), MOVE_SALT, 600_000, 32)


def move_topic(public: bytes) -> str:
    return "gg" + hashlib.sha256(b"gg-relay|" + public).hexdigest()[:30]


def move_code(public_hex: str) -> str:
    """A short code for the owner to compare between the old and the new server (same password, same code)."""
    if not public_hex:
        return ""
    digest = hashlib.sha256(b"gg-code|" + bytes.fromhex(public_hex)).hexdigest()[:8].upper()
    return digest[:4] + "-" + digest[4:]


def _move_stream(public: bytes, nonce: bytes, length: int) -> bytes:
    key = hashlib.sha256(b"gg-move-enc|" + public).digest()
    out = bytearray()
    counter = 0
    while len(out) < length:
        out += hashlib.sha256(key + nonce + counter.to_bytes(4, "big")).digest()
        counter += 1
    return bytes(out[:length])


def move_seal(seed: bytes, link: str, at: int) -> str:
    public = ed_public(seed)
    signature = ed_sign(seed, f"gg-move|{link}|{at}".encode("utf-8"))
    plain = json.dumps({"v": 1, "link": link, "at": at, "sig": signature.hex()}, separators=(",", ":")).encode("utf-8")
    nonce = secrets.token_bytes(16)
    body = bytes(a ^ b for a, b in zip(plain, _move_stream(public, nonce, len(plain))))
    return "ggmv1." + base64.urlsafe_b64encode(nonce + body).decode("ascii")


def move_publish(record: str, public: bytes) -> str:
    """Puts the order on the relay; "" when done, else why not."""
    try:
        request_ = urllib.request.Request(f"{MOVE_RELAY}/{move_topic(public)}", data=record.encode("ascii"), method="POST",
                                          headers={"User-Agent": "groups-control/1.0", "Content-Type": "text/plain"})
        with urllib.request.urlopen(request_, timeout=20) as answer:
            answer.read(4096)
        return ""
    except Exception as exc:
        return f"{type(exc).__name__}: {str(exc)[:120]}"


def load_move() -> dict:
    data = read_private_json(MOVE_PATH) or {}
    return data if isinstance(data, dict) else {}


def republish_moves_in_background() -> None:
    while True:
        move = load_move()
        now = int(time.time())
        if move.get("record") and move.get("public") and now < int(move.get("until") or 0) \
                and now - int(move.get("published") or 0) >= MOVE_REPEAT_HOURS * 3600 - 60:
            if not move_publish(move["record"], bytes.fromhex(move["public"])):
                move["published"] = now
                write_private_json(MOVE_PATH, move)
        time.sleep(600)


# ---- «نسخة احتياطية»: all the server's data in one file, encrypted with the control panel's password ----
BACKUP_FILES = ("secrets.json", "codes.json", "keys.json", "usage.json", "notices.json", "acts.json", "support.json",
                "move.json", "prices.json", "welcomed.json", "lifetime.json", "pace.json", "history.json", "prompt.json",
                "devices.json", "server.crt", "server.key")
BACKUP_MAGIC = b"GGBAK1"


def _backup_keys(password: str, salt: bytes) -> tuple[bytes, bytes]:
    key = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, 300_000, 64)
    return key[:32], key[32:]


def backup_pack(password: str) -> bytes:
    files = {}
    for name in BACKUP_FILES:
        path = DATA_DIR / name
        if path.is_file():
            files[name] = base64.b64encode(path.read_bytes()).decode("ascii")
    plain = json.dumps({"v": 1, "at": int(time.time()), "files": files}).encode("utf-8")
    salt, nonce = secrets.token_bytes(16), secrets.token_bytes(16)
    enc_key, mac_key = _backup_keys(password, salt)
    body = bytes(a ^ b for a, b in zip(plain, key_stream(enc_key, nonce, len(plain))))
    head = BACKUP_MAGIC + salt + nonce
    return head + body + hmac.new(mac_key, head + body, hashlib.sha256).digest()


def backup_unpack(blob: bytes, password: str) -> dict:
    """The files in a backup, or raises ValueError with the reason for the owner."""
    if not blob.startswith(BACKUP_MAGIC) or len(blob) < len(BACKUP_MAGIC) + 32 + 32:
        raise ValueError("هذا ليس ملف نسخة احتياطية من لوحة التحكّم.")
    salt, nonce = blob[6:22], blob[22:38]
    body, mac = blob[38:-32], blob[-32:]
    enc_key, mac_key = _backup_keys(password, salt)
    if not hmac.compare_digest(hmac.new(mac_key, blob[:38] + body, hashlib.sha256).digest(), mac):
        raise ValueError("كلمة المرور لا تطابق كلمة مرور هذه النسخة، أو الملف تالف.")
    plain = bytes(a ^ b for a, b in zip(body, key_stream(enc_key, nonce, len(body))))
    data = json.loads(plain.decode("utf-8"))
    files = {name: base64.b64decode(value) for name, value in (data.get("files") or {}).items() if name in BACKUP_FILES}
    if "secrets.json" not in files or "server.crt" not in files or "server.key" not in files:
        raise ValueError("النسخة ناقصة: لا تحمل أسرار الخادم وشهادته.")
    return {"at": int(data.get("at") or 0), "files": files}


def load_secrets() -> dict:
    data = read_private_json(SECRETS_PATH) or {}
    changed = False
    if not data.get("seal_secret"):
        data["seal_secret"] = secrets.token_hex(32); changed = True
    if not data.get("token_secret"):
        data["token_secret"] = secrets.token_hex(32); changed = True
    if not data.get("session_secret"):
        data["session_secret"] = secrets.token_hex(32); changed = True
    if not data.get("api_secret") or not re.fullmatch(r"[A-Za-z0-9_\-]{16,64}", data["api_secret"]):
        data["api_secret"] = new_secret(40); changed = True
    if not data.get("admin_path") or not re.fullmatch(r"[A-Za-z0-9_\-]{16,64}", data["admin_path"]):
        data["admin_path"] = new_secret(40); changed = True
    if not data.get("app_dl") or not re.fullmatch(r"[A-Za-z0-9_\-]{16,64}", data["app_dl"]):
        data["app_dl"] = new_secret(24); changed = True       # (the app's download link: fixed, kept in backups)
    forced = os.environ.get("CONTROL_ADMIN_PASSWORD")
    if forced:
        data["admin_salt"] = secrets.token_hex(16)
        data["admin_hash"] = hash_password(forced, data["admin_salt"])
        data["admin_plain_once"] = ""
        changed = True
    if not data.get("admin_hash"):
        made = new_secret(12)
        data["admin_salt"] = secrets.token_hex(16)
        data["admin_hash"] = hash_password(made, data["admin_salt"])
        data["admin_plain_once"] = made            # printed once on first start, then forgotten
        changed = True
    if forced or data.get("admin_plain_once"):
        # «الربط»: the public half of the key made from the password (see move_seed); apps keep it.
        data["move_public"] = ed_public(move_seed(forced or data["admin_plain_once"])).hex()
        changed = True
    if changed:
        write_private_json(SECRETS_PATH, data)
    return data


SECRETS = load_secrets()


# ----------------------------------------------------------------------------- sealing keys at rest
def seal_material() -> bytes:
    return hashlib.sha256(b"control-seal|" + SECRETS["seal_secret"].encode("utf-8")).digest()


def key_stream(material: bytes, nonce: bytes, length: int) -> bytes:
    out = bytearray()
    counter = 0
    while len(out) < length:
        out += hashlib.sha256(material + nonce + counter.to_bytes(4, "big")).digest()
        counter += 1
    return bytes(out[:length])


def seal_key(text: str) -> str:
    if not text:
        return ""
    material, nonce, raw = seal_material(), os.urandom(16), text.encode("utf-8")
    body = bytes(a ^ b for a, b in zip(raw, key_stream(material, nonce, len(raw))))
    tag = hmac.new(material, nonce + body, hashlib.sha256).digest()[:16]
    return "s1:" + base64.b64encode(nonce + tag + body).decode("ascii")


def open_key(sealed) -> str:
    if not isinstance(sealed, str) or not sealed.startswith("s1:"):
        return ""
    try:
        data = base64.b64decode(sealed[3:], validate=True)
    except ValueError:
        return ""
    if len(data) <= 32:
        return ""
    nonce, tag, body = data[:16], data[16:32], data[32:]
    material = seal_material()
    if not hmac.compare_digest(tag, hmac.new(material, nonce + body, hashlib.sha256).digest()[:16]):
        return ""
    try:
        return bytes(a ^ b for a, b in zip(body, key_stream(material, nonce, len(body)))).decode("utf-8")
    except UnicodeDecodeError:
        return ""


# ----------------------------------------------------------------------------- access codes
def load_codes() -> list:
    data = read_private_json(CODES_PATH) or {}
    codes = data.get("codes")
    return codes if isinstance(codes, list) else []


def save_codes(codes: list) -> None:
    write_private_json(CODES_PATH, {"version": 1, "codes": codes})


def make_code() -> str:
    # Easy to read and type: letters and digits without the ones people confuse (0/O, 1/I/L).
    alphabet = "ABCDEFGHJKMNPQRSTUVWXYZ23456789"
    return "-".join("".join(secrets.choice(alphabet) for _ in range(4)) for _ in range(3))


def find_code(entered: str) -> dict | None:
    entered = re.sub(r"[^A-Za-z0-9]", "", str(entered or "")).upper()
    if not entered:
        return None
    with LOCK:
        for row in load_codes():
            if re.sub(r"[^A-Za-z0-9]", "", row.get("code", "")).upper() == entered:
                return row
    return None


# ----------------------------------------------------------------------------- the keys and which one writes
def load_keys() -> dict:
    data = read_private_json(KEYS_PATH) or {}
    return {
        "engine": data.get("engine") if data.get("engine") in ("gemini", "claude") else "gemini",
        # Gemini goes either straight to Google ("google", the default) or through OpenRouter ("openrouter")
        # with the owner's OpenRouter key and an OpenRouter model id.
        "gemini_provider": data.get("gemini_provider") if data.get("gemini_provider") in ("google", "openrouter") else "google",
        "gemini_sealed": data.get("gemini_sealed") or "",
        "gemini_model": data.get("gemini_model") or "",
        "openrouter_sealed": data.get("openrouter_sealed") or "",
        "openrouter_model": data.get("openrouter_model") or "",
        "claude_sealed": data.get("claude_sealed") or "",
        "claude_model": data.get("claude_model") or "",
    }


def save_keys(keys: dict) -> None:
    write_private_json(KEYS_PATH, {"version": 1, **keys})


# ----------------------------------------------------------------------------- what each user (and account) used
COST_PER_COMMENT = 0.01            # التكلفة لكل تعليق (قبل «أسعار الخدمات»، وسعره الأول فيها)

# «أسعار الخدمات»: what each service costs the user, as the owner sets them: a comment, and each successful
# repost, like and bookmark. A cost is counted at the price of its time (a new price does not change what was
# counted before). At first: a comment as before, the others free.
SERVICES = ("repost", "like", "bookmark", "comment")
PRICES_PATH = DATA_DIR / "prices.json"


def load_prices() -> dict:
    data = read_private_json(PRICES_PATH) or {}
    prices = {"repost": 0.0, "like": 0.0, "bookmark": 0.0, "comment": COST_PER_COMMENT}
    for name in SERVICES:
        try:
            value = float(data.get(name))
        except (TypeError, ValueError):
            continue
        if 0 <= value <= 100:
            prices[name] = round(value, 4)
    return prices


def save_prices(prices: dict, welcome: float | None = None) -> None:
    welcome = load_welcome() if welcome is None else welcome
    write_private_json(PRICES_PATH, {"version": 1, **{name: round(float(prices.get(name) or 0), 4) for name in SERVICES},
                                     "welcome": round(float(welcome), 2)})


# «رصيد الحساب الجديد»: whoever makes an account in the app starts with this trial balance ($1 until the owner sets
# another in «أسعار الخدمات»; 0 gives none). Once per phone: a phone that already had an account or a code, or got
# it before (its account deleted since), starts a new account at $0, so a new account is not a new $1 each time.
WELCOME_DEFAULT = 1.0
WELCOME_NOTE = "رصيد تجريبي (حساب جديد)"
WELCOMED_PATH = DATA_DIR / "welcomed.json"


def load_welcome() -> float:
    data = read_private_json(PRICES_PATH) or {}
    try:
        value = float(data.get("welcome", WELCOME_DEFAULT))
    except (TypeError, ValueError):
        return WELCOME_DEFAULT
    return round(value, 2) if 0 <= value <= 100 else WELCOME_DEFAULT


# «الأجهزة»: a user (a code or an account) on any number of phones (each that signs in with it is added to its
# phones), or on one phone only, the first, until the owner frees it («تحرير الأجهزة»), as it was before.
DEVICES_PATH = DATA_DIR / "devices.json"
DEVICES_KEPT = 50                   # the phones remembered after the first (the oldest of them goes beyond this)


def one_device() -> bool:
    data = read_private_json(DEVICES_PATH) or {}
    return bool(data.get("one_device"))


def devices_of(row: dict) -> list:
    """The phones this user signed in on: the first one, then the others."""
    found = []
    for device in [row.get("bound_device") or ""] + list(row.get("devices") or []):
        if device and device not in found:
            found.append(device)
    return found


def allowed_devices(row: dict) -> list:
    """The phones this user may work on now (one only, the first, when «جهاز واحد» is chosen)."""
    if one_device():
        return [row["bound_device"]] if row.get("bound_device") else []
    return devices_of(row)


def add_device(row: dict, device: str) -> None:
    """(Under LOCK.) This phone signs in with this user: its first one, or one more of them."""
    if not row.get("bound_device"):
        row["bound_device"] = device
        return
    if device == row["bound_device"]:
        return
    others = [item for item in (row.get("devices") or []) if item and item != device and item != row["bound_device"]]
    row["devices"] = (others + [device])[-DEVICES_KEPT:]


def phone_of(body: dict) -> str:
    """The phone as Android knows it for the app (its ANDROID_ID, hashed by the app): the same after the app is deleted
    and installed again, or its data cleared. "" from an app too old to send it."""
    value = str(body.get("hw") or "").strip().lower()
    return value if re.fullmatch(r"[0-9a-f]{32}", value) else ""


def account_made_on(codes: list, phone: str) -> dict | None:
    """The account already made on this phone (one per phone), if it is still there."""
    if not phone:
        return None
    return next((row for row in codes if row.get("account") and row.get("hw") == phone), None)


def take_welcome(codes: list, device: str, phone: str = "") -> float:
    """(Under LOCK, as an account is made on this phone.) Its trial balance, or 0: an app too old to say which phone it
    is on (it could be deleted and installed again for another), or a phone that had it already or signed in before."""
    amount = load_welcome()
    if amount <= 0 or not phone or any(device in devices_of(row) for row in codes):
        return 0.0
    keys = [hashlib.sha256(("welcome-phone|" + phone).encode("utf-8")).hexdigest()[:32]]
    if device:
        keys.append(hashlib.sha256(("welcome|" + device).encode("utf-8")).hexdigest()[:32])
    data = read_private_json(WELCOMED_PATH) or {}
    phones = data.get("devices") if isinstance(data.get("devices"), list) else []
    if any(key in phones for key in keys):
        return 0.0
    phones.extend(keys)
    write_private_json(WELCOMED_PATH, {"devices": phones[-100000:]})
    return amount


# «سرعة التنفيذ»: how long the app takes to type a whole comment, how long it waits between one button press and the
# next, and how long once a tweet has loaded before its first press, in seconds (each time at random between «من»
# and «إلى»). Set in the users tab, given to every
# app with each task's start, so every user's next task goes at it.
PACE_PATH = DATA_DIR / "pace.json"
PACE_DEFAULTS = {"typing": (3.0, 8.0), "gap": (0.3, 1.0), "settle": (0.6, 1.5), "in_page": (1, 3)}
PACE_LIMITS = {"typing": 60.0, "gap": 10.0, "settle": 10.0, "in_page": 50}
# ("in_page": how many tweets the app opens inside the same X page, without loading it in full, before the next
# one is loaded in full: whole numbers, from 1)


# «الدفع عبر Binance»: the app's «شحن رصيد» shows the owner's Binance Pay ID; a user sends it dollar coins (USDT),
# then types the amount and the transfer's Order ID. With the owner's Binance API key (reading only), this server
# finds that transfer in the owner's Binance Pay history: received (not sent), in a dollar coin, of the amount typed,
# and not used before; then the user's balance is topped up by what arrived, at once, with a line in its «سجل
# الرصيد» (and a note to the owner in «رسائل العملاء»). Without a key, the request goes to «رسائل العملاء» for the
# owner to check by hand. The key and its secret stay in this server's private folder; the panel never shows them.
BINANCE_PATH = DATA_DIR / "binance.json"
TOPUPS_PATH = DATA_DIR / "topups.json"          # the transfers used already: each tops up one balance, once
BINANCE_API = os.environ.get("CONTROL_BINANCE_API", "https://api.binance.com").rstrip("/")
TOPUP_COINS = ("USDT", "USDC", "FDUSD")         # counted as dollars, one for one
TOPUP_LOOKBACK_DAYS = 30
TOPUP_TRIES_PER_HOUR = 12
TOPUP_MAX = 10000.0
_topup_tries: dict[str, list] = {}


def load_binance() -> dict:
    data = read_private_json(BINANCE_PATH) or {}
    return {"binance_id": re.sub(r"\D", "", str(data.get("binance_id") or ""))[:20],
            "note": str(data.get("note") or "").strip()[:500],
            "key": str(data.get("key") or "").strip()[:128], "secret": str(data.get("secret") or "").strip()[:128]}


def public_payment() -> dict:
    """What the app shows in «شحن رصيد» (never the key)."""
    data = load_binance()
    return {"binance_id": data["binance_id"], "note": data["note"], "auto": bool(data["key"] and data["secret"]),
            "coins": list(TOPUP_COINS)}


class BinanceError(RuntimeError):
    pass


def binance_history(key: str, secret: str) -> list:
    """The owner's Binance Pay transactions of the last TOPUP_LOOKBACK_DAYS (GET /sapi/v1/pay/transactions)."""
    now = int(time.time() * 1000)
    query = urllib.parse.urlencode({"startTime": now - TOPUP_LOOKBACK_DAYS * 86_400_000, "endTime": now, "limit": 100,
                                    "recvWindow": 10000, "timestamp": now})
    signature = hmac.new(secret.encode("utf-8"), query.encode("utf-8"), hashlib.sha256).hexdigest()
    request_ = urllib.request.Request(f"{BINANCE_API}/sapi/v1/pay/transactions?{query}&signature={signature}",
                                      headers={"X-MBX-APIKEY": key, "User-Agent": "bot-grob-control"})
    try:
        with urllib.request.urlopen(request_, timeout=15) as response:
            data = json.loads(response.read().decode("utf-8") or "{}")
    except urllib.error.HTTPError as exc:
        try:
            said = json.loads(exc.read().decode("utf-8") or "{}")
        except (ValueError, OSError):
            said = {}
        raise BinanceError(f"Binance: {said.get('msg') or exc.reason} ({said.get('code', exc.code)})") from exc
    except (urllib.error.URLError, OSError, ValueError) as exc:
        raise BinanceError(f"تعذّر الوصول إلى Binance ({type(exc).__name__}).") from exc
    if str(data.get("code")) not in ("000000", "0") and data.get("success") is not True:
        raise BinanceError(f"Binance: {data.get('message') or data.get('msg') or 'جواب غير متوقع'}")
    rows = data.get("data")
    return [row for row in rows if isinstance(row, dict)] if isinstance(rows, list) else []


def _tx_key(value) -> str:
    return re.sub(r"[^A-Z0-9]", "", str(value or "").upper())


def tx_matches(tx_id, typed: str) -> bool:
    """The Order ID the user typed is this transfer's (as Binance writes it, with or without its letters before)."""
    a, b = _tx_key(tx_id), _tx_key(typed)
    if len(b) < 6 or not a:
        return False
    return a == b or (len(b) >= 8 and a.endswith(b)) or (len(a) >= 8 and b.endswith(a))


def load_topups() -> dict:
    data = read_private_json(TOPUPS_PATH) or {}
    return {"used": data.get("used") if isinstance(data.get("used"), dict) else {}}


def topup_amount(raw) -> float:
    text = str(raw or "").strip().translate(str.maketrans("٠١٢٣٤٥٦٧٨٩۰۱۲۳۴۵۶۷۸۹٫،", "01234567890123456789.."))
    try:
        return round(float(re.sub(r"[^\d.]", "", text) or "0"), 2)
    except ValueError:
        return 0.0


def load_pace() -> dict:
    data = read_private_json(PACE_PATH) or {}
    out = {}
    for key, default in PACE_DEFAULTS.items():
        try:
            low, high = (round(float(value), 2) for value in data.get(key))
        except (TypeError, ValueError):
            low, high = default
        if key == "in_page":
            low, high = int(low), int(high)
        out[key] = [low, high] if (1 if key == "in_page" else 0) <= low <= high <= PACE_LIMITS[key] else list(default)
    out["in_page_on"] = data.get("in_page_on") is True     # «الفتح السريع»: off unless turned on in the panel
    return out


def form_dollars(raw) -> float:
    """A dollar amount typed in the panel (Arabic digits, $ and spaces are fine; empty is 0), or -1 if not a number."""
    raw = str(raw or "").strip().translate(str.maketrans("٠١٢٣٤٥٦٧٨٩٫،", "0123456789..")).replace("$", "").replace(" ", "")
    try:
        return float(raw or "0")
    except ValueError:
        return -1.0


def _with_cost(row: dict, count_key: str) -> dict:
    """Usage counted before the prices had its comments only, at the old fixed price: its cost is set from that once."""
    if "cost" not in row:
        row["cost"] = round(int(row.get(count_key) or 0) * COST_PER_COMMENT, 4)
    return row


def load_usage() -> dict:
    data = read_private_json(USAGE_PATH) or {}
    return data if isinstance(data, dict) else {}


def record_comment(code_id: str, account: str, name: str, price: float = COST_PER_COMMENT) -> None:
    """Count one written comment, at its price, against this code and the X account that asked for it."""
    account = (account or "—")[:48]
    with LOCK:
        usage = load_usage()
        code = _with_cost(usage.setdefault(code_id, {"total": 0, "accounts": {}}), "total")
        code.setdefault("accounts", {})
        code["total"] = int(code.get("total") or 0) + 1
        code["cost"] = round(float(code.get("cost") or 0) + price, 4)
        services = code.setdefault("services", {})
        services["comment"] = int(services.get("comment") or 0) + 1
        who = _with_cost(code["accounts"].setdefault(account, {"n": 0, "name": ""}), "n")
        who["n"] = int(who.get("n") or 0) + 1
        who["cost"] = round(float(who.get("cost") or 0) + price, 4)
        if name:
            who["name"] = name[:40]
        write_private_json(USAGE_PATH, usage)
        history_add({"comment": 1})


def record_actions(code_id: str, items: list, prices: dict) -> float:
    """Successful reposts, likes and bookmarks the app reports: counted, with their cost at today's prices. A report
    the app sends again (its answer was lost) has the same id and is not counted twice. Returns the cost added."""
    added = 0.0
    with LOCK:
        usage = load_usage()
        code = _with_cost(usage.setdefault(code_id, {"total": 0, "accounts": {}}), "total")
        code.setdefault("accounts", {})
        services = code.setdefault("services", {})
        seen = code.get("seen") if isinstance(code.get("seen"), list) else []
        known = set(seen)
        for item in items:
            report = str(item.get("id") or "")[:40]
            if report and report in known:
                continue
            done = item.get("done") if isinstance(item.get("done"), dict) else {}
            account = (str(item.get("account") or "") or "—")[:48]
            who = _with_cost(code["accounts"].setdefault(account, {"n": 0, "name": ""}), "n")
            acts = who.setdefault("acts", {})
            for action in ("repost", "like", "bookmark"):
                try:
                    count = max(0, min(1000, int(done.get(action) or 0)))
                except (TypeError, ValueError):
                    count = 0
                if not count:
                    continue
                cost = count * float(prices.get(action) or 0)
                services[action] = int(services.get(action) or 0) + count
                acts[action] = int(acts.get(action) or 0) + count
                who["cost"] = round(float(who.get("cost") or 0) + cost, 4)
                code["cost"] = round(float(code.get("cost") or 0) + cost, 4)
                added += cost
            if item.get("name"):
                who["name"] = str(item.get("name"))[:40]
            if report:
                seen.append(report)
                known.add(report)
        code["seen"] = seen[-3000:]
        write_private_json(USAGE_PATH, usage)
    return round(added, 4)


# «منذ البداية»: what «تصفير التكلفة» clears is kept here, so the panel can show all the comments and all the cost
# since the beginning under the numbers now (with the users deleted since, whose counts stay in usage.json).
LIFETIME_PATH = DATA_DIR / "lifetime.json"


def _lifetime_cleared() -> dict:
    data = read_private_json(LIFETIME_PATH) or {}
    try:
        return {"comments": int(data.get("comments") or 0), "cost": float(data.get("cost") or 0)}
    except (TypeError, ValueError):
        return {"comments": 0, "cost": 0.0}


def _add_up(totals: dict, rows) -> dict:
    for row in rows:
        if isinstance(row, dict):
            totals["comments"] += int(row.get("total") or 0)
            totals["cost"] += float(_with_cost(dict(row), "total").get("cost") or 0)
    return totals


def _keep_cleared(rows) -> None:
    """(Under LOCK.) Counts about to be cleared go into the totals since the beginning."""
    totals = _add_up(_lifetime_cleared(), rows)
    write_private_json(LIFETIME_PATH, {"version": 1, "comments": totals["comments"], "cost": round(totals["cost"], 4)})


def lifetime_totals(usage: dict | None = None) -> dict:
    """All the comments and all the cost since the beginning: what is counted now plus what was cleared."""
    totals = _add_up(_lifetime_cleared(), (load_usage() if usage is None else usage).values())
    return {"comments": totals["comments"], "cost": round(totals["cost"], 2)}


def reset_usage(code_id: str) -> None:
    """تصفير تكلفة رمز واحد (ويبقى محسوبًا في «منذ البداية»)."""
    with LOCK:
        usage = load_usage()
        if code_id in usage:
            _keep_cleared([usage[code_id]])
            usage.pop(code_id, None)
            write_private_json(USAGE_PATH, usage)


def reset_all_usage() -> None:
    """تصفير كل التكاليف (ويبقى محسوبًا في «منذ البداية»)."""
    with LOCK:
        _keep_cleared(load_usage().values())
        write_private_json(USAGE_PATH, {})


def _cost(row: dict, count_key: str) -> float:
    if "cost" in row:
        return round(float(row.get("cost") or 0), 2)
    return round(int(row.get(count_key) or 0) * COST_PER_COMMENT, 2)


def usage_of(code_id: str, data: dict | None = None) -> dict:
    row = (data if data is not None else load_usage()).get(code_id) or {"total": 0, "accounts": {}}
    accounts = sorted(
        ({"id": key, "name": value.get("name") or "", "n": int(value.get("n") or 0), "cost": _cost(value, "n")}
         for key, value in (row.get("accounts") or {}).items() if isinstance(value, dict)),
        key=lambda item: (-item["cost"], -item["n"]))
    total = int(row.get("total") or 0)
    return {"total": total, "cost": _cost(row, "total"), "accounts": accounts}


def usage_by_account(code_id: str) -> dict:
    """What the app shows its user: the comments of their code and their cost, by X account. Accounts go by
    their @name: one signed in again (in the app, or after the app was installed again) is the same account,
    whatever its new key; one whose name was never read stays on its own."""
    row = load_usage().get(code_id) or {"total": 0, "accounts": {}}
    merged: dict[str, dict] = {}
    for key, value in (row.get("accounts") or {}).items():
        if not isinstance(value, dict):
            continue
        name = str(value.get("name") or "").strip().lstrip("@")[:40]
        slot = merged.setdefault(name.lower() if name else "id:" + str(key), {"name": name, "n": 0, "cost": 0.0})
        slot["n"] += int(value.get("n") or 0)
        slot["cost"] += _cost(value, "n")
        if name and not slot["name"]:
            slot["name"] = name
    accounts = sorted(
        ({"name": slot["name"], "n": slot["n"], "cost": round(slot["cost"], 2)} for slot in merged.values()),
        key=lambda item: (-item["cost"], -item["n"]))
    total = int(row.get("total") or 0)
    prices = load_prices()
    return {"total": total, "cost": _cost(row, "total"), "price": prices["comment"], "prices": prices, "accounts": accounts}


# ----------------------------------------------------------------------------- how each user pays
# «آجل»: the comments are counted and the owner collects their cost later (as before). «مسبق»: the user has a
# balance the owner tops up (or gives as a trial); each service takes its price from it («أسعار الخدمات»), and with
# too little left it is not done. Any user can be either; one who makes an account in the app starts «مسبق».
PAY_LATER, PAY_PREPAID = "later", "prepaid"
LEDGER_KEEP = 100


def pay_of(row: dict) -> str:
    return PAY_PREPAID if row.get("pay") == PAY_PREPAID else PAY_LATER


def balance_of(row: dict) -> float:
    try:
        return round(float(row.get("balance") or 0), 4)
    except (TypeError, ValueError):
        return 0.0


def money(amount: float) -> str:
    """$1.25 ($0.035 when it is not whole cents), and −$0.40 for a balance below zero (a debt the next top-up pays
    first), as the panel's usd() writes it. Kept whole inside Arabic text (else it shows as 1.25$ or 0.40$−)."""
    amount = round(float(amount or 0), 4)
    whole = abs(abs(amount) * 100 - round(abs(amount) * 100)) < 1e-6
    text = f"{abs(amount):.2f}" if whole else f"{abs(amount):.4f}".rstrip("0")
    return "\u2066" + ("−$" if amount < 0 else "$") + text + "\u2069"


# A «مسبق» user cannot start a task without balance for its paid services, but a task that started goes on to its
# end even when the balance runs out on the way (the balance may go below zero; the next top-up pays that first).
# At its start the app gets a pass signed here, which lets that task's comments through.
TASK_PASS_HOURS = 12


def make_task_pass(code_id: str) -> str:
    until = int(time.time()) + TASK_PASS_HOURS * 3600
    sig = hmac.new(SECRETS["token_secret"].encode("utf-8"), f"task|{code_id}|{until}".encode("utf-8"), hashlib.sha256).hexdigest()[:32]
    return f"{until}.{sig}"


def task_pass_ok(code_id: str, value) -> bool:
    try:
        until_text, sig = str(value or "").split(".", 1)
        until = int(until_text)
    except ValueError:
        return False
    good = hmac.new(SECRETS["token_secret"].encode("utf-8"), f"task|{code_id}|{until}".encode("utf-8"), hashlib.sha256).hexdigest()[:32]
    return until > time.time() and hmac.compare_digest(sig, good)


def take_comment_price(code_id: str, price: float = COST_PER_COMMENT, in_task: bool = False) -> str:
    """Before a prepaid user's comment its price is taken from the balance at once (so two comments at the same
    moment cannot both spend the last cent). "" when it may go ahead, else why not. A «آجل» user always may, and
    so does a comment of a task that started with balance (its pass): the balance may then go below zero."""
    with LOCK:
        codes = load_codes()
        row = next((item for item in codes if item.get("id") == code_id), None)
        if row is None or pay_of(row) != PAY_PREPAID:
            return ""
        balance = balance_of(row)
        if price <= 0:
            return ""
        if balance + 1e-9 < price and not in_task:
            return f"رصيدك لا يكفي لكتابة التعليقات (الرصيد {money(balance)}). اطلب من صاحب البرنامج شحن رصيدك."
        row["balance"] = round(balance - price, 4)
        save_codes(codes)
    return ""


def give_back_comment_price(code_id: str, price: float = COST_PER_COMMENT) -> None:
    """The comment was not written after all: its price goes back to the balance."""
    with LOCK:
        codes = load_codes()
        row = next((item for item in codes if item.get("id") == code_id), None)
        if row is not None and pay_of(row) == PAY_PREPAID and price > 0:
            row["balance"] = round(balance_of(row) + price, 4)
            save_codes(codes)


# ----------------------------------------------------------------------------- accounts (a name and a password)
# A user may also come in with an account made in the app instead of a code. Inside it is a code like any other
# (the same row: bound to one phone, stopped and released the same way), with a name and a password to sign in.
ACCOUNT_NAME = re.compile(r"^[\w.\-]{3,24}$")
PASSWORD_ROUNDS = 200_000
_signin_failures: dict[str, list] = {}
_signups: dict[str, list] = {}
_signin_lock = threading.Lock()


def account_pw_hash(password: str, salt: bytes | None = None) -> str:
    salt = salt or secrets.token_bytes(16)
    digest = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, PASSWORD_ROUNDS)
    return f"pbkdf2${PASSWORD_ROUNDS}${salt.hex()}${digest.hex()}"


def account_pw_ok(password: str, stored: str) -> bool:
    try:
        kind, rounds, salt, digest = str(stored).split("$")
        if kind != "pbkdf2":
            return False
        mine = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), bytes.fromhex(salt), int(rounds)).hex()
        return hmac.compare_digest(mine, digest)
    except (ValueError, TypeError):
        return False


_NO_ONE = account_pw_hash(secrets.token_hex(8))      # (a name nobody has costs the same time as a wrong password)


def account_key(name) -> str:
    return str(name or "").strip().casefold()


def account_row(codes: list, name: str) -> dict | None:
    key = account_key(name)
    return next((row for row in codes if key and account_key((row.get("account") or {}).get("user")) == key), None)


def _recent(times: list, seconds: float) -> list:
    now = time.time()
    return [moment for moment in times if now - moment < seconds]


def signin_blocked(key: str) -> bool:
    """Five wrong passwords in 15 minutes for one name (or twenty from one address): wait."""
    with _signin_lock:
        for slot, limit in ((key, 5), ("ip:" + (request.remote_addr or ""), 20)):
            _signin_failures[slot] = _recent(_signin_failures.get(slot, []), 900)
            if len(_signin_failures[slot]) >= limit:
                return True
    return False


def signin_failed(key: str) -> None:
    with _signin_lock:
        for slot in (key, "ip:" + (request.remote_addr or "")):
            _signin_failures.setdefault(slot, []).append(time.time())


def signup_allowed() -> bool:
    """At most five new accounts an hour from one address."""
    address = request.remote_addr or ""
    with _signin_lock:
        _signups[address] = _recent(_signups.get(address, []), 3600)
        if len(_signups[address]) >= 5:
            return False
        _signups[address].append(time.time())
    return True


# ----------------------------------------------------------------------------- what each user's app did
# أرقام التنفيذ التي يعرضها التطبيق في رأس صفحته (الرتويت والإعجاب والمرجعية والتعليقات) لكل حساب X، كما
# يرسلها التطبيق: قيمها كاملة في كل مرة (لا زيادات)، فتُستبدل ولا تُعدّ مرتين.
ACT_NAMES = ("repost", "like", "bookmark", "comment")
ACT_MAX_ACCOUNTS = 10


def load_acts() -> dict:
    data = read_private_json(ACTS_PATH) or {}
    return data if isinstance(data, dict) else {}


# «الرسم البياني»: the activity of all the users together, hour by hour (kept HISTORY_HOURS), from the day this server
# started keeping it: reposts, likes and bookmarks as they grow in the apps' reports, comments as they are written.
HISTORY_PATH = DATA_DIR / "history.json"
HISTORY_HOURS = 24 * 90
HISTORY_KEYS = ("repost", "like", "bookmark", "comment")


def history_add(grown: dict) -> None:
    """(Under LOCK.) Add to this hour's counts."""
    if not any(int(grown.get(name) or 0) for name in HISTORY_KEYS):
        return
    data = read_private_json(HISTORY_PATH) or {}
    hours = data.get("hours") if isinstance(data.get("hours"), dict) else {}
    key = str(int(time.time() // 3600))
    row = (list(hours.get(key)) if isinstance(hours.get(key), list) else []) + [0] * 4
    hours[key] = [int(row[i] or 0) + int(grown.get(name) or 0) for i, name in enumerate(HISTORY_KEYS)]
    if len(hours) > HISTORY_HOURS:
        for old in sorted(hours, key=lambda item: int(item) if str(item).isdigit() else 0)[:-HISTORY_HOURS]:
            hours.pop(old, None)
    write_private_json(HISTORY_PATH, {"version": 1, "since": int(data.get("since") or time.time()), "hours": hours})


ACTS_PHONES_KEPT = 60                 # a user's phones whose numbers are kept apart (the oldest is folded into "kept")


def save_acts_of(code_id: str, accounts: list, device: str = "", first_device: str = "") -> None:
    """The app's numbers now, for each of its X accounts: they replace what this phone sent before (each phone of the
    user has its own: one phone's numbers never replace another's). What the app no longer has (it was deleted and
    set up again, or its data cleared: an account gone from its numbers, or one counting again from zero) is kept
    here ("kept"), so the panel's numbers never go down because of the phone. first_device: the user's first phone,
    whose numbers were all the user's before (kept as that phone's)."""
    clean = {}
    for row in accounts[:ACT_MAX_ACCOUNTS]:
        if not isinstance(row, dict):
            continue
        key = re.sub(r"[^A-Za-z0-9]", "", str(row.get("id") or ""))[:48]
        if not key:
            continue
        name = str(row.get("name") or "").strip().lstrip("@")
        if not re.fullmatch(r"[A-Za-z0-9_]{1,15}", name):
            name = ""
        counts = {}
        for act in ACT_NAMES:
            try:
                counts[act] = min(max(0, int(row.get(act) or 0)), 10 ** 9)
            except (TypeError, ValueError):
                counts[act] = 0
        clean[key] = dict(counts, name=name)
    with LOCK:
        data = load_acts()
        before_row = data.get(code_id) or {}
        phones = before_row.get("phones") if isinstance(before_row.get("phones"), dict) else {}
        if isinstance(before_row.get("accounts"), dict) and before_row["accounts"]:
            # (from before a user could have several phones: those were the first phone's numbers)
            phones.setdefault(first_device or device, {"at": int(before_row.get("at") or 0), "accounts": before_row["accounts"]})
        mine = phones.get(device) if isinstance(phones.get(device), dict) else {}
        before = mine.get("accounts") if isinstance(mine.get("accounts"), dict) else {}
        kept = before_row.get("kept") if isinstance(before_row.get("kept"), dict) else {}
        grown = {name: 0 for name in ("repost", "like", "bookmark")}
        for key, old in before.items():
            if not isinstance(old, dict):
                continue
            new = clean.get(key)
            if new is None or any(new[act] < int(old.get(act) or 0) for act in ACT_NAMES):
                # Gone from the app, or counting again from zero (its numbers never go down otherwise): what it
                # had is kept, and what it shows now is new.
                slot = kept.setdefault(key, dict({act: 0 for act in ACT_NAMES}, name=""))
                for act in ACT_NAMES:
                    slot[act] = int(slot.get(act) or 0) + int(old.get(act) or 0)
                slot["name"] = old.get("name") or slot.get("name") or ""
                if new is not None:
                    for name in grown:
                        grown[name] += min(new[name], 100_000)
                continue
            for name in grown:
                step = new[name] - int(old.get(name) or 0)
                if 0 < step < 100_000:
                    grown[name] += step
        # (an account seen for the first time adds nothing to the chart: its numbers are from before)
        now = int(time.time())
        phones.pop(device, None)
        phones[device] = {"at": now, "accounts": clean}
        while len(phones) > ACTS_PHONES_KEPT:            # (the phone not heard from the longest: its numbers are kept)
            oldest = min(phones, key=lambda key: int((phones[key] or {}).get("at") or 0))
            for key, old in ((phones.pop(oldest) or {}).get("accounts") or {}).items():
                if isinstance(old, dict):
                    slot = kept.setdefault(key, dict({act: 0 for act in ACT_NAMES}, name=""))
                    for act in ACT_NAMES:
                        slot[act] = int(slot.get(act) or 0) + int(old.get(act) or 0)
                    slot["name"] = old.get("name") or slot.get("name") or ""
        data[code_id] = {"at": now, "phones": phones, **({"kept": kept} if kept else {})}
        write_private_json(ACTS_PATH, data)
        history_add(grown)


def acts_of(code_id: str, data: dict | None = None) -> dict:
    """A user's totals and, by X account (by @name, as the comments are), what their app shows; at is when it
    last sent them (0: never)."""
    row = (data if data is not None else load_acts()).get(code_id) or {}
    merged: dict[str, dict] = {}
    # (what each account shows in the app now, on each phone, and what was kept of it when an app lost it: the same
    # @name adds up)
    parts = list((row.get("accounts") or {}).items()) + list((row.get("kept") or {}).items())
    for phone in (row.get("phones") or {}).values():
        if isinstance(phone, dict):
            parts += list((phone.get("accounts") or {}).items())
    for key, value in parts:
        if not isinstance(value, dict):
            continue
        name = str(value.get("name") or "")
        slot = merged.setdefault(name.lower() if name else "id:" + key, dict({act: 0 for act in ACT_NAMES}, name=name))
        for act in ACT_NAMES:
            slot[act] += int(value.get(act) or 0)
    accounts = sorted(merged.values(), key=lambda item: -(item["repost"] + item["like"] + item["bookmark"]))
    totals = {act: sum(item[act] for item in accounts) for act in ACT_NAMES}
    return dict(totals, accounts=accounts, at=int(row.get("at") or 0))


# ----------------------------------------------------------------------------- the users' messages («مساعدة»)
# From the app's «مساعدة» button: a description of the problem, with up to five pictures or short videos, and what
# the app adds by itself (its version, the phone, its last log lines). Files come one by one first (support-file),
# then the message that names them (support). They are kept in SUPPORT_DIR/<message id>/.
SUPPORT_MAX = 300                     # the newest messages kept (older ones go, with their files)
SUPPORT_TEXT_MAX = 2000
SUPPORT_FILES_MAX = 5
SUPPORT_IMAGE_MAX = 8 * 1024 * 1024
SUPPORT_VIDEO_MAX = 25 * 1024 * 1024
SUPPORT_PENDING_HOURS = 3             # a file never named by a message goes after this
SUPPORT_PER_HOUR = 10                 # messages a code may send in an hour
SUPPORT_SHOWN = 100                   # the newest shown on the panel (the page stays light)


def light_support(item: dict) -> dict:
    """The message as the list keeps it: its log goes to its folder (log.txt), loaded when it is opened."""
    meta = item.get("meta") if isinstance(item.get("meta"), dict) else {}
    log = meta.pop("log", "") if meta else ""
    if log:
        folder = SUPPORT_DIR / str(item["id"])
        folder.mkdir(parents=True, exist_ok=True)
        (folder / "log.txt").write_text(str(log), encoding="utf-8")
        meta["has_log"] = True
    return item


def migrate_heavy_records() -> None:
    """Records kept whole by the earlier version: their heavy parts move out of the lists, once."""
    with LOCK:
        failures = load_failures()
        if any(any(key in item for key in FAILURE_HEAVY) for item in failures["items"]):
            failures["items"] = [light_failure(item) for item in failures["items"]]
            save_failures(failures)
        support = load_support()
        if any(isinstance(item.get("meta"), dict) and "log" in item["meta"] for item in support["items"]):
            support["items"] = [light_support(item) for item in support["items"]]
            save_support(support)


def sniff_media(data: bytes) -> tuple[str, str]:
    """(mime type, extension) by the file's own first bytes, or ("", "") when it is not a picture or video."""
    head = data[:16]
    if head.startswith(b"\xff\xd8\xff"):
        return "image/jpeg", "jpg"
    if head.startswith(b"\x89PNG\r\n\x1a\n"):
        return "image/png", "png"
    if head[:4] == b"RIFF" and head[8:12] == b"WEBP":
        return "image/webp", "webp"
    if head[:6] in (b"GIF87a", b"GIF89a"):
        return "image/gif", "gif"
    if head[4:8] == b"ftyp":
        brand = head[8:12]
        if brand.startswith(b"3g"):
            return "video/3gpp", "3gp"
        if brand == b"qt  ":
            return "video/quicktime", "mov"
        if brand in (b"heic", b"heix", b"mif1", b"msf1"):
            return "", ""                # (HEIC pictures: browsers do not show them)
        return "video/mp4", "mp4"
    if head.startswith(b"\x1a\x45\xdf\xa3"):
        return "video/webm", "webm"
    return "", ""


def load_support() -> dict:
    data = read_private_json(SUPPORT_PATH) or {}
    items = data.get("items")
    return {"seq": int(data.get("seq") or 0), "items": items if isinstance(items, list) else []}


def save_support(data: dict) -> None:
    write_private_json(SUPPORT_PATH, {"version": 1, "seq": int(data.get("seq") or 0), "items": data.get("items") or []})


def _support_pending_dir() -> Path:
    path = SUPPORT_DIR / "pending"
    path.mkdir(parents=True, exist_ok=True)
    return path


def prune_support_pending() -> None:
    cutoff = time.time() - SUPPORT_PENDING_HOURS * 3600
    for path in _support_pending_dir().glob("*"):
        try:
            if path.stat().st_mtime < cutoff:
                path.unlink()
        except OSError:
            pass


def support_unread() -> int:
    return sum(1 for item in load_support()["items"] if not item.get("read"))


def support_rows(codes: list) -> list:
    names = {row.get("id"): row for row in codes}
    rows = []
    now = int(time.time())
    for item in load_support()["items"][:SUPPORT_SHOWN]:
        code = names.get(item.get("code_id")) or {}
        delta = now - int(item.get("at") or 0)
        ago = ("الآن" if delta < 60 else f"قبل {delta // 60} د" if delta < 3600
               else f"قبل {delta // 3600} س" if delta < 86400 else f"قبل {delta // 86400} يوم")
        replies = [dict(r, when=time.strftime("%Y-%m-%d %H:%M", time.localtime(int(r.get("at") or 0))))
                   for r in item.get("replies") or [] if isinstance(r, dict)]
        rows.append(dict(item, replies=replies, who=code.get("label") or item.get("label") or "مستخدم محذوف",
                         code=code.get("code") or "", exists=bool(code), ago=ago,
                         when=time.strftime("%Y-%m-%d %H:%M", time.localtime(int(item.get("at") or 0)))))
    return rows


# ----------------------------------------------------------------------------- failures the apps report («الأعطال»)
# Every failure in a user's app (a task that stopped on an error, or ended with actions that failed, or an error in
# the script) arrives here by itself, with that account's log, for the owner to see what went wrong.
FAILURES_MAX = 500
FAILURES_SHOWN = 100                   # the newest shown on the panel (the page stays light)
FAILURE_HEAVY = ("failed", "log", "clicks", "trace")    # kept in failures/<id>.json, loaded when opened
FAILURES_PER_HOUR = 30                # reports a code may send in an hour


def load_failures() -> dict:
    data = read_private_json(FAILURES_PATH) or {}
    items = data.get("items")
    return {"seq": int(data.get("seq") or 0), "items": items if isinstance(items, list) else []}


def save_failures(data: dict) -> None:
    write_private_json(FAILURES_PATH, {"version": 1, "seq": int(data.get("seq") or 0), "items": data.get("items") or []})


def failure_detail_path(failure_id) -> Path:
    return FAILURES_DIR / f"{int(failure_id)}.json"


def drop_failure_details(items: list) -> None:
    for item in items:
        try:
            failure_detail_path(item.get("id") or 0).unlink()
        except (OSError, ValueError, TypeError):
            pass


def light_failure(item: dict) -> dict:
    """The item as the list keeps it: its heavy parts go to their own file."""
    heavy = {key: item.pop(key) for key in FAILURE_HEAVY if key in item}
    failed = heavy.get("failed") or []
    item.setdefault("failed_head", list(failed[:3]))
    item.setdefault("failed_count", len(failed))
    item.setdefault("has_details", any(heavy.get(key) for key in FAILURE_HEAVY))
    if any(heavy.get(key) for key in FAILURE_HEAVY):
        FAILURES_DIR.mkdir(parents=True, exist_ok=True)
        write_private_json(failure_detail_path(item["id"]), heavy)
    return item


def failure_rows(codes: list) -> list:
    names = {row.get("id"): row for row in codes}
    now = int(time.time())
    rows = []
    for item in load_failures()["items"][:FAILURES_SHOWN]:
        code = names.get(item.get("code_id")) or {}
        delta = now - int(item.get("at") or 0)
        ago = ("الآن" if delta < 60 else f"قبل {delta // 60} د" if delta < 3600
               else f"قبل {delta // 3600} س" if delta < 86400 else f"قبل {delta // 86400} يوم")
        rows.append(dict(item, who=code.get("label") or item.get("label") or "مستخدم محذوف", code=code.get("code") or "",
                         ago=ago, when=time.strftime("%Y-%m-%d %H:%M", time.localtime(int(item.get("at") or 0)))))
    return rows


# ----------------------------------------------------------------------------- the script the apps run («السكربت»)
# The owner uploads gg.py (and optionally content.py), then publishes it. Each user's app asks this server for the
# latest version and downloads it over its own pinned, token-checked connection — so the algorithm is updated
# without a new APK, and is served only to a device with a valid code.
SCRIPT_GG_MAX = 8 * 1024 * 1024
SCRIPT_CONTENT_MAX = 4 * 1024 * 1024
SCRIPT_META = "script.json"
STAGED_META = "staged.json"


def script_version(text: str) -> str:
    match = re.search(r'^APP_VERSION = "([0-9][0-9.]*)"', text, re.M)
    return match.group(1) if match else ""


VERSION_FORM = re.compile(r"^[0-9]{1,4}(\.[0-9]{1,4}){0,3}$")


def version_tuple(version: str) -> tuple[int, ...]:
    return tuple(int(part) for part in re.findall(r"\d+", version or "")) or (0,)


def next_version(version: str) -> str:
    """1.0 → 1.1, 1.9 → 1.10, 2 → 3. With nothing published, 1.1 (the apps' built-in script is 1.0)."""
    parts = [int(part) for part in re.findall(r"\d+", version or "")] or [1, 0]
    parts[-1] += 1
    return ".".join(str(part) for part in parts)


def stamp_version(raw: bytes, version: str) -> bytes:
    """The script with its APP_VERSION line set to version (the number the owner chose in the panel)."""
    text = raw.decode("utf-8")
    text = re.sub(r'^APP_VERSION = "[^"\n]*"', f'APP_VERSION = "{version}"', text, flags=re.M)
    return text.encode("utf-8")


def check_script(raw: bytes, name: str, want_version: bool) -> tuple[str, str]:
    """(error, version) for an uploaded file; error is "" when it is a usable script/content file."""
    if not raw:
        return f"ملف {name} فارغ.", ""
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError:
        return f"ملف {name} ليس نصًا سليمًا (UTF-8).", ""
    try:
        compile(text, name, "exec")
    except SyntaxError as exc:
        return f"ملف {name} فيه خطأ برمجي: {exc.msg} (سطر {exc.lineno}).", ""
    if want_version:
        version = script_version(text)
        if not version:
            return f"هذا لا يبدو ملف السكربت الصحيح ({name}): لا يوجد فيه سطر APP_VERSION.", ""
        if "flask" not in text.lower():
            return f"هذا لا يبدو ملف السكربت الصحيح ({name}).", ""
        return "", version
    return "", ""


def load_script_meta(name: str) -> dict:
    data = read_private_json(SCRIPT_DIR / name) or {}
    return data if isinstance(data, dict) else {}


def script_file_sha(filename: str) -> str:
    try:
        return hashlib.sha256((SCRIPT_DIR / filename).read_bytes()).hexdigest()
    except OSError:
        return ""


# «تجريبي»: a version published to some users only (to try it before everyone). Its files sit beside the one
# published to everyone (pilot-gg.py, pilot-content.py, pilot.json with the users' code ids). A user among them
# is offered it; everyone else keeps the version published to all.
PILOT_META = "pilot.json"


def pilot_meta() -> dict:
    """The trial version and who gets it; {} when there is none."""
    meta = load_script_meta(PILOT_META)
    return meta if meta.get("version") and (SCRIPT_DIR / "pilot-gg.py").is_file() else {}


def script_for(code_id: str) -> tuple[dict, str, str]:
    """(meta, script file, content file) of the version this user's app gets: the trial one when the user is among
    its users, else the one published to everyone."""
    pilot = pilot_meta()
    if pilot and code_id in (pilot.get("codes") or []):
        return pilot, "pilot-gg.py", "pilot-content.py"
    return load_script_meta(SCRIPT_META), "gg.py", "content.py"


def highest_published_version() -> str:
    """The highest version published (to everyone or as a trial): a new upload must be above it."""
    versions = [str(load_script_meta(SCRIPT_META).get("version") or ""), str(pilot_meta().get("version") or "")]
    versions = [version for version in versions if version]
    return max(versions, key=version_tuple) if versions else ""


def remove_script_files(*names: str) -> None:
    for name in names:
        try:
            (SCRIPT_DIR / name).unlink()
        except OSError:
            pass


def chosen_codes(values: list) -> list:
    """The ticked users that exist, once each, in order."""
    known = {row.get("id") for row in load_codes()}
    return [value for value in dict.fromkeys(str(item) for item in values) if value in known]


# ----------------------------------------------------------------------------- notices to the apps
# تنبيهات وتعليمات يرسلها المالك من اللوحة إلى التطبيقات: للكل أو لمستخدم واحد (رمز). كل تنبيه برقم يزيد،
# والتطبيق يطلب ما بعد آخر رقم وصله، فلا يصله التنبيه مرتين.
NOTICE_KINDS = {"info": "معلومة", "warn": "تنبيه", "urgent": "عاجل"}
NOTICE_MAX = 200                   # أحدث ٢٠٠ تنبيه تبقى على الخادم
NOTICE_TEXT_MAX = 1000
NOTICE_FIRST_DAYS = 7              # جهاز جديد (لم يصله شيء بعد) يأخذ تنبيهات آخر ٧ أيام فقط


def load_notices() -> dict:
    data = read_private_json(NOTICES_PATH) or {}
    items = data.get("items")
    return {"seq": int(data.get("seq") or 0), "items": items if isinstance(items, list) else []}


def save_notices(data: dict) -> None:
    write_private_json(NOTICES_PATH, {"version": 1, "seq": int(data.get("seq") or 0), "items": data.get("items") or []})


def add_notice(text: str, kind: str, target: str) -> None:
    text = (text or "").strip()[:NOTICE_TEXT_MAX]
    if not text:
        return
    kind = kind if kind in NOTICE_KINDS else "info"
    target = target or "all"
    with LOCK:
        if target != "all" and not any(row.get("id") == target for row in load_codes()):
            return                         # (the user was deleted meanwhile: a message for one person goes to no one else)
        data = load_notices()
        data["seq"] += 1
        data["items"].insert(0, {"id": data["seq"], "text": text, "kind": kind, "target": target,
                                 "at": int(time.time()), "seen": []})
        del data["items"][NOTICE_MAX:]
        save_notices(data)


def delete_notice(notice_id) -> None:
    try:
        notice_id = int(notice_id)
    except (TypeError, ValueError):
        return
    with LOCK:
        data = load_notices()
        data["items"] = [item for item in data["items"] if item.get("id") != notice_id]
        save_notices(data)


def notices_for(code_id: str, after: int) -> tuple[list, int]:
    """The notices for this code (to all, or to it) after the number its app last got, oldest first; and the
    newest number, which the app keeps. Each one remembers which codes got it, for the owner to see."""
    now = int(time.time())
    with LOCK:
        data = load_notices()
        if after > data["seq"]:            # the server's notices were started again: the app's number is stale
            after = 0
        out = []
        changed = False
        for item in data["items"]:
            if item.get("target") not in ("all", code_id):
                continue
            if int(item.get("id") or 0) <= after:
                continue
            if after <= 0 and now - int(item.get("at") or 0) > NOTICE_FIRST_DAYS * 86400:
                continue
            out.append({"id": item["id"], "text": item.get("text", ""), "kind": item.get("kind", "info"),
                        "at": item.get("at", 0)})
            seen = item.setdefault("seen", [])
            if code_id not in seen:
                seen.append(code_id)
                changed = True
        if changed:
            save_notices(data)
        return sorted(out, key=lambda item: item["id"])[-30:], data["seq"]


def notice_rows(codes: list) -> list:
    names = {row.get("id"): (row.get("label") or row.get("code") or "") for row in codes}
    total = len(codes)
    rows = []
    for item in load_notices()["items"]:
        target = item.get("target") or "all"
        seen = len(item.get("seen") or [])
        if target == "all":
            to = "الكل"
            reach = f"وصل إلى {seen} من {total}"
        else:
            to = names.get(target) or "مستخدم محذوف"
            reach = "وصل" if seen else "لم يصل بعد"
        delta = int(time.time()) - int(item.get("at") or 0)
        ago = ("الآن" if delta < 60 else f"قبل {delta // 60} د" if delta < 3600
               else f"قبل {delta // 3600} س" if delta < 86400 else f"قبل {delta // 86400} يوم")
        rows.append(dict(item, to=to, reach=reach, ago=ago, kind_name=NOTICE_KINDS.get(item.get("kind"), "معلومة")))
    return rows


GEMINI_DEFAULT_MODEL = "gemini-3.5-flash"
CLAUDE_DEFAULT_MODEL = "claude-haiku-5-5"
OPENROUTER_DEFAULT_MODEL = "google/gemini-2.5-flash"


def gemini_ready(keys: dict) -> bool:
    """Whether the Gemini engine has a usable key for its chosen provider (Google's key, or OpenRouter's)."""
    if keys.get("gemini_provider") == "openrouter":
        return bool(keys.get("openrouter_sealed"))
    return bool(keys.get("gemini_sealed"))


def active_engine() -> tuple[str, str, str, str]:
    """(engine, key, model, provider) of the engine chosen to write, or ("", "", "", "") when it has no key
    yet. engine is "gemini"/"claude" (for the app's display); provider is "openrouter" when Gemini is routed
    through OpenRouter, else "" (Claude, or Gemini straight to Google)."""
    keys = load_keys()
    engine = keys["engine"]
    if engine == "claude":
        key = open_key(keys["claude_sealed"])
        return ("claude", key, keys["claude_model"] or CLAUDE_DEFAULT_MODEL, "") if key else ("", "", "", "")
    if keys.get("gemini_provider") == "openrouter":
        key = open_key(keys.get("openrouter_sealed") or "")
        return ("gemini", key, keys.get("openrouter_model") or OPENROUTER_DEFAULT_MODEL, "openrouter") if key else ("", "", "", "")
    key = open_key(keys["gemini_sealed"])
    return ("gemini", key, keys["gemini_model"] or GEMINI_DEFAULT_MODEL, "") if key else ("", "", "", "")


# ----------------------------------------------------------------------------- writing one reply (ported from the app)
REPLY_MAX_CHARS = 100
REPLY_TWEET_TEXT = 1200
DEFAULT_REPLY_VOICE = "male"
REPLY_VOICES = {
    "male": "You write as a man: when you speak of yourself, use masculine forms (in Arabic: مبسوط، متأكد).",
    "female": "You write as a woman: when you speak of yourself, use feminine forms (in Arabic: مبسوطة، متأكدة).",
    "neutral": "The reply must suit a man or a woman: never use words that show the writer's gender "
               "(in Arabic, no forms like مبسوط or مبسوطة, متأكد or متأكدة).",
}
VOICE_BY_NUMBER = {0: "male", 1: "female", 2: "neutral"}
REPLY_ANGLES = (
    "a frank remark on its point, the way people talk among friends",
    "you disagree with one point in it, and say why",
    "a detail in it that most people will miss",
    "a light, dry joke about the situation",
    "you doubt one part of it, and say what does not add up",
    "a comparison with something from everyday life",
    "what it will lead to, or what comes next",
    "a short question about one point in it",
)
REPLY_LENGTHS = ((6, 10), (8, 13), (10, 16))
REPLY_MANNERS = (
    "short and direct, no emojis",
    "calm and down-to-earth",
    "sarcastic and witty",
    "blunt and critical, but not rude",
    "easygoing; now and then one emoji at the end",
    "curious; sometimes ends with a short question",
    "matter-of-fact; sticks to what the tweet says",
    "playful, with everyday slang",
)
import random  # noqa: E402  (kept near the reply code it serves)

ARABIC_DIACRITICS = re.compile(r"[\u064b-\u0652\u0656-\u0670\u065f]")   # tashkeel marks
HANGING_WORDS = {"و", "او", "أو", "بس", "لكن", "لان", "لأن", "عشان", "اللي", "الي", "في", "من", "على", "عن", "مع", "الى",
                 "إلى", "يعني", "ثم", "حتى", "اذا", "إذا", "لو", "ما", "لا", "كان", "and", "or", "but", "the", "to", "of",
                 "in", "a", "an", "with", "for", "that", "ve", "ama", "ile", "için", "bir", "de", "da"}


def clean_comment(raw: str) -> str:
    text = re.sub(r"\s+", " ", raw or "").strip()
    text = text.replace("**", "")
    text = re.sub(r"^(?:reply|comment|التعليق|الرد|الدعاء)\s*[:\uff1a\-]\s*", "", text, flags=re.I)
    text = re.sub(r"^[\w\u0600-\u06ff]{2,24}\s*[:\uff1a]\s*", "", text)
    text = text.strip("\"'«»“” ")
    if len(text) > 280:
        cut = text[:280]
        end = max(cut.rfind("؟"), cut.rfind("?"), cut.rfind("!"), cut.rfind("."), cut.rfind("…"))
        text = cut[: end + 1] if end >= 40 else cut.rsplit(" ", 1)[0]
    return text.strip()


def polish_comment(text: str) -> str:
    text = ARABIC_DIACRITICS.sub("", text or "")
    text = re.sub(r"(?<=\d),(?=\d{3})", "", text)
    text = re.sub(r"\s*[،,؛;]\s*", " ", text)
    return re.sub(r"\s+", " ", text).strip()


def fit_comment(text: str, limit: int = REPLY_MAX_CHARS) -> str:
    words = text.split()
    while words and len(" ".join(words)) > limit:
        words.pop()
    while words and words[-1].lower() in HANGING_WORDS:
        words.pop()
    return " ".join(words)


def comment_is_complete(text: str) -> bool:
    text = re.sub(r"[\s\u200d\ufe0f\u2600-\u27bf\U0001f000-\U0001faff]+$", "", text or "")
    words = [word for word in text.split() if word]
    if len(words) < (6 if reply_settings()["max_chars"] >= 90 else 4):
        return False
    if re.search(r"[،,؛;:\uff1a\-\u2013\u2014/\\*]$", text.strip()):
        return False
    last = re.sub(r"[.!?؟…\"'«»“”]+$", "", words[-1])
    return len(last) > 2


# «برومبت التعليقات» in the panel: what the model is told for each reply. text is the instructions, where {angle},
# {manner}, {words}, {max_chars} and {voice} are put in for each reply; angles: one drawn for each reply; manners: one
# for each account (always the same one); max_chars: the longest a reply may be. A field left empty (or nothing saved)
# is the built-in one. Users' comments are written here, so a change applies from the next comment, with no update.
PROMPT_PATH = DATA_DIR / "prompt.json"
PROMPT_TEXT_MAX = 8000
PROMPT_LIST_MAX = 40
PROMPT_LINE_MAX = 300
REPLY_CHARS_RANGE = (60, 280)
PROMPT_MARKS = ("{angle}", "{manner}", "{words}", "{max_chars}", "{voice}")
DEFAULT_PROMPT_TEXT = (
    "Write one public reply to this tweet, as an ordinary person scrolling X who comments on what it says. "
    "Read the whole tweet first and answer what it really says (its point, and its ending when it tells a story); "
    "do not guess beyond it.\n"
    "Not personal: the reply is about the tweet's topic, not about you. No stories or experiences of yours, "
    "nothing that happened to you, your family or your friends, and nothing about your own life (nothing like: "
    "صار معي، جربت، شفت بنفسي، أخوي، عندنا في البيت، أتذكر لما، لو كنت مكانه).\n"
    "Speak about its topic, not to please its author: do not compliment, thank or flatter the author, do not "
    "praise the tweet (nothing like: well said, you're right, great post, صدقت، كفو، أبدعت، كلامك ذهب), and do "
    "not just agree. Honest, never rude: no insults, and do not mock the author.\n"
    "This time: {angle}. Your manner (always the same): {manner}.\n"
    "If the tweet is a prayer (دعاء), about religion, a death, an illness or other sad news, leave the angle and "
    "the manner: reply sincerely and respectfully, with no joke and no disagreement.\n"
    "At most {max_chars} characters, spaces included (about {words} words). Finish the sentence. "
    "Never stop mid-word or mid-phrase.\n"
    "Write in the tweet's own language. An Arabic tweet gets everyday spoken Saudi Arabic (عامية سعودية بيضاء), "
    "the way people really type on X, never formal Arabic (فصحى): no words like الأولى، ينبغي، لا تثبت، ما زال، "
    "إذ، لذا، حيث، كما أن. A tweet in another language (English, Turkish…) gets its reply in that language.\n"
    "Plain letters only: no diacritics (no تشكيل: no fatha, damma, kasra, tanween, shadda or sukun), and no "
    "commas (، or ,).\n"
    "{voice}\n"
    "Sound like a real person, specific and casual, not a teacher, a preacher, a brand or an assistant: no "
    "advice or lessons to the author or to people (nothing like: الأولى أن، يجب، الأفضل أن، تذكّر، نصيحتي), no "
    "general wisdom or sayings, no neat conclusion; just make your point about the topic itself.\n"
    "The image is only a screenshot to read the tweet: never mention it, the picture, the post or the tweet "
    "(no الصورة، المنشور، التغريدة); react to what is in them.\n"
    "Do not open with filler (like صراحة، فعلاً، والله) or by repeating the tweet.\n"
    "No hashtags, no links, no quotes, no labels, no introduction. Return only the finished reply."
)
_prompt_trial = threading.local()           # («جرّب»: the settings typed in the panel, not saved yet)


def prompt_lines(raw) -> list:
    """A list typed one per line (or saved as a list): the lines with something in them."""
    rows = raw if isinstance(raw, list) else str(raw or "").splitlines()
    return [re.sub(r"\s+", " ", str(row)).strip() for row in rows if str(row).strip()]


def prompt_settings(data: dict) -> dict:
    """What a reply is written with: each saved field when it is usable, else the built-in one."""
    text = str(data.get("text") or "").strip()
    angles = prompt_lines(data.get("angles"))
    manners = prompt_lines(data.get("manners"))
    try:
        max_chars = int(data.get("max_chars") or 0)
    except (TypeError, ValueError):
        max_chars = 0
    if not REPLY_CHARS_RANGE[0] <= max_chars <= REPLY_CHARS_RANGE[1]:
        max_chars = REPLY_MAX_CHARS
    out = {"text": text or DEFAULT_PROMPT_TEXT, "angles": angles or list(REPLY_ANGLES),
           "manners": manners or list(REPLY_MANNERS), "max_chars": max_chars}
    out["custom"] = (out["text"] != DEFAULT_PROMPT_TEXT or out["angles"] != list(REPLY_ANGLES)
                     or out["manners"] != list(REPLY_MANNERS) or max_chars != REPLY_MAX_CHARS)
    out["angles_text"], out["manners_text"] = "\n".join(out["angles"]), "\n".join(out["manners"])
    return out


def load_prompt() -> dict:
    return prompt_settings(read_private_json(PROMPT_PATH) or {})


def prompt_from_form(form) -> tuple[dict, str]:
    """(what to save, why not) from the panel's prompt form. Whatever equals the built-in one is saved empty, so the
    built-in one (as later versions improve it) is what it stays on."""
    text = str(form.get("text") or "").replace("\r\n", "\n").strip()
    if len(text) > PROMPT_TEXT_MAX:
        return {}, f"التعليمات أطول من {PROMPT_TEXT_MAX} حرف. اختصرها."
    lists = {}
    for key, name in (("angles", "زوايا الرد"), ("manners", "أساليب الحسابات")):
        rows = prompt_lines(form.get(key))
        if len(rows) > PROMPT_LIST_MAX:
            return {}, f"{name}: {PROMPT_LIST_MAX} سطرًا على الأكثر."
        if any(len(row) > PROMPT_LINE_MAX for row in rows):
            return {}, f"{name}: كل سطر {PROMPT_LINE_MAX} حرف على الأكثر."
        lists[key] = rows
    raw = str(form.get("max_chars") or "").strip().translate(str.maketrans("٠١٢٣٤٥٦٧٨٩", "0123456789"))
    if raw and not raw.isdigit():
        return {}, "اكتب أقصى طول للتعليق رقمًا، مثل 100."
    max_chars = int(raw) if raw else REPLY_MAX_CHARS
    if not REPLY_CHARS_RANGE[0] <= max_chars <= REPLY_CHARS_RANGE[1]:
        return {}, f"أقصى طول للتعليق من {REPLY_CHARS_RANGE[0]} إلى {REPLY_CHARS_RANGE[1]} حرفًا."
    return {"text": "" if text == DEFAULT_PROMPT_TEXT else text,
            "angles": [] if lists["angles"] == list(REPLY_ANGLES) else lists["angles"],
            "manners": [] if lists["manners"] == list(REPLY_MANNERS) else lists["manners"],
            "max_chars": 0 if max_chars == REPLY_MAX_CHARS else max_chars}, ""


# «جرّب» with a tweet's link: the tweet is read from FxTwitter, as the app reads it before writing a comment: its text,
# the post it quotes, and its picture only when its own text is too short to say what it is about.
FX_STATUS_URL = "https://api.fxtwitter.com/status/{}"
TWEET_LINK = re.compile(r"^(?:https?://)?(?:www\.|mobile\.)?(?:x|twitter|fxtwitter|vxtwitter|fixupx)\.com/"
                        r"(?:[A-Za-z0-9_]{1,15}|i(?:/web)?)/status(?:es)?/(\d{5,25})(?:[/?#]\S*)?$", re.I)
TWEET_PICTURE = re.compile(r"https://pbs\.twimg\.com/[A-Za-z0-9_./-]{1,200}(?:\?[A-Za-z0-9_=&.-]{1,80})?")
COMMENT_PICTURE_LETTERS = 60
COMMENT_PICTURE_MAX_BYTES = 3_000_000


def fetch_tweet(status_id: str) -> tuple[dict, str]:
    """(FxTwitter's tweet, why not)."""
    asking = urllib.request.Request(FX_STATUS_URL.format(status_id), headers={
        "User-Agent": "x-group-tool/1.0", "Accept": "application/json"})
    try:
        with urllib.request.urlopen(asking, timeout=20) as response:
            data = json.loads(response.read(4 * 1024 * 1024).decode("utf-8"))
    except urllib.error.HTTPError as exc:
        if exc.code in (401, 404, 410):
            return {}, "التغريدة غير موجودة: محذوفة أو من حساب خاص."
        if exc.code in (403, 429, 503):
            return {}, "خدمة قراءة التغريدات لا تجيب الآن. أعد المحاولة بعد قليل، أو الصق نص التغريدة."
        return {}, f"تعذّر جلب التغريدة (HTTP {exc.code}). الصق نصها بدلًا من الرابط."
    except Exception:
        return {}, "تعذّر الاتصال بخدمة قراءة التغريدات. الصق نص التغريدة بدلًا من الرابط."
    tweet = data.get("tweet") if isinstance(data, dict) else None
    if not isinstance(tweet, dict):
        return {}, "التغريدة غير موجودة: محذوفة أو من حساب خاص."
    return tweet, ""


def tweet_material(tweet: dict) -> tuple[str, str]:
    """(the text a reply is written from, the address of the picture to send with it or "") — as the app makes them."""
    body = re.sub(r"[ \t\u00a0]+", " ", str(tweet.get("text") or "")[:2000]).strip()
    quoted = tweet.get("quote") if isinstance(tweet.get("quote"), dict) else {}
    lines = [body] if body else []
    quote_body = re.sub(r"\s+", " ", str(quoted.get("text") or "")[:1000]).strip()
    if quote_body:
        author = quoted.get("author") if isinstance(quoted.get("author"), dict) else {}
        by = str(author.get("screen_name") or "")
        by = by if re.fullmatch(r"[A-Za-z0-9_]{1,30}", by) else ""
        lines.append(f"[The post it quotes{' (by @' + by + ')' if by else ''}: {quote_body[:600]}]")
    picture = ""
    if len(re.sub(r"[\W_]+", "", re.sub(r"https?://\S+", "", body))) < COMMENT_PICTURE_LETTERS:
        for source in (tweet, quoted):
            media = source.get("media") if isinstance(source.get("media"), dict) else {}
            for item in media.get("all") or []:
                if not isinstance(item, dict):
                    continue
                address = item.get("url") if item.get("type") == "photo" else (
                    item.get("thumbnail_url") if item.get("type") in ("video", "gif") else "")
                if isinstance(address, str) and TWEET_PICTURE.fullmatch(address):
                    picture = address
                    break
            if picture:
                break
    if picture:
        lines.append("[The picture sent with it is the tweet's own picture]")
    return "\n".join(lines).strip(), picture


def tweet_picture(address: str) -> bytes | None:
    """A tweet's picture, small (X's picture server only, as JPEG); None when it cannot be had."""
    if not address or not TWEET_PICTURE.fullmatch(address):
        return None
    base = address.split("?", 1)[0]
    stem = re.sub(r"\.(?:jpe?g|png|webp|gif)$", "", base, flags=re.I)
    for url in (stem + "?format=jpg&name=small", base):
        try:
            asking = urllib.request.Request(url, headers={"User-Agent": "x-group-tool/1.0", "Accept": "image/jpeg"})
            with urllib.request.urlopen(asking, timeout=12) as response:
                data = response.read(COMMENT_PICTURE_MAX_BYTES + 1)
        except Exception:
            continue
        if len(data) <= COMMENT_PICTURE_MAX_BYTES and data[:3] == b"\xff\xd8\xff":
            return data
    return None


def reply_settings() -> dict:
    return getattr(_prompt_trial, "settings", None) or load_prompt()


def reply_prompt(voice: str, manner_number: int, before: list) -> str:
    settings = reply_settings()
    low, high = random.choice(REPLY_LENGTHS)               # (for 100 characters: as many more or fewer words)
    scale = settings["max_chars"] / 100
    low, high = max(3, round(low * scale)), max(4, round(high * scale))
    manners = settings["manners"]
    fill = {"{angle}": random.choice(settings["angles"]), "{manner}": manners[int(manner_number) % len(manners)],
            "{words}": f"{low} to {high}", "{max_chars}": str(settings["max_chars"]),
            "{voice}": REPLY_VOICES.get(voice, REPLY_VOICES[DEFAULT_REPLY_VOICE])}
    prompt = settings["text"]
    for mark, value in fill.items():
        prompt = prompt.replace(mark, value)
    before = [str(text) for text in (before or []) if str(text).strip()][:12]
    if before:
        prompt += ("\n\nReplies already written (to this tweet, or your own recent ones). Yours must say something "
                   "else, in another way (another opening, another shape, other words):\n"
                   + "\n".join("- " + text for text in before))
    return prompt


def gemini_thinking_config(model: str) -> dict | None:
    if re.search(r"2\.5", model):
        return {"thinkingBudget": 0}
    if re.search(r"gemini-3|3\.\d", model):
        return {"thinkingLevel": "low"}
    return None


def gemini_is_busy(status: int, detail: str) -> bool:
    if status in (429, 500, 502, 503, 504):
        return True
    return bool(re.search(r"high demand|try again later|unavailable|overloaded|resource exhausted|rate limit|quota",
                          detail or "", re.I))


def gemini_comment(api_key: str, model: str, image: bytes | None, tweet_text: str, voice: str, manner: int, before: list) -> str:
    prompt = reply_prompt(voice, manner, before)
    if image:
        prompt = "Look at the tweet in the image. " + prompt
    if tweet_text:
        prompt += "\n\nTweet text:\n" + tweet_text[:REPLY_TWEET_TEXT]
    parts: list[dict] = [{"text": prompt}]
    if image:
        parts.append({"inlineData": {"mimeType": "image/jpeg", "data": base64.b64encode(image).decode("ascii")}})
    attempts = [(gemini_thinking_config(model), 2048), (None, 4096)]
    busy_waits = (5, 12, 20, 30)
    best, saw_busy = "", False
    for thinking, max_tokens in attempts:
        config: dict = {"temperature": 1.0, "maxOutputTokens": max_tokens}
        if thinking:
            config["thinkingConfig"] = thinking
        body = {"contents": [{"parts": parts}], "generationConfig": config}
        payload, thinking_rejected = None, False
        for try_index in range(len(busy_waits) + 1):
            req = urllib.request.Request(
                "https://generativelanguage.googleapis.com/v1beta/models/" + quote(model, safe="") + ":generateContent",
                data=json.dumps(body).encode("utf-8"),
                headers={"Content-Type": "application/json", "x-goog-api-key": api_key}, method="POST")
            try:
                with urllib.request.urlopen(req, timeout=45) as response:
                    payload = json.loads(response.read().decode("utf-8"))
                break
            except urllib.error.HTTPError as exc:
                detail = ""
                try:
                    parsed = json.loads(exc.read().decode("utf-8", "replace")[:800])
                    detail = str(((parsed.get("error") or {}).get("message") or ""))[:160]
                except Exception:
                    detail = ""
                if api_key and api_key in detail:
                    detail = ""
                if thinking and re.search(r"thinking", detail, re.I):
                    thinking_rejected = True
                    break
                if exc.code in (401, 403):
                    raise RuntimeError("مفتاح Gemini غير صالح أو بلا صلاحية. راجع صاحب البرنامج.") from None
                if gemini_is_busy(getattr(exc, "code", 0) or 0, detail):
                    saw_busy = True
                    if try_index < len(busy_waits):
                        time.sleep(busy_waits[try_index]); continue
                    break
                raise RuntimeError(detail or "رفض Gemini الطلب") from None
            except Exception as exc:
                if try_index < 2:
                    time.sleep(busy_waits[try_index]); continue
                raise RuntimeError("تعذر الاتصال بـ Gemini") from exc
        if thinking_rejected:
            continue
        if not payload:
            break
        candidate = (payload.get("candidates") or [{}])[0]
        texts = [str(part["text"]) for part in ((candidate.get("content") or {}).get("parts") or [])
                 if isinstance(part, dict) and not part.get("thought") and part.get("text")]
        text = clean_comment(" ".join(texts))
        if comment_is_complete(text):
            return text
        if len(text) > len(best):
            best = text
    if comment_is_complete(best):
        return best
    if saw_busy:
        raise RuntimeError("Gemini مشغول مؤقتًا بعد عدة محاولات. أعد المحاولة بعد قليل.")
    return ""


CLAUDE_URL = "https://api.anthropic.com/v1/messages"
CLAUDE_API_VERSION = "2026-10-21"
CLAUDE_EFFORT = "medium"
claude_effort_refused: set = set()


def claude_answer_text(answer: dict) -> str:
    return "\n".join(str(block.get("text") or "") for block in answer.get("content") or []
                     if isinstance(block, dict) and block.get("type") == "text")


def claude_comment(api_key: str, model: str, image: bytes | None, tweet_text: str, voice: str, manner: int, before: list) -> str:
    prompt = reply_prompt(voice, manner, before)
    if image:
        prompt = "Look at the tweet in the image. " + prompt
    if tweet_text:
        prompt += "\n\nTweet text:\n" + tweet_text[:REPLY_TWEET_TEXT]
    content: list[dict] = []
    if image:
        content.append({"type": "image", "source": {"type": "base64", "media_type": "image/jpeg",
                                                     "data": base64.b64encode(image).decode("ascii")}})
    content.append({"type": "text", "text": prompt})
    effort = model not in claude_effort_refused
    busy_waits = (5, 12, 20, 30)
    best, saw_busy = "", False
    for _ in range(2):
        payload = None
        for try_index in range(len(busy_waits) + 1):
            body: dict = {"model": model, "max_tokens": 2048, "messages": [{"role": "user", "content": content}]}
            if effort:
                body["output_config"] = {"effort": CLAUDE_EFFORT}
            req = urllib.request.Request(CLAUDE_URL, data=json.dumps(body).encode("utf-8"), method="POST",
                                         headers={"Content-Type": "application/json", "x-api-key": api_key,
                                                  "anthropic-version": CLAUDE_API_VERSION})
            try:
                with urllib.request.urlopen(req, timeout=60) as response:
                    payload = json.loads(response.read().decode("utf-8"))
                break
            except urllib.error.HTTPError as exc:
                detail, code = "", ""
                try:
                    data = json.loads(exc.read(4096).decode("utf-8", "replace"))
                    error = data.get("error") if isinstance(data, dict) else None
                    if isinstance(error, dict):
                        detail = str(error.get("message") or "")
                        code = str((error.get("details") or {}).get("error_code") or "") if isinstance(error.get("details"), dict) else ""
                except Exception:
                    detail = ""
                detail = re.sub(r"\s+", " ", detail.replace(api_key, "…") if api_key else detail).strip()[:160]
                if effort and exc.code == 400 and re.search(r"effort|output_config", detail, re.I):
                    effort = False
                    claude_effort_refused.add(model)
                    continue
                if exc.code in (401, 403):
                    raise RuntimeError("مفتاح Claude غير صالح أو بلا صلاحية. راجع صاحب البرنامج.") from None
                if code == "enforced_spend_limit_reached" or re.search(r"usage limits|credit balance|billing", detail, re.I):
                    raise RuntimeError("بلغ حساب Claude حد الصرف أو نفد رصيده. راجع صاحب البرنامج.") from None
                if exc.code in (429, 500, 502, 503, 504, 529):
                    saw_busy = True
                    if try_index < len(busy_waits):
                        time.sleep(busy_waits[try_index]); continue
                    break
                raise RuntimeError(("رفض Claude الطلب: " + detail) if detail else f"تعذر الاتصال بـ Claude (رمز {exc.code}).") from None
            except (urllib.error.URLError, OSError, ValueError) as exc:
                if try_index < 2:
                    time.sleep(busy_waits[try_index]); continue
                raise RuntimeError("تعذر الاتصال بـ Claude") from exc
        if not isinstance(payload, dict):
            break
        if payload.get("stop_reason") == "refusal":
            raise RuntimeError("امتنع Claude عن التعليق على هذه التغريدة.")
        text = clean_comment(claude_answer_text(payload))
        if comment_is_complete(text):
            return text
        if len(text) > len(best):
            best = text
    if comment_is_complete(best):
        return best
    if saw_busy:
        raise RuntimeError("Claude مشغول مؤقتًا بعد عدة محاولات. أعد المحاولة بعد قليل.")
    return ""


# Gemini through OpenRouter (https://openrouter.ai): its OpenAI-style chat endpoint, with the owner's
# OpenRouter key and an OpenRouter model id (e.g. google/gemini-2.5-flash). The reply comes out the same.
OPENROUTER_URL = "https://openrouter.ai/api/v1/chat/completions"


def openrouter_comment(api_key: str, model: str, image: bytes | None, tweet_text: str, voice: str, manner: int, before: list) -> str:
    prompt = reply_prompt(voice, manner, before)
    if image:
        prompt = "Look at the tweet in the image. " + prompt
    if tweet_text:
        prompt += "\n\nTweet text:\n" + tweet_text[:REPLY_TWEET_TEXT]
    content: list[dict] = [{"type": "text", "text": prompt}]
    if image:
        content.append({"type": "image_url", "image_url": {"url": "data:image/jpeg;base64," + base64.b64encode(image).decode("ascii")}})
    body = {"model": model, "messages": [{"role": "user", "content": content}], "temperature": 1.0, "max_tokens": 2048}
    busy_waits = (5, 12, 20, 30)
    best, saw_busy = "", False
    for try_index in range(len(busy_waits) + 1):
        req = urllib.request.Request(
            OPENROUTER_URL, data=json.dumps(body).encode("utf-8"),
            headers={"Content-Type": "application/json", "Authorization": "Bearer " + api_key,
                     "X-Title": "qroobat"}, method="POST")
        try:
            with urllib.request.urlopen(req, timeout=45) as response:
                payload = json.loads(response.read().decode("utf-8"))
        except urllib.error.HTTPError as exc:
            detail = ""
            try:
                parsed = json.loads(exc.read().decode("utf-8", "replace")[:800])
                detail = str(((parsed.get("error") or {}).get("message") or ""))[:160]
            except Exception:
                detail = ""
            if api_key and api_key in detail:
                detail = ""
            if exc.code in (401, 403):
                raise RuntimeError("مفتاح OpenRouter غير صالح أو بلا صلاحية. راجع صاحب البرنامج.") from None
            if gemini_is_busy(getattr(exc, "code", 0) or 0, detail):
                saw_busy = True
                if try_index < len(busy_waits):
                    time.sleep(busy_waits[try_index]); continue
                break
            raise RuntimeError(detail or "رفض OpenRouter الطلب") from None
        except Exception as exc:
            if try_index < 2:
                time.sleep(busy_waits[try_index]); continue
            raise RuntimeError("تعذر الاتصال بـ OpenRouter") from exc
        choice = (payload.get("choices") or [{}])[0]
        raw = (choice.get("message") or {}).get("content")
        if isinstance(raw, list):
            raw = " ".join(str(part.get("text") or "") for part in raw if isinstance(part, dict))
        text = clean_comment(str(raw or ""))
        if comment_is_complete(text):
            return text
        if len(text) > len(best):
            best = text
        break
    if comment_is_complete(best):
        return best
    if saw_busy:
        raise RuntimeError("OpenRouter مشغول مؤقتًا بعد عدة محاولات. أعد المحاولة بعد قليل.")
    return ""


def write_reply(tweet_text: str, image: bytes | None, voice: str, manner: int, before: list) -> str:
    engine, key, model, provider = active_engine()
    if not engine:
        raise RuntimeError("لم يُفعّل أي مفتاح على الخادم بعد. أخبر صاحب البرنامج.")
    if engine == "claude":
        writer = claude_comment
    elif provider == "openrouter":
        writer = openrouter_comment
    else:
        writer = gemini_comment
    text = polish_comment(writer(key, model, image, tweet_text, voice, manner, before))
    if not text:
        raise RuntimeError("لم يُكتب تعليق. أعد المحاولة.")
    limit = reply_settings()["max_chars"]
    if len(text) > limit:
        text = fit_comment(text, limit)
    return text


# ----------------------------------------------------------------------------- the app's unlock token
# The token carries the code and the phone it was given to, signed. A copy of it on another phone is useless: that
# phone's own device id will not match the device inside the token, and only the user's phones are let in (see
# allowed_devices: any phone that signed in with it, or the first one only when «جهاز واحد» is chosen).
def make_token(code_id: str, device: str) -> str:
    exp = int(time.time()) + TOKEN_DAYS * 86400
    head = f"{code_id}.{device}.{exp}"
    sig = hmac.new(SECRETS["token_secret"].encode("utf-8"), head.encode("utf-8"), hashlib.sha256).hexdigest()[:32]
    return base64.urlsafe_b64encode(f"{head}.{sig}".encode("utf-8")).decode("ascii")


def read_token(token: str) -> tuple[str, str]:
    """(code id, device) a valid, unexpired token carries, or ("", "")."""
    try:
        head_sig = base64.urlsafe_b64decode(str(token).encode("ascii")).decode("utf-8")
        code_id, device, exp, sig = head_sig.rsplit(".", 3)
    except (ValueError, Exception):
        return "", ""
    good = hmac.new(SECRETS["token_secret"].encode("utf-8"), f"{code_id}.{device}.{exp}".encode("utf-8"), hashlib.sha256).hexdigest()[:32]
    if not hmac.compare_digest(sig, good):
        return "", ""
    try:
        if int(exp) < int(time.time()):
            return "", ""
    except ValueError:
        return "", ""
    return code_id, device


def code_from_token(token: str) -> dict | None:
    """The active code a token belongs to, only when the token's phone is one the code may work on."""
    code_id, device = read_token(token)
    if not code_id or not device:
        return None
    with LOCK:
        for row in load_codes():
            if row.get("id") == code_id and row.get("active") and device in allowed_devices(row):
                return row
    return None


# ----------------------------------------------------------------------------- the app link + certificate
def ensure_certificate() -> None:
    if CERT_PATH.exists() and CERT_KEY_PATH.exists():
        return
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    subprocess.run(["openssl", "req", "-x509", "-newkey", "rsa:2048", "-nodes",
                    "-keyout", str(CERT_KEY_PATH), "-out", str(CERT_PATH),
                    "-days", "3650", "-subj", "/CN=groups-control"], check=True, capture_output=True)
    try:
        os.chmod(CERT_KEY_PATH, 0o600)
    except OSError:
        pass


def certificate_fingerprint() -> str:
    der = ssl.PEM_cert_to_DER_cert(CERT_PATH.read_text(encoding="utf-8"))
    return hashlib.sha256(der).hexdigest()


def public_host() -> str:
    host = os.environ.get("CONTROL_PUBLIC_HOST")
    if host:
        return host
    try:
        import socket
        return socket.gethostbyname(socket.gethostname())
    except Exception:
        return "YOUR-HOST"


def app_link() -> str:
    host = public_host()
    port = "" if LISTEN_PORT == 443 else f":{LISTEN_PORT}"
    return f"https://{host}{port}/{SECRETS['api_secret']}#{certificate_fingerprint()}"


def admin_link() -> str:
    host = public_host()
    port = "" if LISTEN_PORT == 443 else f":{LISTEN_PORT}"
    return f"https://{host}{port}/{SECRETS['admin_path']}"


# ----------------------------------------------------------------------------- the web app
app = Flask(__name__)
app.secret_key = SECRETS["session_secret"]
API = SECRETS["api_secret"]
ADMIN = SECRETS["admin_path"]
APP_DL = SECRETS["app_dl"]


# «تطبيق المالك» (control/owner-app): the panel in an Android app of the owner's own. It says so in its User-Agent;
# when the owner signs in there, it keeps a login for 90 days (a cookie signed with the server's secret and the
# password's hash: a new password ends it). A browser's login stays as it was, for its session only.
OWNER_APP_MARK = "GroupsOwnerApp/"
OWNER_COOKIE = "gg_owner"
OWNER_DAYS = 90


def _owner_sig(expires: int) -> str:
    return hmac.new(SECRETS["token_secret"].encode("utf-8"), f"owner|{expires}|{SECRETS['admin_hash']}".encode("utf-8"),
                    hashlib.sha256).hexdigest()


def owner_token() -> str:
    expires = int(time.time()) + OWNER_DAYS * 86400
    return f"{expires}.{_owner_sig(expires)}"


def owner_token_ok(value: str) -> bool:
    try:
        expires_text, sig = str(value or "").split(".", 1)
        expires = int(expires_text)
    except ValueError:
        return False
    return expires > time.time() and hmac.compare_digest(sig, _owner_sig(expires))


def logged_in() -> bool:
    if session.get("owner"):
        return True
    if owner_token_ok(request.cookies.get(OWNER_COOKIE) or ""):
        session["owner"] = True
        return True
    return False


def owner_app_link(host: str = "") -> str:
    """What the owner pastes in «تطبيق المالك»: the panel's address, with the certificate's fingerprint after #."""
    if not host:
        host = public_host() + ("" if LISTEN_PORT == 443 else f":{LISTEN_PORT}")
    return f"https://{host}/{ADMIN}#{certificate_fingerprint()}"


LOGIN_PAGE = r"""<!doctype html><html lang="ar" dir="rtl"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<meta name="theme-color" content="#0c3d3a"><meta name="robots" content="noindex,nofollow">
<title>تسجيل الدخول</title>
<link rel="preconnect" href="https://fonts.googleapis.com"><link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Readex+Pro:wght@300..700&display=swap" media="print" onload="this.media='all'">
<script>try{document.documentElement.dataset.theme=localStorage.getItem('th')||(matchMedia('(prefers-color-scheme:dark)').matches?'dark':'light')}catch(e){}</script>
<style>
:root{--bg:#0c3d3a;--card:#fff;--soft:#f3f6f5;--line:#dce4e2;--ink:#10201f;--mut:#566664;--pri:#0f6b66;--prih:#0b5651;--prik:#fff;--ring:rgba(15,107,102,.22);--bad:#b42318;--badsoft:#fdeae7;color-scheme:light}
[data-theme=dark]{--bg:#0a1f1d;--card:#111b1a;--soft:#182423;--line:#243432;--ink:#e3eeec;--mut:#8c9e9b;--pri:#56c8bf;--prih:#74d6ce;--prik:#05201e;--ring:rgba(86,200,191,.28);--bad:#f6817a;--badsoft:#3a1b19;color-scheme:dark}
*{box-sizing:border-box}
html{-webkit-text-size-adjust:100%}
body{margin:0;min-height:100vh;min-height:100dvh;display:flex;flex-direction:column;background:var(--bg);color:var(--ink);font:400 15px/1.65 "Readex Pro","IBM Plex Sans Arabic","Segoe UI",system-ui,-apple-system,"Noto Sans Arabic",Tahoma,sans-serif;-webkit-tap-highlight-color:transparent}
h1,p{margin:0}
.box{flex:1;display:flex;flex-direction:column;width:100%}
.bh{flex:1;display:flex;flex-direction:column;justify-content:flex-end;padding:40px 24px 28px;color:#eef8f6}
.logo{width:52px;height:52px;border-radius:15px;display:grid;place-items:center;background:#eef8f6;color:#0c3d3a;font-weight:600;font-size:26px;margin-bottom:20px}
h1{font-size:26px;font-weight:600;line-height:1.35}
.bh p{color:#a3cbc6;margin-top:4px}
.bb{background:var(--card);border-radius:24px 24px 0 0;padding:26px 24px calc(28px + env(safe-area-inset-bottom,0px))}
label{display:block;font-size:13.5px;font-weight:500;color:var(--mut);margin-bottom:6px}
.pw{position:relative}
input{width:100%;height:50px;padding:0 14px;padding-left:50px;border-radius:13px;border:1px solid var(--line);background:var(--soft);color:var(--ink);font:inherit;font-size:16px;outline:0}
input:focus{border-color:var(--pri);box-shadow:0 0 0 3px var(--ring);background:var(--card)}
.eye{position:absolute;left:5px;top:5px;width:40px;height:40px;border:0;border-radius:10px;background:none;color:var(--mut);cursor:pointer;display:grid;place-items:center}
.eye[aria-pressed=true]{color:var(--pri)}
.i{width:20px;height:20px;fill:none;stroke:currentColor;stroke-width:1.8;stroke-linecap:round;stroke-linejoin:round}
.btn{width:100%;height:50px;margin-top:16px;border:0;border-radius:13px;background:var(--pri);color:var(--prik);font:inherit;font-weight:600;font-size:16px;cursor:pointer}
.btn:hover{background:var(--prih)}
.alert{display:flex;gap:9px;align-items:flex-start;background:var(--badsoft);color:var(--bad);border-radius:13px;padding:11px 14px;font-size:14px;font-weight:500;margin-bottom:18px}
.alert .i{width:18px;height:18px;flex:none;margin-top:3px}
:focus-visible{outline:2px solid var(--pri);outline-offset:2px}
@media(min-width:560px){
body{align-items:center;justify-content:center;padding:24px;background:var(--soft)}
[data-theme=dark] body{background:#0a1211}
.box{flex:none;width:400px;border-radius:22px;overflow:hidden;border:1px solid var(--line);background:var(--bg)}
.bh{flex:none;padding:32px 28px 26px}
.bb{border-radius:0;padding:26px 28px 30px}
}
@media(prefers-reduced-motion:reduce){*{transition:none!important;animation:none!important}}
</style></head><body>
<main class="box">
<header class="bh"><div class="logo" aria-hidden="true">ق</div><h1>لوحة التحكّم</h1><p>سجّل الدخول لإدارة المستخدمين والمفاتيح.</p></header>
<form class="bb" method="post" action="/{{admin}}/login">
{% if error %}<div class="alert" role="alert"><svg class="i" viewBox="0 0 24 24" aria-hidden="true"><circle cx="12" cy="12" r="10"/><path d="M12 8v4M12 16h.01"/></svg><span>{{error}} تأكّد منها ثم أعد المحاولة.</span></div>{% endif %}
<label for="p">كلمة مرور المالك</label>
<div class="pw"><input id="p" type="password" name="password" autocomplete="current-password" autocapitalize="off" autocorrect="off" spellcheck="false" enterkeyhint="go" autofocus required>
<button type="button" class="eye" aria-label="إظهار كلمة المرور" aria-pressed="false" onclick="var p=document.getElementById('p'),s=p.type=='password';p.type=s?'text':'password';this.setAttribute('aria-pressed',s)"><svg class="i" viewBox="0 0 24 24" aria-hidden="true"><path d="M1 12s4-8 11-8 11 8 11 8-4 8-11 8-11-8-11-8z"/><circle cx="12" cy="12" r="3"/></svg></button></div>
<button class="btn">دخول</button>
</form></main></body></html>
"""

DASHBOARD = r"""{% macro usd(v) %}{% set r = (v or 0)|float|round(4) %}{% set a = r|abs %}{{ '−' if r < 0 else '' }}${{ '%.2f'|format(a) if (a * 100 - (a * 100)|round)|abs < 0.000001 else ('%.4f'|format(a)).rstrip('0') }}{% endmacro %}{% macro ic(n) %}<svg class="i" viewBox="0 0 24 24" aria-hidden="true"><use href="#i-{{n}}"/></svg>{% endmacro %}{% set nokey = (engine=='gemini' and not gemini_set) or (engine=='claude' and not claude_set) %}<!doctype html>
<html lang="ar" dir="rtl"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<meta name="theme-color" content="#ffffff"><meta name="robots" content="noindex,nofollow"><meta name="format-detection" content="telephone=no">
<title>لوحة التحكّم</title>
<link rel="preconnect" href="https://fonts.googleapis.com"><link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Readex+Pro:wght@300..700&family=JetBrains+Mono:wght@500;700&display=swap" media="print" onload="this.media='all'">
<script>try{document.documentElement.dataset.theme=localStorage.getItem('th')||(matchMedia('(prefers-color-scheme:dark)').matches?'dark':'light')}catch(e){}</script>
<style>
/* ---- tokens: teal means "working", red means "stopped", everything else stays neutral ---- */
:root{--bg:#eef2f1;--card:#fff;--soft:#f3f6f5;--line:#dce4e2;--dash:#b7c5c2;--ink:#10201f;--mut:#566664;
--pri:#0f6b66;--prih:#0b5651;--prik:#fff;--prisoft:#def0ed;--ring:rgba(15,107,102,.22);
--bad:#b42318;--badk:#fff;--badsoft:#fdeae7;--warn:#7a4f00;--warnsoft:#fbefd2;
--hero:#0c3d3a;--heroline:rgba(255,255,255,.14);--herobd:transparent;--off:#a6b4b1;
--pop:0 18px 48px rgba(12,32,30,.22);--nav:60px;--sb:env(safe-area-inset-bottom,0px);
--mono:"JetBrains Mono",ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;color-scheme:light}
[data-theme=dark]{--bg:#0a1211;--card:#111b1a;--soft:#182423;--line:#243432;--dash:#3a4d4a;--ink:#e3eeec;--mut:#8c9e9b;
--pri:#56c8bf;--prih:#74d6ce;--prik:#05201e;--prisoft:#12322f;--ring:rgba(86,200,191,.28);
--bad:#f6817a;--badk:#2b0a08;--badsoft:#3a1b19;--warn:#f1c35c;--warnsoft:#33290f;
--hero:#0e2a28;--herobd:#1d3d3a;--off:#3b4d4a;--pop:0 18px 48px rgba(0,0,0,.55);color-scheme:dark}

/* ---- base ---- */
*{box-sizing:border-box}[hidden]{display:none!important}
html{-webkit-text-size-adjust:100%}
body{margin:0;color:var(--ink);background:var(--bg);font:400 15px/1.65 "Readex Pro","IBM Plex Sans Arabic","Segoe UI",system-ui,-apple-system,"Noto Sans Arabic",Tahoma,sans-serif;-webkit-tap-highlight-color:transparent}
button,input,select{font:inherit;color:inherit}
button{cursor:pointer;touch-action:manipulation}
h2,h3,p,dl,dd,ul{margin:0}
h2{font-size:18px;font-weight:600;line-height:1.45}
h3{font-size:16px;font-weight:600;line-height:1.45}
.mut{color:var(--mut)}
.i{width:20px;height:20px;fill:none;stroke:currentColor;stroke-width:1.8;stroke-linecap:round;stroke-linejoin:round;flex:none}
:focus-visible{outline:2px solid var(--pri);outline-offset:2px}
.wrap{max-width:1120px;margin:0 auto;padding-inline:16px}

/* ---- top bar + navigation (bottom bar on phones, inline tabs on wide screens) ---- */
.top{background:var(--card);border-bottom:1px solid var(--line)}
.topin{display:flex;align-items:center;gap:12px;min-height:60px}
.brand{display:flex;align-items:center;gap:11px;min-width:0}
.logo{width:38px;height:38px;border-radius:11px;display:grid;place-items:center;background:var(--hero);color:#eef8f6;font-weight:600;font-size:19px;flex:none}
.brand b{display:block;font-size:16px;font-weight:600;line-height:1.4}
.brand small{display:block;font-size:12.5px;color:var(--mut);line-height:1.4}
.acts{display:flex;gap:6px;margin-inline-start:auto}
.ib{width:42px;height:42px;padding:0;border:1px solid var(--line);background:var(--card);border-radius:12px;display:grid;place-items:center;color:var(--mut);flex:none}
.ib:hover{color:var(--ink);background:var(--soft)}
.th .s{display:none}[data-theme=dark] .th .s{display:block}[data-theme=dark] .th .m{display:none}
.nav{position:fixed;inset-inline:0;bottom:0;z-index:30;display:flex;background:var(--card);border-top:1px solid var(--line);padding-bottom:var(--sb)}
.nav button{position:relative;flex:1;height:var(--nav);display:flex;flex-direction:column;align-items:center;justify-content:center;gap:2px;border:0;background:none;color:var(--mut);font-size:12px;font-weight:500}
.nav .i{width:22px;height:22px}
.nav [aria-current]{color:var(--pri);font-weight:600}
.nav [aria-current]::before{content:"";position:absolute;top:-1px;inset-inline:30%;height:3px;border-radius:0 0 4px 4px;background:var(--pri)}
.nav .dot{position:absolute;top:9px;inset-inline-start:calc(50% + 7px);width:8px;height:8px;border-radius:50%;background:var(--bad);box-shadow:0 0 0 2px var(--card)}
main{padding-bottom:calc(var(--nav) + var(--sb) + 28px)}
.panel{display:none}.panel.on{display:block}

/* ---- controls ---- */
input{width:100%;height:46px;padding:0 14px;border:1px solid var(--line);border-radius:12px;background:var(--soft);outline:0;font-size:16px}
input:focus{border-color:var(--pri);box-shadow:0 0 0 3px var(--ring);background:var(--card)}
input::placeholder{color:var(--mut);opacity:.8}
.btn{display:inline-flex;gap:8px;align-items:center;justify-content:center;min-height:46px;padding:0 18px;border:0;border-radius:12px;font-weight:600;font-size:15px;white-space:nowrap;color:var(--prik);background:var(--pri)}
.btn:hover{background:var(--prih)}
.btn.ghost{background:var(--card);color:var(--ink);border:1px solid var(--line)}.btn.ghost:hover{background:var(--soft)}
.btn.danger{background:var(--bad);color:var(--badk)}
.btn.wide{width:100%}
.busy{opacity:.6;pointer-events:none}
.l{display:block;font-size:13.5px;font-weight:500;color:var(--mut);margin:16px 0 6px}.l small{font-weight:400}
.pw{position:relative}.pw input{padding-left:50px}
.eye{position:absolute;left:4px;top:4px;width:38px;height:38px;padding:0;border:0;border-radius:10px;background:none;color:var(--mut);display:grid;place-items:center}
.eye[aria-pressed=true]{color:var(--pri)}
.kin:placeholder-shown{direction:rtl}

/* ---- summary ---- */
.note{display:flex;gap:10px;align-items:flex-start;background:var(--warnsoft);color:var(--warn);border-radius:14px;padding:12px 14px;font-size:14px;margin-top:16px}
.note .i{width:18px;height:18px;margin-top:3px}
.note button{border:0;background:none;padding:0;color:inherit;font-weight:600;text-decoration:underline;text-underline-offset:3px}
.hero{background:var(--hero);border:1px solid var(--herobd);color:#eef8f6;border-radius:20px;padding:16px 18px 0;margin-top:16px}
.ht{display:flex;align-items:flex-start;justify-content:space-between;gap:12px}
.tot{display:flex;align-items:baseline;gap:9px}
.tot b{font-size:42px;font-weight:300;line-height:1;font-variant-numeric:tabular-nums}
.tot span{font-size:14px;color:#a3cbc6}
.hb{display:inline-flex;align-items:center;gap:6px;height:40px;padding:0 12px;border:1px solid rgba(255,255,255,.24);border-radius:10px;background:none;color:#d7ebe8;font-size:13px;font-weight:500}
.hb:hover{background:rgba(255,255,255,.08)}
.hb .i{width:16px;height:16px}
.ratio{display:flex;height:8px;border-radius:99px;background:rgba(255,255,255,.17);overflow:hidden;margin-top:14px}
.ratio i{border-radius:99px;background:#63d6ca}
.rl{display:flex;justify-content:space-between;gap:12px;font-size:13px;color:#a3cbc6;margin-top:7px}
.rl b{color:#fff;font-weight:600;font-variant-numeric:tabular-nums}
.kp{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));margin-top:12px;border-top:1px solid var(--heroline)}
.kp div{padding:10px 0 12px;padding-inline-start:14px;border-inline-start:1px solid var(--heroline)}
.kp div:first-child{padding-inline-start:0;border:0}
.kp dt{font-size:12px;color:#a3cbc6;line-height:1.5}
.kp dd{font-size:20px;font-weight:500;line-height:1.4;font-variant-numeric:tabular-nums}
.kpa{display:block;margin-top:1px;font-size:11px;line-height:1.4;color:#a3cbc6;font-variant-numeric:tabular-nums;white-space:nowrap}

/* ---- search, filter, sort ---- */
.tb{position:sticky;top:0;z-index:10;display:flex;gap:8px;padding:10px 0 8px;margin-top:4px;background:var(--bg)}
.search{position:relative;flex:1;min-width:0}
.search .i{position:absolute;inset-inline-start:13px;top:13px;color:var(--mut);pointer-events:none}
.search input{padding-inline:42px;border-radius:14px;background:var(--card)}
.search input::-webkit-search-cancel-button{display:none}
.qx{position:absolute;inset-inline-end:4px;top:4px;width:38px;height:38px;padding:0;border:0;border-radius:10px;background:none;color:var(--mut);display:grid;place-items:center}
.qx .i{width:17px;height:17px}
.add{border-radius:14px;padding:0 15px}
.add .wd{display:none}
.fr{display:flex;align-items:center;justify-content:space-between;gap:8px;flex-wrap:wrap;margin-bottom:12px}
.seg{display:flex;background:var(--card);border:1px solid var(--line);border-radius:12px;padding:3px}
.seg button{height:38px;padding:0 13px;border:0;border-radius:9px;background:none;color:var(--mut);font-weight:500;font-size:14px}
.seg [aria-pressed=true]{background:var(--ink);color:var(--card);font-weight:600}
.sort{position:relative;display:inline-flex;align-items:center;gap:7px;height:46px;padding:0 12px;border:1px solid var(--line);border-radius:12px;background:var(--card);color:var(--mut);font-size:14px;font-weight:500}
.sort .i{width:17px;height:17px}
.sort select{position:absolute;inset:0;width:100%;height:100%;opacity:0;cursor:pointer;font-size:16px}
.sort:focus-within{outline:2px solid var(--pri);outline-offset:2px}

/* ---- one user ---- */
.list{display:grid;grid-template-columns:minmax(0,1fr);gap:10px}
.u{display:grid;grid-template-columns:minmax(0,1fr) auto;align-items:center;gap:12px 10px;background:var(--card);border:1px solid var(--line);border-radius:16px;padding:14px}
.who{display:flex;gap:12px;align-items:center;min-width:0}
.av{width:44px;height:44px;border-radius:14px;display:grid;place-items:center;flex:none;font-weight:600;font-size:18px;line-height:1;background:hsl(var(--h,174) 50% 50%/.15);color:hsl(var(--h,174) 62% 33%)}
[data-theme=dark] .av{color:hsl(var(--h,174) 58% 72%)}
.nm{min-width:0}
.nm h3{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.nm p{display:flex;flex-wrap:wrap;align-items:center;column-gap:9px;font-size:12.5px;line-height:1.6;color:var(--mut)}
.st{display:inline-flex;align-items:center;gap:5px;font-weight:600;color:var(--pri)}
.st::before{content:"";width:7px;height:7px;border-radius:50%;background:currentColor}
.sw{position:relative;width:52px;height:32px;padding:0;border:0;border-radius:99px;background:var(--off);flex:none;transition:background .2s}
.sw::after{content:"";position:absolute;inset:-7px -5px}
.sw i{position:absolute;top:3px;inset-inline-start:3px;width:26px;height:26px;border-radius:50%;background:#fff;box-shadow:0 1px 3px rgba(0,0,0,.3);transition:inset-inline-start .2s}
.sw.on{background:var(--pri)}.sw.on i{inset-inline-start:23px}
.cr{grid-column:1/-1;display:flex;gap:8px}
.code{flex:1;min-width:0;display:flex;align-items:center;gap:10px;min-height:46px;padding:0 14px;border:1px dashed var(--dash);border-radius:12px;background:var(--soft);transition:background .2s,border-color .2s}
.code bdi{font:700 15.5px/1 var(--mono);letter-spacing:.05em;direction:ltr;white-space:nowrap}
.code .i{width:18px;height:18px;margin-inline-start:auto;color:var(--mut)}
.code:hover{border-color:var(--pri)}
.code.ok{border-style:solid;border-color:var(--pri);background:var(--prisoft)}.code.ok .i{color:var(--pri)}
.cr .ib{width:46px;height:46px}
.facts{grid-column:1/-1;display:flex;flex-wrap:wrap;align-items:center;gap:0 14px;font-size:13.5px;color:var(--mut)}
.facts b{color:var(--ink);font-weight:600;font-variant-numeric:tabular-nums}
.dev{display:inline-flex;align-items:center;gap:5px;margin-inline-start:auto;font-size:12.5px;font-weight:500}
.dev .i{width:15px;height:15px}
.dev.on{color:var(--pri)}
.u.off .st{color:var(--bad)}
.u.off .av{filter:grayscale(1);opacity:.55}
.u.off h3{color:var(--mut)}
.u.off .code bdi{text-decoration:line-through;color:var(--mut)}
.acc{grid-column:1/-1;min-width:0}
.acc summary{min-height:44px;margin-block:-10px;list-style:none;cursor:pointer;border-radius:8px}
.acc summary::-webkit-details-marker{display:none}
.acc summary>.i{width:17px;height:17px;margin-inline-start:-6px;transition:transform .2s}
.acc[open] summary>.i{transform:rotate(180deg)}
.alh{margin-top:14px;padding-top:12px;border-top:1px solid var(--line);font-size:12.5px;font-weight:500;color:var(--mut)}
.al{list-style:none;padding:0;margin-top:8px;display:grid;gap:11px}
.al li{display:grid;grid-template-columns:minmax(0,1fr) auto auto;gap:5px 14px;align-items:baseline;font-size:13.5px;color:var(--mut)}
.al b{font-weight:500;color:var(--ink);overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.al span{font-variant-numeric:tabular-nums}
.pg{grid-column:1/-1;height:4px;border-radius:9px;background:var(--line);overflow:hidden}
.pg i{display:block;height:100%;border-radius:9px;background:var(--pri)}
.kp div:nth-child(3n+1){padding-inline-start:0;border-inline-start:0}
.kp div:nth-child(n+4){border-top:1px solid var(--heroline)}
.ax{grid-column:1/-1;display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:8px}
.ax div{background:var(--soft);border:1px solid var(--line);border-radius:12px;padding:8px 10px;text-align:center;line-height:1.35}
.ax b{display:block;font-size:18px;font-weight:600;color:var(--ink);font-variant-numeric:tabular-nums}
.ax span{font-size:12px;color:var(--mut)}
.axs{display:flex;align-items:center;gap:8px;font-size:12.5px;color:var(--mut)}
.axl{list-style:none;padding:0;margin:10px 0 0;display:grid;gap:9px}
.axl li{display:grid;grid-template-columns:minmax(0,1fr) auto auto auto;gap:4px 12px;align-items:baseline;font-size:13px;color:var(--mut)}
.axl li>b{font-weight:500;color:var(--ink);overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.axl span b{color:var(--ink);font-weight:600;font-variant-numeric:tabular-nums}
.axe{font-size:13px;margin-top:8px}
.axn{grid-column:1/-1;font-size:12.5px;color:var(--mut)}
.empty{text-align:center;padding:40px 20px;color:var(--mut);background:var(--card);border:1px dashed var(--dash);border-radius:16px}
.empty h3{color:var(--ink);margin-bottom:4px}
.empty .btn{margin-top:16px}

/* ---- keys + link ---- */
.card{background:var(--card);border:1px solid var(--line);border-radius:16px;margin-top:16px}
.pad{padding:18px}
.eng{display:grid;gap:10px;margin-top:14px}
.opt{position:relative;display:flex;gap:12px;align-items:center;min-height:66px;padding:10px 14px;border:1.5px solid var(--line);border-radius:14px;background:var(--soft);cursor:pointer}
.opt input{position:absolute;opacity:0;width:1px;height:1px}.au{margin-top:12px}.sa{margin:12px 0 2px}
.opt b{display:block;font-weight:600;line-height:1.45}
.opt small{display:block;font-size:12.5px;color:var(--mut)}
.ck{margin-inline-start:auto;width:24px;height:24px;border-radius:50%;border:1.5px solid var(--dash);display:grid;place-items:center;color:transparent;flex:none}
.ck .i{width:14px;height:14px;stroke-width:3}
.opt:has(input:checked){border-color:var(--pri);background:var(--prisoft)}
.opt:has(input:checked) .ck{background:var(--pri);border-color:var(--pri);color:var(--prik)}
.opt:has(input:focus-visible){outline:2px solid var(--pri);outline-offset:2px}
.pi{width:42px;height:42px;border-radius:12px;display:grid;place-items:center;flex:none;font:700 17px/1 var(--mono);background:var(--card);border:1px solid var(--line)}
.ta{width:100%;box-sizing:border-box;min-height:110px;padding:12px 14px;border:1px solid var(--line);border-radius:12px;background:var(--soft);color:var(--ink);font:inherit;font-size:16px;line-height:1.6;outline:0;resize:vertical}
.ta:focus,.fs:focus{border-color:var(--pri);box-shadow:0 0 0 3px var(--ring);background:var(--card)}
.ta::placeholder{color:var(--mut);opacity:.8}
.fs{width:100%;height:46px;padding:0 12px;border:1px solid var(--line);border-radius:12px;background:var(--soft);font-size:16px;outline:0}
.nk .opt{min-height:58px}
.pi.k-info{color:var(--pri)}.pi.k-warn{color:var(--warn);background:var(--warnsoft)}.pi.k-urgent{color:var(--bad);background:var(--badsoft)}
.nl{list-style:none;padding:0;margin:12px 0 0;display:grid;gap:10px}
.nl li{border:1px solid var(--line);border-radius:14px;padding:10px 12px 12px;background:var(--soft)}
.nh{display:flex;align-items:center;gap:8px;font-size:13px}.nh form{margin-inline-start:auto}.nh .ib{width:36px;height:36px}
.nb{border-radius:99px;padding:1px 10px;font-size:12.5px;font-weight:600;background:var(--prisoft);color:var(--pri)}
.nb.k-warn{background:var(--warnsoft);color:var(--warn)}.nb.k-urgent{background:var(--badsoft);color:var(--bad)}
.ldbar{position:fixed;top:0;inset-inline:0;z-index:200;height:3px;display:none;background:linear-gradient(90deg,transparent,var(--pri),transparent) no-repeat;background-size:45% 100%;animation:ldbar 1s linear infinite}
html.loading .ldbar{display:block}
.ldpill{position:fixed;top:14px;left:50%;transform:translateX(-50%);z-index:201;display:none;align-items:center;gap:9px;padding:9px 16px;border-radius:99px;background:var(--ink);color:var(--card);font-size:14px;font-weight:600;box-shadow:var(--pop);white-space:nowrap}
html.loading .ldpill{display:flex}
.ldpill::before{content:"";width:16px;height:16px;flex:none;border-radius:50%;border:2px solid currentColor;border-top-color:transparent;animation:spin .7s linear infinite}
@keyframes ldbar{0%{background-position:-60% 0}100%{background-position:160% 0}}
.btn.busy,.ib.busy,.hb.busy{opacity:1;position:relative;color:transparent!important;pointer-events:none}
.btn.busy .i,.ib.busy .i,.hb.busy .i{visibility:hidden}
.btn.busy::after,.ib.busy::after,.hb.busy::after{content:"";position:absolute;top:50%;left:50%;width:16px;height:16px;margin:-8px 0 0 -8px;border-radius:50%;border:2px solid rgba(255,255,255,.45);border-top-color:#fff;animation:spin .7s linear infinite}
.btn.ghost.busy::after,.ib.busy::after{border-color:var(--line);border-top-color:var(--pri)}
@keyframes spin{to{transform:rotate(360deg)}}
.lz{margin-top:8px}.lz .wait{color:var(--mut);font-size:13px}.lz h4{margin:10px 0 6px;font-size:13px;color:var(--mut);font-weight:600}
.fl .more{background:none;color:var(--mut);padding-inline:2px}.shown{text-align:center;margin-top:12px;font-size:13px}
.fa-all{display:flex;gap:6px;flex-wrap:wrap}.fa-all form{margin:0}.fa-all .btn{margin:0}
.ft{font-size:14.5px;font-weight:600;line-height:1.6}.fk{display:inline-block;border-radius:99px;padding:0 9px;font-size:12px;font-weight:600;margin-inline-end:4px}
.fk.k-urgent{background:var(--badsoft);color:var(--bad)}.fk.k-warn{background:var(--warnsoft);color:var(--warn)}
.fs2{font-size:12.5px}.fm{font-size:14px}
.fsum{display:flex;flex-wrap:wrap;gap:6px}.fsum span{border:1px solid var(--line);border-radius:9px;padding:3px 10px;font-size:12.5px;color:var(--mut)}.fsum b{color:var(--ink)}.fsum .bad,.fsum .bad b{color:var(--bad)}
.fl{list-style:none;margin:8px 0 0;padding:0;display:grid;gap:4px;font-size:12.5px}.fl li{padding:6px 10px;border-radius:8px;background:var(--soft);overflow-wrap:anywhere}
.prc{padding:0 16px}.prc summary{display:flex;flex-wrap:wrap;gap:6px 12px;align-items:center;min-height:54px;list-style:none;cursor:pointer}
.prc summary::-webkit-details-marker{display:none}.prc summary>.i{order:1;margin-inline-start:auto;width:18px;height:18px;color:var(--mut);transition:transform .2s}
.prc[open] summary>.i{transform:rotate(180deg)}.prc-h{display:flex;gap:8px;align-items:center}.prc-h .i{width:18px;height:18px;color:var(--pri)}
.prc-s{order:2;display:flex;flex-wrap:wrap;gap:4px 10px;font-size:12.5px;color:var(--mut);flex-basis:100%;margin-top:-6px;padding-bottom:12px}.prc form{padding-bottom:16px}.prc .mut{margin:0 0 4px;font-size:13px}
.pr-ta{min-height:300px;font-size:14px;line-height:1.75}.pm{display:inline-block;font:12px/1.6 ui-monospace,Menlo,Consolas,monospace;padding:0 6px;border-radius:6px;background:var(--soft);border:1px solid var(--line);color:var(--ink)}
.prt{margin:2px 0 14px;padding:14px;border:1px dashed var(--line);border-radius:14px}.prt .l{margin-top:0}.prt-r{display:flex;gap:8px;margin-top:8px}.prt-r .fs{flex:1;height:44px}.prt-r .btn{flex:none;min-width:96px}
.prt-o{margin:10px 0 0;padding:12px 14px;border-radius:12px;background:var(--soft);border:1px solid var(--line);font-size:15px;line-height:1.75;overflow-wrap:anywhere}.prt-o small{display:block;margin-top:4px;color:var(--mut);font-size:12px}.prt-t{display:-webkit-box;-webkit-line-clamp:3;-webkit-box-orient:vertical;overflow:hidden;margin-bottom:8px;padding-bottom:8px;border-bottom:1px dashed var(--line);font-size:13px;line-height:1.6;color:var(--mut)}.prt-o.bad{color:var(--bad);background:var(--badsoft);border-color:transparent}
.prg{display:grid;grid-template-columns:1fr 1fr;gap:10px}.prw{margin-top:14px;padding-top:14px;border-top:1px solid var(--line)}.prc .prh{margin:6px 0 0;font-size:12px}.prf{display:grid;gap:6px;font-size:13px;font-weight:500;color:var(--mut)}.prf .fs{height:44px;font-variant-numeric:tabular-nums}
.tg{display:inline-block;margin-inline-start:6px;padding:1px 7px;border-radius:99px;font-size:11px;font-weight:600;vertical-align:2px;background:var(--soft);color:var(--mut);border:1px solid var(--line)}
.tg.pp{background:var(--prisoft);color:var(--pri);border-color:transparent}
.bal b{color:var(--pri)}.bal.low b{color:var(--bad)}
.led{margin-top:8px;font-size:13px}.led summary{cursor:pointer;color:var(--mut);min-height:32px;display:flex;align-items:center}
.led ul{list-style:none;margin:4px 0 0;padding:0;display:grid;gap:6px}.led li{display:grid;grid-template-columns:1fr auto;gap:0 10px;padding:8px 10px;border-radius:10px;background:var(--soft)}
.led li small{grid-column:1/-1;color:var(--mut);font-size:11.5px}.led .pl{color:var(--pri)}.led .mi{color:var(--bad)}
.fl-ok{background:var(--prisoft);color:var(--pri)}.fl-bad{background:var(--badsoft);color:var(--bad)}
.mvd{display:grid;gap:8px;margin:12px 0 4px;font-size:14px}.mvd div{display:flex;gap:12px;align-items:baseline}.mvd dt{color:var(--mut);min-width:72px;flex:none}.mvd dd{margin:0}
.mc{font:700 16px/1 var(--mono);letter-spacing:1px;background:var(--soft);border:1px solid var(--line);border-radius:8px;padding:4px 8px;direction:ltr;display:inline-block}
.bk{display:flex;gap:8px;align-items:center;font-size:14px;margin:10px 0 0;color:var(--pri)}.bk.none{color:var(--warn)}.bk .i{width:18px;height:18px;flex:none}
.ckl{display:flex;gap:10px;align-items:center;margin:14px 0 0;font-size:14px;cursor:pointer}
:root{--s1:#2a78d6;--s2:#eb6834;--s3:#1baf7a}[data-theme=dark]{--s1:#3987e5;--s2:#d95926;--s3:#199e70}
.hch{margin:12px 0 4px}.hch .i{width:17px;height:17px}
.ask.ch{max-width:620px}.ch-h{display:flex;align-items:center;justify-content:space-between;gap:10px}
.ch-seg{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:4px;margin-top:12px;padding:4px;border-radius:12px;background:var(--soft)}
.ch-seg button{height:34px;border:0;border-radius:9px;background:none;color:var(--mut);font:inherit;font-size:13px;font-weight:600;cursor:pointer}
.ch-seg button[aria-selected=true]{background:var(--card);color:var(--ink);box-shadow:0 1px 2px rgba(0,0,0,.08),0 0 0 1px var(--line)}
.ch-lg{display:flex;flex-wrap:wrap;gap:6px;margin-top:12px}
.ch-lg button{display:inline-flex;align-items:center;gap:7px;min-height:34px;padding:0 11px;border:1px solid var(--line);border-radius:99px;background:var(--card);color:var(--ink);font:inherit;font-size:12.5px;cursor:pointer}
.ch-lg button[aria-pressed=false]{opacity:.42}.ch-lg b{font-variant-numeric:tabular-nums}
.ch-lg i,.ch-tip i{display:inline-block;width:14px;height:3px;border-radius:2px;background:var(--c);flex:none}.ch-lg i.sq{width:10px;height:10px;border-radius:3px}
.ch-box{position:relative;margin-top:10px;direction:ltr;min-height:120px}#ch-svg{display:block;width:100%;height:220px;overflow:visible}
.ch-tip{position:absolute;z-index:2;pointer-events:none;min-width:140px;padding:8px 11px;border:1px solid var(--line);border-radius:10px;background:var(--card);box-shadow:var(--pop);font-size:12px;direction:rtl;text-align:right}
.ch-tip .d{color:var(--mut);margin-bottom:2px}.ch-tip .r{display:flex;align-items:center;gap:7px;margin-top:3px}.ch-tip b{font-variant-numeric:tabular-nums;color:var(--ink)}.ch-tip span{color:var(--mut)}
.ch-empty{margin:0;padding:44px 8px;text-align:center;color:var(--mut);font-size:13px;direction:rtl}
.ch-users{display:grid;gap:12px;direction:rtl;padding:2px 0}.ch-u{display:grid;gap:6px;outline:0;border-radius:8px}.ch-u:focus-visible{box-shadow:0 0 0 3px var(--ring)}
.ch-u .nm{display:flex;justify-content:space-between;gap:10px;font-size:13px}.ch-u .nm span{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}.ch-u .nm b{font-variant-numeric:tabular-nums}
.ch-u .bar{display:flex;gap:2px;height:16px}.ch-u .bar span{display:block;height:100%;background:var(--c)}.ch-u .bar span:last-child{border-radius:4px 0 0 4px}
.ch-note{margin:10px 0 0;font-size:12px}.ch-tb{margin-top:10px}.ch-tb summary{cursor:pointer;font-size:13px;color:var(--mut)}
.ch-tw{overflow:auto;max-height:260px;margin-top:8px;border:1px solid var(--line);border-radius:10px}
#ch-table{width:100%;border-collapse:collapse;font-size:12.5px}#ch-table th,#ch-table td{padding:7px 10px;border-bottom:1px solid var(--line);text-align:right;white-space:nowrap}
#ch-table th{position:sticky;top:0;background:var(--soft);color:var(--mut);font-weight:600}#ch-table td.n{font-variant-numeric:tabular-nums}.ckl input{width:20px;height:20px;accent-color:var(--pri);flex:none}
.rs{margin-top:14px}.rs summary{min-height:40px}
.pk{display:none;margin-top:10px;max-height:260px;overflow:auto;border:1px solid var(--line);border-radius:12px;background:var(--soft)}
.pub:has(input[value=some]:checked) .pk,.apub:has(input[value=some]:checked) .pk,.pk.on{display:block}
.pkr{display:flex;gap:10px;align-items:center;min-height:46px;padding:8px 12px;border-bottom:1px solid var(--line);cursor:pointer;font-size:14px}
.pkr:last-child{border-bottom:0}.pkr input{width:20px;height:20px;accent-color:var(--pri);flex:none;margin:0}
.pkn{flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-weight:500}
.pkc{font:12px/1 var(--mono);color:var(--mut);direction:ltr}.pkr.off .pkn{color:var(--mut)}.pke{margin:0;padding:12px;color:var(--mut);font-size:14px}
.pil{margin-top:18px;padding:14px;border:1.5px dashed var(--pri);border-radius:14px;background:var(--prisoft)}
.pil-h,.pil-w{display:flex;gap:10px;align-items:flex-start;margin:0;font-size:14px;line-height:1.6}.pil-h .i,.pil-w .i{width:18px;height:18px;flex:none;margin-top:2px;color:var(--pri)}
.pil-w{margin-top:10px;color:var(--bad)}.pil-w .i{color:var(--bad)}
.pil-a{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin-top:12px}.pil-a form{margin:0}.pil-a .btn{margin:0;width:100%}
input[type=file].fs{height:auto;padding:10px 12px;width:100%;margin-bottom:4px}
.nav .cnt{position:absolute;top:6px;inset-inline-start:calc(50% + 6px);min-width:18px;height:18px;padding:0 5px;border-radius:99px;background:var(--bad);color:var(--badk);font-style:normal;font-size:11px;font-weight:700;line-height:18px;text-align:center;box-shadow:0 0 0 2px var(--card)}
.sh{display:flex;align-items:center;gap:10px;justify-content:space-between}.sh .btn{margin:0}
.btn.sm{min-height:38px;height:38px;padding:0 13px;font-size:13.5px}
.ml{display:grid;gap:12px;margin-top:16px}
.msg{background:var(--card);border:1px solid var(--line);border-radius:16px;padding:14px;display:grid;gap:10px;min-width:0}
.msg.new{border-color:var(--pri);box-shadow:inset 3px 0 0 var(--pri)}
.mh{display:flex;gap:12px;align-items:center;min-width:0}
.mh p{font-size:12.5px;color:var(--mut)}
.nw{display:inline-block;vertical-align:middle;border-radius:99px;padding:0 9px;font-size:11.5px;font-weight:600;background:var(--prisoft);color:var(--pri)}
.nw.tp{background:#fef0c7;color:#93370d}
.mt{white-space:pre-wrap;overflow-wrap:anywhere;font-size:15px;line-height:1.75}
.mf{display:grid;grid-template-columns:repeat(auto-fill,minmax(130px,1fr));gap:8px}
.mi{display:block;border-radius:12px;overflow:hidden;border:1px solid var(--line);background:var(--soft);aspect-ratio:3/4}
.mi img{width:100%;height:100%;object-fit:cover;display:block}
.mv{grid-column:1/-1;width:100%;max-height:420px;border-radius:12px;background:#000}
.mm summary{min-height:36px;margin:0}
.md{display:grid;gap:6px;margin:8px 0;font-size:13px}.md div{display:flex;gap:10px}.md dt{color:var(--mut);min-width:64px}.md dd{margin:0;overflow-wrap:anywhere}
.lg{margin:0;max-height:260px;overflow:auto;padding:10px 12px;border-radius:10px;background:var(--soft);border:1px solid var(--line);font:12px/1.6 var(--mono);white-space:pre-wrap;overflow-wrap:anywhere;direction:rtl;text-align:start;unicode-bidi:plaintext}
.mr{border-radius:12px;background:var(--prisoft);padding:9px 12px;font-size:14px}.mr p{white-space:pre-wrap;overflow-wrap:anywhere;margin-top:2px}
.ma{display:flex;flex-wrap:wrap;gap:8px;align-items:flex-start}.ma .btn{margin:0}.ma .ib{width:38px;height:38px}
.ma form{margin:0}.rp{flex-basis:100%}.rp summary{list-style:none;cursor:pointer;display:inline-flex}.rp summary::-webkit-details-marker{display:none}
.rp[open] summary{margin-bottom:10px}.rp .i{width:16px;height:16px}
.nx{margin-top:6px;white-space:pre-wrap;overflow-wrap:anywhere}.nr{font-size:12.5px;margin-top:4px}
.g2{display:grid;gap:12px;margin-top:12px}.g2 .card{margin:0}
.ph{display:flex;gap:12px;align-items:center}
.b{display:inline-flex;gap:6px;align-items:center;font-size:12.5px;font-weight:600}
.b::before{content:"";width:7px;height:7px;border-radius:50%;background:currentColor}
.b.on{color:var(--pri)}.b.off{color:var(--bad)}
.tag{margin-inline-start:auto;background:var(--prisoft);color:var(--pri);border-radius:99px;padding:2px 11px;font-size:12.5px;font-weight:600;white-space:nowrap}
.hint{display:flex;gap:8px;align-items:flex-start;font-size:13px;color:var(--mut);margin:14px 0 16px}
.hint .i{width:16px;height:16px;margin-top:3px}
.lk{display:block;direction:ltr;text-align:left;word-break:break-all;font:500 13px/1.75 var(--mono);background:var(--soft);border:1px dashed var(--dash);border-radius:12px;padding:12px 14px;margin-top:14px;-webkit-user-select:all;user-select:all}
.da{display:flex;gap:10px;margin-top:20px}.da .btn{flex:1}
.lk + .da{margin-top:12px}
.notes{list-style:none;padding:0;margin-top:20px;display:grid;gap:10px;color:var(--mut);font-size:14px}
.notes li{display:flex;gap:10px;align-items:flex-start}
.notes .i{width:18px;height:18px;margin-top:3px;color:var(--pri)}

/* ---- dialogs: sheets rise from the bottom on phones ---- */
dialog{border:0;padding:0;background:var(--card);color:var(--ink);box-shadow:var(--pop);max-height:calc(100vh - 24px);overflow:auto}
dialog::backdrop{background:rgba(6,14,13,.55)}
dialog[open]{animation:pop .22s cubic-bezier(.2,.8,.2,1)}
.ask{width:calc(100vw - 32px);max-width:420px;margin:12vh auto auto;border-radius:20px}
.sheet{width:100%;max-width:100%;margin:auto 0 0;border-radius:22px 22px 0 0;padding-bottom:var(--sb)}
.sheet[open]{animation:rise .26s cubic-bezier(.2,.8,.2,1)}
@keyframes rise{from{transform:translateY(100%)}}
@keyframes pop{from{transform:translateY(12px);opacity:0}}
.grab{width:38px;height:4px;border-radius:9px;background:var(--dash);margin:9px auto 0}
.dg{padding:20px 18px 18px}
.dg h3{font-size:18px}
.shh{display:flex;gap:12px;align-items:center;padding:12px 16px 14px;border-bottom:1px solid var(--line)}
.shh div:nth-child(2){min-width:0;flex:1}
.shh h3{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.shh bdi{display:block;font:500 13px/1.5 var(--mono);color:var(--mut);direction:ltr;text-align:right}
.shl{display:grid;padding:6px 8px 10px}
.shl button{display:flex;gap:13px;align-items:center;width:100%;min-height:52px;padding:6px 10px;border:0;border-radius:12px;background:none;font-size:15.5px;font-weight:500;text-align:start}
.shl button:hover{background:var(--soft)}
.shl button .i{color:var(--mut)}
.shl small{display:block;font-size:12.5px;font-weight:400;line-height:1.5;color:var(--mut)}
.shl hr{border:0;border-top:1px solid var(--line);margin:6px 10px}
.shl .del button,.shl .del button .i{color:var(--bad)}
.big{display:block;margin-top:16px;padding:22px 8px;border:1.5px dashed var(--dash);border-radius:14px;background:var(--soft);text-align:center;direction:ltr;font:700 clamp(19px,6.2vw,26px)/1 var(--mono);letter-spacing:.06em;-webkit-user-select:all;user-select:all}
.toasts{position:fixed;inset-inline:0;bottom:calc(var(--nav) + var(--sb) + 14px);z-index:99;display:flex;flex-direction:column;align-items:center;gap:8px;padding:0 16px;pointer-events:none}
.toast{background:var(--ink);color:var(--card);padding:10px 18px;border-radius:12px;font-weight:500;font-size:14px;box-shadow:var(--pop);animation:pop .2s}
.toast.out{opacity:0;transition:opacity .3s}

/* ---- wider screens ---- */
@media(min-width:420px){.add .wd{display:inline}}
@media(min-width:600px){
.eng{grid-template-columns:1fr 1fr}
.sheet{width:420px;margin:auto;border-radius:20px;padding-bottom:0}
.sheet[open]{animation-name:pop}
.ask{margin:auto}
.grab{display:none}
.shh{padding-top:16px}
.lk + .da .btn{flex:none}
}
@media(min-width:700px){.list{grid-template-columns:repeat(auto-fill,minmax(330px,1fr));align-items:start;gap:12px}}
@media(min-width:800px){.g2{grid-template-columns:1fr 1fr}.pad{padding:22px}}
@media(min-width:900px){
.wrap{padding-inline:24px}
.topin{min-height:64px}
.nav{position:static;gap:4px;margin-inline-start:20px;padding:0;border:0;background:none}
.nav button{flex:none;flex-direction:row;gap:8px;height:40px;padding:0 14px;border-radius:10px;font-size:14.5px}
.nav .i{width:19px;height:19px}
.nav [aria-current]{background:var(--prisoft)}
.nav [aria-current]::before{display:none}
.nav .dot{position:static;margin-inline-start:-2px;box-shadow:none}
.nav .cnt{position:static;box-shadow:none}
main{padding-bottom:56px}
.toasts{bottom:24px}
.hero{display:grid;grid-template-columns:minmax(0,1fr) minmax(0,1.15fr);align-items:center;gap:0 30px;padding:22px 26px;margin-top:22px}
.kp{margin:0;border-top:0;border-inline-start:1px solid var(--heroline)}
.kp div{padding:6px 0;padding-inline-start:22px}
.kp div:first-child,.kp div:nth-child(3n+1){padding-inline-start:26px}
.kp dd{font-size:24px}
.tb{padding-top:14px}
.search{max-width:420px}
.add{margin-inline-start:auto}
}
@media(prefers-reduced-motion:reduce){*{transition:none!important;animation:none!important}}
</style></head><body>
<svg width="0" height="0" style="position:absolute" aria-hidden="true"><defs>
<symbol id="i-moon" viewBox="0 0 24 24"><path d="M21 12.79A9 9 0 1 1 11.21 3 7 7 0 0 0 21 12.79z"/></symbol>
<symbol id="i-sun" viewBox="0 0 24 24"><circle cx="12" cy="12" r="5"/><path d="M12 1v2M12 21v2M4.22 4.22l1.42 1.42M18.36 18.36l1.42 1.42M1 12h2M21 12h2M4.22 19.78l1.42-1.42M18.36 5.64l1.42-1.42"/></symbol>
<symbol id="i-out" viewBox="0 0 24 24"><path d="M9 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h4M16 17l5-5-5-5M21 12H9"/></symbol>
<symbol id="i-search" viewBox="0 0 24 24"><circle cx="11" cy="11" r="8"/><path d="m21 21-4.35-4.35"/></symbol>
<symbol id="i-plus" viewBox="0 0 24 24"><path d="M12 5v14M5 12h14"/></symbol>
<symbol id="i-more" viewBox="0 0 24 24"><circle cx="12" cy="5" r="1"/><circle cx="12" cy="12" r="1"/><circle cx="12" cy="19" r="1"/></symbol>
<symbol id="i-copy" viewBox="0 0 24 24"><rect x="9" y="9" width="13" height="13" rx="2"/><path d="M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1"/></symbol>
<symbol id="i-phone" viewBox="0 0 24 24"><rect x="5" y="2" width="14" height="20" rx="2"/><path d="M12 18h.01"/></symbol>
<symbol id="i-reset" viewBox="0 0 24 24"><path d="M1 4v6h6"/><path d="M3.51 15a9 9 0 1 0 2.13-9.36L1 10"/></symbol>
<symbol id="i-trash" viewBox="0 0 24 24"><path d="M3 6h18M19 6l-1 14a2 2 0 0 1-2 2H8a2 2 0 0 1-2-2L5 6m3 0V4a2 2 0 0 1 2-2h4a2 2 0 0 1 2 2v2"/></symbol>
<symbol id="i-chev" viewBox="0 0 24 24"><path d="m6 9 6 6 6-6"/></symbol>
<symbol id="i-users" viewBox="0 0 24 24"><path d="M17 21v-2a4 4 0 0 0-4-4H5a4 4 0 0 0-4 4v2"/><circle cx="9" cy="7" r="4"/><path d="M23 21v-2a4 4 0 0 0-3-3.87M16 3.13a4 4 0 0 1 0 7.75"/></symbol>
<symbol id="i-key" viewBox="0 0 24 24"><circle cx="7.5" cy="15.5" r="5.5"/><path d="m11.4 11.6 9.6-9.6M17 6l3 3M14 9l2 2"/></symbol>
<symbol id="i-code" viewBox="0 0 24 24"><path d="M16 18l6-6-6-6M8 6l-6 6 6 6"/></symbol>
<symbol id="i-link" viewBox="0 0 24 24"><path d="M10 13a5 5 0 0 0 7.54.54l3-3a5 5 0 0 0-7.07-7.07l-1.72 1.71"/><path d="M14 11a5 5 0 0 0-7.54-.54l-3 3a5 5 0 0 0 7.07 7.07l1.71-1.71"/></symbol>
<symbol id="i-share" viewBox="0 0 24 24"><path d="M4 12v8a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2v-8M16 6l-4-4-4 4M12 2v13"/></symbol>
<symbol id="i-edit" viewBox="0 0 24 24"><path d="M12 20h9"/><path d="M16.5 3.5a2.12 2.12 0 0 1 3 3L7 19l-4 1 1-4z"/></symbol>
<symbol id="i-check" viewBox="0 0 24 24"><path d="M20 6 9 17l-5-5"/></symbol>
<symbol id="i-x" viewBox="0 0 24 24"><path d="M18 6 6 18M6 6l12 12"/></symbol>
<symbol id="i-eye" viewBox="0 0 24 24"><path d="M1 12s4-8 11-8 11 8 11 8-4 8-11 8-11-8-11-8z"/><circle cx="12" cy="12" r="3"/></symbol>
<symbol id="i-sort" viewBox="0 0 24 24"><path d="M3 6h18M6 12h12M10 18h4"/></symbol><symbol id="i-chart" viewBox="0 0 24 24"><path d="M4 4v16h16M8 15l3.5-4 3 2.5L20 7"/></symbol>
<symbol id="i-alert" viewBox="0 0 24 24"><path d="M10.29 3.86 1.82 18a2 2 0 0 0 1.71 3h16.94a2 2 0 0 0 1.71-3L13.71 3.86a2 2 0 0 0-3.42 0zM12 9v4M12 17h.01"/></symbol>
<symbol id="i-lock" viewBox="0 0 24 24"><rect x="3" y="11" width="18" height="11" rx="2"/><path d="M7 11V7a5 5 0 0 1 10 0v4"/></symbol>
<symbol id="i-msg" viewBox="0 0 24 24"><path d="M21 15a2 2 0 0 1-2 2H7l-4 4V5a2 2 0 0 1 2-2h14a2 2 0 0 1 2 2z"/></symbol>
<symbol id="i-bell" viewBox="0 0 24 24"><path d="M18 8A6 6 0 0 0 6 8c0 7-3 9-3 9h18s-3-2-3-9M13.73 21a2 2 0 0 1-3.46 0"/></symbol>
<symbol id="i-shield" viewBox="0 0 24 24"><path d="M12 22s8-4 8-10V5l-8-3-8 3v7c0 6 8 10 8 10z"/></symbol>
</defs></svg>

<div class="ldbar" aria-hidden="true"></div><div class="ldpill" role="status" aria-live="polite">جارٍ التنفيذ…</div>
<header class="top"><div class="wrap topin">
<div class="brand"><div class="logo" aria-hidden="true">ق</div><div><b>لوحة التحكّم</b><small>رموز الدخول والمفاتيح</small></div></div>
<nav class="nav" aria-label="أقسام اللوحة">
<button type="button" data-t="users" aria-current="page">{{ic('users')}}<span>المستخدمون</span></button>
<button type="button" data-t="keys">{{ic('key')}}<span>المفاتيح</span>{% if nokey %}<i class="dot" title="لا يوجد مفتاح للكاتب الحالي"></i>{% endif %}</button>
<button type="button" data-t="notices">{{ic('bell')}}<span>التنبيهات</span></button>
<button type="button" data-t="support">{{ic('msg')}}<span>الرسائل</span>{% if unread %}<i class="cnt" title="{{unread}} رسالة جديدة">{{unread}}</i>{% endif %}</button>
<button type="button" data-t="failures">{{ic('alert')}}<span>الأعطال</span>{% if failures_new %}<i class="cnt" title="{{failures_new}} عطل جديد">{{failures_new}}</i>{% endif %}</button>
<button type="button" data-t="script">{{ic('code')}}<span>السكربت</span>{% if script_can_publish %}<i class="dot" title="تحديث جاهز للنشر"></i>{% endif %}</button>
<button type="button" data-t="link">{{ic('link')}}<span>الربط</span>{% if not backup_when %}<i class="dot" title="لم تُنزَّل نسخة احتياطية بعد"></i>{% endif %}</button>
</nav>
<div class="acts"><button class="ib th" id="th" type="button" aria-label="تبديل المظهر"><span class="m">{{ic('moon')}}</span><span class="s">{{ic('sun')}}</span></button>
<form method="post" action="/{{admin}}/logout"><button class="ib" aria-label="تسجيل الخروج" title="تسجيل الخروج">{{ic('out')}}</button></form></div>
</div></header>

<main class="wrap">
<section class="panel on" id="p-users">
{% if flash %}<div class="note fl-{{flash.kind}}" role="status">{{ic('alert' if flash.kind != 'ok' else 'check')}}<p>{{flash.text}}</p></div>{% endif %}
{% if nokey and codes %}<div class="note" role="status">{{ic('alert')}}<p>لا يوجد مفتاح للكاتب الحالي، فلن تُكتب أي تعليقات. <button type="button" data-t="keys">أضف المفتاح</button></p></div>{% endif %}
{% if codes %}
<section class="hero" aria-label="ملخّص المستخدمين">
<div>
<div class="ht"><div class="tot"><b>{{stats.users}}</b><span>مستخدم</span></div>
{% if stats.comments %}<form method="post" action="/{{admin}}/reset-cost-all" data-title="تصفير كل التكاليف؟" data-confirm="سيُصفَّر عدّاد التعليقات والتكلفة لكل المستخدمين، ويبقى محسوبًا في «منذ البداية» أعلى الصفحة." data-yes="تصفير التكاليف" data-kind="danger" data-toast="تم تصفير كل التكاليف"><button class="hb">{{ic('reset')}}تصفير التكاليف</button></form>{% endif %}</div>
<div class="ratio" aria-hidden="true"><i style="width:{{ stats.active * 100 / stats.users }}%"></i></div>
<div class="rl"><span><b>{{stats.active}}</b> يعمل</span><span><b>{{stats.users - stats.active}}</b> موقوف</span></div>
<button type="button" class="hb hch" id="ch-open" data-open="chart">{{ic('chart')}}الرسم البياني</button>
</div>
<dl class="kp">
<div><dt>أجهزة مربوطة</dt><dd>{{stats.bound}}</dd></div>
<div><dt>تعليقات مكتوبة</dt><dd>{{ '{:,}'.format(stats.comments) }}</dd><small class="kpa">منذ البداية <bdi dir="ltr">{{ '{:,}'.format(stats.all_comments) }}</bdi></small></div>
<div><dt>التكلفة</dt><dd>${{ '%.2f'|format(stats.cost) }}</dd><small class="kpa">منذ البداية <bdi dir="ltr">${{ '%.2f'|format(stats.all_cost) }}</bdi></small></div>
<div><dt>الرتويت</dt><dd>{{ '{:,}'.format(stats.repost) }}</dd></div>
<div><dt>الإعجاب</dt><dd>{{ '{:,}'.format(stats.like) }}</dd></div>
<div><dt>المرجعية</dt><dd>{{ '{:,}'.format(stats.bookmark) }}</dd></div>
</dl>
</section>
{% set pn = {'comment': 'تعليق', 'like': 'إعجاب', 'repost': 'إعادة نشر', 'bookmark': 'مرجعية'} %}
<details class="card prc"><summary><span class="prc-h">{{ic('key')}}<b>أسعار الخدمات</b></span><span class="prc-s">{% for k in ['comment', 'like', 'repost', 'bookmark'] %}<span>{{pn[k]}} <bdi dir="ltr">${{ '%g'|format(prices[k]) }}</bdi></span>{% endfor %}<span>حساب جديد <bdi dir="ltr">${{ '%g'|format(welcome) }}</bdi></span></span>{{ic('chev')}}</summary>
<form method="post" action="/{{admin}}/prices" data-toast="تم حفظ الأسعار"><p class="mut">سعر كل خدمة ناجحة بالدولار، و0 للمجانية. «آجل»: تُجمع التكلفة. «مسبق»: تُخصم من الرصيد، ولا تبدأ مهمة إن لم يكفِ لأرخص خدماتها؛ والمهمة التي بدأت تكمل إلى آخرها ولو نفد الرصيد في نصها (يصير بالسالب، وتسدّه الشحنة التالية). السعر الجديد يُطبَّق من الآن، وما حُسب قبله يبقى.</p>
<div class="prg">{% for k in ['comment', 'like', 'repost', 'bookmark'] %}<label class="prf"><span>{{pn[k]}}</span><input class="fs" name="{{k}}" dir="ltr" inputmode="decimal" autocomplete="off" value="{{ '%g'|format(prices[k]) }}"></label>{% endfor %}</div>
<label class="prf prw"><span>رصيد الحساب الجديد</span><input class="fs" name="welcome" dir="ltr" inputmode="decimal" autocomplete="off" value="{{ '%g'|format(welcome) }}"></label>
<p class="mut prh">يُضاف تلقائيًا لكل من ينشئ حسابًا جديدًا في التطبيق، مرة واحدة لكل جوال. و0 يوقفه.</p>
<button class="btn wide" style="margin-top:14px">حفظ الأسعار</button></form></details>
<details class="card prc" id="pay-card"><summary><span class="prc-h">{{ic('key')}}<b>الدفع عبر Binance</b></span><span class="prc-s"><span>{{ ('المعرّف ' ~ pay.binance_id) if pay.binance_id else 'لم يُحدَّد المعرّف' }}</span><span>{{ 'تحقق تلقائي' if pay.auto else 'تحقق يدوي' }}</span></span>{{ic('chev')}}</summary>
<form method="post" action="/{{admin}}/payment" data-toast="تم الحفظ"><p class="mut">يظهر معرّفك للمستخدم في «شحن رصيد»: يحوّل إليه عبر Binance Pay بعملة USDT، ثم يكتب المبلغ ورقم العملية (Order ID). مع مفتاح Binance API يتحقق الخادم من وصول التحويل إلى حسابك (وارد، بعملة دولارية، بالمبلغ نفسه، ولم يُستخدم من قبل) ويشحن رصيده فورًا. بدون المفتاح يصلك طلبه في «رسائل العملاء» لتتحقق بنفسك.</p>
<p class="l">معرّف Binance Pay (Binance ID)</p>
<input class="fs" name="binance_id" dir="ltr" inputmode="numeric" autocomplete="off" value="{{ pay.binance_id }}" placeholder="123456789">
<p class="l">ملاحظة للمستخدم <small>(اختياري)</small></p>
<textarea class="ta" name="note" maxlength="500" rows="3" placeholder="مثال: أقل شحن 5$.">{{ pay.note }}</textarea>
<p class="l">مفتاح Binance API <small>(للتحقق التلقائي، بصلاحية القراءة فقط)</small></p>
<input class="fs" name="api_key" dir="ltr" autocomplete="off" spellcheck="false" placeholder="{{ 'محفوظ: اتركه فارغًا ليبقى' if pay.auto else 'API Key' }}">
<p class="l">السر (Secret Key)</p>
<input class="fs" name="api_secret" type="password" dir="ltr" autocomplete="new-password" spellcheck="false" placeholder="{{ 'محفوظ: اتركه فارغًا ليبقى' if pay.auto else 'Secret Key' }}">
<p class="mut" style="margin-top:8px">أنشئ المفتاح من Binance ← API Management بصلاحية «Enable Reading» فقط، بلا تداول ولا سحب، ويُفضَّل تقييده بعنوان IP هذا الخادم. يبقى على هذا الخادم ولا يظهر في اللوحة.</p>
<button class="btn wide" style="margin-top:14px">حفظ</button></form>
{% if pay.auto %}<div class="row" style="display:flex;gap:8px;margin-top:10px"><form method="post" action="/{{admin}}/binance/test" style="flex:1"><button class="btn ghost wide">اختبار الاتصال</button></form>
<form method="post" action="/{{admin}}/binance/forget" style="flex:1" data-title="حذف مفتاح Binance؟" data-confirm="يتوقف التحقق التلقائي، وتصلك طلبات الشحن في «رسائل العملاء»." data-yes="حذف" data-kind="danger" data-toast="حُذف المفتاح"><button class="btn ghost wide">حذف المفتاح</button></form></div>{% endif %}</details>
<details class="card prc"><summary><span class="prc-h">{{ic('sort')}}<b>سرعة التنفيذ</b></span><span class="prc-s"><span>كتابة التعليق <bdi dir="ltr">{{ '%g'|format(pace.typing[0]) }}–{{ '%g'|format(pace.typing[1]) }}</bdi> ث</span><span>بين الأزرار <bdi dir="ltr">{{ '%g'|format(pace.gap[0]) }}–{{ '%g'|format(pace.gap[1]) }}</bdi> ث</span><span>بعد التحميل <bdi dir="ltr">{{ '%g'|format(pace.settle[0]) }}–{{ '%g'|format(pace.settle[1]) }}</bdi> ث</span>{% if pace.in_page_on %}<span>فتح سريع <bdi dir="ltr">{{ pace.in_page[0] }}–{{ pace.in_page[1] }}</bdi> تغريدات</span>{% else %}<span>فتح سريع: متوقف</span>{% endif %}</span>{{ic('chev')}}</summary>
<form method="post" action="/{{admin}}/pace" data-toast="تم حفظ سرعة التنفيذ"><p class="mut">بالثواني، ويختار التطبيق كل مرة رقمًا عشوائيًا بين «من» و«إلى». تُطبَّق على كل المستخدمين من مهمتهم التالية.</p>
<p class="l">مدة كتابة التعليق كله</p>
<div class="prg"><label class="prf"><span>من</span><input class="fs" name="typing_from" dir="ltr" inputmode="decimal" autocomplete="off" value="{{ '%g'|format(pace.typing[0]) }}"></label><label class="prf"><span>إلى</span><input class="fs" name="typing_to" dir="ltr" inputmode="decimal" autocomplete="off" value="{{ '%g'|format(pace.typing[1]) }}"></label></div>
<p class="l">بين نقر كل زر والذي بعده</p>
<div class="prg"><label class="prf"><span>من</span><input class="fs" name="gap_from" dir="ltr" inputmode="decimal" autocomplete="off" value="{{ '%g'|format(pace.gap[0]) }}"></label><label class="prf"><span>إلى</span><input class="fs" name="gap_to" dir="ltr" inputmode="decimal" autocomplete="off" value="{{ '%g'|format(pace.gap[1]) }}"></label></div>
<p class="l">بعد تحميل التغريدة وقبل أول نقرة <small>(لا ينقر قبل أن تظهر أزرار التغريدة)</small></p>
<div class="prg"><label class="prf"><span>من</span><input class="fs" name="settle_from" dir="ltr" inputmode="decimal" autocomplete="off" value="{{ '%g'|format(pace.settle[0]) }}"></label><label class="prf"><span>إلى</span><input class="fs" name="settle_to" dir="ltr" inputmode="decimal" autocomplete="off" value="{{ '%g'|format(pace.settle[1]) }}"></label></div>
<input type="hidden" name="in_page_form" value="1">
<label class="opt au"><input type="checkbox" name="in_page_on" value="1"{% if pace.in_page_on %} checked{% endif %}><span class="pi">{{ic('sort')}}</span><span><b>الفتح السريع للتغريدات</b><small>تُفتح التغريدة داخل صفحة X بدون تحميلها كاملة، بالعدد الذي تحدده تحت. متوقف: كل تغريدة تُحمَّل كاملة</small></span><span class="ck">{{ic('check')}}</span></label>
<p class="l">عدد التغريدات التي تُفتح بدون تحميل الصفحة كاملة <small>(مع الفتح السريع؛ عدد صحيح، وبعدها تُحمَّل التغريدة التالية كاملة)</small></p>
<div class="prg"><label class="prf"><span>من</span><input class="fs" name="in_page_from" dir="ltr" inputmode="numeric" autocomplete="off" value="{{ pace.in_page[0] }}"></label><label class="prf"><span>إلى</span><input class="fs" name="in_page_to" dir="ltr" inputmode="numeric" autocomplete="off" value="{{ pace.in_page[1] }}"></label></div>
<button class="btn wide" style="margin-top:14px">حفظ سرعة التنفيذ</button></form></details>
<details class="card prc" id="dv-card"><summary><span class="prc-h">{{ic('phone')}}<b>الأجهزة</b></span><span class="prc-s"><span>{{ 'جهاز واحد لكل مستخدم' if one_device else 'عدة أجهزة لكل مستخدم' }}</span><span>الأجوال المسجّلة: <bdi dir="ltr">{{stats.bound}}</bdi></span></span>{{ic('chev')}}</summary>
<form method="post" action="/{{admin}}/devices" data-toast="تم الحفظ"><p class="mut">على كم جوال يعمل رمز المستخدم أو حسابه. الرصيد والتعليقات والأرقام واحدة له على كل جوالاته.</p>
<div class="eng">
<label class="opt"><input type="radio" name="one_device" value="0"{% if not one_device %} checked{% endif %}><span class="pi">{{ic('users')}}</span><span><b>عدة أجهزة</b><small>يدخل برمزه أو حسابه من أي جوال، وتعمل كلها معًا</small></span><span class="ck">{{ic('check')}}</span></label>
<label class="opt"><input type="radio" name="one_device" value="1"{% if one_device %} checked{% endif %}><span class="pi">{{ic('lock')}}</span><span><b>جهاز واحد</b><small>يعمل على أول جوال دخل به فقط، حتى «تحرير الأجهزة»؛ وأجواله الأخرى تخرج</small></span><span class="ck">{{ic('check')}}</span></label>
</div>
<button class="btn wide" style="margin-top:14px">حفظ</button></form></details>
<details class="card prc" id="pr-card"><summary><span class="prc-h">{{ic('edit')}}<b>برومبت التعليقات</b></span><span class="prc-s"><span>{{ 'مُعدَّل' if prompt.custom else 'الافتراضي' }}</span><span>حتى <bdi dir="ltr">{{prompt.max_chars}}</bdi> حرف</span><span><bdi dir="ltr">{{prompt.angles|length}}</bdi> زاوية · <bdi dir="ltr">{{prompt.manners|length}}</bdi> أسلوب</span></span>{{ic('chev')}}</summary>
<form method="post" action="/{{admin}}/prompt" data-toast="تم حفظ البرومبت" id="pr-form"><p class="mut">ما يُطلب من الذكاء الاصطناعي في كل تعليق. التعليقات تُكتب على هذا الخادم، فيُطبَّق التعديل على كل المستخدمين من التعليق التالي، بلا تحديث للتطبيق أو السكربت.</p>
<label class="l" for="pr-text">التعليمات</label>
<textarea id="pr-text" class="ta pr-ta" name="text" dir="auto" rows="12" maxlength="8000" spellcheck="false">{{prompt.text}}</textarea>
<p class="mut prh">يوضع في كل تعليق مكان: <bdi class="pm">{angle}</bdi> زاوية من القائمة · <bdi class="pm">{manner}</bdi> أسلوب الحساب · <bdi class="pm">{words}</bdi> عدد الكلمات · <bdi class="pm">{max_chars}</bdi> أقصى طول · <bdi class="pm">{voice}</bdi> صيغة الرد التي اختارها المستخدم (مذكر، مؤنث، محايد).</p>
<label class="l" for="pr-angles">زوايا الرد <small>(سطر لكل زاوية، تُختار واحدة عشوائيًا لكل تعليق)</small></label>
<textarea id="pr-angles" class="ta" name="angles" dir="auto" rows="6" spellcheck="false">{{prompt.angles_text}}</textarea>
<label class="l" for="pr-manners">أساليب الكتابة <small>(سطر لكل أسلوب، ولكل حساب أسلوب ثابت منها)</small></label>
<textarea id="pr-manners" class="ta" name="manners" dir="auto" rows="6" spellcheck="false">{{prompt.manners_text}}</textarea>
<label class="prf prw"><span>أقصى طول للتعليق (حروف مع المسافات)</span><input class="fs" name="max_chars" dir="ltr" inputmode="numeric" autocomplete="off" value="{{prompt.max_chars}}"></label>
<p class="mut prh">من 60 إلى 280، وعدد الكلمات المطلوب يتبعه تلقائيًا. الخانة الفارغة تعني الافتراضي.</p>
<button class="btn wide" style="margin-top:14px">حفظ البرومبت</button></form>
<div class="prt"><p class="l">جرّب قبل الحفظ</p>
<textarea id="pr-tweet" class="ta" rows="3" dir="auto" maxlength="4000" placeholder="الصق رابط التغريدة أو نصها…" aria-label="رابط تغريدة أو نصها للتجربة"></textarea>
<div class="prt-r"><select id="pr-voice" class="fs" aria-label="صيغة الرد"><option value="male">مذكر</option><option value="female">مؤنث</option><option value="neutral">محايد</option></select><button type="button" class="btn ghost" id="pr-go">جرّب</button></div>
<p id="pr-out" class="prt-o" aria-live="polite" hidden></p>
<p class="mut prh">يكتب تعليقًا واحدًا بما هو مكتوب أعلاه ولو لم تحفظه، بمفتاحك الحالي، ولا يُحسب على أي مستخدم. ومن الرابط يقرأ التغريدة كما يقرأها التطبيق: نصها، والتغريدة التي تقتبسها، وصورتها إن كان نصها قصيرًا.</p></div>
{% if prompt.custom %}<form method="post" action="/{{admin}}/prompt/reset" data-title="استعادة البرومبت الافتراضي؟" data-confirm="تُمسح تعديلاتك على التعليمات والزوايا والأساليب والطول، ويعود كل شيء كما كان في البداية." data-yes="استعادة الافتراضي" data-kind="danger" data-toast="عاد البرومبت الافتراضي"><button class="btn ghost wide" style="margin:0 0 16px">استعادة الافتراضي</button></form>{% endif %}
<script>(function(){var f=document.getElementById('pr-form'),go=document.getElementById('pr-go'),out=document.getElementById('pr-out');if(!f||!go)return;
function show(text,bad,note,tweet){out.hidden=false;out.className='prt-o'+(bad?' bad':'');out.textContent='';
if(tweet){var t=document.createElement('span');t.className='prt-t';t.textContent=(tweet.by?'\u2066@'+tweet.by+'\u2069: ':'')+(tweet.text||'')+(tweet.picture?' (مع صورتها)':'');out.appendChild(t)}
out.appendChild(document.createTextNode(text));if(note){var s=document.createElement('small');s.textContent=note;out.appendChild(s)}}
go.addEventListener('click',function(){var tw=document.getElementById('pr-tweet').value.trim();if(!tw){show('الصق رابط تغريدة أو نصها أولًا.',true);return}
var d=new FormData(f);d.append('tweet',tw);d.append('voice',document.getElementById('pr-voice').value);go.disabled=true;show('يكتب تعليقًا…');
fetch('/{{admin}}/prompt/try',{method:'POST',body:d,credentials:'same-origin'}).then(function(r){return r.json()}).then(function(j){
if(j.ok){show(j.comment,false,'\u2066'+j.chars+' / '+j.limit+'\u2069 حرف',j.tweet)}else{show(j.error||'تعذّرت التجربة.',true)}}).catch(function(){show('تعذّر الاتصال بالخادم.',true)}).then(function(){go.disabled=false})})})();</script>
</details>
<div class="tb">
<label class="search">{{ic('search')}}<input id="q" type="search" placeholder="ابحث بالاسم أو الرمز" aria-label="ابحث بالاسم أو الرمز" autocomplete="off" autocapitalize="off" spellcheck="false" enterkeyhint="search"><button type="button" class="qx" id="qx" aria-label="مسح البحث" hidden>{{ic('x')}}</button></label>
<button class="btn add" type="button" data-open="nu" aria-label="إضافة مستخدم">{{ic('plus')}}<span>إضافة<span class="wd"> مستخدم</span></span></button>
</div>
<div class="fr">
<div class="seg" id="flt" role="group" aria-label="تصفية حسب الحالة"><button type="button" data-f="all" aria-pressed="true">الكل</button><button type="button" data-f="on" aria-pressed="false">يعمل</button><button type="button" data-f="off" aria-pressed="false">موقوف</button></div>
<label class="sort">{{ic('sort')}}<span id="sol">الأحدث</span><select id="so" aria-label="ترتيب المستخدمين"><option value="new" data-s="الأحدث">الأحدث إضافةً</option><option value="seen" data-s="آخر دخول">آخر دخول</option><option value="top" data-s="الأكثر تعليقًا">الأكثر تعليقًا</option><option value="acts" data-s="الأكثر تنفيذًا">الأكثر تنفيذًا</option><option value="name" data-s="الاسم">الاسم</option></select></label>
</div>
{% endif %}

<div class="list" id="list">
{% for c in codes %}{% set hue = (c.id[:2]|int(0,16)) * 360 // 256 %}
<article class="u{{ '' if c.active else ' off' }}" data-id="{{c.id}}" data-s="{{ 'on' if c.active else 'off' }}" data-name="{{c.label}}" data-code="{{c.code}}" data-bound="{{ '1' if c.device_count else '' }}" data-pay="{{c.pay}}" data-bal="{{ usd(c.balance) }}" data-acct="{{c.account_user}}" data-n="{{c.usage.total}}" data-x="{{ c.acts.repost + c.acts.like + c.acts.bookmark }}" data-seen="{{c.last_seen or 0}}" data-q="{{ (c.label ~ ' ' ~ c.code ~ ' ' ~ c.code|replace('-','') ~ ' ' ~ c.usage.accounts|map(attribute='name')|join(' '))|lower }}">
<div class="who"><div class="av" style="--h:{{hue}}" aria-hidden="true">{{ (c.label or '؟')[:1] }}</div>
<div class="nm"><h3>{{ c.label or 'بدون اسم' }}{% if c.account_user %}<span class="tg">حساب</span>{% endif %}{% if c.pay == 'prepaid' %}<span class="tg pp">مسبق</span>{% endif %}</h3><p><span class="st">{{ 'يعمل' if c.active else 'موقوف' }}</span><span>{% if c.last_seen %}آخر دخول {{c.last_seen_text}}{% else %}لم يدخل بعد{% endif %}</span></p></div></div>
<form method="post" action="/{{admin}}/code/toggle" data-toast="{{ 'تم إيقاف الرمز' if c.active else 'تم تشغيل الرمز' }}"><input type="hidden" name="id" value="{{c.id}}"><button class="sw{{ ' on' if c.active else '' }}" role="switch" aria-checked="{{ 'true' if c.active else 'false' }}" aria-label="رمز {{ c.label or 'بدون اسم' }} يعمل"><i></i></button></form>
<div class="cr"><button type="button" class="code" data-copy="{{c.code}}" aria-label="نسخ الرمز {{c.code}}"><bdi>{{c.code}}</bdi>{{ic('copy')}}</button><button type="button" class="ib" data-more aria-label="خيارات {{ c.label or 'المستخدم' }}">{{ic('more')}}</button></div>
{% set facts %}{% if c.pay == 'prepaid' %}<span class="bal{{ ' low' if c.balance < 0.05 else '' }}" title="الرصيد المسبق">رصيد <b dir="ltr">{{ usd(c.balance) }}</b></span>{% endif %}<span><b>{{ '{:,}'.format(c.usage.total) }}</b> تعليق</span><span title="التكلفة التقديرية"><b>${{ '%.2f'|format(c.usage.cost) }}</b></span><span class="dev{{ ' on' if c.device_count else '' }}">{{ic('phone')}}{{c.devices_text}}</span>{% endset %}
{% if c.usage.accounts %}<details class="acc"><summary class="facts" title="التعليقات حسب حساب X">{{facts}}{{ic('chev')}}</summary>
<p class="alh">حسابات X ({{c.usage.accounts|length}})</p><ul class="al">
{% for a in c.usage.accounts %}<li><b><bdi>{{ ('@' ~ a.name) if a.name else ('#' ~ a.id[:8]) }}</bdi></b><span>{{ '{:,}'.format(a.n) }} تعليق</span><span>${{ '%.2f'|format(a.cost) }}</span><div class="pg"><i style="width:{{ ((a.n * 100 / c.usage.total)|round|int) if c.usage.total else 0 }}%"></i></div></li>{% endfor %}
</ul></details>{% else %}<div class="facts">{{facts}}</div>{% endif %}
{% if c.ledger %}<details class="led"><summary>سجل الرصيد</summary><ul>{% for e in c.ledger %}<li><span>{{e.note}}</span><b class="{{ 'pl' if e.amount > 0 else 'mi' }}" dir="ltr">{{ '+' if e.amount > 0 else '−' }}${{ '%.2f'|format(e.amount|abs) }}</b><small>{{e.when}} · الرصيد <bdi dir="ltr">{{ usd(e.after) }}</bdi></small></li>{% endfor %}</ul></details>{% endif %}
{% if c.acts.at %}<div class="ax" role="group" aria-label="التنفيذ في تطبيق {{ c.label or 'المستخدم' }}">
<div><b>{{ '{:,}'.format(c.acts.repost) }}</b><span>الرتويت</span></div>
<div><b>{{ '{:,}'.format(c.acts.like) }}</b><span>الإعجاب</span></div>
<div><b>{{ '{:,}'.format(c.acts.bookmark) }}</b><span>المرجعية</span></div></div>
<details class="acc axd"><summary class="axs"><span>حسابات <bdi>X</bdi> ({{c.acts.accounts|length}}) · آخر تحديث {{c.acts_text}}</span>{{ic('chev')}}</summary>
{% if c.acts.accounts %}<ul class="axl">
{% for a in c.acts.accounts %}<li><b><bdi>{{ ('@' ~ a.name) if a.name else 'حساب بلا اسم' }}</bdi></b><span><b>{{ '{:,}'.format(a.repost) }}</b> رتويت</span><span><b>{{ '{:,}'.format(a.like) }}</b> إعجاب</span><span><b>{{ '{:,}'.format(a.bookmark) }}</b> مرجعية</span></li>{% endfor %}
</ul>{% else %}<p class="mut axe">لا يوجد حساب X في تطبيقه الآن.</p>{% endif %}</details>
{% else %}<p class="axn">لم يرسل تطبيقه أرقام التنفيذ بعد.</p>{% endif %}
</article>
{% endfor %}
</div>
{% if not codes %}<div class="empty" style="margin-top:16px"><h3>لا يوجد مستخدمون بعد</h3><p>أضف مستخدمًا ليُنشأ له رمز دخول يفتح به التطبيق.</p><button class="btn" type="button" data-open="nu">{{ic('plus')}}إضافة مستخدم</button></div>{% endif %}
<div class="empty" id="nomatch" hidden><h3>لا نتائج</h3><p>جرّب اسمًا أو رمزًا آخر، أو غيّر التصفية.</p><button class="btn ghost" type="button" id="clr">عرض كل المستخدمين</button></div>
</section>

<section class="panel" id="p-keys">
<div class="card pad"><h2>الكاتب الحالي</h2><p class="mut">اختر المحرّك الذي يكتب التعليقات. يمكنك التبديل بينهما في أي لحظة.</p>
<form class="eng" method="post" action="/{{admin}}/engine" data-toast="تم تغيير الكاتب">
<label class="opt"><input type="radio" name="engine" value="gemini" {{ 'checked' if engine=='gemini' else '' }} onchange="this.form.requestSubmit()"><span class="pi" aria-hidden="true">G</span><span><b>Gemini</b><small>{{ 'المفتاح مضبوط' if gemini_set else 'لا يوجد مفتاح' }}</small></span><span class="ck">{{ic('check')}}</span></label>
<label class="opt"><input type="radio" name="engine" value="claude" {{ 'checked' if engine=='claude' else '' }} onchange="this.form.requestSubmit()"><span class="pi" aria-hidden="true">C</span><span><b>Claude</b><small>{{ 'المفتاح مضبوط' if claude_set else 'لا يوجد مفتاح' }}</small></span><span class="ck">{{ic('check')}}</span></label>
<noscript><button class="btn">تفعيل</button></noscript></form>
{% if nokey %}<div class="note" role="status">{{ic('alert')}}<p>الكاتب المختار بلا مفتاح، فلن تُكتب أي تعليقات. أضف مفتاحه في الأسفل أو اختر الكاتب الآخر.</p></div>{% endif %}
<p style="margin:14px 2px 6px;font-weight:700;font-size:14px">اتصال Gemini</p>
<form class="eng" method="post" action="/{{admin}}/gemini-provider" data-toast="تم تغيير اتصال Gemini">
<label class="opt"><input type="radio" name="provider" value="google" {{ 'checked' if gemini_provider=='google' else '' }} onchange="this.form.requestSubmit()"><span class="pi" aria-hidden="true">G</span><span><b>مباشر Google</b><small>{{ 'المفتاح مضبوط' if google_set else 'لا يوجد مفتاح' }}</small></span><span class="ck">{{ic('check')}}</span></label>
<label class="opt"><input type="radio" name="provider" value="openrouter" {{ 'checked' if gemini_provider=='openrouter' else '' }} onchange="this.form.requestSubmit()"><span class="pi" aria-hidden="true">R</span><span><b>عبر OpenRouter</b><small>{{ 'المفتاح مضبوط' if openrouter_set else 'لا يوجد مفتاح' }}</small></span><span class="ck">{{ic('check')}}</span></label>
<noscript><button class="btn">تطبيق</button></noscript></form>
{% if engine=='gemini' and gemini_provider=='openrouter' and not openrouter_set %}<div class="note" role="status">{{ic('alert')}}<p>اخترت «عبر OpenRouter» دون مفتاح OpenRouter. أضف المفتاح في الأسفل.</p></div>{% endif %}
</div>
<div class="g2">
{% for k in [('gemini','Gemini',google_set,gemini_model,gemini_default,'G','الصق مفتاح Gemini'),('claude','Claude',claude_set,claude_model,claude_default,'C','الصق مفتاح Claude (sk-ant-…)')] %}
<form class="card pad" method="post" action="/{{admin}}/key" data-toast="تم حفظ إعدادات {{k[1]}}"><input type="hidden" name="which" value="{{k[0]}}">
<div class="ph"><span class="pi" aria-hidden="true">{{k[5]}}</span><div><h3>{{k[1]}}</h3><span class="b {{ 'on' if k[2] else 'off' }}">{{ 'المفتاح مضبوط' if k[2] else 'لا يوجد مفتاح' }}</span></div>{% if engine==k[0] %}<span class="tag">الكاتب الحالي</span>{% endif %}</div>
<label class="l" for="k-{{k[0]}}">مفتاح API</label>
<div class="pw"><input class="kin" id="k-{{k[0]}}" type="password" name="api_key" dir="ltr" autocomplete="off" autocapitalize="off" autocorrect="off" spellcheck="false" placeholder="{{ 'الصق مفتاحًا جديدًا للتبديل' if k[2] else k[6] }}"><button type="button" class="eye" data-eye aria-label="إظهار المفتاح" aria-pressed="false">{{ic('eye')}}</button></div>
<label class="l" for="m-{{k[0]}}">النموذج</label><input id="m-{{k[0]}}" name="model" dir="ltr" value="{{k[3]}}" placeholder="{{k[4]}}" autocomplete="off" autocapitalize="off" autocorrect="off" spellcheck="false">
<p class="hint">{{ic('lock')}}<span>يُحفظ المفتاح مختومًا على الخادم ولا يُرسل إلى الأجهزة.</span></p>
<button class="btn wide">حفظ الإعدادات</button></form>
{% endfor %}
<form class="card pad" method="post" action="/{{admin}}/key" data-toast="تم حفظ إعدادات OpenRouter"><input type="hidden" name="which" value="openrouter">
<div class="ph"><span class="pi" aria-hidden="true">R</span><div><h3>OpenRouter</h3><span class="b {{ 'on' if openrouter_set else 'off' }}">{{ 'المفتاح مضبوط' if openrouter_set else 'لا يوجد مفتاح' }}</span></div>{% if engine=='gemini' and gemini_provider=='openrouter' %}<span class="tag">الكاتب الحالي</span>{% endif %}</div>
<label class="l" for="k-openrouter">مفتاح OpenRouter</label>
<div class="pw"><input class="kin" id="k-openrouter" type="password" name="api_key" dir="ltr" autocomplete="off" autocapitalize="off" autocorrect="off" spellcheck="false" placeholder="{{ 'الصق مفتاحًا جديدًا للتبديل' if openrouter_set else 'الصق مفتاح OpenRouter (sk-or-…)' }}"><button type="button" class="eye" data-eye aria-label="إظهار المفتاح" aria-pressed="false">{{ic('eye')}}</button></div>
<label class="l" for="m-openrouter">نموذج Gemini على OpenRouter</label><input id="m-openrouter" name="model" dir="ltr" value="{{openrouter_model}}" placeholder="{{openrouter_default}}" autocomplete="off" autocapitalize="off" autocorrect="off" spellcheck="false">
<p class="hint">{{ic('lock')}}<span>عند اختيار «عبر OpenRouter» تُكتب تعليقات Gemini بهذا المفتاح وهذا النموذج. يُحفظ مختومًا على الخادم ولا يُرسل إلى الأجهزة.</span></p>
<button class="btn wide">حفظ الإعدادات</button></form>
</div>
</section>

<section class="panel" id="p-notices">
<form class="card pad" method="post" action="/{{admin}}/notice/new" data-toast="تم إرسال التنبيه">
<h2>إرسال تنبيه أو تعليمات</h2><p class="mut">تصل الرسالة إلى التطبيق خلال دقيقة تقريبًا، فتفتح قائمة التنبيهات داخله وحدها، ويظهر إشعار على الجوال إن كان التطبيق في الخلفية.</p>
<label class="l" for="n-text">الرسالة</label>
<textarea id="n-text" class="ta" name="text" rows="4" maxlength="1000" required placeholder="اكتب التنبيه أو التعليمات…"></textarea>
<p class="l">النوع</p>
<div class="eng nk">{% for k, name in notice_kinds.items() %}<label class="opt"><input type="radio" name="kind" value="{{k}}" {{ 'checked' if k=='info' else '' }}><span class="pi k-{{k}}" aria-hidden="true">{{ {'info':'i','warn':'!','urgent':'!!'}[k] }}</span><span><b>{{name}}</b><small>{{ {'info':'رسالة عادية','warn':'شيء يجب الانتباه له','urgent':'مهم جدًا، يُعرض بالأحمر'}[k] }}</small></span><span class="ck">{{ic('check')}}</span></label>{% endfor %}</div>
<label class="l" for="n-to">إلى</label>
<select id="n-to" class="fs" name="target"><option value="all">كل المستخدمين</option>{% for c in codes %}<option value="{{c.id}}">{{ c.label or 'بدون اسم' }} — {{c.code}}</option>{% endfor %}</select>
<button class="btn wide" style="margin-top:18px">{{ic('bell')}}إرسال</button>
</form>
<div class="card pad"><h2>المرسَلة</h2>
{% if notices %}<ul class="nl">{% for n in notices %}<li>
<div class="nh"><span class="nb k-{{n.kind}}">{{n.kind_name}}</span><span class="mut">إلى {{n.to}} · {{n.ago}}</span>
<form method="post" action="/{{admin}}/notice/delete" data-title="حذف التنبيه؟" data-confirm="يُحذف من الخادم فلا يصل إلى من لم يستلمه بعد. ما وصل إلى الأجهزة يبقى في قوائمها." data-yes="حذف" data-kind="danger" data-toast="تم حذف التنبيه"><input type="hidden" name="id" value="{{n.id}}"><button class="ib" aria-label="حذف التنبيه">{{ic('trash')}}</button></form></div>
<p class="nx">{{n.text}}</p><p class="mut nr">{{n.reach}}</p></li>{% endfor %}</ul>
{% else %}<p class="mut" style="margin-top:8px">لم ترسل أي تنبيه بعد.</p>{% endif %}
</div>
</section>

<section class="panel" id="p-support">
<div class="card pad"><div class="sh"><h2>رسائل العملاء</h2>{% if unread %}<form method="post" action="/{{admin}}/support/read" data-toast="تم تعليم الكل كمقروء"><input type="hidden" name="id" value="0"><button class="btn ghost sm">تعليم الكل كمقروء</button></form>{% endif %}</div>
<p class="mut">تصل من زر «مساعدة» في تطبيق كل مستخدم: وصف المشكلة، والصور أو الفيديو، ومعلومات الجهاز وآخر سطور السجل. ردّك يصل إلى تطبيقه في قائمة التنبيهات.</p></div>
{% if messages %}<div class="ml">{% for m in messages %}{% set hue = ((m.code_id or '00')[:2]|int(0,16)) * 360 // 256 %}
<article class="msg{{ '' if m.read else ' new' }}" id="m{{m.id}}">
<div class="mh"><div class="av" style="--h:{{hue}}" aria-hidden="true">{{ (m.who or '؟')[:1] }}</div>
<div class="nm"><h3>{{m.who}}{% if m.kind == 'topup' %} <span class="nw tp">طلب شحن رصيد</span>{% endif %}{% if not m.read %} <span class="nw">جديدة</span>{% endif %}</h3><p>{% if m.code %}<bdi>{{m.code}}</bdi> · {% endif %}{{m.ago}} · <span dir="ltr">{{m.when}}</span></p></div></div>
{% if m.text %}<p class="mt">{{m.text}}</p>{% endif %}
{% if m.files %}<div class="mf">{% for f in m.files %}{% set url = '/' ~ admin ~ '/support/' ~ m.id ~ '/' ~ loop.index0 %}{% if (f.type or '').startswith('image/') %}<a class="mi" href="{{url}}" target="_blank" rel="noopener" aria-label="فتح الصورة {{loop.index}}"><img src="{{url}}" alt="صورة {{loop.index}} من المستخدم" loading="lazy"></a>{% else %}<video class="mv" src="{{url}}" controls preload="none" playsinline aria-label="فيديو {{loop.index}} من المستخدم"></video>{% endif %}{% endfor %}</div>{% endif %}
{% if m.meta and (m.meta.version or m.meta.device or m.meta.has_log or m.meta.log) %}<details class="acc mm{{ ' lazy' if m.meta.has_log else '' }}"{% if m.meta.has_log %} data-src="/{{admin}}/support/{{m.id}}/log"{% endif %}><summary class="axs"><span>معلومات الجهاز والسجل</span>{{ic('chev')}}</summary>
<dl class="md">{% if m.meta.version %}<div><dt>الإصدار</dt><dd dir="ltr">{{m.meta.version}}</dd></div>{% endif %}{% if m.meta.device %}<div><dt>الجهاز</dt><dd dir="ltr">{{m.meta.device}}</dd></div>{% endif %}{% if m.meta.accounts %}<div><dt>حسابات X</dt><dd dir="ltr">{{m.meta.accounts}}</dd></div>{% endif %}</dl>
{% if m.meta.has_log %}<div class="lz"></div>{% elif m.meta.log %}<pre class="lg">{{m.meta.log}}</pre>{% endif %}</details>{% endif %}
{% for r in m.replies %}<div class="mr"><b>ردّك</b> <span class="mut" dir="ltr">{{r.when}}</span><p>{{r.text}}</p></div>{% endfor %}
<div class="ma">
{% if m.exists %}<details class="rp"><summary class="btn sm">{{ic('edit')}}ردّ</summary><form method="post" action="/{{admin}}/support/reply" data-toast="تم إرسال الرد"><input type="hidden" name="id" value="{{m.id}}"><textarea class="ta" name="text" rows="3" maxlength="1000" required placeholder="اكتب ردّك… يصل إلى تطبيقه في قائمة التنبيهات"></textarea><button class="btn wide" style="margin-top:10px">إرسال الرد</button></form></details>{% endif %}
<form method="post" action="/{{admin}}/support/read"><input type="hidden" name="id" value="{{m.id}}"><button class="btn ghost sm">{{ 'تعليم كغير مقروءة' if m.read else 'تعليم كمقروءة' }}</button></form>
<form method="post" action="/{{admin}}/support/delete" data-title="حذف الرسالة؟" data-confirm="تُحذف الرسالة ومرفقاتها نهائيًا." data-yes="حذف" data-kind="danger" data-toast="تم حذف الرسالة"><input type="hidden" name="id" value="{{m.id}}"><button class="ib" aria-label="حذف الرسالة">{{ic('trash')}}</button></form>
</div></article>{% endfor %}</div>
{% if messages_total > messages|length %}<p class="mut shown">تُعرض أحدث {{messages|length}} من {{messages_total}}. احذف القديمة لتظهر.</p>{% endif %}
{% else %}<div class="empty" style="margin-top:16px"><h3>لا توجد رسائل بعد</h3><p>تظهر هنا رسائل المستخدمين من زر «مساعدة» في التطبيق.</p></div>{% endif %}
</section>

<section class="panel" id="p-failures">
<div class="card pad"><div class="sh"><h2>الأعطال</h2>{% if failures %}<div class="fa-all">{% if failures_new %}<form method="post" action="/{{admin}}/failures/read" data-toast="تم تعليم الكل كمقروء"><input type="hidden" name="id" value="0"><button class="btn ghost sm">تعليم الكل كمقروء</button></form>{% endif %}<form method="post" action="/{{admin}}/failures/delete" data-title="حذف كل الأعطال؟" data-confirm="تُحذف كل تقارير الأعطال نهائيًا." data-yes="حذف الكل" data-kind="danger" data-toast="حُذفت كل الأعطال"><input type="hidden" name="id" value="0"><button class="btn ghost sm">حذف الكل</button></form></div>{% endif %}</div>
<p class="mut">يصل هنا تلقائيًا كل فشل في تطبيق أي مستخدم: مهمة توقفت بخطأ، أو اكتملت وفيها إجراءات فاشلة، أو خطأ في السكربت؛ ومعه سجل ذلك الحساب. لا يرى المستخدم شيئًا من ذلك.</p></div>
{% if failures %}<div class="ml">{% for f in failures %}{% set hue = ((f.code_id or '00')[:2]|int(0,16)) * 360 // 256 %}
<article class="msg fa{{ '' if f.read else ' new' }}" id="f{{f.id}}">
<div class="mh"><div class="av" style="--h:{{hue}}" aria-hidden="true">{{ (f.who or '؟')[:1] }}</div>
<div class="nm"><h3>{{f.who}}{% if f.account %} · <bdi dir="ltr">@{{f.account}}</bdi>{% endif %}{% if not f.read %} <span class="nw">جديد</span>{% endif %}</h3><p>{{f.ago}} · <span dir="ltr">{{f.when}}</span>{% if f.version %} · الإصدار {{f.version}}{% endif %}</p></div></div>
<p class="ft"><span class="fk k-{{ 'urgent' if f.kind != 'actions' else 'warn' }}">{{ {'task': 'فشلت مهمة', 'actions': 'إجراءات فاشلة', 'error': 'خطأ في السكربت'}.get(f.kind, 'عطل') }}</span> {{f.title}}</p>
{% if f.task %}<p class="mut fs2">المهمة: {{f.task}}</p>{% endif %}
{% if f.message %}<p class="mt fm">{{f.message}}</p>{% endif %}
{% if f.summary %}<div class="fsum">{% if f.summary.requested is defined %}<span>المطلوب <b>{{f.summary.requested}}</b></span>{% endif %}{% if f.summary.done is defined %}<span>المنفَّذ <b>{{f.summary.done}}</b></span>{% endif %}{% if f.summary.failed is defined %}<span class="bad">الفاشل <b>{{f.summary.failed}}</b></span>{% endif %}</div>{% endif %}
{% if f.failed_head %}<ul class="fl">{% for line in f.failed_head %}<li dir="auto">{{line}}</li>{% endfor %}{% if f.failed_count > f.failed_head|length %}<li class="more">و{{ f.failed_count - f.failed_head|length }} أخرى في «التفاصيل والسجل»</li>{% endif %}</ul>{% endif %}
{% if f.has_details %}<details class="acc mm lazy" data-src="/{{admin}}/failures/{{f.id}}"><summary class="axs"><span>التفاصيل والسجل</span>{{ic('chev')}}</summary><div class="lz"></div></details>{% endif %}

{% if f.device %}<p class="mut fs2" dir="ltr">{{f.device}}</p>{% endif %}
<div class="ma"><button type="button" class="btn ghost sm" data-fcopy="/{{admin}}/failures/{{f.id}}">{{ic('copy')}}نسخ</button>
<form method="post" action="/{{admin}}/failures/read"><input type="hidden" name="id" value="{{f.id}}"><button class="btn ghost sm">{{ 'تعليم كغير مقروء' if f.read else 'تعليم كمقروء' }}</button></form>
<form method="post" action="/{{admin}}/failures/delete" data-toast="حُذف العطل"><input type="hidden" name="id" value="{{f.id}}"><button class="ib" aria-label="حذف العطل">{{ic('trash')}}</button></form></div>
</article>{% endfor %}</div>
{% if failures_total > failures|length %}<p class="mut shown">تُعرض أحدث {{failures|length}} من {{failures_total}}. احذف القديمة لتظهر.</p>{% endif %}
{% else %}<div class="empty" style="margin-top:16px"><h3>لا توجد أعطال</h3><p>يظهر هنا كل فشل في تطبيقات المستخدمين، تلقائيًا ومعه السجل.</p></div>{% endif %}
</section>

<section class="panel" id="p-script">
{% if flash %}<div class="note fl-{{flash.kind}}" role="status">{{ic('alert' if flash.kind != 'ok' else 'check')}}<p>{{flash.text}}</p></div>{% endif %}
<div class="card pad"><h2>سكربت التطبيق</h2>
<p class="mut">هذا هو برنامج التطبيق. حدّثه من هنا: ارفع الملف المعدّل ثم اضغط «نشر التحديث»، فيظهر للمستخدمين زر «تحديث» داخل التطبيق، أو يُثبَّت عندهم وحده إن اخترت «تثبيت تلقائي» — دون بناء تطبيق جديد. رقم الإصدار تحدده هنا، ولا حاجة لتعديله داخل الملف.</p>
<dl class="mvd">
<div><dt>للجميع</dt><dd>{% if script_live.version %}الإصدار <b>{{script_live.version}}</b> · نُشر {{script_live_when}}{% if script_live.has_content %} · مع content.py{% endif %}{% if script_live.auto %} · <span class="b on">تثبيت تلقائي</span>{% endif %}{% else %}<span class="mut">لا يوجد سكربت منشور بعد. التطبيقات تعمل بالسكربت المدمج فيها.</span>{% endif %}</dd></div>
{% if script_pilot.version %}<div><dt>تجريبي</dt><dd>الإصدار <b>{{script_pilot.version}}</b> · عند {{script_pilot_names|length}} مستخدم · نُشر {{script_pilot_when}}{% if script_pilot.auto %} · <span class="b on">تثبيت تلقائي</span>{% endif %}</dd></div>{% endif %}
{% if script_staged.version %}<div><dt>المرفوع</dt><dd>الإصدار <b>{{script_staged.version}}</b>{% if script_can_publish %} · <span class="b on">جاهز للنشر</span>{% else %} · <span class="mut">منشور</span>{% endif %}</dd></div>{% endif %}
</dl>
{% if script_live.version %}{% if script_live.auto %}<form method="post" action="/{{admin}}/script/auto" data-toast="أُوقف التثبيت التلقائي"><input type="hidden" name="which" value="live"><input type="hidden" name="auto" value="0"><button class="btn sm ghost sa">{{ic('reset')}}إيقاف التثبيت التلقائي للإصدار {{script_live.version}}</button></form>
{% else %}<form method="post" action="/{{admin}}/script/auto" data-title="تثبيت تلقائي للإصدار {{script_live.version}}؟" data-confirm="يُثبَّت الإصدار {{script_live.version}} وحده عند كل مستخدم نسخته أقدم، دون زر «تحديث»، فور ألا تكون عنده مهمة جارية." data-yes="تثبيت تلقائي" data-toast="صار التثبيت تلقائيًا"><input type="hidden" name="which" value="live"><input type="hidden" name="auto" value="1"><button class="btn sm ghost sa">{{ic('reset')}}تثبيت الإصدار {{script_live.version}} تلقائيًا عند الجميع</button></form>
{% endif %}{% endif %}<form method="post" action="/{{admin}}/script/upload" enctype="multipart/form-data" data-keep-busy>
<label class="l" for="sc-gg">ملف السكربت (script_original.py أو gg.py)</label>
<input id="sc-gg" class="fs" type="file" name="gg" accept=".py,text/x-python,text/plain" required>
<label class="l" for="sc-content">ملف content.py <small>(اختياري، إن تغيّر)</small></label>
<input id="sc-content" class="fs" type="file" name="content" accept=".py,text/x-python,text/plain">
<label class="l" for="sc-ver">رقم الإصدار <small>(مقترح تلقائيًا، يجب أن يكون أعلى من {{script_floor or "1.0"}})</small></label>
<input id="sc-ver" name="version" dir="ltr" value="{{script_next}}" inputmode="decimal" pattern="[0-9٠-٩]+([.٫][0-9٠-٩]+){0,3}" autocomplete="off" autocapitalize="off" spellcheck="false" required>
<button class="btn wide ghost" style="margin-top:12px">{{ic('code')}}رفع السكربت</button></form>
{% if script_can_publish %}<form class="pub" method="post" action="/{{admin}}/script/publish" data-v="{{script_staged.version}}" data-title="نشر التحديث؟" data-confirm="سيصل الإصدار {{script_staged.version}} إلى كل المستخدمين، فيظهر لهم زر «تحديث» في التطبيق. تأكد أنك جرّبت الملف." data-yes="نشر" data-toast="تم نشر التحديث">
<p class="l">لمن يصل الإصدار {{script_staged.version}}؟</p>
<div class="eng">
<label class="opt"><input type="radio" name="target" value="all" checked><span class="pi">{{ic('users')}}</span><span><b>كل المستخدمين</b><small>يصل إلى كل من نسخته أقدم</small></span><span class="ck">{{ic('check')}}</span></label>
<label class="opt"><input type="radio" name="target" value="some"><span class="pi">{{ic('edit')}}</span><span><b>مستخدمون أختارهم (تجريبي)</b><small>جرّبه عندهم أولًا؛ الباقون يبقون على الإصدار الحالي</small></span><span class="ck">{{ic('check')}}</span></label>
</div>
<div class="pk" role="group" aria-label="من يصله الإصدار التجريبي">{% for c in codes %}<label class="pkr{{ '' if c.active else ' off' }}"><input type="checkbox" name="codes" value="{{c.id}}"><span class="pkn">{{ c.label or 'بدون اسم' }}</span><span class="pkc">{{c.code}}</span></label>{% else %}<p class="pke">لا يوجد مستخدمون بعد.</p>{% endfor %}</div>
<label class="opt au"><input type="checkbox" name="auto" value="1"><span class="pi">{{ic('reset')}}</span><span><b>تثبيت تلقائي</b><small>يُثبَّت عندهم وحده دون زر «تحديث»، فور ألا تكون عندهم مهمة جارية</small></span><span class="ck">{{ic('check')}}</span></label>
<button class="btn wide" style="margin-top:12px">{{ic('check')}}نشر التحديث (الإصدار {{script_staged.version}})</button></form>
<script>(function(){var f=document.querySelector('form.pub');if(!f)return;var v=f.dataset.v;
function sync(){var some=f.querySelector('input[name=target][value=some]').checked,n=f.querySelectorAll('input[name=codes]:checked').length,au=f.querySelector('input[name=auto]').checked;
f.dataset.confirm=some?(n?'سيصل الإصدار '+v+' إلى '+n+' مستخدم فقط، '+(au?'ويُثبَّت عندهم تلقائيًا دون زر «تحديث» (بعد انتهاء مهامهم الجارية)':'ويظهر لهم زر «تحديث»')+'. الباقون يبقون على الإصدار الحالي.':'لم تختر أي مستخدم. اختر من القائمة من يصله الإصدار التجريبي.'):'سيصل الإصدار '+v+' إلى كل المستخدمين، '+(au?'ويُثبَّت عندهم تلقائيًا دون زر «تحديث» (بعد انتهاء مهامهم الجارية)':'فيظهر لهم زر «تحديث» في التطبيق')+'. تأكد أنك جرّبت الملف.';
f.dataset.yes=some?'نشر تجريبي':'نشر'}
f.addEventListener('change',sync);sync()})();</script>{% endif %}
{% if script_pilot.version %}<div class="pil">
<p class="pil-h">{{ic('edit')}}<span>الإصدار التجريبي <b>{{script_pilot.version}}</b> يصل الآن إلى: {{ script_pilot_names|join('، ') if script_pilot_names else 'لا أحد (حُذف من اخترتهم)' }}</span></p>
{% if not script_live.version %}<p class="pil-w">{{ic('alert')}}<span>لا يوجد إصدار منشور للجميع بعد، فالمستخدمون الجدد خارج التجربة لا يستطيعون تجهيز التطبيق. انشر للجميع حين تتأكد.</span></p>{% endif %}
<div class="pil-a">
<form method="post" action="/{{admin}}/script/pilot/promote" data-title="نشر للجميع؟" data-confirm="سيصل الإصدار {{script_pilot.version}} إلى كل المستخدمين، {{ 'ويُثبَّت عندهم تلقائيًا دون زر «تحديث».' if script_pilot.auto else 'فيظهر لهم زر «تحديث».' }}" data-yes="نشر للجميع" data-toast="تم النشر للجميع"><button class="btn">{{ic('check')}}نشر للجميع</button></form>
<form method="post" action="/{{admin}}/script/auto" data-toast="{{ 'أُوقف التثبيت التلقائي' if script_pilot.auto else 'صار التثبيت تلقائيًا' }}"><input type="hidden" name="which" value="pilot"><input type="hidden" name="auto" value="{{ '0' if script_pilot.auto else '1' }}"><button class="btn ghost">{{ic('reset')}}{{ 'إيقاف التلقائي' if script_pilot.auto else 'تثبيت تلقائي' }}</button></form>
<form method="post" action="/{{admin}}/script/pilot/cancel" data-title="إلغاء الإصدار التجريبي؟" data-confirm="لن يُعرض الإصدار {{script_pilot.version}} على أحد بعد الآن. من حدّث إليه يبقى على نسخته حتى يُنشر إصدار أعلى للجميع." data-yes="إلغاء التجريبي" data-kind="danger" data-toast="أُلغي الإصدار التجريبي"><button class="btn ghost">إلغاء التجريبي</button></form>
</div>
<details class="rs"><summary>تعديل من يصله</summary>
<form method="post" action="/{{admin}}/script/pilot/users" data-toast="تم حفظ المستخدمين">
<div class="pk on" role="group" aria-label="من يصله الإصدار التجريبي">{% for c in codes %}<label class="pkr{{ '' if c.active else ' off' }}"><input type="checkbox" name="codes" value="{{c.id}}"{% if c.id in script_pilot_ids %} checked{% endif %}><span class="pkn">{{ c.label or 'بدون اسم' }}</span><span class="pkc">{{c.code}}</span></label>{% endfor %}</div>
<button class="btn wide ghost" style="margin-top:10px">حفظ</button></form></details>
</div>{% endif %}
<ul class="notes"><li>{{ic('shield')}}<span>يُنزَّل السكربت عبر اتصال التطبيق المحمي بخادمك، ولا يصل إلا لجهاز يحمل رمزًا صالحًا.</span></li>
<li>{{ic('alert')}}<span>يُجرّب التطبيق تشغيل الإصدار الجديد قبل اعتماده؛ إن لم يعمل، يبقى على القديم ولا يتعطّل.</span></li>
<li>{{ic('edit')}}<span>«تجريبي»: انشر لمستخدمين تختارهم (أنت مثلًا) أولًا، ثم «نشر للجميع» حين تتأكد أنه سليم.</span></li>
<li>{{ic('reset')}}<span>«تثبيت تلقائي»: يسأل التطبيق عن التحديث كل 10 دقائق، ويثبّته وحده حين لا تكون عنده مهمة جارية أو نافذة تسجيل دخول، ثم يعيد تشغيل نفسه. يعمل عند من سكربته فيه هذه الميزة؛ من بقي على إصدار أقدم يظهر له زر «تحديث» هذه المرة فقط.</span></li></ul></div>

<div class="card pad" id="apk"><h2>ملف التطبيق (APK)</h2>
<p class="mut">ارفع آخر نسخة بنيتها من التطبيق، ثم انشرها للجميع أو لمستخدمين تختارهم (تجريبي): يظهر لمن نسخته أقدم زر «تنزيل التطبيق» أعلى صفحة السكربت. ورابط التنزيل الثابت يعطي دائمًا النسخة المنشورة للجميع.</p>
{% set al, ap, ast = app_slots.live, app_slots.pilot, app_slots.staged %}
<dl class="mvd">
<div><dt>للجميع</dt><dd>{% if al %}الإصدار <b>{{al.version}}</b> <span class="mut">(رقم {{al.code}})</span> · {{al.size_text}} · نُشر {{al.when}}{% else %}<span class="mut">لم تُنشر نسخة للجميع بعد.</span>{% endif %}</dd></div>
{% if ap %}<div><dt>تجريبي</dt><dd>الإصدار <b>{{ap.version}}</b> <span class="mut">(رقم {{ap.code}})</span> · عند {{ap.names|length}} مستخدم · نُشر {{ap.when}}</dd></div>{% endif %}
{% if ast %}<div><dt>المرفوع</dt><dd>الإصدار <b>{{ast.version}}</b> <span class="mut">(رقم {{ast.code}})</span> · {{ast.size_text}} · <span class="b on">جاهز للنشر</span>{% if ast.package != app_package %} · <span class="b">حزمة أخرى: <bdi dir="ltr">{{ast.package}}</bdi></span>{% endif %}</dd></div>{% endif %}
</dl>
<form method="post" action="/{{admin}}/app/upload" enctype="multipart/form-data" data-keep-busy>
<label class="l" for="ap-file">ملف التطبيق <small>(‎.apk)</small></label>
<input id="ap-file" class="fs" type="file" name="apk" accept=".apk,application/vnd.android.package-archive" required>
<button class="btn wide ghost" style="margin-top:12px">{{ic('phone')}}رفع التطبيق</button></form>
{% if ast %}<form class="apub" method="post" action="/{{admin}}/app/publish" data-v="{{ast.version}}" data-title="نشر التطبيق؟" data-confirm="يصل الإصدار {{ast.version}} من التطبيق إلى كل المستخدمين، فيظهر زر «تنزيل التطبيق» لكل من نسخته أقدم." data-yes="نشر" data-toast="تم نشر التطبيق">
<p class="l">لمن يصل الإصدار {{ast.version}}؟</p>
<div class="eng">
<label class="opt"><input type="radio" name="target" value="all" checked><span class="pi">{{ic('users')}}</span><span><b>كل المستخدمين</b><small>يظهر زر «تنزيل التطبيق» لكل من نسخته أقدم</small></span><span class="ck">{{ic('check')}}</span></label>
<label class="opt"><input type="radio" name="target" value="some"><span class="pi">{{ic('edit')}}</span><span><b>مستخدمون أختارهم (تجريبي)</b><small>جرّبه عندهم أولًا؛ الباقون يبقون على نسختهم</small></span><span class="ck">{{ic('check')}}</span></label>
</div>
<div class="pk" role="group" aria-label="من تصله النسخة التجريبية">{% for c in codes %}<label class="pkr{{ '' if c.active else ' off' }}"><input type="checkbox" name="codes" value="{{c.id}}"><span class="pkn">{{ c.label or 'بدون اسم' }}</span><span class="pkc">{{c.code}}</span></label>{% else %}<p class="pke">لا يوجد مستخدمون بعد.</p>{% endfor %}</div>
<label class="ckl" style="margin-top:12px"><input type="checkbox" name="notify" value="1" checked> أرسل لهم تنبيهًا بالنسخة</label>
<button class="btn wide" style="margin-top:12px">{{ic('check')}}نشر التطبيق (الإصدار {{ast.version}})</button></form>
<script>(function(){var f=document.querySelector('form.apub');if(!f)return;var v=f.dataset.v;
function sync(){var some=f.querySelector('input[name=target][value=some]').checked,n=f.querySelectorAll('input[name=codes]:checked').length;
f.dataset.confirm=some?(n?'يصل الإصدار '+v+' من التطبيق إلى '+n+' مستخدم فقط، ويظهر لهم زر «تنزيل التطبيق». الباقون يبقون على نسختهم.':'لم تختر أي مستخدم. اختر من القائمة من تصله النسخة التجريبية.'):'يصل الإصدار '+v+' من التطبيق إلى كل المستخدمين، فيظهر زر «تنزيل التطبيق» لكل من نسخته أقدم.';
f.dataset.yes=some?'نشر تجريبي':'نشر'}
f.addEventListener('change',sync);sync()})();</script>{% endif %}
{% if ap %}<div class="pil">
<p class="pil-h">{{ic('edit')}}<span>النسخة التجريبية <b>{{ap.version}}</b> من التطبيق تصل الآن إلى: {{ ap.names|join('، ') if ap.names else 'لا أحد (حُذف من اخترتهم)' }}</span></p>
<div class="pil-a">
<form method="post" action="/{{admin}}/app/pilot/promote" data-title="نشر للجميع؟" data-confirm="يصل الإصدار {{ap.version}} من التطبيق إلى كل المستخدمين، فيظهر زر «تنزيل التطبيق» لكل من نسخته أقدم." data-yes="نشر للجميع" data-toast="تم النشر للجميع"><button class="btn">{{ic('check')}}نشر للجميع</button></form>
<form method="post" action="/{{admin}}/app/pilot/cancel" data-title="إلغاء النسخة التجريبية؟" data-confirm="لن يُعرض الإصدار {{ap.version}} من التطبيق على أحد بعد الآن. من نزّله يبقى عليه." data-yes="إلغاء التجريبي" data-kind="danger" data-toast="أُلغيت النسخة التجريبية"><button class="btn ghost">إلغاء التجريبي</button></form>
</div>
<details class="rs"><summary>تعديل من تصله</summary>
<form method="post" action="/{{admin}}/app/pilot/users" data-toast="تم حفظ المستخدمين">
<div class="pk on" role="group" aria-label="من تصله النسخة التجريبية">{% for c in codes %}<label class="pkr{{ '' if c.active else ' off' }}"><input type="checkbox" name="codes" value="{{c.id}}"{% if c.id in ap.codes %} checked{% endif %}><span class="pkn">{{ c.label or 'بدون اسم' }}</span><span class="pkc">{{c.code}}</span></label>{% endfor %}</div>
<button class="btn wide ghost" style="margin-top:10px">حفظ</button></form></details>
</div>{% endif %}
{% if al %}<p class="l">رابط التنزيل <small>(النسخة المنشورة للجميع)</small></p>
<code class="lk">{{app_dl_link}}</code>
<div class="da"><button type="button" class="btn" data-copy="{{app_dl_link}}">{{ic('copy')}}نسخ الرابط</button><button type="button" class="btn ghost" data-share="{{app_dl_link}}">{{ic('share')}}مشاركة</button></div>
<form method="post" action="/{{admin}}/app/notify" data-title="إرسال تنبيه؟" data-confirm="يصل لكل المستخدمين تنبيه بأن الإصدار {{al.version}} من التطبيق جاهز، مع رابط التنزيل." data-yes="إرسال" data-toast="تم إرسال التنبيه"><button class="btn wide" style="margin-top:12px">{{ic('bell')}}إرسال تنبيه للمستخدمين</button></form>{% endif %}
<ul class="notes"><li>{{ic('shield')}}<span>زر «تنزيل التطبيق» داخل التطبيق يُنزّله عبر اتصاله المحمي بخادمك ويحفظه في «التنزيلات» بلا أي تحذير. أما الرابط فيُفتح في المتصفح، وقد يعرض «الاتصال غير خاص» لأن شهادة خادمك ذاتية: اضغط «متقدم» ثم «متابعة».</span></li>
<li>{{ic('edit')}}<span>«تجريبي»: انشره لمستخدمين تختارهم (أنت مثلًا) أولًا، ثم «نشر للجميع» حين تتأكد أنه يعمل.</span></li>
<li>{{ic('alert')}}<span>ليُثبَّت فوق النسخة الموجودة دون حذفها: نفس مفتاح التوقيع (keystore) الذي بنيت به النسخة السابقة، ورقم إصدار (versionCode) أعلى منها.</span></li></ul></div>
</section>

<section class="panel" id="p-link">
{% if flash %}<div class="note fl-{{flash.kind}}" role="status">{{ic('alert' if flash.kind != 'ok' else 'check')}}<p>{{flash.text}}</p></div>{% endif %}
<div class="card pad"><h2>رابط التطبيق</h2><p class="mut">انسخه كاملًا وضعه في التطبيق عند إعداد الخادم.</p>
<code class="lk">{{app_link}}</code>
<div class="da"><button type="button" class="btn" data-copy="{{app_link}}">{{ic('copy')}}نسخ الرابط</button><button type="button" class="btn ghost" data-share="{{app_link}}">{{ic('share')}}مشاركة</button></div>
<ul class="notes"><li>{{ic('shield')}}<span>يحمل الرابط بصمة شهادة الخادم، فلا يقبل التطبيق أي خادم آخر.</span></li><li>{{ic('lock')}}<span>الرابط سرّي: شاركه فقط مع من تعطيه رمز دخول.</span></li></ul></div>

{% if not in_owner_app %}<div class="card pad"><h2>تطبيق المالك</h2><p class="mut">افتح لوحة التحكّم من تطبيق أندرويد خاص بك، ويصلك إشعار عند كل عطل أو رسالة جديدة من المستخدمين. الصق هذا الرابط فيه أول مرة.</p>
<code class="lk">{{owner_link}}</code>
<div class="da"><button type="button" class="btn" data-copy="{{owner_link}}">{{ic('copy')}}نسخ رابط تطبيق المالك</button></div>
<ul class="notes"><li>{{ic('lock')}}<span>هذا الرابط يفتح لوحتك (مع كلمة المرور): لا تعطه أحدًا. يحمل بصمة شهادة الخادم، فلا يقبل التطبيق خادمًا غيره.</span></li></ul></div>{% endif %}

<div class="card pad"><h2>نقل التطبيقات إلى هذا الخادم</h2>
<p class="mut">إذا تعطّل خادمك القديم وشغّلت لوحة التحكّم هنا: اضغط «ربط» وأدخل <b>كلمة مرور لوحة التحكّم نفسها التي كانت على الخادم القديم</b>. يصل للتطبيقات أمر موقَّع بها بأن الخادم انتقل إلى هنا، فتتصل بهذا الخادم خلال دقائق.</p>
<dl class="mvd">
<div><dt>رمز الربط</dt><dd>{% if move_code %}<bdi class="mc">{{move_code}}</bdi> <span class="mut">يجب أن يكون نفسه على الخادم القديم والجديد (يأتي من كلمة المرور).</span>{% else %}<span class="mut">يظهر بعد تسجيل الدخول مرة.</span>{% endif %}</dd></div>
<div><dt>آخر ربط</dt><dd>{% if move_when %}{{move_when}}{% if move_active %} · <span class="b on">يُعاد إرساله تلقائيًا</span>{% endif %}{% if not move_moved_here %} <span class="mut">(لخادم آخر)</span>{% endif %}{% else %}<span class="mut">لم يُضغط «ربط» على هذا الخادم.</span>{% endif %}</dd></div>
</dl>
<button class="btn wide" type="button" data-open="mv">{{ic('link')}}ربط التطبيقات بهذا الخادم</button>
<ul class="notes"><li>{{ic('shield')}}<span>لا تتبع التطبيقات إلا أمرًا موقَّعًا بمفتاح من كلمة مرورك، فلا يستطيع أحد غيرك نقلها. ويمرّ الأمر مشفّرًا عبر {{relay}}.</span></li>
<li>{{ic('alert')}}<span>من غير نسخة احتياطية: تنتقل التطبيقات، لكن رموز المستخدمين القديمة لا تعمل هنا، فيطلب التطبيق رمزًا جديدًا تنشئه لهم من «المستخدمون».</span></li></ul></div>

<div class="card pad"><h2>النسخة الاحتياطية</h2>
<p class="mut">ملف واحد فيه كل بيانات الخادم: المستخدمون ورموزهم، والمفاتيح، والإحصاءات، والتنبيهات، وأسرار الخادم وشهادته. مشفّر بكلمة مرور لوحة التحكّم. احفظه خارج هذا الخادم (جوالك أو بريدك)، ونزّل نسخة جديدة كلما أضفت مستخدمين.</p>
<p class="bk{{ '' if backup_when else ' none' }}">{{ic('shield' if backup_when else 'alert')}}<span>{% if backup_when %}آخر نسخة نُزّلت {{backup_when}}.{% else %}لم تُنزَّل أي نسخة احتياطية بعد.{% endif %}</span></p>
<form method="post" action="/{{admin}}/backup"><label class="l" for="bk-pw">كلمة مرور لوحة التحكّم</label>
<div class="pw"><input id="bk-pw" type="password" name="password" required autocomplete="current-password"><button type="button" class="eye" data-eye aria-label="إظهار كلمة المرور" aria-pressed="false">{{ic('eye')}}</button></div>
<button class="btn wide">{{ic('shield')}}تنزيل نسخة احتياطية</button></form>
<details class="acc rs"><summary class="axs"><span>استعادة نسخة احتياطية على هذا الخادم</span>{{ic('chev')}}</summary>
<form method="post" action="/{{admin}}/restore" enctype="multipart/form-data" data-title="استعادة النسخة؟" data-confirm="تُستبدل كل بيانات هذا الخادم ببيانات النسخة (يُحفظ ما قبلها في مجلد before-restore)، ثم يُعاد تشغيله. يصير رابط لوحة المالك وكلمة مرورها كما في الخادم القديم." data-yes="استعادة" data-kind="danger">
<label class="l" for="rs-file">ملف النسخة (.ggbak)</label><input id="rs-file" class="fs" type="file" name="file" accept=".ggbak,application/octet-stream" required>
<label class="l" for="rs-pw">كلمة مرور النسخة (كلمة مرور الخادم القديم)</label>
<div class="pw"><input id="rs-pw" type="password" name="password" required autocomplete="off"><button type="button" class="eye" data-eye aria-label="إظهار كلمة المرور" aria-pressed="false">{{ic('eye')}}</button></div>
<label class="ckl"><input type="checkbox" name="confirm" value="1" required> أفهم أن بيانات هذا الخادم تُستبدل</label>
<button class="btn wide danger">استعادة وإعادة التشغيل</button></form></details></div>
</section>
</main>

<dialog id="sheet" class="sheet" aria-labelledby="sh-name"><div class="grab"></div>
<div class="shh"><div class="av" id="sh-av" aria-hidden="true"></div><div><h3 id="sh-name"></h3><bdi id="sh-code"></bdi></div><button type="button" class="ib" data-close aria-label="إغلاق">{{ic('x')}}</button></div>
<div class="shl">
<button type="button" id="sh-copy" data-copy="" data-close>{{ic('copy')}}نسخ الرمز</button>
<button type="button" id="sh-share" data-share="" data-close>{{ic('share')}}مشاركة الرمز</button>
<button type="button" id="sh-rename">{{ic('edit')}}تعديل الاسم</button>
<form id="sh-release" method="post" action="/{{admin}}/code/release" data-title="تحرير الأجهزة؟" data-confirm="يخرج الرمز من كل جوال دخل به، ويدخل صاحبه من جديد على الجوال الذي يريده." data-yes="تحرير الأجهزة" data-toast="تم تحرير الأجهزة"><input type="hidden" name="id"><button>{{ic('phone')}}<span>تحرير الأجهزة<small>يخرج من كل جوالاته، ليدخل من جديد على ما يريد</small></span></button></form>
<form id="sh-pay" method="post" action="/{{admin}}/code/pay" data-toast="تم تغيير نوع الدفع"><input type="hidden" name="id"><input type="hidden" name="pay" value="prepaid"><button>{{ic('key')}}<span id="sh-pay-t">تحويل إلى دفع مسبق</span></button></form>
<button type="button" id="sh-bal">{{ic('plus')}}<span>إضافة رصيد<small>تجريبي أو شحن، ويُخصم حسب أسعار الخدمات</small></span></button>
<button type="button" id="sh-pw">{{ic('lock')}}<span>تعيين كلمة سر جديدة<small>لصاحب حساب نسي كلمة سره</small></span></button>
<form id="sh-reset" method="post" action="/{{admin}}/code/reset-cost" data-title="تصفير التكلفة؟" data-confirm="سيُصفَّر عدّاد التعليقات والتكلفة لهذا المستخدم فقط، ويبقى محسوبًا في «منذ البداية» أعلى الصفحة." data-yes="تصفير التكلفة" data-kind="danger" data-toast="تم تصفير التكلفة"><input type="hidden" name="id"><button>{{ic('reset')}}تصفير التكلفة</button></form>
<hr>
<form class="del" method="post" action="/{{admin}}/code/delete" data-title="حذف المستخدم؟" data-confirm="يُحذف رمزه نهائيًا وتُفقد إحصائياته، ولا يمكن التراجع." data-yes="حذف المستخدم" data-kind="danger" data-toast="تم حذف المستخدم"><input type="hidden" name="id"><button>{{ic('trash')}}حذف المستخدم</button></form>
</div></dialog>

<dialog id="nu" class="ask" aria-labelledby="nu-t"><form class="dg" method="post" action="/{{admin}}/code/new" data-fresh><h3 id="nu-t">إضافة مستخدم</h3><p class="mut">يُنشأ له رمز دخول فريد تعطيه إيّاه.</p>
<label class="l" for="nu-l">اسم المستخدم <small>(اختياري)</small></label><input id="nu-l" name="label" maxlength="40" placeholder="مثال: أحمد" autocomplete="off" enterkeyhint="done">
<div class="da"><button type="button" class="btn ghost" data-close>إلغاء</button><button class="btn">إضافة المستخدم</button></div></form></dialog>

<dialog id="mv" class="ask" aria-labelledby="mv-t"><form class="dg" method="post" action="/{{admin}}/move">
<h3 id="mv-t">ربط التطبيقات بهذا الخادم</h3>
<p class="mut">تنتقل كل التطبيقات إلى هذا الخادم. تأكّد من عنوانه: هو ما تكتبه في المتصفح لتفتح هذه اللوحة.</p>
<label class="l" for="mv-host">عنوان هذا الخادم</label><input id="mv-host" name="host" dir="ltr" value="{{this_host}}" data-keep required autocomplete="off" autocapitalize="off" spellcheck="false">
<label class="l" for="mv-pw">كلمة مرور لوحة التحكّم <small>(نفس كلمة مرور الخادم القديم)</small></label>
<div class="pw"><input id="mv-pw" type="password" name="password" required autocomplete="current-password"><button type="button" class="eye" data-eye aria-label="إظهار كلمة المرور" aria-pressed="false">{{ic('eye')}}</button></div>
<label class="ckl"><input type="checkbox" name="confirm" value="1" required> أؤكد نقل كل التطبيقات إلى هذا الخادم</label>
<div class="da"><button class="btn" type="submit">{{ic('link')}}ربط</button><button class="btn ghost" type="button" data-close>إلغاء</button></div>
</form></dialog>
<dialog id="bal" class="ask" aria-labelledby="bal-t"><form class="dg" method="post" action="/{{admin}}/code/balance" data-toast="تم تحديث الرصيد"><input type="hidden" name="id"><h3 id="bal-t">إضافة رصيد</h3><p class="mut" id="bal-now"></p>
<label class="l" for="bal-a">المبلغ بالدولار <small>(بإشارة سالب للخصم)</small></label><input id="bal-a" class="fs" name="amount" dir="ltr" inputmode="decimal" autocomplete="off" placeholder="2.00" required>
<label class="l" for="bal-n">الوصف <small>(اختياري)</small></label><input id="bal-n" class="fs" name="note" maxlength="60" autocomplete="off" placeholder="رصيد تجريبي">
<div class="da"><button type="button" class="btn ghost" data-close>إلغاء</button><button class="btn">إضافة</button></div></form></dialog>
<dialog id="pwd" class="ask" aria-labelledby="pwd-t"><form class="dg" method="post" action="/{{admin}}/code/password" data-toast="تم تعيين كلمة السر"><input type="hidden" name="id"><h3 id="pwd-t">كلمة سر جديدة</h3><p class="mut" id="pwd-for"></p>
<label class="l" for="pwd-p">كلمة السر الجديدة <small>(6 أحرف على الأقل)</small></label><input id="pwd-p" class="fs" name="password" dir="ltr" minlength="6" maxlength="128" autocomplete="new-password" required>
<div class="da"><button type="button" class="btn ghost" data-close>إلغاء</button><button class="btn">حفظ</button></div></form></dialog>
<dialog id="rn" class="ask" aria-labelledby="rn-t"><form class="dg" method="post" action="/{{admin}}/code/rename" data-toast="تم حفظ الاسم"><input type="hidden" name="id"><h3 id="rn-t">تعديل الاسم</h3><p class="mut">الاسم يظهر لك وحدك في هذه اللوحة، والرمز لا يتغيّر.</p>
<label class="l" for="rn-l">اسم المستخدم</label><input id="rn-l" name="label" maxlength="40" autocomplete="off" enterkeyhint="done">
<div class="da"><button type="button" class="btn ghost" data-close>إلغاء</button><button class="btn">حفظ الاسم</button></div></form></dialog>

<dialog id="rd" class="sheet" aria-labelledby="rd-h"><div class="grab"></div><div class="dg"><h3 id="rd-h">الرمز جاهز</h3><p class="mut" id="rd-t">أعطِ هذا الرمز للمستخدم ليفتح به التطبيق. يرتبط الرمز بأول جوال يُدخَل فيه.</p>
<bdi class="big" id="rd-code"></bdi>
<div class="da"><button type="button" class="btn ghost" id="rd-share" data-share="" data-close>{{ic('share')}}مشاركة</button><button type="button" class="btn" id="rd-copy" data-copy="" data-close>{{ic('copy')}}نسخ الرمز</button></div></div></dialog>

<dialog id="chart" class="ask ch" aria-labelledby="ch-t" data-url="/{{admin}}/chart"><div class="dg">
<div class="ch-h"><h3 id="ch-t">نشاط المستخدمين</h3><button type="button" class="ib" data-close aria-label="إغلاق">{{ic('x')}}</button></div>
<div class="ch-seg" role="tablist" aria-label="المدة"><button type="button" role="tab" data-r="7" aria-selected="true">7 أيام</button><button type="button" role="tab" data-r="30" aria-selected="false">30 يومًا</button><button type="button" role="tab" data-r="u" aria-selected="false">المستخدمون</button></div>
<div class="ch-lg" id="ch-lg" aria-label="السلاسل (اضغط لإخفاء أو إظهار)"></div>
<div class="ch-box" id="ch-box"><svg id="ch-svg" role="img" aria-labelledby="ch-t"></svg><div class="ch-users" id="ch-users" hidden></div><p class="ch-empty" id="ch-empty">جارٍ التحميل…</p><div class="ch-tip" id="ch-tip" hidden></div></div>
<p class="mut ch-note" id="ch-note"></p>
<details class="ch-tb"><summary>عرض كجدول</summary><div class="ch-tw"><table id="ch-table"></table></div></details>
</div></dialog>
<script>(function(){
var D=document,dlg=D.getElementById('chart');if(!dlg)return;
var NS='http://www.w3.org/2000/svg';
var S=[{k:'like',n:'الإعجاب',c:'var(--s1)'},{k:'bookmark',n:'المرجعية',c:'var(--s2)'},{k:'comment',n:'التعليقات',c:'var(--s3)'}];
var WD=['الأحد','الإثنين','الثلاثاء','الأربعاء','الخميس','الجمعة','السبت'];
var data=null,range='7',off={};
var svg=D.getElementById('ch-svg'),tip=D.getElementById('ch-tip'),lg=D.getElementById('ch-lg'),us=D.getElementById('ch-users'),
empty=D.getElementById('ch-empty'),note=D.getElementById('ch-note'),tb=D.getElementById('ch-table'),box=D.getElementById('ch-box');
function fmt(v){return Number(v||0).toLocaleString('en-US')}
function mk(n,a){var e=D.createElementNS(NS,n);for(var k in a)e.setAttribute(k,a[k]);return e}
function h(t,c,x){var e=D.createElement(t);if(c)e.className=c;if(x!=null)e.textContent=x;return e}
function shown(){return S.filter(function(s){return !off[s.k]})}
function dkey(d){return d.getFullYear()+'-'+d.getMonth()+'-'+d.getDate()}
function dl(d){return d.getDate()+'/'+(d.getMonth()+1)}
function days(n){var out=[],t=new Date(),base=new Date(t.getFullYear(),t.getMonth(),t.getDate()),at={};
for(var i=n-1;i>=0;i--){var d=new Date(base);d.setDate(base.getDate()-i);var r={d:d,v:{like:0,bookmark:0,comment:0}};at[dkey(d)]=r;out.push(r)}
var hrs=data.hours||{};for(var k in hrs){var r2=at[dkey(new Date(Number(k)*3600000))];if(r2){var row=hrs[k];r2.v.like+=row[1]||0;r2.v.bookmark+=row[2]||0;r2.v.comment+=row[3]||0}}
if(!data.since)return out;var s=new Date(data.since*1000),s0=new Date(s.getFullYear(),s.getMonth(),s.getDate());
return out.filter(function(r){return r.d>=s0})}
function nice(max){var raw=max/4,p=Math.pow(10,Math.floor(Math.log10(raw))),m=raw/p;return Math.max(1,(m<=1?1:m<=2?2:m<=5?5:10)*p)}
function legend(tot,bars){lg.replaceChildren();S.forEach(function(s){var b=h('button');b.type='button';b.setAttribute('aria-pressed',String(!off[s.k]));
var key=h('i',bars?'sq':null);key.style.setProperty('--c',s.c);b.append(key,h('span',null,s.n),h('b',null,fmt(tot[s.k])));
b.onclick=function(){if(!off[s.k]&&shown().length===1)return;off[s.k]=!off[s.k];draw()};lg.append(b)})}
function table(head,body){tb.replaceChildren();var tr=h('tr');head.forEach(function(x){tr.append(h('th',null,x))});var th=h('thead');th.append(tr);
var bd=h('tbody');body.forEach(function(r){var row=h('tr');r.forEach(function(c,i){row.append(h('td',i?'n':null,i?fmt(c):c))});bd.append(row)});tb.append(th,bd)}
function say(text){svg.style.display='none';us.hidden=true;empty.hidden=false;empty.textContent=text}
function place(px,py){var bw=box.clientWidth,tw=tip.offsetWidth;tip.style.left=Math.max(0,Math.min(bw-tw,px-tw/2))+'px';tip.style.top=Math.max(0,py)+'px'}
function tipFill(title,vals){tip.replaceChildren(h('div','d',title));shown().forEach(function(s){var r=h('div','r'),k=h('i');k.style.setProperty('--c',s.c);r.append(k,h('b',null,fmt(vals[s.k])),h('span',null,s.n));tip.append(r)});tip.hidden=false}
function lines(){var rows=days(Number(range)),tot={like:0,bookmark:0,comment:0};
rows.forEach(function(r){S.forEach(function(s){tot[s.k]+=r.v[s.k]})});legend(tot,false);
table(['اليوم'].concat(S.map(function(s){return s.n})),rows.slice().reverse().map(function(r){return [WD[r.d.getDay()]+' '+dl(r.d)].concat(S.map(function(s){return r.v[s.k]}))}));
note.textContent=data.since?'يُسجَّل النشاط من '+dl(new Date(data.since*1000))+' (بتوقيت جهازك)، فالأيام قبله لا تظهر.':'يبدأ تسجيل النشاط من الآن.';
if(!rows.some(function(r){return S.some(function(s){return r.v[s.k]})}))return say('لا يوجد نشاط مسجّل في هذه المدة بعد. يُسجَّل من الآن، فارجع بعد قليل.');
empty.hidden=true;us.hidden=true;svg.style.display='';svg.replaceChildren();
var W=Math.max(280,box.clientWidth),H=220,L=42,R=14,T=12,B=26,sh=shown(),n=rows.length,max=1;svg.setAttribute('viewBox','0 0 '+W+' '+H);
rows.forEach(function(r){sh.forEach(function(s){max=Math.max(max,r.v[s.k])})});
var st=nice(max),top=Math.ceil(max/st)*st,X=function(i){return n===1?(L+W-R)/2:L+i*(W-L-R)/(n-1)},Y=function(v){return T+(H-T-B)*(1-v/top)};
for(var g=0;g<=top+1e-9;g+=st){svg.append(mk('line',{x1:L,x2:W-R,y1:Y(g),y2:Y(g),stroke:'var(--line)','stroke-width':1}));
var tx=mk('text',{x:L-8,y:Y(g)+4,'text-anchor':'end','font-size':11,fill:'var(--mut)'});tx.textContent=g>=10000?fmt(g/1000)+'K':fmt(g);svg.append(tx)}
var every=n<=8?1:Math.ceil(n/6);rows.forEach(function(r,i){if(i!==n-1&&(i%every||n-1-i<every*0.7))return;var tx2=mk('text',{x:X(i),y:H-7,'text-anchor':'middle','font-size':11,fill:'var(--mut)'});tx2.textContent=dl(r.d);svg.append(tx2)});
sh.forEach(function(s){var d='';rows.forEach(function(r,i){d+=(i?'L':'M')+X(i).toFixed(1)+' '+Y(r.v[s.k]).toFixed(1)});
svg.append(mk('path',{d:d,fill:'none',stroke:s.c,'stroke-width':2,'stroke-linejoin':'round','stroke-linecap':'round'}))});
sh.forEach(function(s){rows.forEach(function(r,i){if(n<=8||i===n-1)svg.append(mk('circle',{cx:X(i),cy:Y(r.v[s.k]),r:4,fill:s.c,stroke:'var(--card)','stroke-width':2}))})});
var cross=mk('line',{y1:T,y2:H-B,stroke:'var(--mut)','stroke-width':1,visibility:'hidden'}),hit=mk('rect',{x:0,y:0,width:W,height:H,fill:'transparent'});svg.append(cross,hit);
function at(ev){var b=svg.getBoundingClientRect(),x=(ev.clientX-b.left)*W/b.width;return n===1?0:Math.max(0,Math.min(n-1,Math.round((x-L)*(n-1)/(W-L-R))))}
function show(i){var r=rows[i];cross.setAttribute('x1',X(i));cross.setAttribute('x2',X(i));cross.setAttribute('visibility','visible');
tipFill(WD[r.d.getDay()]+' '+dl(r.d),r.v);place(X(i)*svg.getBoundingClientRect().width/W,0)}
hit.addEventListener('pointermove',function(ev){show(at(ev))});hit.addEventListener('pointerdown',function(ev){show(at(ev))});
hit.addEventListener('pointerleave',function(){cross.setAttribute('visibility','hidden');tip.hidden=true})}
function users(){var list=data.users||[],sh=shown(),tot={like:0,bookmark:0,comment:0};list.forEach(function(u){S.forEach(function(s){tot[s.k]+=u[s.k]})});legend(tot,true);
table(['المستخدم'].concat(S.map(function(s){return s.n})),list.map(function(u){return [u.name].concat(S.map(function(s){return u[s.k]}))}));
note.textContent='كل ما فعله كل مستخدم حتى الآن (الإعجاب والمرجعية كما في تطبيقه، والتعليقات المكتوبة)، الأكثر نشاطًا أولًا'+(data.more?'، ويُخفى '+data.more+' أقل نشاطًا':'')+'.';
if(!list.length)return say('لا يوجد نشاط للمستخدمين بعد.');
svg.style.display='none';empty.hidden=true;us.hidden=false;us.replaceChildren();
var sum=function(u){return sh.reduce(function(a,s){return a+u[s.k]},0)},max=Math.max.apply(null,list.map(sum).concat([1]));
list.forEach(function(u){var row=h('div','ch-u'),nm=h('div','nm'),bar=h('div','bar');nm.append(h('span',null,u.name),h('b',null,fmt(sum(u))));
bar.style.width=Math.max(2,sum(u)*100/max)+'%';sh.forEach(function(s){if(!u[s.k])return;var seg=h('span');seg.style.setProperty('--c',s.c);seg.style.flex=u[s.k]+' 0 0';bar.append(seg)});
row.append(nm,bar);row.tabIndex=0;var open=function(){tipFill(u.name,u);place(box.clientWidth/2,row.offsetTop+row.offsetHeight+4)};
row.addEventListener('pointerenter',open);row.addEventListener('focus',open);row.addEventListener('pointerleave',function(){tip.hidden=true});row.addEventListener('blur',function(){tip.hidden=true});us.append(row)})}
function draw(){tip.hidden=true;if(data)(range==='u'?users:lines)()}
dlg.querySelectorAll('.ch-seg button').forEach(function(b){b.addEventListener('click',function(){range=b.dataset.r;
dlg.querySelectorAll('.ch-seg button').forEach(function(x){x.setAttribute('aria-selected',String(x===b))});draw()})});
D.getElementById('ch-open').addEventListener('click',function(){say('جارٍ التحميل…');fetch(dlg.dataset.url,{cache:'no-store',credentials:'same-origin'})
.then(function(r){return r.json()}).then(function(j){if(!j||!j.ok)throw 0;data=j;draw()}).catch(function(){say('تعذّر جلب البيانات. أعد فتح الرسم.')})});
addEventListener('resize',function(){if(dlg.open)draw()})})();</script>
<dialog id="cf" class="sheet" aria-labelledby="cft"><div class="grab"></div><div class="dg"><h3 id="cft"></h3><p class="mut" id="cfm"></p><div class="da"><button type="button" class="btn ghost" data-close>إلغاء</button><button type="button" class="btn" id="cfok">تأكيد</button></div></div></dialog>
<div class="toasts" aria-live="polite"></div>

<script>
(function(){
var D=document,R=D.documentElement,
$=function(s,r){return(r||D).querySelector(s)},
$$=function(s,r){return[].slice.call((r||D).querySelectorAll(s))},
NOW=Date.now();
function lget(k){try{return localStorage.getItem(k)}catch(e){return null}}
function lset(k,v){try{localStorage.setItem(k,v)}catch(e){}}
function sget(k){try{return sessionStorage.getItem(k)}catch(e){return null}}
function sset(k,v){try{v==null?sessionStorage.removeItem(k):sessionStorage.setItem(k,v)}catch(e){}}
/* a value left for the very next page load only (it is dropped if that load comes late) */
function leave(k,v){sset(k,Date.now()+'|'+v)}
function take(k){var v=sget(k);if(v==null)return null;sset(k);var at=v.indexOf('|');return NOW-(+v.slice(0,at))<15000?v.slice(at+1):null}
function toast(m){var t=D.createElement('div');t.className='toast';t.textContent=m;$('.toasts').appendChild(t);setTimeout(function(){t.classList.add('out');setTimeout(function(){t.remove()},300)},2400)}

/* sections */
var TABS=['users','keys','notices','support','failures','script','link'];
function tab(n,byUser){if(TABS.indexOf(n)<0)n='users';
$$('.panel').forEach(function(p){p.classList.toggle('on',p.id==='p-'+n)});
$$('.nav button').forEach(function(b){if(b.dataset.t===n)b.setAttribute('aria-current','page');else b.removeAttribute('aria-current')});
lset('tab',n);if(byUser)window.scrollTo(0,0)}
$$('[data-t]').forEach(function(b){b.addEventListener('click',function(){tab(b.dataset.t,true)})});
tab((location.hash||'').slice(1)||lget('tab'));
addEventListener('hashchange',function(){tab((location.hash||'').slice(1),true)});

/* light / dark */
var tc=$('meta[name=theme-color]');
function paint(){tc.content=R.dataset.theme==='dark'?'#111b1a':'#ffffff'}
paint();
$('#th').onclick=function(){R.dataset.theme=R.dataset.theme==='dark'?'light':'dark';lset('th',R.dataset.theme);paint()};

/* search, filter and sort of the users */
var list=$('#list'),rows=$$('.u'),q=$('#q'),so=$('#so'),nomatch=$('#nomatch'),fl=sget('fl')||'all';
rows.forEach(function(u,i){u._i=i});
var ORDER={
'new':function(a,b){return a._i-b._i},
seen:function(a,b){return b.dataset.seen-a.dataset.seen||a._i-b._i},
top:function(a,b){return b.dataset.n-a.dataset.n||a._i-b._i},
acts:function(a,b){return b.dataset.x-a.dataset.x||a._i-b._i},
name:function(a,b){return a.dataset.name.localeCompare(b.dataset.name,'ar')||a._i-b._i}};
function filter(){if(!q)return;var s=q.value.trim().toLowerCase(),n=0;
rows.forEach(function(u){var ok=(fl==='all'||u.dataset.s===fl)&&(!s||u.dataset.q.indexOf(s)>-1);u.hidden=!ok;if(ok)n++});
nomatch.hidden=n>0;$('#qx').hidden=!s;
$$('#flt button').forEach(function(b){b.setAttribute('aria-pressed',String(b.dataset.f===fl))});sset('fl',fl)}
function sort(){if(!so)return;if(!ORDER[so.value])so.value='new';
$('#sol').textContent=so.options[so.selectedIndex].dataset.s;
rows.slice().sort(ORDER[so.value]).forEach(function(u){list.appendChild(u)});sset('so',so.value)}
if(q){
q.value=take('q')||'';so.value=sget('so')||'new';
q.oninput=filter;so.onchange=sort;
$('#qx').onclick=function(){q.value='';filter();q.focus()};
$('#clr').onclick=function(){q.value='';fl='all';filter()};
$$('#flt button').forEach(function(b){b.onclick=function(){fl=b.dataset.f;filter()}});
}

/* a user just added: show the new code, ready to copy or share */
var added=take('new');
if(added!=null&&rows.length===+added+1){var nu=rows[0],rd=$('#rd'),nc=nu.dataset.code;
if(q){q.value='';fl='all';so.value='new'}
$('#rd-code').textContent=nc;$('#rd-copy').dataset.copy=nc;$('#rd-share').dataset.share='رمز الدخول: '+nc;
if(nu.dataset.name)$('#rd-t').textContent='أعطِ هذا الرمز لـ«'+nu.dataset.name+'» ليفتح به التطبيق. يرتبط الرمز بأول جوال يُدخَل فيه.';
rd.showModal()}
sort();filter();
var y=take('y');if(y)window.scrollTo(0,+y);
var note=take('toast');if(note)toast(note);

/* copy and share */
function copy(v,el){
function ok(){toast('تم النسخ');if(el&&el.classList.contains('code')){var us=$('use',el),h=us.getAttribute('href');el.classList.add('ok');us.setAttribute('href','#i-check');setTimeout(function(){el.classList.remove('ok');us.setAttribute('href',h)},1300)}}
function old(){var a=D.createElement('textarea');a.value=v;a.style.cssText='position:fixed;top:0;opacity:0';($('dialog[open]')||D.body).appendChild(a);a.select();var done=false;try{done=D.execCommand('copy')}catch(x){}a.remove();done?ok():toast('تعذّر النسخ. انسخه يدويًا.')}
if(navigator.clipboard&&window.isSecureContext)navigator.clipboard.writeText(v).then(ok,old);else old()}
if(!navigator.share)$$('[data-share]').forEach(function(b){b.hidden=true});

/* the options sheet of one user */
var sheet=$('#sheet'),cur=null;
function openSheet(u){cur=u;var d=u.dataset,av=$('.av',u),sa=$('#sh-av');
$('#sh-name').textContent=d.name||'بدون اسم';$('#sh-code').textContent=d.code;
sa.textContent=av.textContent;sa.style.setProperty('--h',av.style.getPropertyValue('--h'));
$$('input[name=id]',sheet).forEach(function(i){i.value=d.id});
$('#sh-copy').dataset.copy=d.code;$('#sh-share').dataset.share='رمز الدخول: '+d.code;
$('#sh-release').hidden=!d.bound;$('#sh-reset').hidden=!+d.n;
var pre=d.pay==='prepaid';$('input[name=pay]',$('#sh-pay')).value=pre?'later':'prepaid';
$('#sh-pay-t').innerHTML=pre?'تحويل إلى «آجل»<small>تُحسب التكلفة ويدفعها لاحقًا، ولا يُخصم من الرصيد</small>':'تحويل إلى «دفع مسبق»<small>لا تبدأ مهمة بخدمات مدفوعة بلا رصيد (الرصيد ⁦'+(d.bal||'$0.00')+'⁩)</small>';
$('#sh-pw').hidden=!d.acct;
sheet.showModal()}
$('#sh-bal').onclick=function(){sheet.close();var g=$('#bal');$('input[name=id]',g).value=cur.dataset.id;
$('#bal-now').textContent=(cur.dataset.name||'المستخدم')+' · الرصيد الآن ⁦'+(cur.dataset.bal||'$0.00')+'⁩'+(cur.dataset.pay==='prepaid'?'':' (هذا المستخدم «آجل»؛ حوّله إلى «مسبق» ليُستخدم رصيده)');
var a=$('#bal-a');a.value='';$('#bal-n').value='';g.showModal();a.focus()};
$('#sh-pw').onclick=function(){sheet.close();var g=$('#pwd');$('input[name=id]',g).value=cur.dataset.id;
$('#pwd-for').textContent='لحساب '+cur.dataset.acct+'. أعطه كلمة السر الجديدة بعد الحفظ.';var i=$('#pwd-p');i.value='';g.showModal();i.focus()};
$('#sh-rename').onclick=function(){sheet.close();var d=$('#rn'),i=$('#rn-l');$('input[name=id]',d).value=cur.dataset.id;i.value=cur.dataset.name;d.showModal();i.focus();i.select()};

D.addEventListener('click',function(e){var t=e.target,el;
if((el=t.closest('[data-more]'))){openSheet(el.closest('.u'));return}
if((el=t.closest('[data-open]'))){var d=$('#'+el.dataset.open),i=$('input:not([type=hidden])',d);d.showModal();if(i){if(!i.hasAttribute('data-keep'))i.value='';i.focus()}return}
if((el=t.closest('[data-eye]'))){var p=$('input',el.parentNode),show=p.type==='password';p.type=show?'text':'password';el.setAttribute('aria-pressed',String(show));return}
if((el=t.closest('[data-copy]')))copy(el.dataset.copy,el);
if((el=t.closest('[data-share]'))&&navigator.share)navigator.share({text:el.dataset.share}).catch(function(){});
if((el=t.closest('[data-close]'))){el=el.closest('dialog');if(el)el.close()}
else if(t.tagName==='DIALOG')t.close()});

/* the loading bar: shows from the moment a change is sent until the page comes back */
function loading(f){R.classList.add('loading');var go=f&&$('button:not([type=button])',f);if(go&&!$('.sw',f))go.classList.add('busy')}
addEventListener('pageshow',function(){R.classList.remove('loading');$$('.busy').forEach(function(b){b.classList.remove('busy')})});

/* details that load when opened (a report's log, a message's log): the page itself stays light */
function lazy(d,then){var box=$('.lz',d);if(d.dataset.done){if(then)then(d._data);return}
if(box&&!box.firstChild){var w=D.createElement('p');w.className='wait';w.textContent='جارٍ التحميل…';box.appendChild(w)}
fetch(d.dataset.src,{credentials:'same-origin',cache:'no-store'}).then(function(r){if(r.status===401){location.reload();throw 0}return r.json()}).then(function(j){
d.dataset.done='1';d._data=j;if(box){box.textContent='';
function part(title,text){if(!text)return;var h=D.createElement('h4');h.textContent=title;var p=D.createElement('pre');p.className='lg';p.textContent=text;box.appendChild(h);box.appendChild(p)}
if(j.failed&&j.failed.length){var h=D.createElement('h4');h.textContent='الإجراءات الفاشلة ('+j.failed.length+')';var u=D.createElement('ul');u.className='fl';
j.failed.forEach(function(x){var li=D.createElement('li');li.dir='auto';li.textContent=x;u.appendChild(li)});box.appendChild(h);box.appendChild(u)}
part('الخطأ',j.trace);part('السجل',j.log);part('سجل النقر',j.clicks);if(!box.firstChild)box.textContent='لا يوجد سجل.'}
if(then)then(j)}).catch(function(x){if(x!==0&&box)box.textContent='تعذّر التحميل. أغلقه وافتحه للمحاولة مرة أخرى.'})}
D.addEventListener('toggle',function(e){var d=e.target;if(d.open&&d.dataset&&d.dataset.src&&!d.dataset.done)lazy(d)},true);
D.addEventListener('click',function(e){var b=e.target.closest('[data-fcopy]');if(!b)return;
var d=b.closest('article').querySelector('details[data-src]');if(!d)return;b.classList.add('busy');
lazy(d,function(j){b.classList.remove('busy');copy([j.title,j.message,(j.failed||[]).join('\n'),j.trace,j.log].filter(Boolean).join('\n\n'))})});

/* in «تطبيق المالك»: the backup comes as a file the app saves in «التنزيلات» */
if(window.OwnerApp)D.addEventListener('submit',function(e){var f=e.target;if(!/\/backup$/.test(f.getAttribute('action')||''))return;
e.preventDefault();e.stopImmediatePropagation();loading(f);
fetch(f.action,{method:'POST',body:new FormData(f),credentials:'same-origin'}).then(function(r){var cd=r.headers.get('Content-Disposition')||'';
if(cd.indexOf('attachment')<0){location.reload();throw 0}var m=cd.match(/filename="?([^";]+)/);return r.blob().then(function(b){return [m?m[1]:'control-backup.ggbak',b]})})
.then(function(x){var rd=new FileReader();rd.onload=function(){var ok=OwnerApp.saveFile(x[0],String(rd.result).split(',')[1]);
R.classList.remove('loading');$$('.busy').forEach(function(b){b.classList.remove('busy')});f.reset();toast(ok?'حُفظت النسخة في «التنزيلات»':'تعذّر حفظ النسخة')};rd.readAsDataURL(x[1])})
.catch(function(x){if(x!==0){R.classList.remove('loading');toast('تعذّر تنزيل النسخة')}})},true);

/* every change is a form post; risky ones ask first */
var cf=$('#cf'),pending=null;
function keep(f){if(f.dataset.toast)leave('toast',f.dataset.toast);
if(f.hasAttribute('data-fresh'))leave('new',rows.length);
else{leave('y',window.scrollY);if(q)leave('q',q.value)}}
$('#cfok').onclick=function(){var f=pending;pending=null;cf.close();if(f){keep(f);loading(f);f.submit()}};
D.addEventListener('submit',function(e){var f=e.target;
if(f.dataset.confirm){e.preventDefault();var o=f.closest('dialog'),b=$('#cfok');if(o)o.close();pending=f;
$('#cft').textContent=f.dataset.title||'تأكيد الإجراء';$('#cfm').textContent=f.dataset.confirm;
b.textContent=f.dataset.yes||'تأكيد';b.classList.toggle('danger',f.dataset.kind==='danger');cf.showModal();return}
keep(f);
var sw=$('.sw',f),go=$('button:not([type=button])',f);
if(sw){sw.classList.toggle('on');sw.setAttribute('aria-checked',String(sw.classList.contains('on')))}
if(go&&!sw)go.classList.add('busy');
R.classList.add('loading')});
})();
</script>
</body></html>
"""

def seen_text(row: dict) -> str:
    when = row.get("last_seen") or 0
    if not when:
        return "لم يدخل"
    delta = int(time.time()) - int(when)
    if delta < 60:
        return "الآن"
    if delta < 3600:
        return f"قبل {delta // 60} د"
    if delta < 86400:
        return f"قبل {delta // 3600} س"
    return f"قبل {delta // 86400} يوم"


@app.after_request
def compress_pages(response):
    """The panel's pages and data go compressed to a browser that asks so (about a tenth of their size): the
    phone loads them faster. The apps' requests, the files and the pictures go as they are."""
    if (response.direct_passthrough or response.status_code != 200 or response.headers.get("Content-Encoding")
            or response.mimetype not in ("text/html", "application/json")
            or "gzip" not in (request.headers.get("Accept-Encoding") or "")):
        return response
    body = response.get_data()
    if len(body) < 2048:
        return response
    packed = gzip.compress(body, 5)
    response.set_data(packed)
    response.headers["Content-Encoding"] = "gzip"
    response.headers["Content-Length"] = str(len(packed))
    response.headers.add("Vary", "Accept-Encoding")
    return response


@app.get(f"/{ADMIN}")
def dashboard():
    if not logged_in():
        return render_template_string(LOGIN_PAGE, admin=ADMIN, error="")
    keys = load_keys()
    with LOCK:
        codes = load_codes()
    acts_data = load_acts()
    usage_data = load_usage()
    rows = [dict(c, last_seen_text=seen_text(c), usage=usage_of(c["id"], usage_data), acts=acts_of(c["id"], acts_data)) for c in codes]
    for r in rows:
        r["pay"] = pay_of(r)
        r["balance"] = balance_of(r)
        r["account_user"] = str((r.get("account") or {}).get("user") or "")
        r["ledger"] = [dict(e, when=seen_text({"last_seen": int(e.get("at") or 0)}))
                       for e in (r.get("ledger") if isinstance(r.get("ledger"), list) else [])[:6] if isinstance(e, dict)]
        r.pop("account", None)                       # (no password hash goes into the page)
        r["acts_text"] = ("الآن" if time.time() - r["acts"]["at"] < 60 else seen_text({"last_seen": r["acts"]["at"]})) if r["acts"]["at"] else ""
        n = len(devices_of(r))
        r["device_count"] = n
        r["devices_text"] = ("غير مربوط", "جهاز مربوط", "جهازان")[n] if n < 3 else f"{n} {'أجهزة' if n <= 10 else 'جهازًا'}"
        r.pop("devices", None)                       # (the phones' ids stay out of the page)
        r.pop("hw", None)
    stats = {"users": len(rows), "active": sum(1 for r in rows if r.get("active")),
             "bound": sum(r["device_count"] for r in rows),
             "comments": sum(r["usage"]["total"] for r in rows),
             "cost": round(sum(r["usage"]["cost"] for r in rows), 2),
             "repost": sum(r["acts"]["repost"] for r in rows), "like": sum(r["acts"]["like"] for r in rows),
             "bookmark": sum(r["acts"]["bookmark"] for r in rows)}
    since_start = lifetime_totals(usage_data)
    stats["all_comments"], stats["all_cost"] = since_start["comments"], since_start["cost"]
    notices = notice_rows(codes)
    messages = support_rows(codes)
    move = load_move()
    last_backup = int(SECRETS.get("last_backup") or 0)
    script_live = load_script_meta(SCRIPT_META)
    script_staged = load_script_meta(STAGED_META)
    script_pilot = pilot_meta()
    pilot_ids = set(script_pilot.get("codes") or [])
    script_pilot_names = [row.get("label") or row.get("code") or "" for row in rows if row.get("id") in pilot_ids]
    failures = failure_rows(codes)
    all_failures = load_failures()["items"]
    all_messages = load_support()["items"]
    return render_template_string(
        DASHBOARD, admin=ADMIN, app_link=app_link(), codes=rows, stats=stats,
        notices=notices, notice_kinds=NOTICE_KINDS, messages=messages,
        unread=sum(1 for m in all_messages if not m.get("read")), messages_total=len(all_messages),
        failures=failures, failures_new=sum(1 for f in all_failures if not f.get("read")), failures_total=len(all_failures),
        flash=session.pop("flash", None), move_code=move_code(SECRETS.get("move_public", "")),
        move_link=move.get("link") or "", move_when=seen_text({"last_seen": int(move.get("at") or 0)}) if move.get("at") else "",
        move_active=bool(move.get("record")) and int(time.time()) < int(move.get("until") or 0),
        move_moved_here=(move.get("link") or "").split("#")[0].split("/")[-1] == SECRETS["api_secret"],
        backup_when=seen_text({"last_seen": last_backup}) if last_backup else "",
        owner_link=owner_app_link(request.host), in_owner_app=OWNER_APP_MARK in (request.headers.get("User-Agent") or ""),
        this_host=request.host, relay=MOVE_RELAY.split("//")[-1],
        prices=load_prices(), welcome=load_welcome(), pace=load_pace(), prompt=load_prompt(), one_device=one_device(),
        pay=public_payment(),
        app_slots=app_panel(codes), app_dl_link=app_download_link(), app_package=APP_PACKAGE,
        script_live=script_live, script_staged=script_staged, script_next=next_version(highest_published_version()),
        script_floor=highest_published_version(), script_pilot=script_pilot, script_pilot_ids=pilot_ids,
        script_pilot_names=script_pilot_names,
        script_pilot_when=seen_text({"last_seen": int(script_pilot.get("published_at") or 0)}) if script_pilot.get("published_at") else "",
        script_live_when=seen_text({"last_seen": int(script_live.get("published_at") or 0)}) if script_live.get("published_at") else "",
        script_can_publish=bool(script_staged.get("version")) and all(
            (script_staged.get("sha256"), script_staged.get("content_sha256")) != (meta.get("sha256"), meta.get("content_sha256"))
            for meta in (script_live, script_pilot)),
        engine=keys["engine"], gemini_set=gemini_ready(keys), claude_set=bool(keys["claude_sealed"]),
        gemini_model=keys["gemini_model"], claude_model=keys["claude_model"],
        gemini_default=GEMINI_DEFAULT_MODEL, claude_default=CLAUDE_DEFAULT_MODEL,
        gemini_provider=keys["gemini_provider"], google_set=bool(keys["gemini_sealed"]),
        openrouter_set=bool(keys["openrouter_sealed"]), openrouter_model=keys["openrouter_model"],
        openrouter_default=OPENROUTER_DEFAULT_MODEL)


@app.post(f"/{ADMIN}/login")
def login():
    password = request.form.get("password") or ""
    if hmac.compare_digest(hash_password(password, SECRETS["admin_salt"]), SECRETS["admin_hash"]):
        session["owner"] = True
        if not SECRETS.get("move_public"):
            remember_move_public(password)
        response = redirect(f"/{ADMIN}")
        if OWNER_APP_MARK in (request.headers.get("User-Agent") or ""):
            response.set_cookie(OWNER_COOKIE, owner_token(), max_age=OWNER_DAYS * 86400, secure=True, httponly=True,
                                samesite="Strict", path=f"/{ADMIN}")
        return response
    return render_template_string(LOGIN_PAGE, admin=ADMIN, error="كلمة المرور غير صحيحة.")


def remember_move_public(password: str) -> str:
    public = ed_public(move_seed(password)).hex()
    data = read_private_json(SECRETS_PATH) or {}
    data["move_public"] = public
    write_private_json(SECRETS_PATH, data)
    SECRETS["move_public"] = public
    return public


def password_ok(password: str) -> bool:
    return bool(password) and hmac.compare_digest(hash_password(password, SECRETS["admin_salt"]), SECRETS["admin_hash"])


def flash(kind: str, text: str) -> None:
    session["flash"] = {"kind": kind, "text": text}


@app.post(f"/{ADMIN}/move")
def move_apps_here():
    """«ربط التطبيقات بهذا الخادم»: a move order signed with the password's key, to this server's app link."""
    if not logged_in():
        return redirect(f"/{ADMIN}")
    password = request.form.get("password") or ""
    if not password_ok(password):
        flash("bad", "كلمة المرور غير صحيحة. لم يتم الربط.")
        return redirect(f"/{ADMIN}")
    if request.form.get("confirm") != "1":
        flash("bad", "أكّد النقل أولًا. لم يتم الربط.")
        return redirect(f"/{ADMIN}")
    host = re.sub(r"\s+", "", request.form.get("host") or "")
    if not re.fullmatch(r"(\[[0-9A-Fa-f:]{2,39}\]|[A-Za-z0-9](?:[A-Za-z0-9.\-]{0,251}[A-Za-z0-9])?)(:\d{1,5})?", host):
        flash("bad", "عنوان الخادم غير صالح. اكتب الـ IP أو النطاق (ويمكن معه رقم المنفذ).")
        return redirect(f"/{ADMIN}")
    if not re.search(r"(^[^\[\]:]+|\])(:\d{1,5})$", host) and LISTEN_PORT != 443:
        host = f"{host}:{LISTEN_PORT}"
    seed = move_seed(password)
    public = ed_public(seed)
    if SECRETS.get("move_public") != public.hex():
        remember_move_public(password)
    link = f"https://{host}/{SECRETS['api_secret']}#{certificate_fingerprint()}"
    now = int(time.time())
    record = move_seal(seed, link, now)
    problem = move_publish(record, public)
    write_private_json(MOVE_PATH, {"record": record, "public": public.hex(), "link": link, "at": now,
                                   "until": now + MOVE_REPEAT_DAYS * 86400, "published": 0 if problem else now})
    if problem:
        flash("warn", "حُفظ أمر النقل، لكن تعذّر إرساله الآن (" + problem + "). يحاول الخادم إرساله من جديد تلقائيًا كل ١٠ دقائق حتى ينجح.")
    else:
        flash("ok", "تم الربط. تنتقل التطبيقات إلى هذا الخادم خلال دقائق متى ما تعذّر عليها الوصول للخادم القديم "
                    "(وإلا خلال ٣ ساعات). يُعاد إرسال الأمر كل ٦ ساعات لمدة ٩٠ يومًا.")
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/backup")
def backup_download():
    if not logged_in():
        return redirect(f"/{ADMIN}")
    password = request.form.get("password") or ""
    if not password_ok(password):
        flash("bad", "كلمة المرور غير صحيحة. لم تُنزَّل النسخة.")
        return redirect(f"/{ADMIN}")
    blob = backup_pack(password)
    data = read_private_json(SECRETS_PATH) or {}
    data["last_backup"] = int(time.time())
    write_private_json(SECRETS_PATH, data)
    SECRETS["last_backup"] = data["last_backup"]
    name = "control-backup-" + time.strftime("%Y%m%d-%H%M") + ".ggbak"
    return send_file(io.BytesIO(blob), mimetype="application/octet-stream", as_attachment=True, download_name=name)


RESTORED_PAGE = r"""<!doctype html><html lang="ar" dir="rtl"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><meta name="robots" content="noindex,nofollow"><title>تمت الاستعادة</title>
<style>body{margin:0;min-height:100vh;display:grid;place-items:center;padding:16px;background:#eef2f1;color:#10201f;font:15px/1.7 system-ui,sans-serif}
.box{background:#fff;border:1px solid #dce4e2;border-radius:18px;padding:22px;max-width:520px}h1{font-size:19px;margin:0 0 8px}
code{display:block;direction:ltr;text-align:left;background:#f3f6f5;border:1px solid #dce4e2;border-radius:10px;padding:10px;margin:10px 0;overflow-wrap:anywhere;font-size:13px}
a{color:#0f6b66;font-weight:600}</style></head><body><div class="box">
<h1>تمت استعادة النسخة الاحتياطية</h1>
<p>يُعاد تشغيل خادم التحكّم الآن ليعمل ببيانات النسخة (المستخدمون ورموزهم والمفاتيح والشهادة). صار رابط لوحة المالك
رابطَ الخادم القديم، وكلمة مرورها كلمة مرور النسخة:</p>
<code>{{ link }}</code>
<p><a href="{{ link }}">افتح لوحة التحكّم</a> بعد ثوانٍ، ثم من تبويب «الربط» اضغط «ربط التطبيقات بهذا الخادم».</p>
</div></body></html>"""


@app.post(f"/{ADMIN}/restore")
def backup_restore():
    """A backup in place of this server's data; the server then starts again with it."""
    if not logged_in():
        return redirect(f"/{ADMIN}")
    password = request.form.get("password") or ""
    upload = request.files.get("file")
    if request.form.get("confirm") != "1":
        flash("bad", "أكّد الاستعادة أولًا. لم يتغيّر شيء.")
        return redirect(f"/{ADMIN}")
    if not upload:
        flash("bad", "اختر ملف النسخة الاحتياطية.")
        return redirect(f"/{ADMIN}")
    try:
        restored = backup_unpack(upload.read(64 * 1024 * 1024), password)
    except ValueError as exc:
        flash("bad", str(exc))
        return redirect(f"/{ADMIN}")
    except Exception:
        flash("bad", "تعذّر فتح النسخة: الملف تالف.")
        return redirect(f"/{ADMIN}")
    keep = DATA_DIR / ("before-restore-" + time.strftime("%Y%m%d-%H%M%S"))
    keep.mkdir(parents=True, exist_ok=True)
    with LOCK:
        for name in BACKUP_FILES:
            current = DATA_DIR / name
            if current.is_file():
                shutil.copy2(current, keep / name)
        for name, content in restored["files"].items():
            target = DATA_DIR / name
            temporary = target.with_name(name + ".restore")
            temporary.write_bytes(content)
            os.chmod(temporary, 0o600)
            os.replace(temporary, target)
    old = json.loads(restored["files"]["secrets.json"].decode("utf-8"))
    port = "" if LISTEN_PORT == 443 else f":{LISTEN_PORT}"
    link = f"https://{request.host.split(':')[0] if not request.host.startswith('[') else request.host.split(']')[0] + ']'}{port}/{old.get('admin_path', '')}"

    def again() -> None:
        time.sleep(1.5)
        print("استُعيدت نسخة احتياطية: يُعاد تشغيل خادم التحكّم…", flush=True)
        # (the listening socket is left inheritable by the web server: closed now, so the new start can bind it)
        for fd in range(3, 4096):
            try:
                os.set_inheritable(fd, False)
            except OSError:
                pass
        os.execv(sys.executable, [sys.executable] + sys.argv)
    threading.Thread(target=again, daemon=True).start()
    session.clear()
    return render_template_string(RESTORED_PAGE, link=link)


@app.post(f"/{ADMIN}/logout")
def logout():
    session.clear()
    response = redirect(f"/{ADMIN}")
    response.delete_cookie(OWNER_COOKIE, path=f"/{ADMIN}")
    return response


@app.get(f"/{ADMIN}/pulse")
def owner_pulse():
    """For «تطبيق المالك» (every 15 minutes): the failures and the users' messages newer than the ones it knows."""
    if not logged_in():
        return jsonify(ok=False), 401
    try:
        after_f = int(request.args.get("f") or 0)
        after_m = int(request.args.get("m") or 0)
    except ValueError:
        after_f = after_m = 0
    names = {row.get("id"): (row.get("label") or row.get("code") or "") for row in load_codes()}
    failures = load_failures()["items"]
    messages = load_support()["items"]
    new_f = [item for item in failures if int(item.get("id") or 0) > after_f]
    new_m = [item for item in messages if int(item.get("id") or 0) > after_m]
    return jsonify(
        ok=True,
        f_last=max((int(item.get("id") or 0) for item in failures), default=0),
        m_last=max((int(item.get("id") or 0) for item in messages), default=0),
        failures_new=len(new_f), messages_new=len(new_m),
        failures=[{"id": item.get("id"), "who": names.get(item.get("code_id")) or item.get("label") or "مستخدم",
                   "title": str(item.get("title") or "")[:140]} for item in new_f[:5]],
        messages=[{"id": item.get("id"), "who": names.get(item.get("code_id")) or item.get("label") or "مستخدم",
                   "text": str(item.get("text") or "")[:140]} for item in new_m[:5]])


@app.post(f"/{ADMIN}/code/new")
def code_new():
    if not logged_in():
        return redirect(f"/{ADMIN}")
    label = (request.form.get("label") or "").strip()[:40]
    with LOCK:
        codes = load_codes()
        codes.insert(0, {"id": secrets.token_hex(8), "code": make_code(), "label": label,
                         "active": True, "created": int(time.time()), "last_seen": 0, "bound_device": ""})
        save_codes(codes)
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/code/toggle")
def code_toggle():
    if not logged_in():
        return redirect(f"/{ADMIN}")
    code_id = request.form.get("id")
    with LOCK:
        codes = load_codes()
        for row in codes:
            if row.get("id") == code_id:
                row["active"] = not row.get("active")
        save_codes(codes)
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/code/delete")
def code_delete():
    if not logged_in():
        return redirect(f"/{ADMIN}")
    code_id = request.form.get("id")
    with LOCK:
        save_codes([row for row in load_codes() if row.get("id") != code_id])
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/code/release")
def code_release():
    """Unbind a code from its phones: each is signed out, and the user signs in again on the phone (or phones) wanted."""
    if not logged_in():
        return redirect(f"/{ADMIN}")
    code_id = request.form.get("id")
    with LOCK:
        codes = load_codes()
        for row in codes:
            if row.get("id") == code_id:
                row["bound_device"] = ""
                row.pop("devices", None)
        save_codes(codes)
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/devices")
def devices_save():
    """«الأجهزة»: each user on any number of phones, or on one only (the first)."""
    if not logged_in():
        return redirect(f"/{ADMIN}")
    one = request.form.get("one_device") == "1"
    with LOCK:
        write_private_json(DEVICES_PATH, {"version": 1, "one_device": one})
        if one:                                     # (the other phones are signed out, and stay out if it is undone)
            codes = load_codes()
            if any(row.get("devices") for row in codes):
                for row in codes:
                    row.pop("devices", None)
                save_codes(codes)
    flash("ok", "صار كل مستخدم على جهاز واحد: يبقى أول جوال دخل به، وتخرج أجواله الأخرى."
          if one else "صار كل مستخدم يدخل برمزه أو حسابه من أي عدد من الأجوال، وتعمل كلها معًا.")
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/code/rename")
def code_rename():
    """Change the name the owner sees for a code; the code itself and its phone stay as they are."""
    if not logged_in():
        return redirect(f"/{ADMIN}")
    code_id = request.form.get("id")
    label = (request.form.get("label") or "").strip()[:40]
    with LOCK:
        codes = load_codes()
        for row in codes:
            if row.get("id") == code_id:
                row["label"] = label
        save_codes(codes)
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/prices")
def prices_save():
    """«أسعار الخدمات»."""
    if not logged_in():
        return redirect(f"/{ADMIN}")
    prices = load_prices()
    for name in SERVICES:
        value = form_dollars(request.form.get(name))
        if not 0 <= value <= 100:
            flash("bad", "اكتب كل سعر رقمًا بالدولار من 0 إلى 100، مثل 0.01 (و0 للخدمة المجانية).")
            return redirect(f"/{ADMIN}")
        prices[name] = round(value, 4)
    welcome = None                                   # (a form without the field leaves it as it is)
    if request.form.get("welcome") is not None:
        welcome = form_dollars(request.form.get("welcome"))
        if not 0 <= welcome <= 100:
            flash("bad", "اكتب رصيد الحساب الجديد رقمًا بالدولار من 0 إلى 100، مثل 1 (و0 لإيقافه).")
            return redirect(f"/{ADMIN}")
    save_prices(prices, None if welcome is None else round(welcome, 2))
    flash("ok", "حُفظت الأسعار. تُحسب بها الخدمات من الآن، وما حُسب قبلها يبقى كما هو. "
                f"رصيد الحساب الجديد: {money(load_welcome())}.")
    return redirect(f"/{ADMIN}")


@app.get(f"/{ADMIN}/chart")
def chart_data():
    """«الرسم البياني»: the hours kept, and each user's numbers now (likes and bookmarks from the app, comments counted
    here)."""
    if not logged_in():
        return jsonify(ok=False), 403
    data = read_private_json(HISTORY_PATH) or {}
    hours = {key: [int(value or 0) for value in row[:4]] for key, row in (data.get("hours") or {}).items()
             if str(key).isdigit() and isinstance(row, list)}
    with LOCK:
        codes = load_codes()
    usage, acts = load_usage(), load_acts()
    users = []
    for row in codes:
        done = acts_of(row["id"], acts)
        users.append({"name": row.get("label") or row.get("code") or "", "like": done["like"], "bookmark": done["bookmark"],
                      "comment": usage_of(row["id"], usage)["total"]})
    users = [user for user in users if user["like"] or user["bookmark"] or user["comment"]]
    users.sort(key=lambda user: -(user["like"] + user["bookmark"] + user["comment"]))
    return jsonify(ok=True, since=int(data.get("since") or 0), hours=hours, users=users[:12], more=max(0, len(users) - 12))


@app.post(f"/{ADMIN}/pace")
def pace_save():
    """«سرعة التنفيذ»: comment typing and the wait between buttons, from / to, in seconds."""
    if not logged_in():
        return redirect(f"/{ADMIN}")
    pace = load_pace()
    for key, name in (("typing", "كتابة التعليق"), ("gap", "الانتظار بين الأزرار"), ("settle", "الانتظار بعد تحميل التغريدة"),
                      ("in_page", "عدد التغريدات بدون تحميل الصفحة كاملة")):
        if request.form.get(key + "_from") is None and request.form.get(key + "_to") is None:
            continue                                 # (a form from before this pair: it stays as it is)
        low, high = form_dollars(request.form.get(key + "_from")), form_dollars(request.form.get(key + "_to"))
        if key == "in_page":
            if not (low == low and high == high and low >= 1 and high >= 1 and low == int(low) and high == int(high)):
                flash("bad", f"اكتب {name} أعدادًا صحيحة من 1، مثل 1 و3.")
                return redirect(f"/{ADMIN}")
            if low > high:
                flash("bad", f"في {name}: «من» يجب ألا يكون أكبر من «إلى».")
                return redirect(f"/{ADMIN}")
            if high > PACE_LIMITS[key]:
                flash("bad", f"{name} حتى {PACE_LIMITS[key]:g} على الأكثر.")
                return redirect(f"/{ADMIN}")
            pace[key] = [int(low), int(high)]
            continue
        if low < 0 or high < 0 or low != low or high != high:          # (and not «nan»)
            flash("bad", f"اكتب {name} بالثواني أرقامًا، مثل {dict(typing='3 و8', gap='0.3 و1', settle='0.6 و1.5')[key]}.")
            return redirect(f"/{ADMIN}")
        if low > high:
            flash("bad", f"في {name}: «من» يجب ألا يكون أكبر من «إلى».")
            return redirect(f"/{ADMIN}")
        if high > PACE_LIMITS[key]:
            flash("bad", f"{name} حتى {PACE_LIMITS[key]:g} ثانية على الأكثر.")
            return redirect(f"/{ADMIN}")
        pace[key] = [round(low, 2), round(high, 2)]
    if request.form.get("in_page_form"):                  # (a form with the switch: checked or not)
        pace["in_page_on"] = request.form.get("in_page_on") == "1"
    write_private_json(PACE_PATH, {"version": 1, **pace})
    flash("ok", f"حُفظت سرعة التنفيذ: كتابة التعليق من {pace['typing'][0]:g} إلى {pace['typing'][1]:g} ثانية، وبين الأزرار من "
                f"{pace['gap'][0]:g} إلى {pace['gap'][1]:g}، وبعد تحميل التغريدة من {pace['settle'][0]:g} إلى {pace['settle'][1]:g}، "
                + (f"والفتح السريع مشغّل: تحميل الصفحة كاملة بعد {pace['in_page'][0]} إلى {pace['in_page'][1]} تغريدات. "
                   if pace.get("in_page_on") else "والفتح السريع متوقف: كل تغريدة تُحمَّل كاملة. ")
                + "تُطبَّق على كل المستخدمين من مهمتهم التالية.")
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/payment")
def payment_save():
    """«الدفع عبر Binance»: the Binance Pay ID shown to users, a note, and the API key for checking transfers."""
    if not logged_in():
        return redirect(f"/{ADMIN}")
    data = load_binance()
    binance_id = re.sub(r"\s+", "", str(request.form.get("binance_id") or ""))
    if binance_id and not re.fullmatch(r"\d{5,20}", binance_id):
        flash("bad", "معرّف Binance Pay أرقام فقط (من 5 إلى 20 رقمًا).")
        return redirect(f"/{ADMIN}")
    note = str(request.form.get("note") or "").replace("\r\n", "\n").strip()
    if len(note) > 500:
        flash("bad", "الملاحظة حتى 500 حرف.")
        return redirect(f"/{ADMIN}")
    key = str(request.form.get("api_key") or "").strip()
    secret = str(request.form.get("api_secret") or "").strip()
    for value, name in ((key, "مفتاح API"), (secret, "السر")):
        if value and not re.fullmatch(r"[A-Za-z0-9]{16,128}", value):
            flash("bad", f"{name} غير صالح: انسخه من Binance كما هو.")
            return redirect(f"/{ADMIN}")
    if bool(key) != bool(secret) and not (data["key"] and data["secret"]):
        flash("bad", "اكتب مفتاح API والسر معًا.")
        return redirect(f"/{ADMIN}")
    data.update(binance_id=binance_id, note=note)
    if key:
        data["key"] = key
    if secret:
        data["secret"] = secret
    write_private_json(BINANCE_PATH, {"version": 1, **data})
    flash("ok", "حُفظ الدفع عبر Binance: " + ("التحقق تلقائي." if data["key"] and data["secret"] else
                                            "بلا مفتاح API تصلك طلبات الشحن في «رسائل العملاء» لتتحقق بنفسك."))
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/binance/test")
def binance_test():
    """Reads the last transfers with the saved key: that it works, and how Binance writes their Order IDs."""
    if not logged_in():
        return redirect(f"/{ADMIN}")
    data = load_binance()
    if not (data["key"] and data["secret"]):
        flash("bad", "احفظ مفتاح API والسر أولًا.")
        return redirect(f"/{ADMIN}")
    try:
        rows = binance_history(data["key"], data["secret"])
    except BinanceError as exc:
        flash("bad", f"لم ينجح الاتصال: {exc}")
        return redirect(f"/{ADMIN}")
    received = [row for row in rows if topup_amount(row.get("amount")) > 0 and float(row.get("amount") or 0) > 0]
    last = "، ".join(f"{row.get('transactionId')} ({row.get('amount')} {row.get('currency')})" for row in received[:3])
    flash("ok", f"الاتصال يعمل: {len(rows)} عملية في آخر {TOPUP_LOOKBACK_DAYS} يومًا، منها {len(received)} واردة."
                + (f" آخرها: {last}." if last else ""))
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/binance/forget")
def binance_forget():
    if not logged_in():
        return redirect(f"/{ADMIN}")
    data = load_binance()
    data.update(key="", secret="")
    write_private_json(BINANCE_PATH, {"version": 1, **data})
    flash("ok", "حُذف مفتاح Binance: طلبات الشحن تصلك في «رسائل العملاء».")
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/prompt")
def prompt_save():
    """«برومبت التعليقات»: the instructions, the angles, the manners and the longest reply."""
    if not logged_in():
        return redirect(f"/{ADMIN}")
    saved, problem = prompt_from_form(request.form)
    if problem:
        flash("bad", problem + " لم يُحفظ شيء.")
        return redirect(f"/{ADMIN}")
    write_private_json(PROMPT_PATH, {"version": 1, **saved, "saved_at": int(time.time())})
    settings = load_prompt()
    missing = [mark for mark in PROMPT_MARKS if mark not in settings["text"]]
    note = (" لاحظ أن التعليمات بلا " + "، ".join(missing) + "، فلا يوضع ما تعنيه.") if missing else ""
    flash("ok", "حُفظ برومبت التعليقات، ويُطبَّق على كل المستخدمين من التعليق التالي." + note)
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/prompt/reset")
def prompt_reset():
    if not logged_in():
        return redirect(f"/{ADMIN}")
    try:
        PROMPT_PATH.unlink()
    except OSError:
        pass
    flash("ok", "عاد برومبت التعليقات إلى الافتراضي.")
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/prompt/try")
def prompt_try():
    """«جرّب»: one reply to the tweet text typed in the panel, written with the settings as typed there (not saved),
    with the active key, like any comment (it is not counted)."""
    if not logged_in():
        return jsonify(ok=False, error="انتهت الجلسة. أعد تحميل الصفحة وسجّل الدخول."), 401
    saved, problem = prompt_from_form(request.form)
    if problem:
        return jsonify(ok=False, error=problem)
    given = str(request.form.get("tweet") or "").strip()
    if not given:
        return jsonify(ok=False, error="الصق رابط تغريدة أو نصها أولًا.")
    link = TWEET_LINK.match(given)
    image, shown = None, None
    if link:                                    # (a link: the tweet as the app reads it)
        tweet, problem = fetch_tweet(link.group(1))
        if problem:
            return jsonify(ok=False, error=problem)
        text, picture = tweet_material(tweet)
        image = tweet_picture(picture) if picture else None
        if not text and not image:
            return jsonify(ok=False, error="لا نص ولا صورة في هذه التغريدة.")
        author = tweet.get("author") if isinstance(tweet.get("author"), dict) else {}
        shown = {"by": str(author.get("screen_name") or "")[:30], "text": str(tweet.get("text") or "")[:400],
                 "picture": bool(image)}
    else:
        text = given[:4000]
    voice = request.form.get("voice") if request.form.get("voice") in REPLY_VOICES else DEFAULT_REPLY_VOICE
    settings = prompt_settings(saved)
    _prompt_trial.settings = settings
    try:
        comment = write_reply(text, image, voice, random.randrange(len(settings["manners"])), [])
    except RuntimeError as exc:
        return jsonify(ok=False, error=str(exc))
    finally:
        _prompt_trial.settings = None
    return jsonify(ok=True, comment=comment, chars=len(comment), limit=settings["max_chars"], tweet=shown)


@app.post(f"/{ADMIN}/code/pay")
def code_pay():
    """«آجل» or «مسبق» for one user."""
    if not logged_in():
        return redirect(f"/{ADMIN}")
    code_id = request.form.get("id")
    pay = PAY_PREPAID if request.form.get("pay") == PAY_PREPAID else PAY_LATER
    with LOCK:
        codes = load_codes()
        for row in codes:
            if row.get("id") == code_id:
                row["pay"] = pay
        save_codes(codes)
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/code/balance")
def code_balance():
    """Add to (or, with a minus, take from) one user's balance: a trial balance, a top-up, a correction."""
    if not logged_in():
        return redirect(f"/{ADMIN}")
    code_id = request.form.get("id")
    raw = (request.form.get("amount") or "").strip().translate(str.maketrans("٠١٢٣٤٥٦٧٨٩٫،", "0123456789.."))
    raw = raw.replace("$", "").replace(" ", "")
    try:
        amount = round(float(raw), 2)
    except ValueError:
        amount = 0.0
    if not amount or abs(amount) > 10000:
        flash("bad", "اكتب المبلغ رقمًا بالدولار، مثل 2 أو 0.50 (وبإشارة سالب للخصم).")
        return redirect(f"/{ADMIN}")
    note = (request.form.get("note") or "").strip()[:60] or ("رصيد تجريبي" if amount > 0 else "تصحيح")
    with LOCK:
        codes = load_codes()
        row = next((item for item in codes if item.get("id") == code_id), None)
        if row is None:
            flash("bad", "المستخدم غير موجود.")
            return redirect(f"/{ADMIN}")
        row["balance"] = round(balance_of(row) + amount, 4)
        ledger = row.get("ledger") if isinstance(row.get("ledger"), list) else []
        ledger.insert(0, {"at": int(time.time()), "amount": amount, "note": note, "after": round(row["balance"], 2)})
        row["ledger"] = ledger[:LEDGER_KEEP]
        save_codes(codes)
        name = row.get("label") or row.get("code") or ""
        later = pay_of(row) != PAY_PREPAID
    flash("ok", f"{'أُضيف' if amount > 0 else 'خُصم'} {money(abs(amount))} {'إلى' if amount > 0 else 'من'} رصيد {name}. "
                f"الرصيد الآن {money(row['balance'])}."
                + (" (هذا المستخدم «آجل»: لا يُستخدم الرصيد حتى تحوّله إلى «مسبق».)" if later else ""))
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/code/password")
def code_password():
    """A new password for an account (its owner forgot it): the owner gives it to them."""
    if not logged_in():
        return redirect(f"/{ADMIN}")
    code_id = request.form.get("id")
    password = request.form.get("password") or ""
    if not 6 <= len(password) <= 128:
        flash("bad", "كلمة السر 6 أحرف على الأقل.")
        return redirect(f"/{ADMIN}")
    stored = account_pw_hash(password)
    with LOCK:
        codes = load_codes()
        row = next((item for item in codes if item.get("id") == code_id and isinstance(item.get("account"), dict)), None)
        if row is None:
            flash("bad", "هذا المستخدم ليس له حساب بكلمة سر.")
            return redirect(f"/{ADMIN}")
        row["account"]["pw"] = stored
        save_codes(codes)
        key = account_key(row["account"].get("user"))
    with _signin_lock:
        _signin_failures.pop(key, None)
    flash("ok", f"عُيّنت كلمة سر جديدة لـ {row['account'].get('user')}. أعطه إياها، ويدخل بها.")
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/code/reset-cost")
def code_reset_cost():
    if not logged_in():
        return redirect(f"/{ADMIN}")
    reset_usage(request.form.get("id"))
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/reset-cost-all")
def reset_cost_all():
    if not logged_in():
        return redirect(f"/{ADMIN}")
    reset_all_usage()
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/key")
def set_key():
    if not logged_in():
        return redirect(f"/{ADMIN}")
    which = request.form.get("which")
    api_key = (request.form.get("api_key") or "").strip()
    model = (request.form.get("model") or "").strip()[:60]
    if which not in ("gemini", "claude", "openrouter"):
        return redirect(f"/{ADMIN}")
    with LOCK:
        keys = load_keys()
        if api_key:
            keys[f"{which}_sealed"] = seal_key(api_key)
        keys[f"{which}_model"] = model
        save_keys(keys)
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/gemini-provider")
def set_gemini_provider():
    if not logged_in():
        return redirect(f"/{ADMIN}")
    provider = request.form.get("provider")
    if provider in ("google", "openrouter"):
        with LOCK:
            keys = load_keys()
            keys["gemini_provider"] = provider
            save_keys(keys)
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/engine")
def set_engine():
    if not logged_in():
        return redirect(f"/{ADMIN}")
    engine = request.form.get("engine")
    if engine in ("gemini", "claude"):
        with LOCK:
            keys = load_keys()
            keys["engine"] = engine
            save_keys(keys)
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/notice/new")
def notice_new():
    if not logged_in():
        return redirect(f"/{ADMIN}")
    add_notice(request.form.get("text") or "", request.form.get("kind") or "info", request.form.get("target") or "all")
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/notice/delete")
def notice_delete():
    if not logged_in():
        return redirect(f"/{ADMIN}")
    delete_notice(request.form.get("id"))
    return redirect(f"/{ADMIN}")


@app.get(f"/{ADMIN}/support/<int:message_id>/<int:index>")
def support_file(message_id: int, index: int):
    if not logged_in():
        return "", 401
    item = next((row for row in load_support()["items"] if row.get("id") == message_id), None)
    files = (item or {}).get("files") or []
    if not 0 <= index < len(files):
        return "", 404
    entry = files[index]
    path = SUPPORT_DIR / str(message_id) / str(entry.get("stored") or "")
    if not path.is_file():
        return "", 404
    response = send_file(path, mimetype=entry.get("type") or "application/octet-stream", conditional=True,
                         download_name=f"{message_id}-{index + 1}.{path.suffix.lstrip('.')}")
    response.headers["Cache-Control"] = "private, max-age=3600"
    return response


@app.get(f"/{ADMIN}/support/<int:message_id>/log")
def support_log(message_id: int):
    """A message's log (the last lines of the app's log when it was sent), loaded when it is opened."""
    if not logged_in():
        return jsonify(ok=False), 401
    try:
        log = (SUPPORT_DIR / str(message_id) / "log.txt").read_text(encoding="utf-8")
    except OSError:
        log = ""
    return jsonify(ok=True, log=log)


@app.post(f"/{ADMIN}/support/read")
def support_read():
    if not logged_in():
        return redirect(f"/{ADMIN}")
    try:
        message_id = int(request.form.get("id") or 0)
    except ValueError:
        return redirect(f"/{ADMIN}")
    with LOCK:
        data = load_support()
        for item in data["items"]:
            if message_id == 0 or item.get("id") == message_id:
                item["read"] = True if message_id == 0 else not item.get("read")
        save_support(data)
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/support/delete")
def support_delete():
    if not logged_in():
        return redirect(f"/{ADMIN}")
    try:
        message_id = int(request.form.get("id") or 0)
    except ValueError:
        return redirect(f"/{ADMIN}")
    with LOCK:
        data = load_support()
        data["items"] = [item for item in data["items"] if item.get("id") != message_id]
        save_support(data)
    shutil.rmtree(SUPPORT_DIR / str(message_id), ignore_errors=True)
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/support/reply")
def support_reply():
    """The owner's answer: it goes to that user's app as a notice (its notifications list opens by itself)."""
    if not logged_in():
        return redirect(f"/{ADMIN}")
    try:
        message_id = int(request.form.get("id") or 0)
    except ValueError:
        return redirect(f"/{ADMIN}")
    text = (request.form.get("text") or "").strip()[:NOTICE_TEXT_MAX]
    if not text:
        return redirect(f"/{ADMIN}")
    with LOCK:
        data = load_support()
        item = next((row for row in data["items"] if row.get("id") == message_id), None)
        code_id = (item or {}).get("code_id") or ""
        if item is not None:
            item.setdefault("replies", []).append({"text": text, "at": int(time.time())})
            item["read"] = True
            save_support(data)
    if code_id:
        add_notice("ردّ على رسالتك: " + text, "info", code_id)
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/failures/read")
def failures_read():
    if not logged_in():
        return redirect(f"/{ADMIN}")
    try:
        failure_id = int(request.form.get("id") or 0)
    except ValueError:
        return redirect(f"/{ADMIN}")
    with LOCK:
        data = load_failures()
        for item in data["items"]:
            if failure_id == 0 or item.get("id") == failure_id:
                item["read"] = True if failure_id == 0 else not item.get("read")
        save_failures(data)
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/failures/delete")
def failures_delete():
    if not logged_in():
        return redirect(f"/{ADMIN}")
    try:
        failure_id = int(request.form.get("id") or 0)
    except ValueError:
        return redirect(f"/{ADMIN}")
    with LOCK:
        data = load_failures()
        gone = [item for item in data["items"] if failure_id == 0 or item.get("id") == failure_id]
        data["items"] = [item for item in data["items"] if failure_id != 0 and item.get("id") != failure_id]
        save_failures(data)
    drop_failure_details(gone)
    return redirect(f"/{ADMIN}")


@app.get(f"/{ADMIN}/failures/<int:failure_id>")
def failure_details(failure_id: int):
    """A report's heavy parts (all its failed actions, the log, the clicks), loaded when it is opened."""
    if not logged_in():
        return jsonify(ok=False), 401
    data = read_private_json(failure_detail_path(failure_id)) or {}
    item = next((row for row in load_failures()["items"] if row.get("id") == failure_id), {})
    return jsonify(ok=True, title=item.get("title") or "", message=item.get("message") or "",
                   **{key: data.get(key) or ([] if key == "failed" else "") for key in FAILURE_HEAVY})


# ----------------------------------------------------------------------------- the app itself (its APK)
# «ملف التطبيق» in the «السكربت» tab: the owner uploads the app's APK, then publishes it to everyone or, as a trial,
# to the users they choose (as with the script). The apps get it through their own protected connection: their page
# shows «تنزيل التطبيق» when the one meant for them is newer than theirs, and saves it in the phone's downloads (no
# browser, so no warning about the server's own certificate). A fixed secret link gives everyone's (to share anywhere).
APP_DIR = DATA_DIR / "app"
APP_SLOTS = ("staged", "pilot", "live")        # uploaded, not offered yet · a trial for the chosen users · everyone's
APP_MAX = 300 * 1024 * 1024
APP_PACKAGE = "app.tg.groups.session"          # (the users' app; another package is kept, but no app offers it)
APK_MIME = "application/vnd.android.package-archive"


def apk_manifest(raw: bytes) -> dict:
    """package, versionName and versionCode from an APK's AndroidManifest.xml (Android's binary XML)."""
    def u16(at): return struct.unpack_from("<H", raw, at)[0]
    def u32(at): return struct.unpack_from("<I", raw, at)[0]
    if len(raw) < 8 or u16(0) != 0x0003:
        raise ValueError("not binary XML")
    strings: list[str] = []
    res_ids: list[int] = []
    at = u16(2)
    while at + 8 <= len(raw):
        kind, head, size = u16(at), u16(at + 2), u32(at + 4)
        if size < 8 or at + size > len(raw):
            raise ValueError("bad chunk")
        if kind == 0x0001:                                    # the strings
            count, flags, start = u32(at + 8), u32(at + 16), u32(at + 20)
            for i in range(count):
                p = at + start + u32(at + head + 4 * i)
                if flags & 0x100:                             # UTF-8: characters, then bytes
                    p += 2 if raw[p] & 0x80 else 1
                    n = raw[p]; p += 1
                    if n & 0x80:
                        n = ((n & 0x7F) << 8) | raw[p]; p += 1
                    strings.append(raw[p:p + n].decode("utf-8", "replace"))
                else:
                    n = u16(p); p += 2
                    if n & 0x8000:
                        n = ((n & 0x7FFF) << 16) | u16(p); p += 2
                    strings.append(raw[p:p + 2 * n].decode("utf-16-le", "replace"))
        elif kind == 0x0180:                                  # the attribute names' resource ids
            res_ids = [u32(at + 8 + 4 * i) for i in range((size - 8) // 4)]
        elif kind == 0x0102:                                  # the first element: <manifest>
            base = at + 16
            first, step, count = u16(base + 8), u16(base + 10), u16(base + 12)
            found = {}
            for i in range(count):
                a = base + first + i * step
                name_i, raw_i, dtype, data = u32(a + 4), u32(a + 8), raw[a + 15], u32(a + 16)
                rid = res_ids[name_i] if name_i < len(res_ids) else 0
                key = {0x0101021B: "versionCode", 0x0101021C: "versionName"}.get(rid) or \
                    (strings[name_i] if name_i < len(strings) else "")
                if key not in ("package", "versionCode", "versionName"):
                    continue
                if raw_i != 0xFFFFFFFF and raw_i < len(strings):
                    found[key] = strings[raw_i]
                elif dtype == 0x03 and data < len(strings):
                    found[key] = strings[data]
                elif dtype in (0x10, 0x11):
                    found[key] = data
            return found
        at += size
    raise ValueError("no <manifest>")


def apk_info(path: Path) -> dict:
    """What an uploaded APK says about itself, or raises ValueError with the reason for the owner."""
    import zipfile
    try:
        with zipfile.ZipFile(path) as archive:
            if archive.getinfo("AndroidManifest.xml").file_size > 4 * 1024 * 1024:
                raise ValueError("manifest too big")
            manifest = archive.read("AndroidManifest.xml")
            has_code = any(name.startswith("classes") and name.endswith(".dex") for name in archive.namelist())
    except Exception:                       # (not a zip, no manifest, a broken or odd one: all the same to the owner)
        raise ValueError("هذا ليس ملف تطبيق أندرويد (APK). اختر ملف ‎.apk‎ الذي بنيته.") from None
    try:
        info = apk_manifest(manifest)
        code = int(info["versionCode"])
    except (ValueError, KeyError, IndexError, TypeError, struct.error):
        raise ValueError("تعذّرت قراءة رقم إصدار التطبيق من الملف. تأكد أنه ملف APK سليم.") from None
    if not info.get("package") or not has_code:
        raise ValueError("ملف التطبيق ناقص. تأكد أنه ملف APK كامل.")
    return {"package": str(info["package"])[:120], "code": code,
            "version": str(info.get("versionName") or code).strip()[:40] or str(code)}


def app_path(slot: str) -> Path:
    return APP_DIR / f"{slot}.apk"


def app_meta(slot: str = "live") -> dict:
    """One of the kept apps (version, code, package, size, sha256, at; a trial's codes), or {} when there is none."""
    meta = read_private_json(APP_DIR / f"{slot}.json") or {}
    return meta if meta.get("sha256") and app_path(slot).is_file() else {}


def app_drop(slot: str) -> None:
    for path in (app_path(slot), APP_DIR / f"{slot}.json"):
        try:
            path.unlink()
        except OSError:
            pass


def app_move(source: str, target: str, **extra) -> dict:
    """(Under LOCK.) The app in one place goes to another (no copy of a big file), with its record."""
    meta = dict(app_meta(source), **extra)
    os.replace(app_path(source), app_path(target))
    write_private_json(APP_DIR / f"{target}.json", meta)
    try:
        (APP_DIR / f"{source}.json").unlink()
    except OSError:
        pass
    return meta


def app_for(code_id: str) -> tuple[dict, str]:
    """The app meant for this user: their trial if they are in one, else everyone's; ({}, "") when there is none."""
    pilot = app_meta("pilot")
    if pilot and code_id in (pilot.get("codes") or []):
        return pilot, "pilot"
    live = app_meta("live")
    return (live, "live") if live else ({}, "")


def app_panel(codes: list) -> dict:
    """The three places as the panel shows them."""
    names = {row.get("id"): row.get("label") or row.get("code") or "" for row in codes}
    out = {}
    for slot in APP_SLOTS:
        meta = app_meta(slot)
        if meta:
            meta = dict(meta, size_text=size_text(int(meta.get("size") or 0)),
                        when=seen_text({"last_seen": int(meta.get("published_at") or meta.get("at") or 0)}))
            if slot == "pilot":
                meta["names"] = [names[code] for code in meta.get("codes") or [] if code in names]
        out[slot] = meta
    return out


def _app_from_first_build() -> None:
    """The first build of this kept one file, offered to everyone (app.apk): it is everyone's."""
    old = APP_DIR / "app.apk"
    if old.is_file() and (APP_DIR / "app.json").is_file() and not app_path("live").is_file():
        try:
            os.replace(old, app_path("live"))
            os.replace(APP_DIR / "app.json", APP_DIR / "live.json")
        except OSError:
            pass


_app_from_first_build()


def app_file_name(meta: dict) -> str:
    version = re.sub(r"[^0-9A-Za-z._-]", "", str(meta.get("version") or ""))[:40]
    return f"BOT-GROB-{version}.apk" if version else "BOT-GROB.apk"


def app_download_link() -> str:
    """The fixed link (it always gives everyone's latest), at the address the apps use."""
    port = "" if LISTEN_PORT == 443 else f":{LISTEN_PORT}"
    return f"https://{public_host()}{port}/{APP_DL}/BOT-GROB.apk"


def size_text(size: int) -> str:
    return f"{size / 1048576:.1f} ميجابايت" if size >= 1048576 else f"{max(1, round(size / 1024))} كيلوبايت"


@app.post(f"/{ADMIN}/app/upload")
def app_upload():
    """«رفع التطبيق»: the APK, checked (an APK whose package and version can be read), kept ready to publish."""
    if not logged_in():
        return redirect(f"/{ADMIN}")
    upload = request.files.get("apk")
    if not upload or not upload.filename:
        flash("bad", "اختر ملف التطبيق (APK).")
        return redirect(f"/{ADMIN}")
    APP_DIR.mkdir(parents=True, exist_ok=True)
    temporary = APP_DIR / f"upload-{secrets.token_hex(6)}.part"
    digest, size = hashlib.sha256(), 0
    try:
        with open(temporary, "wb") as out:
            while True:
                chunk = upload.stream.read(1 << 20)
                if not chunk:
                    break
                size += len(chunk)
                if size > APP_MAX:
                    raise ValueError("ملف التطبيق أكبر من المسموح (٣٠٠ ميجابايت).")
                digest.update(chunk)
                out.write(chunk)
        info = apk_info(temporary)
        live = app_meta("live")
        if live and info["package"] == live.get("package") and info["code"] < int(live.get("code") or 0):
            raise ValueError(f"رقم البناء (versionCode) في هذا الملف {info['code']} أقل من النسخة المنشورة للجميع "
                             f"({live['code']})، فلن يُثبَّت فوقها. ابنِ التطبيق برقم أعلى.")
        with LOCK:
            temporary.replace(app_path("staged"))
            write_private_json(APP_DIR / "staged.json", {**info, "size": size, "sha256": digest.hexdigest(), "at": int(time.time())})
    except ValueError as exc:
        flash("bad", str(exc))
        return redirect(f"/{ADMIN}")
    except OSError:
        flash("bad", "تعذّر حفظ الملف على الخادم. تأكد من وجود مساحة كافية.")
        return redirect(f"/{ADMIN}")
    finally:
        try:
            temporary.unlink()
        except OSError:
            pass
    other = "" if info["package"] == APP_PACKAGE else (
        f" تنبيه: اسم حزمته {info['package']} لا يطابق تطبيق المستخدمين ({APP_PACKAGE})، فلن يعرضه التطبيق عليهم.")
    flash("ok", f"رُفع التطبيق: الإصدار {info['version']} (رقم {info['code']}) وجاهز للنشر. اختر لمن يصل ثم اضغط «نشر التطبيق».{other}")
    return redirect(f"/{ADMIN}")


def app_notice_to(meta: dict, codes: list | None) -> None:
    """A notice that this version is ready: to everyone with the link, or to each of a trial's users."""
    if codes is None:
        add_notice(f"نسخة جديدة من التطبيق ({meta['version']}) جاهزة. افتح التطبيق واضغط «تنزيل التطبيق» في أعلى الصفحة، "
                   f"أو نزّلها من الرابط: {app_download_link()}", "info", "all")
        return
    for code in codes:
        add_notice(f"نسخة تجريبية من التطبيق ({meta['version']}) جاهزة لك. افتح التطبيق واضغط «تنزيل التطبيق» في أعلى الصفحة.",
                   "info", code)


@app.post(f"/{ADMIN}/app/publish")
def app_publish():
    """The uploaded app goes to everyone, or as a trial to the chosen users; with a notice to them if asked."""
    if not logged_in():
        return redirect(f"/{ADMIN}")
    some = request.form.get("target") == "some"
    chosen = chosen_codes(request.form.getlist("codes")) if some else None
    if some and not chosen:
        flash("bad", "اختر مستخدمًا واحدًا على الأقل لتصله النسخة التجريبية.")
        return redirect(f"/{ADMIN}")
    with LOCK:
        if not app_meta("staged"):
            flash("bad", "لا يوجد ملف تطبيق مرفوع لنشره. ارفع الملف أولًا.")
            return redirect(f"/{ADMIN}")
        now = int(time.time())
        if some:
            app_drop("pilot")
            meta = app_move("staged", "pilot", published_at=now, codes=chosen)
        else:
            meta = app_move("staged", "live", published_at=now)
            app_drop("pilot")                       # (everyone has it now: a trial before it is over)
    told = request.form.get("notify") == "1"
    if told:
        app_notice_to(meta, chosen)
    if some:
        flash("ok", f"نُشر الإصدار {meta['version']} من التطبيق تجريبيًا لـ {len(chosen)} مستخدم: يظهر لهم زر «تنزيل التطبيق»"
                    f"{' ووصلهم تنبيه' if told else ''}، والباقون يبقون على نسختهم.")
    else:
        flash("ok", f"نُشر الإصدار {meta['version']} من التطبيق للجميع: يظهر زر «تنزيل التطبيق» لكل من نسخته أقدم"
                    f"{'، ووصلهم تنبيه بالرابط' if told else ''}.")
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/app/pilot/promote")
def app_pilot_promote():
    if not logged_in():
        return redirect(f"/{ADMIN}")
    with LOCK:
        if not app_meta("pilot"):
            flash("bad", "لا توجد نسخة تجريبية.")
            return redirect(f"/{ADMIN}")
        meta = app_move("pilot", "live", published_at=int(time.time()))
        meta.pop("codes", None)
        write_private_json(APP_DIR / "live.json", meta)
    flash("ok", f"صار الإصدار {meta['version']} من التطبيق للجميع. اضغط «إرسال تنبيه للمستخدمين» ليصلهم الرابط.")
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/app/pilot/cancel")
def app_pilot_cancel():
    if not logged_in():
        return redirect(f"/{ADMIN}")
    with LOCK:
        app_drop("pilot")
    flash("ok", "أُلغيت النسخة التجريبية من التطبيق. من نزّلها يبقى عليها.")
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/app/pilot/users")
def app_pilot_users():
    if not logged_in():
        return redirect(f"/{ADMIN}")
    chosen = chosen_codes(request.form.getlist("codes"))
    if not chosen:
        flash("bad", "اختر مستخدمًا واحدًا على الأقل، أو اضغط «إلغاء التجريبي».")
        return redirect(f"/{ADMIN}")
    with LOCK:
        meta = app_meta("pilot")
        if not meta:
            flash("bad", "لا توجد نسخة تجريبية.")
            return redirect(f"/{ADMIN}")
        meta["codes"] = chosen
        write_private_json(APP_DIR / "pilot.json", meta)
    flash("ok", f"تصل النسخة التجريبية الآن إلى {len(chosen)} مستخدم.")
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/app/notify")
def app_notify():
    """«إرسال تنبيه»: a notice to all users that everyone's version is ready, with its link."""
    if not logged_in():
        return redirect(f"/{ADMIN}")
    meta = app_meta("live")
    if not meta:
        flash("bad", "انشر التطبيق للجميع أولًا.")
        return redirect(f"/{ADMIN}")
    app_notice_to(meta, None)
    flash("ok", f"أُرسل لكل المستخدمين تنبيه بالإصدار {meta['version']} ورابطه.")
    return redirect(f"/{ADMIN}")


@app.get(f"/{APP_DL}/<name>")
def app_public_download(name):
    """The fixed link to everyone's latest app, for a browser (any name after it gives the same file)."""
    meta = app_meta("live")
    if not meta:
        return "لا يوجد تطبيق منشور بعد.", 404
    return send_file(app_path("live"), mimetype=APK_MIME, as_attachment=True, download_name=app_file_name(meta),
                     conditional=True, max_age=0)


@app.post(f"/{ADMIN}/script/upload")
def script_upload():
    """Stage an uploaded script (and content), checked, ready for «نشر التحديث»."""
    if not logged_in():
        return redirect(f"/{ADMIN}")
    gg = request.files.get("gg")
    content = request.files.get("content")
    if not gg or not gg.filename:
        flash("bad", "اختر ملف السكربت (gg.py / script_original.py).")
        return redirect(f"/{ADMIN}")
    gg_raw = gg.read(SCRIPT_GG_MAX + 1)
    if len(gg_raw) > SCRIPT_GG_MAX:
        flash("bad", "ملف السكربت أكبر من المسموح (٨ ميجابايت).")
        return redirect(f"/{ADMIN}")
    problem, _ = check_script(gg_raw, "السكربت", want_version=True)
    if problem:
        flash("bad", problem)
        return redirect(f"/{ADMIN}")
    live_version = highest_published_version()
    version = (request.form.get("version") or "").strip().translate(str.maketrans("٠١٢٣٤٥٦٧٨٩٫", "0123456789."))
    if not version:
        version = next_version(live_version)
    if not VERSION_FORM.match(version):
        flash("bad", "رقم الإصدار غير صحيح. اكتبه أرقامًا ونقاطًا فقط، مثل 1.1")
        return redirect(f"/{ADMIN}")
    if live_version and version_tuple(version) <= version_tuple(live_version):
        flash("bad", f"رقم الإصدار يجب أن يكون أعلى من آخر إصدار منشور ({live_version})، وإلا لن يظهر التحديث للمستخدمين. "
                     f"مثلًا: {next_version(live_version)}")
        return redirect(f"/{ADMIN}")
    gg_raw = stamp_version(gg_raw, version)
    content_raw = b""
    if content and content.filename:
        content_raw = content.read(SCRIPT_CONTENT_MAX + 1)
        if len(content_raw) > SCRIPT_CONTENT_MAX:
            flash("bad", "ملف content.py أكبر من المسموح (٤ ميجابايت).")
            return redirect(f"/{ADMIN}")
        problem, _ = check_script(content_raw, "content.py", want_version=False)
        if problem:
            flash("bad", problem)
            return redirect(f"/{ADMIN}")
    with LOCK:
        SCRIPT_DIR.mkdir(parents=True, exist_ok=True)
        (SCRIPT_DIR / "staged-gg.py").write_bytes(gg_raw)
        meta = {"version": version, "sha256": hashlib.sha256(gg_raw).hexdigest(),
                "size": len(gg_raw), "at": int(time.time()), "has_content": bool(content_raw)}
        if content_raw:
            (SCRIPT_DIR / "staged-content.py").write_bytes(content_raw)
            meta["content_sha256"] = hashlib.sha256(content_raw).hexdigest()
        else:
            try:
                (SCRIPT_DIR / "staged-content.py").unlink()
            except OSError:
                pass
        write_private_json(SCRIPT_DIR / STAGED_META, meta)
    flash("ok", f"رُفع السكربت (الإصدار {version}) وجاهز للنشر. اضغط «نشر التحديث» ليصل إلى المستخدمين.")
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/script/publish")
def script_publish():
    """Make the staged script the one the apps download: everyone's, or a trial for the chosen users."""
    if not logged_in():
        return redirect(f"/{ADMIN}")
    some = request.form.get("target") == "some"
    auto = request.form.get("auto") == "1"            # («تثبيت تلقائي»: no «تحديث» button, it installs itself)
    with LOCK:
        staged = load_script_meta(STAGED_META)
        if not staged.get("version") or not (SCRIPT_DIR / "staged-gg.py").is_file():
            flash("bad", "لا يوجد سكربت مرفوع لنشره. ارفع الملف أولًا.")
            return redirect(f"/{ADMIN}")
        if some:
            chosen = chosen_codes(request.form.getlist("codes"))
            if not chosen:
                flash("bad", "اختر مستخدمًا واحدًا على الأقل ليصله الإصدار التجريبي.")
                return redirect(f"/{ADMIN}")
            shutil.copy2(SCRIPT_DIR / "staged-gg.py", SCRIPT_DIR / "pilot-gg.py")
            if staged.get("has_content") and (SCRIPT_DIR / "staged-content.py").is_file():
                shutil.copy2(SCRIPT_DIR / "staged-content.py", SCRIPT_DIR / "pilot-content.py")
            else:
                remove_script_files("pilot-content.py")
            write_private_json(SCRIPT_DIR / PILOT_META, dict(staged, published_at=int(time.time()), codes=chosen, auto=auto))
            flash("ok", f"نُشر الإصدار {staged['version']} تجريبيًا لـ {len(chosen)} مستخدم. "
                        + ("يُثبَّت عندهم تلقائيًا خلال دقائق، بعد انتهاء مهامهم الجارية" if auto else
                           "يظهر لهم زر «تحديث» خلال دقيقة تقريبًا") + "، والباقون يبقون على الإصدار الحالي.")
            return redirect(f"/{ADMIN}")
        shutil.copy2(SCRIPT_DIR / "staged-gg.py", SCRIPT_DIR / "gg.py")
        if staged.get("has_content") and (SCRIPT_DIR / "staged-content.py").is_file():
            shutil.copy2(SCRIPT_DIR / "staged-content.py", SCRIPT_DIR / "content.py")
        else:
            try:
                (SCRIPT_DIR / "content.py").unlink()
            except OSError:
                pass
        staged["published_at"] = int(time.time())
        staged["auto"] = auto
        write_private_json(SCRIPT_DIR / SCRIPT_META, staged)
        remove_script_files("pilot-gg.py", "pilot-content.py", PILOT_META)      # (everyone has a newer one now)
    flash("ok", f"نُشر الإصدار {staged['version']}. " + ("يُثبَّت عند المستخدمين تلقائيًا خلال دقائق، بعد انتهاء مهامهم الجارية."
                                                          if auto else "يظهر للمستخدمين زر «تحديث» خلال دقيقة تقريبًا، أو عند فتح الصفحة."))
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/script/pilot/promote")
def script_pilot_promote():
    """The trial version goes to everyone."""
    if not logged_in():
        return redirect(f"/{ADMIN}")
    with LOCK:
        pilot = pilot_meta()
        if not pilot:
            flash("bad", "لا يوجد إصدار تجريبي.")
            return redirect(f"/{ADMIN}")
        shutil.copy2(SCRIPT_DIR / "pilot-gg.py", SCRIPT_DIR / "gg.py")
        if pilot.get("has_content") and (SCRIPT_DIR / "pilot-content.py").is_file():
            shutil.copy2(SCRIPT_DIR / "pilot-content.py", SCRIPT_DIR / "content.py")
        else:
            remove_script_files("content.py")
        live = {key: value for key, value in pilot.items() if key != "codes"}
        live["published_at"] = int(time.time())
        write_private_json(SCRIPT_DIR / SCRIPT_META, live)
        remove_script_files("pilot-gg.py", "pilot-content.py", PILOT_META)
    flash("ok", f"نُشر الإصدار {pilot['version']} لكل المستخدمين. " + ("يُثبَّت عندهم تلقائيًا خلال دقائق، بعد انتهاء مهامهم الجارية."
                                                                        if pilot.get("auto") else "يظهر لهم زر «تحديث» خلال دقيقة تقريبًا."))
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/script/auto")
def script_auto():
    """«تثبيت تلقائي» on or off for the version published to everyone, or for the trial one."""
    if not logged_in():
        return redirect(f"/{ADMIN}")
    which = "pilot" if request.form.get("which") == "pilot" else "live"
    on = request.form.get("auto") == "1"
    with LOCK:
        meta = pilot_meta() if which == "pilot" else load_script_meta(SCRIPT_META)
        if not meta.get("version"):
            flash("bad", "لا يوجد إصدار منشور بعد.")
            return redirect(f"/{ADMIN}")
        meta["auto"] = on
        write_private_json(SCRIPT_DIR / (PILOT_META if which == "pilot" else SCRIPT_META), meta)
    who = "من اخترتهم في التجربة" if which == "pilot" else "كل مستخدم نسخته أقدم"
    flash("ok", f"يُثبَّت الإصدار {meta['version']} الآن تلقائيًا عند {who}، خلال دقائق وبعد انتهاء مهامهم الجارية، دون زر «تحديث»."
          if on else f"أُوقف التثبيت التلقائي للإصدار {meta['version']}: يظهر زر «تحديث» بدلًا منه.")
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/script/pilot/cancel")
def script_pilot_cancel():
    """No one is offered the trial version any more (those who installed it keep it)."""
    if not logged_in():
        return redirect(f"/{ADMIN}")
    with LOCK:
        remove_script_files("pilot-gg.py", "pilot-content.py", PILOT_META)
    flash("ok", "أُلغي الإصدار التجريبي. من حدّث إليه يبقى على نسخته حتى يُنشر إصدار أعلى للجميع، والباقون على الإصدار المنشور للجميع.")
    return redirect(f"/{ADMIN}")


@app.post(f"/{ADMIN}/script/pilot/users")
def script_pilot_users():
    """Change who gets the trial version."""
    if not logged_in():
        return redirect(f"/{ADMIN}")
    with LOCK:
        pilot = pilot_meta()
        if not pilot:
            flash("bad", "لا يوجد إصدار تجريبي.")
            return redirect(f"/{ADMIN}")
        chosen = chosen_codes(request.form.getlist("codes"))
        if not chosen:
            flash("bad", "اختر مستخدمًا واحدًا على الأقل، أو ألغِ الإصدار التجريبي.")
            return redirect(f"/{ADMIN}")
        pilot["codes"] = chosen
        write_private_json(SCRIPT_DIR / PILOT_META, pilot)
    flash("ok", f"صار الإصدار التجريبي {pilot['version']} يصل لـ {len(chosen)} مستخدم.")
    return redirect(f"/{ADMIN}")


# ----------------------------------------------------------------------------- the app API (link protocol)
def api_ok(**data):
    return jsonify(ok=True, **data)


def api_err(message: str, status: int = 200):
    return jsonify(ok=False, error=message), status


@app.post(f"/{API}/activate")
def api_activate():
    body = request.get_json(silent=True) or {}
    device = re.sub(r"[^A-Za-z0-9]", "", str(body.get("device") or ""))[:64]
    if not device:
        return api_err("لم يصل معرّف الجهاز. حدّث التطبيق.")
    row = find_code(body.get("code"))
    if not row:
        return api_err("الرمز غير معروف. تأكد منه أو اطلب رمزًا من صاحب البرنامج.")
    if not row.get("active"):
        return api_err("هذا الرمز موقوف. راجع صاحب البرنامج.")
    with LOCK:
        codes = load_codes()
        target = next((item for item in codes if item.get("id") == row["id"]), None)
        if target is None:
            return api_err("الرمز غير معروف.")
        if one_device() and target.get("bound_device") and target["bound_device"] != device:
            return api_err("هذا الرمز مُستخدم على جهاز آخر. اطلب من صاحب البرنامج تحريره أو رمزًا جديدًا.")
        add_device(target, device)
        target["last_seen"] = int(time.time())
        save_codes(codes)
    engine, _, _, _ = active_engine()
    return api_ok(token=make_token(row["id"], device), engine=engine or "none", move_key=SECRETS.get("move_public", ""))


def signed_in(row: dict, device: str):
    """The answer for a phone that may come in (as for a code): its token."""
    engine, _, _, _ = active_engine()
    return api_ok(token=make_token(row["id"], device), engine=engine or "none", move_key=SECRETS.get("move_public", ""),
                  pay=pay_of(row), balance=round(balance_of(row), 4))


def _device_of(body: dict) -> str:
    return re.sub(r"[^A-Za-z0-9]", "", str(body.get("device") or ""))[:64]


@app.post(f"/{API}/register")
def api_register():
    """A new account made in the app: a user like any other, bound to this phone, paying in advance («مسبق»). One account
    per phone: a phone that made one (still there) is told to sign in with it."""
    body = request.get_json(silent=True) or {}
    device = _device_of(body)
    phone = phone_of(body)
    name = str(body.get("user") or "").strip()
    password = str(body.get("password") or "")
    if not device:
        return api_err("لم يصل معرّف الجهاز. حدّث التطبيق.")
    if not ACCOUNT_NAME.match(name):
        return api_err("اسم المستخدم من 3 إلى 24 حرفًا أو رقمًا، بلا مسافات (يُسمح بـ _ و . و -).")
    if not 6 <= len(password) <= 128:
        return api_err("كلمة السر 6 أحرف على الأقل.")
    with LOCK:
        codes = load_codes()
        taken = account_row(codes, name) is not None
        made = account_made_on(codes, phone)
    if made:
        return api_err(f"أُنشئ على هذا الجوال حساب من قبل باسم «{(made.get('account') or {}).get('user') or made.get('label')}». "
                       "سجّل الدخول به. لكل جوال حساب واحد.")
    if taken:
        return api_err("اسم المستخدم مأخوذ. اختر اسمًا آخر.")
    if not signup_allowed():
        return api_err("حسابات كثيرة من هذه الشبكة. حاول بعد ساعة.")
    stored = account_pw_hash(password)
    with LOCK:
        codes = load_codes()
        if account_row(codes, name) is not None:
            return api_err("اسم المستخدم مأخوذ. اختر اسمًا آخر.")
        if account_made_on(codes, phone):
            return api_err("أُنشئ على هذا الجوال حساب من قبل. سجّل الدخول به. لكل جوال حساب واحد.")
        now = int(time.time())
        gift = take_welcome(codes, device, phone)
        waits = not phone and load_welcome() > 0 and not any(device in devices_of(row) for row in codes)
        row = {"id": secrets.token_hex(8), "code": make_code(), "label": name, "active": True, "created": now,
               "last_seen": now, "bound_device": device, "pay": PAY_PREPAID, "balance": gift,
               "ledger": [{"at": now, "amount": gift, "note": WELCOME_NOTE, "after": gift}] if gift else [],
               "account": {"user": name, "pw": stored, "at": now}, **({"hw": phone} if phone else {}),
               **({"welcome_pending": now} if waits else {})}
        codes.insert(0, row)
        save_codes(codes)
    return signed_in(row, device)


@app.post(f"/{API}/login")
def api_login():
    """Sign in with an account's name and password (on the phone it is bound to, as a code is)."""
    body = request.get_json(silent=True) or {}
    device = _device_of(body)
    name = str(body.get("user") or "").strip()
    password = str(body.get("password") or "")
    if not device:
        return api_err("لم يصل معرّف الجهاز. حدّث التطبيق.")
    key = account_key(name)
    if not key or not password:
        return api_err("أدخل اسم المستخدم وكلمة السر.")
    if signin_blocked(key):
        return api_err("محاولات دخول كثيرة. حاول بعد 15 دقيقة.")
    with LOCK:
        row = account_row(load_codes(), name)
    if not account_pw_ok(password, (row.get("account") or {}).get("pw") if row else _NO_ONE) or row is None:
        signin_failed(key)
        return api_err("اسم المستخدم أو كلمة السر غير صحيحة.")
    if not row.get("active"):
        return api_err("هذا الحساب موقوف. راجع صاحب البرنامج.")
    with LOCK:
        codes = load_codes()
        target = next((item for item in codes if item.get("id") == row["id"]), None)
        if target is None:
            return api_err("الحساب غير موجود.")
        if one_device() and target.get("bound_device") and target["bound_device"] != device:
            return api_err("هذا الحساب مُستخدم على جهاز آخر. اطلب من صاحب البرنامج تحرير الجهاز.")
        add_device(target, device)
        target["last_seen"] = int(time.time())
        save_codes(codes)
    return signed_in(target, device)


WELCOME_CLAIM_DAYS = 3


@app.post(f"/{API}/welcome-claim")
def api_welcome_claim():
    """An account made on the first-run page of an older app (it could not say which phone it was on): its script,
    which can, names the phone now, once. It gets the trial balance only as a new account would: the first account
    made on that phone, on a phone that never had it, within WELCOME_CLAIM_DAYS of being made."""
    body = request.get_json(silent=True) or {}
    row = code_from_token(body.get("token"))
    if not row:
        return api_err("انتهت صلاحية الدخول أو أوقِف الرمز أو نُقل لجهاز آخر. أعد إدخال الرمز.", 200)
    phone = phone_of(body)
    gift = 0.0
    with LOCK:
        codes = load_codes()
        target = next((item for item in codes if item.get("id") == row["id"]), None)
        pending = int((target or {}).get("welcome_pending") or 0)
        if target is None or not pending or not phone:
            return api_ok(gift=0)
        target.pop("welcome_pending", None)
        others = [item for item in codes if item is not target]
        if time.time() - pending <= WELCOME_CLAIM_DAYS * 86400 and not account_made_on(others, phone):
            target["hw"] = phone                     # (this phone's one account)
            gift = take_welcome(others, target.get("bound_device") or "", phone)
            if gift:
                target["balance"] = round(balance_of(target) + gift, 4)
                ledger = target.get("ledger") if isinstance(target.get("ledger"), list) else []
                ledger.insert(0, {"at": int(time.time()), "amount": gift, "note": WELCOME_NOTE, "after": round(target["balance"], 2)})
                target["ledger"] = ledger[:LEDGER_KEEP]
        save_codes(codes)
        balance = round(balance_of(target), 4)
    return api_ok(gift=gift, balance=balance)


@app.post(f"/{API}/check")
def api_check():
    body = request.get_json(silent=True) or {}
    return api_ok(active=bool(code_from_token(body.get("token"))), move_key=SECRETS.get("move_public", ""))


@app.post(f"/{API}/usage")
def api_usage():
    """The app's page shows these at its top: the comments written for this code and their cost, in all and by
    X account (kept here, so they stay when the app is installed again)."""
    body = request.get_json(silent=True) or {}
    row = code_from_token(body.get("token"))
    if not row:
        return api_err("انتهت صلاحية الدخول أو أوقِف الرمز أو نُقل لجهاز آخر. أعد إدخال الرمز.", 200)
    return api_ok(**usage_by_account(row["id"]), pay=pay_of(row), balance=round(balance_of(row), 4), payment=public_payment())


@app.post(f"/{API}/topup")
def api_topup():
    """«شحن رصيد»: a user's Binance Pay transfer (its amount and Order ID). With the owner's key, checked in the owner's
    Binance Pay history and, when it is there, the balance topped up at once; without one: «manual» (the app sends it
    to «رسائل العملاء»)."""
    body = request.get_json(silent=True) or {}
    row = code_from_token(body.get("token"))
    if not row:
        return api_err("انتهت صلاحية الدخول أو أوقِف الرمز أو نُقل لجهاز آخر. أعد إدخال الرمز.", 200)
    amount = topup_amount(body.get("amount"))
    typed = str(body.get("order_id") or "").strip()[:80]
    if not 0 < amount <= TOPUP_MAX:
        return api_err("اكتب المبلغ الذي حوّلته بالدولار.")
    if len(_tx_key(typed)) < 6:
        return api_err("اكتب رقم العملية (Order ID) من تفاصيل التحويل في Binance.")
    settings = load_binance()
    if not (settings["key"] and settings["secret"]):
        return api_ok(manual=True)
    now = time.time()
    with LOCK:
        tries = [at for at in _topup_tries.get(row["id"], []) if now - at < 3600]
        if len(tries) >= TOPUP_TRIES_PER_HOUR:
            return api_err("محاولات كثيرة خلال ساعة. انتظر قليلًا ثم أعد المحاولة.")
        _topup_tries[row["id"]] = tries + [now]
        if any(tx_matches(used, typed) for used in load_topups()["used"]):
            return api_err("رقم العملية هذا استُخدم من قبل لشحن رصيد.")
    try:
        rows = binance_history(settings["key"], settings["secret"])
    except BinanceError as exc:
        print(f"شحن رصيد: تعذّر التحقق من Binance: {exc}", flush=True)
        return api_err("تعذّر التحقق من Binance الآن. أعد المحاولة بعد قليل.")
    found = next((tx for tx in rows if tx_matches(tx.get("transactionId"), typed)), None)
    try:
        came = float((found or {}).get("amount") or 0)          # (positive: received; negative: the owner sent it)
    except (TypeError, ValueError):
        came = 0.0
    coin = str((found or {}).get("currency") or "").upper()
    if not found or came <= 0:
        return api_err("لم يُعثر على هذا التحويل في حساب صاحب البرنامج بعد. تأكد من رقم العملية، أو انتظر دقيقة ثم أعد المحاولة.")
    if coin not in TOPUP_COINS:
        return api_err(f"التحويل بعملة {coin}، والمقبول: {'، '.join(TOPUP_COINS)}.")
    received = round(came, 2)
    if abs(received - amount) > 0.01:
        return api_err("المبلغ الذي كتبته لا يطابق مبلغ هذا التحويل.")
    tx_id = str(found.get("transactionId") or typed)
    with LOCK:
        topups = load_topups()
        if any(tx_matches(used, tx_id) for used in topups["used"]):
            return api_err("رقم العملية هذا استُخدم من قبل لشحن رصيد.")
        codes = load_codes()
        target = next((item for item in codes if item.get("id") == row["id"]), None)
        if target is None:
            return api_err("المستخدم غير موجود.")
        target["balance"] = round(balance_of(target) + received, 4)
        ledger = target.get("ledger") if isinstance(target.get("ledger"), list) else []
        ledger.insert(0, {"at": int(now), "amount": received, "note": f"Binance Pay · {tx_id[-8:]}",
                          "after": round(target["balance"], 2)})
        target["ledger"] = ledger[:LEDGER_KEEP]
        save_codes(codes)
        topups["used"][tx_id] = {"code_id": row["id"], "amount": received, "coin": coin, "at": int(now)}
        write_private_json(TOPUPS_PATH, {"version": 1, **topups})
        support = load_support()
        support["seq"] += 1
        support["items"].insert(0, {"id": support["seq"], "code_id": row["id"], "label": row.get("label") or "",
                                    "text": f"شُحن رصيده تلقائيًا عبر Binance Pay: {money(received)} ({coin}).\nرقم العملية: {tx_id}",
                                    "files": [], "meta": {}, "at": int(now), "read": False, "replies": [], "kind": "topup"})
        del support["items"][SUPPORT_MAX:]
        save_support(support)
        balance, pay = target["balance"], pay_of(target)
    print(f"شحن رصيد عبر Binance Pay: {money(received)} لـ {row.get('label') or row['id']}", flush=True)
    return api_ok(credited=received, balance=round(balance, 4), pay=pay)


@app.post(f"/{API}/task-start")
def api_task_start():
    """A task is about to start (a new one, a retry, or one whose turn came). A «مسبق» user's task with paid services
    needs at least the cheapest of them in the balance; then it gets its pass and goes on to its end."""
    body = request.get_json(silent=True) or {}
    row = code_from_token(body.get("token"))
    if not row:
        return api_err("انتهت صلاحية الدخول أو أوقِف الرمز أو نُقل لجهاز آخر. أعد إدخال الرمز.", 200)
    prices = load_prices()
    services = [name for name in body.get("services") if name in SERVICES] if isinstance(body.get("services"), list) else []
    paid = [prices[name] for name in services if prices[name] > 0]
    balance = balance_of(row)
    if pay_of(row) == PAY_PREPAID and paid and balance + 1e-9 < min(paid):
        return api_err(f"رصيدك {money(balance)} لا يكفي لبدء مهمة جديدة. اطلب من صاحب البرنامج شحن رصيدك.")
    return api_ok(**{"pass": make_task_pass(row["id"]), "pay": pay_of(row), "balance": round(balance, 4), "prices": prices,
                     "pace": load_pace()})


@app.post(f"/{API}/charge")
def api_charge():
    """The app's successful reposts, likes and bookmarks: counted at today's prices, and a «مسبق» user's balance pays
    for them. Answers how this user pays now, the balance and the prices."""
    body = request.get_json(silent=True) or {}
    row = code_from_token(body.get("token"))
    if not row:
        return api_err("انتهت صلاحية الدخول أو أوقِف الرمز أو نُقل لجهاز آخر. أعد إدخال الرمز.", 200)
    items = body.get("items") if isinstance(body.get("items"), list) else []
    items = [item for item in items[:500] if isinstance(item, dict)]
    prices = load_prices()
    cost = record_actions(row["id"], items, prices) if items else 0.0
    with LOCK:
        codes = load_codes()
        target = next((item for item in codes if item.get("id") == row["id"]), None) or row
        if cost > 0 and pay_of(target) == PAY_PREPAID:
            target["balance"] = round(balance_of(target) - cost, 4)
            save_codes(codes)
    return api_ok(pay=pay_of(target), balance=round(balance_of(target), 4), prices=prices, charged=cost)


@app.post(f"/{API}/stats")
def api_stats():
    """The app's numbers (as at the top of its page) for each of its X accounts, for the owner to see."""
    body = request.get_json(silent=True) or {}
    row = code_from_token(body.get("token"))
    if not row:
        return api_err("انتهت صلاحية الدخول أو أوقِف الرمز أو نُقل لجهاز آخر. أعد إدخال الرمز.", 200)
    accounts = body.get("accounts")
    if not isinstance(accounts, list):
        return api_err("لم تصل الأرقام.")
    save_acts_of(row["id"], accounts, read_token(body.get("token"))[1], row.get("bound_device") or "")
    return api_ok()


@app.post(f"/{API}/support-file")
def api_support_file():
    """One picture or short video for a message about to be sent; answers its file number for that message."""
    body = request.get_json(silent=True) or {}
    row = code_from_token(body.get("token"))
    if not row:
        return api_err("انتهت صلاحية الدخول أو أوقِف الرمز أو نُقل لجهاز آخر. أعد إدخال الرمز.", 200)
    raw = body.get("data")
    if not isinstance(raw, str) or not raw:
        return api_err("لم يصل الملف.")
    if len(raw) > SUPPORT_VIDEO_MAX * 4 // 3 + 8:
        return api_err("الملف أكبر من المسموح (الفيديو حتى ٢٥ ميجابايت، والصورة حتى ٨).")
    try:
        data = base64.b64decode(raw, validate=True)
    except ValueError:
        return api_err("وصل الملف تالفًا. أعد المحاولة.")
    mime, ext = sniff_media(data)
    if not mime:
        return api_err("نوع الملف غير مدعوم. أرفق صورة (JPG أو PNG) أو فيديو (MP4).")
    if len(data) > (SUPPORT_IMAGE_MAX if mime.startswith("image/") else SUPPORT_VIDEO_MAX):
        return api_err("الملف أكبر من المسموح (الفيديو حتى ٢٥ ميجابايت، والصورة حتى ٨).")
    prune_support_pending()
    file_id = secrets.token_hex(12)
    folder = _support_pending_dir()
    (folder / f"{file_id}.{ext}").write_bytes(data)
    name = re.sub(r"[\x00-\x1f/\\]", "", str(body.get("name") or ""))[:80]
    write_private_json(folder / f"{file_id}.json", {"code_id": row["id"], "type": mime, "ext": ext, "name": name,
                                                    "size": len(data)})
    return api_ok(file=file_id)


@app.post(f"/{API}/support")
def api_support():
    """A message from a user's app (its «مساعدة» button), naming the files it sent before."""
    body = request.get_json(silent=True) or {}
    row = code_from_token(body.get("token"))
    if not row:
        return api_err("انتهت صلاحية الدخول أو أوقِف الرمز أو نُقل لجهاز آخر. أعد إدخال الرمز.", 200)
    text = str(body.get("text") or "").strip()[:SUPPORT_TEXT_MAX]
    ids = body.get("files") if isinstance(body.get("files"), list) else []
    ids = [str(item) for item in ids if re.fullmatch(r"[0-9a-f]{24}", str(item))][:SUPPORT_FILES_MAX]
    if not text and not ids:
        return api_err("اكتب وصف المشكلة.")
    meta = body.get("meta") if isinstance(body.get("meta"), dict) else {}
    meta = {key: str(meta.get(key) or "")[:limit] for key, limit in
            (("version", 40), ("device", 300), ("accounts", 300), ("log", 12000))}
    now = int(time.time())
    folder = _support_pending_dir()
    with LOCK:
        data = load_support()
        recent = sum(1 for item in data["items"] if item.get("code_id") == row["id"] and now - int(item.get("at") or 0) < 3600)
        if recent >= SUPPORT_PER_HOUR:
            return api_err("أرسلت رسائل كثيرة خلال ساعة. انتظر قليلًا ثم أعد الإرسال.")
        files = []
        for file_id in ids:
            info = read_private_json(folder / f"{file_id}.json") or {}
            if info.get("code_id") != row["id"]:
                continue
            source = folder / f"{file_id}.{info.get('ext')}"
            if source.is_file():
                files.append((source, info))
        data["seq"] += 1
        message_id = data["seq"]
        target = SUPPORT_DIR / str(message_id)
        target.mkdir(parents=True, exist_ok=True)
        stored = []
        for index, (source, info) in enumerate(files):
            name = f"{index + 1}.{info.get('ext')}"
            shutil.move(str(source), str(target / name))
            try:
                (folder / f"{source.stem}.json").unlink()
            except OSError:
                pass
            stored.append({"stored": name, "type": info.get("type"), "name": info.get("name") or "",
                           "size": int(info.get("size") or 0)})
        data["items"].insert(0, light_support({"id": message_id, "code_id": row["id"], "label": row.get("label") or "",
                                               "text": text, "files": stored, "meta": meta, "at": now, "read": False,
                                               "replies": [], "kind": "topup" if body.get("kind") == "topup" else "help"}))
        dropped = data["items"][SUPPORT_MAX:]
        del data["items"][SUPPORT_MAX:]
        save_support(data)
    for item in dropped:
        shutil.rmtree(SUPPORT_DIR / str(item.get("id")), ignore_errors=True)
    return api_ok(id=message_id)


@app.post(f"/{API}/failure")
def api_failure():
    """A failure in this app (sent by itself, without asking the user): what failed, and that account's log."""
    body = request.get_json(silent=True) or {}
    row = code_from_token(body.get("token"))
    if not row:
        return api_err("انتهت صلاحية الدخول أو أوقِف الرمز أو نُقل لجهاز آخر. أعد إدخال الرمز.", 200)
    report = body.get("report") if isinstance(body.get("report"), dict) else {}
    text = lambda key, limit: str(report.get(key) or "")[:limit]
    failed = [str(line)[:300] for line in (report.get("failed") or []) if isinstance(line, (str, int, float))][:50]
    summary = report.get("summary") if isinstance(report.get("summary"), dict) else {}
    summary = {key: int(summary[key]) for key in ("requested", "done", "failed")
               if key in summary and str(summary[key]).isdigit()}
    now = int(time.time())
    with LOCK:
        data = load_failures()
        recent = sum(1 for item in data["items"] if item.get("code_id") == row["id"] and now - int(item.get("at") or 0) < 3600)
        if recent >= FAILURES_PER_HOUR:
            return api_ok(kept=False)          # (too many this hour: dropped, the app does not send it again)
        data["seq"] += 1
        data["items"].insert(0, light_failure({
            "id": data["seq"], "code_id": row["id"], "label": row.get("label") or "", "at": now, "read": False,
            "kind": text("kind", 20), "title": text("title", 200), "message": text("message", 1000), "task": text("task", 120),
            "account": text("account", 40), "summary": summary, "failed": failed, "log": text("log", 20000),
            "clicks": text("clicks", 8000), "trace": text("trace", 6000), "version": text("version", 40),
            "device": text("device", 300)}))
        dropped = data["items"][FAILURES_MAX:]
        del data["items"][FAILURES_MAX:]
        save_failures(data)
    drop_failure_details(dropped)
    return api_ok(kept=True)


@app.post(f"/{API}/script-latest")
def api_script_latest():
    """The app asks for the published script's version, to know whether to offer «تحديث»."""
    body = request.get_json(silent=True) or {}
    row = code_from_token(body.get("token"))
    if not row:
        return api_err("انتهت صلاحية الدخول أو أوقِف الرمز أو نُقل لجهاز آخر. أعد إدخال الرمز.", 200)
    meta, gg_name, content_name = script_for(row["id"])
    if not meta.get("version") or not (SCRIPT_DIR / gg_name).is_file():
        return api_ok(version="")
    return api_ok(version=str(meta.get("version") or ""), sha256=script_file_sha(gg_name),
                  has_content=bool(meta.get("has_content")), content_sha256=script_file_sha(content_name),
                  auto=bool(meta.get("auto")))


@app.post(f"/{API}/script-download")
def api_script_download():
    """The app downloads the published script (gg.py, and content.py when there is one), base64."""
    body = request.get_json(silent=True) or {}
    row = code_from_token(body.get("token"))
    if not row:
        return api_err("انتهت صلاحية الدخول أو أوقِف الرمز أو نُقل لجهاز آخر. أعد إدخال الرمز.", 200)
    meta, gg_name, content_name = script_for(row["id"])
    gg_path = SCRIPT_DIR / gg_name
    if not meta.get("version") or not gg_path.is_file():
        return api_err("لا يوجد سكربت منشور.")
    answer = {"version": str(meta.get("version") or ""),
              "gg": base64.b64encode(gg_path.read_bytes()).decode("ascii")}
    content_path = SCRIPT_DIR / content_name
    if meta.get("has_content") and content_path.is_file():
        answer["content"] = base64.b64encode(content_path.read_bytes()).decode("ascii")
    return api_ok(**answer)


@app.post(f"/{API}/notices")
def api_notices():
    """The owner's notices for this app (to all, or to its code) after the last number it got."""
    body = request.get_json(silent=True) or {}
    row = code_from_token(body.get("token"))
    if not row:
        return api_err("انتهت صلاحية الدخول أو أوقِف الرمز أو نُقل لجهاز آخر. أعد إدخال الرمز.", 200)
    try:
        after = max(0, int(body.get("after") or 0))
    except (TypeError, ValueError):
        after = 0
    items, last = notices_for(row["id"], after)
    return api_ok(notices=items, last=last)


@app.post(f"/{API}/app-latest")
def api_app_latest():
    """The app meant for this user (their trial, else everyone's), for their page to offer «تنزيل التطبيق» when it
    is newer than the one installed."""
    body = request.get_json(silent=True) or {}
    row = code_from_token(body.get("token"))
    if not row:
        return api_err("انتهت صلاحية الدخول أو أوقِف الرمز أو نُقل لجهاز آخر. أعد إدخال الرمز.", 200)
    meta, slot = app_for(row["id"])
    if not meta:
        return api_ok(available=False)
    return api_ok(available=True, version=meta["version"], code=meta["code"], package=meta["package"],
                  size=meta["size"], sha256=meta["sha256"], name=app_file_name(meta), trial=slot == "pilot")


@app.post(f"/{API}/app-download")
def api_app_download():
    """The APK meant for this user, through the app's protected connection; from byte «start» on to go on with a cut
    download. The answer says where it starts, the whole size and the file's fingerprint (a newer file meanwhile is
    another fingerprint: the app then starts again)."""
    body = request.get_json(silent=True) or {}
    row = code_from_token(body.get("token"))
    if not row:
        return api_err("انتهت صلاحية الدخول أو أوقِف الرمز أو نُقل لجهاز آخر. أعد إدخال الرمز.", 200)
    meta, slot = app_for(row["id"])
    if not meta:
        return api_err("لا يوجد تطبيق منشور على خادم التحكّم.")
    path = app_path(slot)
    size = path.stat().st_size
    try:
        start = max(0, int(body.get("start") or 0))
    except (TypeError, ValueError):
        start = 0
    if start >= size:
        return api_err("الجزء المطلوب خارج حجم الملف.")
    marks = {"X-App-Start": str(start), "X-App-Total": str(size), "X-App-Sha256": meta["sha256"]}
    if not start:
        response = send_file(path, mimetype=APK_MIME, as_attachment=True, download_name=app_file_name(meta), max_age=0)
        response.headers.update(marks)
        return response

    def rest():
        with open(path, "rb") as source:
            source.seek(start)
            while True:
                chunk = source.read(1 << 16)
                if not chunk:
                    break
                yield chunk

    return app.response_class(rest(), mimetype=APK_MIME, direct_passthrough=True, headers={
        **marks, "Content-Length": str(size - start), "Content-Disposition": f'attachment; filename="{app_file_name(meta)}"'})


@app.post(f"/{API}/comment")
def api_comment():
    body = request.get_json(silent=True) or {}
    row = code_from_token(body.get("token"))
    if not row:
        return api_err("انتهت صلاحية الدخول أو أوقِف الرمز أو نُقل لجهاز آخر. أعد إدخال الرمز.", 200)
    tweet_text = str(body.get("text") or "")[:4000]
    image = None
    raw_image = body.get("image")
    if isinstance(raw_image, str) and raw_image:
        try:
            image = base64.b64decode(raw_image, validate=True)
            if len(image) > 4_000_000:
                image = None
        except (ValueError, Exception):
            image = None
    voice = body.get("voice")
    if isinstance(voice, (int, float)):
        voice = VOICE_BY_NUMBER.get(int(voice), DEFAULT_REPLY_VOICE)
    elif voice not in REPLY_VOICES:
        voice = DEFAULT_REPLY_VOICE
    try:
        manner = int(body.get("manner") or 0)
    except (TypeError, ValueError):
        manner = 0
    before = body.get("before") if isinstance(body.get("before"), list) else []
    if not tweet_text and not image:
        return api_err("لا نص ولا صورة للتغريدة.")
    price = load_prices()["comment"]
    refused = take_comment_price(row["id"], price, task_pass_ok(row["id"], body.get("pass")))   # («مسبق»: held first)
    if refused:
        return api_err(refused)
    try:
        comment = write_reply(tweet_text, image, voice, manner, before)
    except RuntimeError as exc:
        give_back_comment_price(row["id"], price)
        return api_err(str(exc))
    except BaseException:
        give_back_comment_price(row["id"], price)
        raise
    record_comment(row["id"], str(body.get("account") or ""), str(body.get("name") or ""), price)
    return api_ok(comment=comment)


@app.get("/")
def root():
    return "control server", 200


class TLSServer(ThreadedWSGIServer):
    """The web server. Each connection does its TLS handshake in its own thread, with a time limit: one that never
    finishes it (a page refresh cut short, a scanner on the internet) used to stop the whole server — Flask's own
    server does the handshake in the one thread that accepts every connection, with no time limit."""
    HANDSHAKE_SECONDS = 15
    IDLE_SECONDS = 60                  # a kept-alive connection that sends nothing for this long is closed
    MAX_CONNECTIONS = 200              # beyond this, a new connection is closed at once (a flood, not the owner)

    def __init__(self, host: str, port: int, wsgi_app, tls: ssl.SSLContext):
        super().__init__(host, port, wsgi_app)          # (a plain socket: no handshake while accepting)
        self.tls = tls
        self.ssl_context = tls                           # (so the requests are seen as https)

    def process_request(self, request, client_address):
        if threading.active_count() > self.MAX_CONNECTIONS:
            self.shutdown_request(request)
            return
        super().process_request(request, client_address)

    def finish_request(self, request, client_address):
        try:
            request.settimeout(self.HANDSHAKE_SECONDS)
            connection = self.tls.wrap_socket(request, server_side=True)
        except (OSError, ValueError):
            return                                       # (no handshake in time, or not TLS: dropped)
        try:
            connection.settimeout(self.IDLE_SECONDS)
            super().finish_request(connection, client_address)
        except (OSError, ValueError):
            pass
        finally:
            try:
                connection.close()
            except OSError:
                pass


def run() -> None:
    ensure_certificate()
    migrate_heavy_records()
    threading.Thread(target=republish_moves_in_background, name="move-republish", daemon=True).start()
    context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
    context.load_cert_chain(str(CERT_PATH), str(CERT_KEY_PATH))
    print("=" * 70, flush=True)
    print("خادم التحكّم يعمل.", flush=True)
    print("لوحة المالك:", admin_link(), flush=True)
    print("رابط تطبيق المالك:", owner_app_link(), flush=True)
    if SECRETS.get("admin_plain_once"):
        print("كلمة مرور المالك (تظهر مرة واحدة، احفظها):", SECRETS["admin_plain_once"], flush=True)
        data = read_private_json(SECRETS_PATH) or {}
        data["admin_plain_once"] = ""
        write_private_json(SECRETS_PATH, data)
    print("رابط التطبيق:", app_link(), flush=True)
    print("=" * 70, flush=True)
    TLSServer(LISTEN_HOST, LISTEN_PORT, app, context).serve_forever()


if __name__ == "__main__":
    run()
