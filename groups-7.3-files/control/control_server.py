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
import subprocess
import sys
import threading
import time
import urllib.error
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
                "move.json", "server.crt", "server.key")
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
COST_PER_COMMENT = 0.01            # التكلفة لكل تعليق


def load_usage() -> dict:
    data = read_private_json(USAGE_PATH) or {}
    return data if isinstance(data, dict) else {}


def record_comment(code_id: str, account: str, name: str) -> None:
    """Count one written comment against this code and the X account that asked for it."""
    account = (account or "—")[:48]
    with LOCK:
        usage = load_usage()
        code = usage.setdefault(code_id, {"total": 0, "accounts": {}})
        code["total"] = int(code.get("total") or 0) + 1
        who = code["accounts"].setdefault(account, {"n": 0, "name": ""})
        who["n"] = int(who.get("n") or 0) + 1
        if name:
            who["name"] = name[:40]
        write_private_json(USAGE_PATH, usage)


def reset_usage(code_id: str) -> None:
    """تصفير تكلفة رمز واحد."""
    with LOCK:
        usage = load_usage()
        if code_id in usage:
            usage.pop(code_id, None)
            write_private_json(USAGE_PATH, usage)


def reset_all_usage() -> None:
    """تصفير كل التكاليف."""
    with LOCK:
        write_private_json(USAGE_PATH, {})


def usage_of(code_id: str, data: dict | None = None) -> dict:
    row = (data if data is not None else load_usage()).get(code_id) or {"total": 0, "accounts": {}}
    accounts = sorted(
        ({"id": key, "name": value.get("name") or "", "n": int(value.get("n") or 0),
          "cost": round(int(value.get("n") or 0) * COST_PER_COMMENT, 2)}
         for key, value in (row.get("accounts") or {}).items()),
        key=lambda item: -item["n"])
    total = int(row.get("total") or 0)
    return {"total": total, "cost": round(total * COST_PER_COMMENT, 2), "accounts": accounts}


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
        slot = merged.setdefault(name.lower() if name else "id:" + str(key), {"name": name, "n": 0})
        slot["n"] += int(value.get("n") or 0)
        if name and not slot["name"]:
            slot["name"] = name
    accounts = sorted(
        ({"name": slot["name"], "n": slot["n"], "cost": round(slot["n"] * COST_PER_COMMENT, 2)} for slot in merged.values()),
        key=lambda item: -item["n"])
    total = int(row.get("total") or 0)
    return {"total": total, "cost": round(total * COST_PER_COMMENT, 2), "price": COST_PER_COMMENT, "accounts": accounts}


# ----------------------------------------------------------------------------- how each user pays
# «آجل»: the comments are counted and the owner collects their cost later (as before). «مسبق»: the user has a
# balance the owner tops up (or gives as a trial); each comment takes COST_PER_COMMENT from it, and with too
# little left no comment is written. Any user can be either; one who makes an account in the app starts «مسبق».
PAY_LATER, PAY_PREPAID = "later", "prepaid"
LEDGER_KEEP = 100


def pay_of(row: dict) -> str:
    return PAY_PREPAID if row.get("pay") == PAY_PREPAID else PAY_LATER


def balance_of(row: dict) -> float:
    try:
        return round(float(row.get("balance") or 0), 4)
    except (TypeError, ValueError):
        return 0.0


def take_comment_price(code_id: str) -> str:
    """Before a prepaid user's comment its price is taken from the balance at once (so two comments at the same
    moment cannot both spend the last cent). "" when it may go ahead, else why not. A «آجل» user always may."""
    with LOCK:
        codes = load_codes()
        row = next((item for item in codes if item.get("id") == code_id), None)
        if row is None or pay_of(row) != PAY_PREPAID:
            return ""
        balance = balance_of(row)
        if balance + 1e-9 < COST_PER_COMMENT:
            return f"رصيدك لا يكفي لكتابة التعليقات (الرصيد ${max(balance, 0):.2f}). اطلب من صاحب البرنامج شحن رصيدك."
        row["balance"] = round(balance - COST_PER_COMMENT, 4)
        save_codes(codes)
    return ""


def give_back_comment_price(code_id: str) -> None:
    """The comment was not written after all: its price goes back to the balance."""
    with LOCK:
        codes = load_codes()
        row = next((item for item in codes if item.get("id") == code_id), None)
        if row is not None and pay_of(row) == PAY_PREPAID:
            row["balance"] = round(balance_of(row) + COST_PER_COMMENT, 4)
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


def save_acts_of(code_id: str, accounts: list) -> None:
    """The app's numbers now, for each of its X accounts: they replace what it sent before."""
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
        data[code_id] = {"at": int(time.time()), "accounts": clean}
        write_private_json(ACTS_PATH, data)


def acts_of(code_id: str, data: dict | None = None) -> dict:
    """A user's totals and, by X account (by @name, as the comments are), what their app shows; at is when it
    last sent them (0: never)."""
    row = (data if data is not None else load_acts()).get(code_id) or {}
    merged: dict[str, dict] = {}
    for key, value in (row.get("accounts") or {}).items():
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
    if len(words) < 6:
        return False
    if re.search(r"[،,؛;:\uff1a\-\u2013\u2014/\\*]$", text.strip()):
        return False
    last = re.sub(r"[.!?؟…\"'«»“”]+$", "", words[-1])
    return len(last) > 2


def reply_prompt(voice: str, manner_number: int, before: list) -> str:
    low, high = random.choice(REPLY_LENGTHS)
    manner = REPLY_MANNERS[int(manner_number) % len(REPLY_MANNERS)]
    prompt = (
        "Write one public reply to this tweet, as an ordinary person scrolling X who comments on what it says. "
        "Read the whole tweet first and answer what it really says (its point, and its ending when it tells a story); "
        "do not guess beyond it. "
        "Not personal: the reply is about the tweet's topic, not about you. No stories or experiences of yours, "
        "nothing that happened to you, your family or your friends, and nothing about your own life (nothing like: "
        "صار معي، جربت، شفت بنفسي، أخوي، عندنا في البيت، أتذكر لما، لو كنت مكانه). "
        "Speak about its topic, not to please its author: do not compliment, thank or flatter the author, do not "
        "praise the tweet (nothing like: well said, you're right, great post, صدقت، كفو، أبدعت، كلامك ذهب), and do "
        "not just agree. Honest, never rude: no insults, and do not mock the author. "
        f"This time: {random.choice(REPLY_ANGLES)}. Your manner (always the same): {manner}. "
        "If the tweet is a prayer (دعاء), about religion, a death, an illness or other sad news, leave the angle and "
        "the manner: reply sincerely and respectfully, with no joke and no disagreement. "
        f"At most {REPLY_MAX_CHARS} characters, spaces included (about {low} to {high} words). Finish the sentence. "
        "Never stop mid-word or mid-phrase. "
        "Write in the tweet's own language. An Arabic tweet gets everyday spoken Saudi Arabic (عامية سعودية بيضاء), "
        "the way people really type on X, never formal Arabic (فصحى): no words like الأولى، ينبغي، لا تثبت، ما زال، "
        "إذ، لذا، حيث، كما أن. A tweet in another language (English, Turkish…) gets its reply in that language. "
        "Plain letters only: no diacritics (no تشكيل: no fatha, damma, kasra, tanween, shadda or sukun), and no "
        "commas (، or ,). " + REPLY_VOICES.get(voice, REPLY_VOICES[DEFAULT_REPLY_VOICE]) + " "
        "Sound like a real person, specific and casual, not a teacher, a preacher, a brand or an assistant: no "
        "advice or lessons to the author or to people (nothing like: الأولى أن، يجب، الأفضل أن، تذكّر، نصيحتي), no "
        "general wisdom or sayings, no neat conclusion; just make your point about the topic itself. "
        "The image is only a screenshot to read the tweet: never mention it, the picture, the post or the tweet "
        "(no الصورة، المنشور، التغريدة); react to what is in them. "
        "Do not open with filler (like صراحة، فعلاً، والله) or by repeating the tweet. "
        "No hashtags, no links, no quotes, no labels, no introduction. Return only the finished reply."
    )
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
    if len(text) > REPLY_MAX_CHARS:
        text = fit_comment(text)
    return text


# ----------------------------------------------------------------------------- the app's unlock token
# The token carries the code and the one device it was bound to, signed. A copy of it on another phone is useless:
# that phone's own device id will not match the device inside the token (and the code is bound to the first device).
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
    """The active code a token belongs to, only when the token's device is the one the code is bound to."""
    code_id, device = read_token(token)
    if not code_id:
        return None
    with LOCK:
        for row in load_codes():
            if row.get("id") == code_id and row.get("active") and (row.get("bound_device") or "") == device:
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

DASHBOARD = r"""{% macro ic(n) %}<svg class="i" viewBox="0 0 24 24" aria-hidden="true"><use href="#i-{{n}}"/></svg>{% endmacro %}{% set nokey = (engine=='gemini' and not gemini_set) or (engine=='claude' and not claude_set) %}<!doctype html>
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
.opt input{position:absolute;opacity:0;width:1px;height:1px}
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
.ckl{display:flex;gap:10px;align-items:center;margin:14px 0 0;font-size:14px;cursor:pointer}.ckl input{width:20px;height:20px;accent-color:var(--pri);flex:none}
.rs{margin-top:14px}.rs summary{min-height:40px}
.pk{display:none;margin-top:10px;max-height:260px;overflow:auto;border:1px solid var(--line);border-radius:12px;background:var(--soft)}
.pub:has(input[value=some]:checked) .pk,.pk.on{display:block}
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
<symbol id="i-sort" viewBox="0 0 24 24"><path d="M3 6h18M6 12h12M10 18h4"/></symbol>
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
{% if stats.comments %}<form method="post" action="/{{admin}}/reset-cost-all" data-title="تصفير كل التكاليف؟" data-confirm="سيُصفَّر عدّاد التعليقات والتكلفة لكل المستخدمين." data-yes="تصفير التكاليف" data-kind="danger" data-toast="تم تصفير كل التكاليف"><button class="hb">{{ic('reset')}}تصفير التكاليف</button></form>{% endif %}</div>
<div class="ratio" aria-hidden="true"><i style="width:{{ stats.active * 100 / stats.users }}%"></i></div>
<div class="rl"><span><b>{{stats.active}}</b> يعمل</span><span><b>{{stats.users - stats.active}}</b> موقوف</span></div>
</div>
<dl class="kp">
<div><dt>أجهزة مربوطة</dt><dd>{{stats.bound}}</dd></div>
<div><dt>تعليقات مكتوبة</dt><dd>{{ '{:,}'.format(stats.comments) }}</dd></div>
<div><dt>التكلفة التقديرية</dt><dd>${{ '%.2f'|format(stats.cost) }}</dd></div>
<div><dt>الرتويت</dt><dd>{{ '{:,}'.format(stats.repost) }}</dd></div>
<div><dt>الإعجاب</dt><dd>{{ '{:,}'.format(stats.like) }}</dd></div>
<div><dt>المرجعية</dt><dd>{{ '{:,}'.format(stats.bookmark) }}</dd></div>
</dl>
</section>
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
<article class="u{{ '' if c.active else ' off' }}" data-id="{{c.id}}" data-s="{{ 'on' if c.active else 'off' }}" data-name="{{c.label}}" data-code="{{c.code}}" data-bound="{{ '1' if c.bound_device else '' }}" data-pay="{{c.pay}}" data-bal="{{ '%.2f'|format(c.balance) }}" data-acct="{{c.account_user}}" data-n="{{c.usage.total}}" data-x="{{ c.acts.repost + c.acts.like + c.acts.bookmark }}" data-seen="{{c.last_seen or 0}}" data-q="{{ (c.label ~ ' ' ~ c.code ~ ' ' ~ c.code|replace('-','') ~ ' ' ~ c.usage.accounts|map(attribute='name')|join(' '))|lower }}">
<div class="who"><div class="av" style="--h:{{hue}}" aria-hidden="true">{{ (c.label or '؟')[:1] }}</div>
<div class="nm"><h3>{{ c.label or 'بدون اسم' }}{% if c.account_user %}<span class="tg">حساب</span>{% endif %}{% if c.pay == 'prepaid' %}<span class="tg pp">مسبق</span>{% endif %}</h3><p><span class="st">{{ 'يعمل' if c.active else 'موقوف' }}</span><span>{% if c.last_seen %}آخر دخول {{c.last_seen_text}}{% else %}لم يدخل بعد{% endif %}</span></p></div></div>
<form method="post" action="/{{admin}}/code/toggle" data-toast="{{ 'تم إيقاف الرمز' if c.active else 'تم تشغيل الرمز' }}"><input type="hidden" name="id" value="{{c.id}}"><button class="sw{{ ' on' if c.active else '' }}" role="switch" aria-checked="{{ 'true' if c.active else 'false' }}" aria-label="رمز {{ c.label or 'بدون اسم' }} يعمل"><i></i></button></form>
<div class="cr"><button type="button" class="code" data-copy="{{c.code}}" aria-label="نسخ الرمز {{c.code}}"><bdi>{{c.code}}</bdi>{{ic('copy')}}</button><button type="button" class="ib" data-more aria-label="خيارات {{ c.label or 'المستخدم' }}">{{ic('more')}}</button></div>
{% set facts %}{% if c.pay == 'prepaid' %}<span class="bal{{ ' low' if c.balance < 0.05 else '' }}" title="الرصيد المسبق">رصيد <b dir="ltr">${{ '%.2f'|format(c.balance) }}</b></span>{% endif %}<span><b>{{ '{:,}'.format(c.usage.total) }}</b> تعليق</span><span title="التكلفة التقديرية"><b>${{ '%.2f'|format(c.usage.cost) }}</b></span><span class="dev{{ ' on' if c.bound_device else '' }}">{{ic('phone')}}{{ 'جهاز مربوط' if c.bound_device else 'غير مربوط' }}</span>{% endset %}
{% if c.usage.accounts %}<details class="acc"><summary class="facts" title="التعليقات حسب حساب X">{{facts}}{{ic('chev')}}</summary>
<p class="alh">حسابات X ({{c.usage.accounts|length}})</p><ul class="al">
{% for a in c.usage.accounts %}<li><b><bdi>{{ ('@' ~ a.name) if a.name else ('#' ~ a.id[:8]) }}</bdi></b><span>{{ '{:,}'.format(a.n) }} تعليق</span><span>${{ '%.2f'|format(a.cost) }}</span><div class="pg"><i style="width:{{ ((a.n * 100 / c.usage.total)|round|int) if c.usage.total else 0 }}%"></i></div></li>{% endfor %}
</ul></details>{% else %}<div class="facts">{{facts}}</div>{% endif %}
{% if c.ledger %}<details class="led"><summary>سجل الرصيد</summary><ul>{% for e in c.ledger %}<li><span>{{e.note}}</span><b class="{{ 'pl' if e.amount > 0 else 'mi' }}" dir="ltr">{{ '+' if e.amount > 0 else '−' }}${{ '%.2f'|format(e.amount|abs) }}</b><small>{{e.when}} · الرصيد <bdi dir="ltr">${{ '%.2f'|format(e.after) }}</bdi></small></li>{% endfor %}</ul></details>{% endif %}
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
<div class="nm"><h3>{{m.who}}{% if not m.read %} <span class="nw">جديدة</span>{% endif %}</h3><p>{% if m.code %}<bdi>{{m.code}}</bdi> · {% endif %}{{m.ago}} · <span dir="ltr">{{m.when}}</span></p></div></div>
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
<p class="mut">هذا هو برنامج التطبيق. حدّثه من هنا: ارفع الملف المعدّل ثم اضغط «نشر التحديث»، فيظهر للمستخدمين زر «تحديث» داخل التطبيق — دون بناء تطبيق جديد. رقم الإصدار تحدده هنا، ولا حاجة لتعديله داخل الملف.</p>
<dl class="mvd">
<div><dt>للجميع</dt><dd>{% if script_live.version %}الإصدار <b>{{script_live.version}}</b> · نُشر {{script_live_when}}{% if script_live.has_content %} · مع content.py{% endif %}{% else %}<span class="mut">لا يوجد سكربت منشور بعد. التطبيقات تعمل بالسكربت المدمج فيها.</span>{% endif %}</dd></div>
{% if script_pilot.version %}<div><dt>تجريبي</dt><dd>الإصدار <b>{{script_pilot.version}}</b> · عند {{script_pilot_names|length}} مستخدم · نُشر {{script_pilot_when}}</dd></div>{% endif %}
{% if script_staged.version %}<div><dt>المرفوع</dt><dd>الإصدار <b>{{script_staged.version}}</b>{% if script_can_publish %} · <span class="b on">جاهز للنشر</span>{% else %} · <span class="mut">منشور</span>{% endif %}</dd></div>{% endif %}
</dl>
<form method="post" action="/{{admin}}/script/upload" enctype="multipart/form-data" data-keep-busy>
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
<label class="opt"><input type="radio" name="target" value="all" checked><span class="pi">{{ic('users')}}</span><span><b>كل المستخدمين</b><small>يظهر زر «تحديث» للجميع</small></span><span class="ck">{{ic('check')}}</span></label>
<label class="opt"><input type="radio" name="target" value="some"><span class="pi">{{ic('edit')}}</span><span><b>مستخدمون أختارهم (تجريبي)</b><small>جرّبه عندهم أولًا؛ الباقون يبقون على الإصدار الحالي</small></span><span class="ck">{{ic('check')}}</span></label>
</div>
<div class="pk" role="group" aria-label="من يصله الإصدار التجريبي">{% for c in codes %}<label class="pkr{{ '' if c.active else ' off' }}"><input type="checkbox" name="codes" value="{{c.id}}"><span class="pkn">{{ c.label or 'بدون اسم' }}</span><span class="pkc">{{c.code}}</span></label>{% else %}<p class="pke">لا يوجد مستخدمون بعد.</p>{% endfor %}</div>
<button class="btn wide" style="margin-top:12px">{{ic('check')}}نشر التحديث (الإصدار {{script_staged.version}})</button></form>
<script>(function(){var f=document.querySelector('form.pub');if(!f)return;var v=f.dataset.v;
function sync(){var some=f.querySelector('input[name=target][value=some]').checked,n=f.querySelectorAll('input[name=codes]:checked').length;
f.dataset.confirm=some?(n?'سيصل الإصدار '+v+' إلى '+n+' مستخدم فقط، ويظهر لهم زر «تحديث». الباقون يبقون على الإصدار الحالي.':'لم تختر أي مستخدم. اختر من القائمة من يصله الإصدار التجريبي.'):'سيصل الإصدار '+v+' إلى كل المستخدمين، فيظهر لهم زر «تحديث» في التطبيق. تأكد أنك جرّبت الملف.';
f.dataset.yes=some?'نشر تجريبي':'نشر'}
f.addEventListener('change',sync);sync()})();</script>{% endif %}
{% if script_pilot.version %}<div class="pil">
<p class="pil-h">{{ic('edit')}}<span>الإصدار التجريبي <b>{{script_pilot.version}}</b> يصل الآن إلى: {{ script_pilot_names|join('، ') if script_pilot_names else 'لا أحد (حُذف من اخترتهم)' }}</span></p>
{% if not script_live.version %}<p class="pil-w">{{ic('alert')}}<span>لا يوجد إصدار منشور للجميع بعد، فالمستخدمون الجدد خارج التجربة لا يستطيعون تجهيز التطبيق. انشر للجميع حين تتأكد.</span></p>{% endif %}
<div class="pil-a">
<form method="post" action="/{{admin}}/script/pilot/promote" data-title="نشر للجميع؟" data-confirm="سيصل الإصدار {{script_pilot.version}} إلى كل المستخدمين، فيظهر لهم زر «تحديث»." data-yes="نشر للجميع" data-toast="تم النشر للجميع"><button class="btn">{{ic('check')}}نشر للجميع</button></form>
<form method="post" action="/{{admin}}/script/pilot/cancel" data-title="إلغاء الإصدار التجريبي؟" data-confirm="لن يُعرض الإصدار {{script_pilot.version}} على أحد بعد الآن. من حدّث إليه يبقى على نسخته حتى يُنشر إصدار أعلى للجميع." data-yes="إلغاء التجريبي" data-kind="danger" data-toast="أُلغي الإصدار التجريبي"><button class="btn ghost">إلغاء التجريبي</button></form>
</div>
<details class="rs"><summary>تعديل من يصله</summary>
<form method="post" action="/{{admin}}/script/pilot/users" data-toast="تم حفظ المستخدمين">
<div class="pk on" role="group" aria-label="من يصله الإصدار التجريبي">{% for c in codes %}<label class="pkr{{ '' if c.active else ' off' }}"><input type="checkbox" name="codes" value="{{c.id}}"{% if c.id in script_pilot_ids %} checked{% endif %}><span class="pkn">{{ c.label or 'بدون اسم' }}</span><span class="pkc">{{c.code}}</span></label>{% endfor %}</div>
<button class="btn wide ghost" style="margin-top:10px">حفظ</button></form></details>
</div>{% endif %}
<ul class="notes"><li>{{ic('shield')}}<span>يُنزَّل السكربت عبر اتصال التطبيق المحمي بخادمك، ولا يصل إلا لجهاز يحمل رمزًا صالحًا.</span></li>
<li>{{ic('alert')}}<span>يُجرّب التطبيق تشغيل الإصدار الجديد قبل اعتماده؛ إن لم يعمل، يبقى على القديم ولا يتعطّل.</span></li>
<li>{{ic('edit')}}<span>«تجريبي»: انشر لمستخدمين تختارهم (أنت مثلًا) أولًا، ثم «نشر للجميع» حين تتأكد أنه سليم.</span></li></ul></div>
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
<form id="sh-release" method="post" action="/{{admin}}/code/release" data-title="تحرير الجهاز؟" data-confirm="يُفكّ ارتباط الرمز بجواله الحالي ليتمكّن صاحبه من تفعيله على جوال آخر." data-yes="تحرير الجهاز" data-toast="تم تحرير الجهاز"><input type="hidden" name="id"><button>{{ic('phone')}}<span>تحرير الجهاز<small>ليُفعَّل الرمز على جوال آخر</small></span></button></form>
<form id="sh-pay" method="post" action="/{{admin}}/code/pay" data-toast="تم تغيير نوع الدفع"><input type="hidden" name="id"><input type="hidden" name="pay" value="prepaid"><button>{{ic('key')}}<span id="sh-pay-t">تحويل إلى دفع مسبق</span></button></form>
<button type="button" id="sh-bal">{{ic('plus')}}<span>إضافة رصيد<small>تجريبي أو شحن، ويُخصم <bdi dir="ltr">${{ '%.2f'|format(price) }}</bdi> لكل تعليق</small></span></button>
<button type="button" id="sh-pw">{{ic('lock')}}<span>تعيين كلمة سر جديدة<small>لصاحب حساب نسي كلمة سره</small></span></button>
<form id="sh-reset" method="post" action="/{{admin}}/code/reset-cost" data-title="تصفير التكلفة؟" data-confirm="سيُصفَّر عدّاد التعليقات والتكلفة لهذا المستخدم فقط." data-yes="تصفير التكلفة" data-kind="danger" data-toast="تم تصفير التكلفة"><input type="hidden" name="id"><button>{{ic('reset')}}تصفير التكلفة</button></form>
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
$('#sh-pay-t').innerHTML=pre?'تحويل إلى «آجل»<small>تُحسب التكلفة ويدفعها لاحقًا، ولا يُخصم من الرصيد</small>':'تحويل إلى «دفع مسبق»<small>لا تُكتب التعليقات إلا برصيد (الرصيد ⁦$'+(d.bal||'0.00')+'⁩)</small>';
$('#sh-pw').hidden=!d.acct;
sheet.showModal()}
$('#sh-bal').onclick=function(){sheet.close();var g=$('#bal');$('input[name=id]',g).value=cur.dataset.id;
$('#bal-now').textContent=(cur.dataset.name||'المستخدم')+' · الرصيد الآن ⁦$'+(cur.dataset.bal||'0.00')+'⁩'+(cur.dataset.pay==='prepaid'?'':' (هذا المستخدم «آجل»؛ حوّله إلى «مسبق» ليُستخدم رصيده)');
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
    stats = {"users": len(rows), "active": sum(1 for r in rows if r.get("active")),
             "bound": sum(1 for r in rows if r.get("bound_device")),
             "comments": sum(r["usage"]["total"] for r in rows),
             "cost": round(sum(r["usage"]["cost"] for r in rows), 2),
             "repost": sum(r["acts"]["repost"] for r in rows), "like": sum(r["acts"]["like"] for r in rows),
             "bookmark": sum(r["acts"]["bookmark"] for r in rows)}
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
        price=COST_PER_COMMENT,
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
    """Unbind a code from its phone, so the user can sign in on a new one with the same code."""
    if not logged_in():
        return redirect(f"/{ADMIN}")
    code_id = request.form.get("id")
    with LOCK:
        codes = load_codes()
        for row in codes:
            if row.get("id") == code_id:
                row["bound_device"] = ""
        save_codes(codes)
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
    flash("ok", f"{'أُضيف' if amount > 0 else 'خُصم'} ${abs(amount):.2f} {'إلى' if amount > 0 else 'من'} رصيد {name}. "
                f"الرصيد الآن ${row['balance']:.2f}."
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
            write_private_json(SCRIPT_DIR / PILOT_META, dict(staged, published_at=int(time.time()), codes=chosen))
            flash("ok", f"نُشر الإصدار {staged['version']} تجريبيًا لـ {len(chosen)} مستخدم. يظهر لهم زر «تحديث» خلال "
                        "دقيقة تقريبًا، والباقون يبقون على الإصدار الحالي.")
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
        write_private_json(SCRIPT_DIR / SCRIPT_META, staged)
        remove_script_files("pilot-gg.py", "pilot-content.py", PILOT_META)      # (everyone has a newer one now)
    flash("ok", f"نُشر الإصدار {staged['version']}. يظهر للمستخدمين زر «تحديث» خلال دقيقة تقريبًا، أو عند فتح الصفحة.")
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
    flash("ok", f"نُشر الإصدار {pilot['version']} لكل المستخدمين. يظهر لهم زر «تحديث» خلال دقيقة تقريبًا.")
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
        bound = target.get("bound_device") or ""
        if bound and bound != device:
            return api_err("هذا الرمز مُستخدم على جهاز آخر. اطلب من صاحب البرنامج تحريره أو رمزًا جديدًا.")
        target["bound_device"] = device
        target["last_seen"] = int(time.time())
        save_codes(codes)
    engine, _, _, _ = active_engine()
    return api_ok(token=make_token(row["id"], device), engine=engine or "none", move_key=SECRETS.get("move_public", ""))


def signed_in(row: dict, device: str):
    """The answer for a phone that may come in (as for a code): its token."""
    engine, _, _, _ = active_engine()
    return api_ok(token=make_token(row["id"], device), engine=engine or "none", move_key=SECRETS.get("move_public", ""),
                  pay=pay_of(row), balance=round(balance_of(row), 2))


def _device_of(body: dict) -> str:
    return re.sub(r"[^A-Za-z0-9]", "", str(body.get("device") or ""))[:64]


@app.post(f"/{API}/register")
def api_register():
    """A new account made in the app: a user like any other, bound to this phone, paying in advance («مسبق»)."""
    body = request.get_json(silent=True) or {}
    device = _device_of(body)
    name = str(body.get("user") or "").strip()
    password = str(body.get("password") or "")
    if not device:
        return api_err("لم يصل معرّف الجهاز. حدّث التطبيق.")
    if not ACCOUNT_NAME.match(name):
        return api_err("اسم المستخدم من 3 إلى 24 حرفًا أو رقمًا، بلا مسافات (يُسمح بـ _ و . و -).")
    if not 6 <= len(password) <= 128:
        return api_err("كلمة السر 6 أحرف على الأقل.")
    with LOCK:
        taken = account_row(load_codes(), name) is not None
    if taken:
        return api_err("اسم المستخدم مأخوذ. اختر اسمًا آخر.")
    if not signup_allowed():
        return api_err("حسابات كثيرة من هذه الشبكة. حاول بعد ساعة.")
    stored = account_pw_hash(password)
    with LOCK:
        codes = load_codes()
        if account_row(codes, name) is not None:
            return api_err("اسم المستخدم مأخوذ. اختر اسمًا آخر.")
        now = int(time.time())
        row = {"id": secrets.token_hex(8), "code": make_code(), "label": name, "active": True, "created": now,
               "last_seen": now, "bound_device": device, "pay": PAY_PREPAID, "balance": 0.0, "ledger": [],
               "account": {"user": name, "pw": stored, "at": now}}
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
        bound = target.get("bound_device") or ""
        if bound and bound != device:
            return api_err("هذا الحساب مُستخدم على جهاز آخر. اطلب من صاحب البرنامج تحرير الجهاز.")
        target["bound_device"] = device
        target["last_seen"] = int(time.time())
        save_codes(codes)
    return signed_in(target, device)


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
    return api_ok(**usage_by_account(row["id"]), pay=pay_of(row), balance=round(balance_of(row), 2))


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
    save_acts_of(row["id"], accounts)
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
                                               "replies": []}))
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
                  has_content=bool(meta.get("has_content")), content_sha256=script_file_sha(content_name))


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
    refused = take_comment_price(row["id"])        # («مسبق»: its price is held from the balance first)
    if refused:
        return api_err(refused)
    try:
        comment = write_reply(tweet_text, image, voice, manner, before)
    except RuntimeError as exc:
        give_back_comment_price(row["id"])
        return api_err(str(exc))
    except BaseException:
        give_back_comment_price(row["id"])
        raise
    record_comment(row["id"], str(body.get("account") or ""), str(body.get("name") or ""))
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
