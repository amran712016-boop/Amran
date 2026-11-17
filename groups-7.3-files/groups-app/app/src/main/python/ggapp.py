"""The app's side of running the groups script. The app (Engine.java) calls main() once, in a thread of its own:
the script runs there as it runs on a server (python gg.py), with its page on 127.0.0.1 for the app's own screen
and a stand-in for Playwright (the playwright package beside this file) that drives the app's browser. What the
script prints is also kept here, for «السجل» in the app."""
from __future__ import annotations

import collections
import json
import os
import runpy
import sys
import threading
import time
import traceback
import urllib.request

# Where «تحديث السكربت» takes the script's newest files from.
RAW = "https://raw.githubusercontent.com/husaynalshehari/husaynalshehari/ccr-695f6c04-mlgxcr"
STATE = {"phase": "idle", "error": "", "folder": ""}
# Each line with the account whose work printed it ("" for the app's own lines), so «السجل» shows one account's.
LOG: collections.deque = collections.deque(maxlen=6000)
_log_lock = threading.Lock()
_thread_account = threading.local()
# The account the panel shows now (the script says when it changes): its key and its name.
ACTIVE = {"key": "", "name": ""}


def set_thread_account(key) -> None:
    """The script: what this thread prints from now on belongs to this account ("" for none)."""
    _thread_account.key = str(key or "")


def set_active_account(key, name="") -> None:
    """The script: the panel now shows this account; «السجل» is its log."""
    ACTIVE.update(key=str(key or ""), name=str(name or ""))


class _Tee:
    """What is printed goes where it went (Android's log) and into LOG, a line at a time, with the time."""

    def __init__(self, stream):
        self._stream = stream
        self._rests = {}                   # (each thread's unfinished line, so lines of two threads never mix)

    def write(self, text):
        if not isinstance(text, str):          # (as a text stream refuses bytes: what asks takes it for one)
            raise TypeError("write() argument must be str, not " + type(text).__name__)
        try:
            self._stream.write(text)
        except Exception:
            pass
        tag = getattr(_thread_account, "key", "")
        me = threading.get_ident()
        with _log_lock:
            rest = self._rests.get(me, "") + text
            while "\n" in rest:
                line, rest = rest.split("\n", 1)
                LOG.append((tag, time.strftime("%H:%M:%S ") + line))
            if rest:
                self._rests[me] = rest
            else:
                self._rests.pop(me, None)
        return len(text)

    def flush(self):
        try:
            self._stream.flush()
        except Exception:
            pass

    def isatty(self):
        return False

    def __getattr__(self, name):
        return getattr(self._stream, name)


def _keep_output() -> None:
    if not isinstance(sys.stdout, _Tee):
        sys.stdout = _Tee(sys.stdout)
    if not isinstance(sys.stderr, _Tee):
        sys.stderr = _Tee(sys.stderr)


def main(folder: str, port: int, access: str) -> None:
    """Run the groups script (folder/gg.py) until the app ends. Does not return while the script runs."""
    _keep_output()
    folder = str(folder)
    script = os.path.join(folder, "gg.py")
    os.environ["PORT"] = str(int(port))
    os.environ["BIND_HOST"] = "127.0.0.1"
    os.environ["X_ACCESS_PATH"] = str(access)
    os.environ["GG_IN_APP"] = "1"                 # (the script clicks without scrolling the page: see IN_APP there)
    os.chdir(folder)
    sys.argv = [script]
    try:
        threading.stack_size(4 * 1024 * 1024)      # (room for the script's own threads: Android's are small)
    except (ValueError, RuntimeError):
        pass
    STATE.update(phase="running", error="", folder=folder)
    try:
        print(f"تشغيل السكربت {script} على المنفذ {port} (Python {sys.version.split()[0]})", flush=True)
        runpy.run_path(script, run_name="__main__")
        STATE.update(phase="stopped", error="توقف السكربت.")
    except SystemExit as exc:
        STATE.update(phase="stopped", error=f"توقف السكربت ({exc.code}).")
    except BaseException:
        detail = traceback.format_exc()
        print(detail, flush=True)
        STATE.update(phase="failed", error=detail[-3000:])


def state() -> str:
    return json.dumps(STATE, ensure_ascii=False)


def _lines_of(key: str, lines: int) -> list:
    with _log_lock:
        return [line for tag, line in LOG if tag == key][-int(lines):]


def log_text(lines: int = 500) -> str:
    """«السجل»: the last lines printed by the work of the account the panel shows (each account its own)."""
    key, name = ACTIVE.get("key") or "", ACTIVE.get("name") or ""
    if not key:
        return general_log_text(lines)
    rows = _lines_of(key, lines)
    head = "سجل الحساب " + ("@" + name if name else "المختار") + " فقط."
    return head + "\n\n" + ("\n".join(rows) if rows else "لا شيء في سجل هذا الحساب بعد.")


def general_log_text(lines: int = 500) -> str:
    """«السجل العام»: what the app itself printed (its start, its errors), outside any account's work."""
    rows = _lines_of("", lines)
    return "السجل العام للتطبيق (خارج مهام الحسابات).\n\n" + ("\n".join(rows) if rows else "لا شيء في السجل بعد.")


def click_log_text() -> str:
    """The click trace of the account the panel shows, plus the last lines its work printed."""
    folder = STATE.get("folder") or os.getcwd()
    key = ACTIVE.get("key") or ""
    path = os.path.join(folder, "data", "accounts", key, "click-log.txt") if key else os.path.join(folder, "data", "click-log.txt")
    try:
        with open(path, encoding="utf-8") as handle:
            body = handle.read()[-20000:]
    except OSError:
        body = ""
    printed = "\n".join(_lines_of(key, 250))
    head = device_line()
    if not body:
        body = "لا يوجد سجل نقر بعد. نفّذ مهمة على تغريدة ثم ارجع إلى هذه القائمة."
    return head + "\n\n" + body + "\n\n--- آخر ما طُبع ---\n" + printed


def device_line() -> str:
    """This phone, in one line (it heads the check's report)."""
    try:
        from java import jclass
        build = jclass("android.os.Build")
        version = jclass("android.os.Build$VERSION")
        package = jclass("android.webkit.WebView").getCurrentWebViewPackage()
        host = jclass("app.tg.groups.BrowserHost")
        return (f"الجهاز: {build.MANUFACTURER} {build.MODEL} · أندرويد {version.RELEASE} · "
                f"WebView {package.versionName if package is not None else '؟'} · "
                f"ملف مستقل لكل حساب: {'نعم' if bool(host.profilesSupported()) else 'لا'} · Python {sys.version.split()[0]}")
    except Exception as exc:
        return f"الجهاز: غير معروف ({type(exc).__name__}) · Python {sys.version.split()[0]}"


def check(online, listener=None) -> str:
    """«فحص المتصفح»: the report. listener.add(line), when given (the app's page), gets each line as it comes."""
    _keep_output()
    import ggcheck

    def say(line: str) -> None:
        if listener is not None:
            listener.add(str(line))

    head = device_line()
    say(head)
    say("")
    folder = STATE.get("folder") or os.getcwd()
    try:
        report = ggcheck.run(profile_root=os.path.join(folder, "check"), online=bool(online), say=say)
    except BaseException:
        report = "✗ تعذّر تشغيل الفحص:\n" + traceback.format_exc()[-1500:]
        say(report)
    print("فحص المتصفح:\n" + head + "\n" + report, flush=True)
    return head + "\n\n" + report


def update_script() -> str:
    """Take the script's newest files from its repository, in place of the ones here. They are used the next time
    the app starts. Nothing is replaced unless both arrive whole and are Python that compiles."""
    folder = STATE.get("folder") or os.getcwd()
    fetched = []
    try:
        for name, target in (("script_original.py", "gg.py"), ("content.py", "content.py")):
            request = urllib.request.Request(f"{RAW}/{name}", headers={"User-Agent": "tg-groups-app/1.0", "Cache-Control": "no-cache"})
            with urllib.request.urlopen(request, timeout=60) as answer:
                body = answer.read(8 << 20)
            text = body.decode("utf-8")
            if len(text) < 20_000 or "flask" not in text:
                return f"لم يكتمل التحديث: ملف {name} وصل ناقصًا."
            compile(text, target, "exec")
            fetched.append((target, body))
    except SyntaxError as exc:
        return f"لم يكتمل التحديث: الملف الجديد فيه خطأ ({exc.msg})."
    except Exception as exc:
        return f"تعذّر التحديث: {type(exc).__name__}: {str(exc)[:160]}"
    same = True
    for target, body in fetched:
        path = os.path.join(folder, target)
        try:
            with open(path, "rb") as handle:
                same = same and handle.read() == body
        except OSError:
            same = False
    if same:
        return "السكربت محدَّث: لا يوجد أحدث منه."
    for target, body in fetched:
        path = os.path.join(folder, target)
        with open(path + ".new", "wb") as handle:
            handle.write(body)
        os.replace(path + ".new", path)
    return "OK"
