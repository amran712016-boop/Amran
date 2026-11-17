#!/usr/bin/env python3
"""One-file Flask page to verify an X session and act on a chat group's tweets.

Saved sessions (auth token + the account username) are written beside this
script and survive a restart. Job progress is kept too, so leaving the browser
and coming back shows whether the work is still running, where it stopped,
or that it finished. The token is not returned except to this same page.
"""
from __future__ import annotations

import atexit
import base64
import gzip
import hashlib
import hmac
import concurrent.futures
import importlib.util
import itertools
import json
import logging
import math
import os
import queue
import random
import re
import secrets
import shutil
import socket
import subprocess
import sys
import traceback
import threading
import time
import urllib.error
import urllib.request
from collections import defaultdict, deque
from pathlib import Path
from types import SimpleNamespace
from urllib.parse import quote

from flask import Flask, abort, jsonify, make_response, redirect, render_template_string, request, session
from playwright.sync_api import TimeoutError as PlaywrightTimeoutError
from playwright.sync_api import Page, sync_playwright
from werkzeug.serving import make_server

app = Flask(__name__)
app.secret_key = secrets.token_bytes(32)
app.config.update(
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE="Strict",
    SESSION_COOKIE_SECURE=os.getenv("X_APP_SECURE_COOKIE", "0") == "1",
    MAX_CONTENT_LENGTH=64 * 1024,
)
# Every request stays under 8 KB, except starting a task from «روابط التغريدات» (up to 1000 links).
SMALL_REQUEST_BYTES = 8 * 1024

ACCESS_PATH = os.getenv("X_ACCESS_PATH", "desk")
# This copy's version. In users' copies it is the version the owner published from «توزيع البرنامج»
# (g.py writes it into the file it hands out); in the owner's copy it does not change.
APP_VERSION = "1.0"
# In a copy given to a user: the owner's address to take updates from, and that user's key.
# The owner's copy fills both in when it hands the program out; both stay empty in the owner's copy.
UPDATE_SOURCE = ""
UPDATE_KEY = ""
# In a copy given to a user: the owner's content.py («إنشاء محتوى»), packed in by g.py when it hands the
# program out (gzip, then base64), so the user's copy has the page with no file of its own. Empty in the
# owner's copy, which uses content.py beside it.
CONTENT_EMBEDDED = ""
# On users' copies, the posts «إنشاء محتوى» may make in one day (Saudi time). The owner's copy has no limit.
USER_POSTS_PER_DAY = 1
ATTEMPT_WINDOW_SECONDS = 300
MAX_ATTEMPTS_PER_CLIENT = 5
MAX_REPOSTS_REQUEST = 1000
jobs: dict[str, dict] = {}
attempts: dict[str, deque[float]] = defaultdict(deque)
attempts_lock = threading.Lock()
jobs_lock = threading.Lock()
sessions_lock = threading.Lock()
gemini_lock = threading.Lock()
JOB_TTL_SECONDS = 86400
DATA_DIR = Path(__file__).resolve().with_name("data")
CLICK_LOG_PATH = DATA_DIR / "click-log.txt"
_click_log_lock = threading.Lock()


# Each account is kept apart as if it were a copy of the program of its own: its own browser, its own folder
# of data (data/accounts/<its key>/: what its panel showed, its groups, its log), its own tasks. The work of
# a thread is one account's: account_context says which, and its log lines, its groups' ids… go there.
ACCOUNTS_DIR = DATA_DIR / "accounts"
account_context = threading.local()


def current_account() -> str:
    """The account the running work belongs to (its profile key), or "" for the program's own work."""
    return getattr(account_context, "key", "") or ""


def account_dir(key: str) -> Path:
    return ACCOUNTS_DIR / key


def set_account_context(key: str) -> None:
    account_context.key = key or ""
    if os.environ.get("GG_IN_APP") == "1":
        try:
            import ggapp                          # the app's side: what this thread prints is this account's
            ggapp.set_thread_account(key or "")
        except Exception:
            pass


class as_account:
    """with as_account(key): what follows is that account's work (nested uses give back the one before)."""

    def __init__(self, key: str):
        self.key = key or ""
        self.before = ""

    def __enter__(self):
        self.before = current_account()
        set_account_context(self.key)
        return self

    def __exit__(self, *exc):
        set_account_context(self.before)
        return False


def trace_click(message: str) -> None:
    """One line in the account's click log (data/accounts/<key>/click-log.txt; data/click-log.txt for the
    program's own work) and in the app's «السجل», so a failed press can be read afterwards."""
    line = time.strftime("%H:%M:%S ") + str(message).replace("\n", " ")[:500]
    print("نقر: " + line, flush=True)
    key = current_account()
    path = account_dir(key) / "click-log.txt" if key else CLICK_LOG_PATH
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        with _click_log_lock:
            with path.open("a", encoding="utf-8") as handle:
                handle.write(line + "\n")
            if path.stat().st_size > 180_000:
                kept = path.read_text(encoding="utf-8")[-120_000:]
                path.write_text(kept, encoding="utf-8")
    except Exception:
        pass


def trace_page(page, why: str) -> None:
    try:
        snap = page.evaluate(
            """() => {
              const tests = [...document.querySelectorAll("[data-testid]")].slice(0, 40)
                .map((el) => el.getAttribute("data-testid"));
              return {url: location.href, w: innerWidth, h: innerHeight, dpr: window.devicePixelRatio || 1, tests};
            }"""
        )
    except Exception as exc:
        snap = type(exc).__name__ + ": " + str(exc)[:160]
    trace_click(why + " | " + str(snap)[:450])
SESSIONS_PATH = DATA_DIR / "sessions.json"
JOBS_PATH = DATA_DIR / "jobs.json"
GEMINI_PATH = DATA_DIR / "gemini.json"
saved_sessions: list[dict] = []
saved_gemini = {"api_key": "", "model": "gemini-3.5-flash"}
JOB_FIELDS = (
    "owner", "client_id", "created_at", "updated_at", "status", "phase", "kind",
    "collected", "done", "requested", "message", "success",
    "username", "actions", "items", "results", "key_hash", "auth_digest", "account",
)
logging.getLogger("werkzeug").disabled = True

def load_page() -> str:
    external = Path(__file__).with_name("templates").joinpath("index.html")
    if external.is_file():
        return external.read_text(encoding="utf-8")
    return EMBEDDED_PAGE


EMBEDDED_PAGE = r'''<!doctype html>
<html lang="ar" dir="rtl">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
  <title>مراجعة إعادات النشر</title>
  <style>
    @font-face {
      font-family: "IBM Plex Sans Arabic";
      font-style: normal;
      font-weight: 400;
      font-display: swap;
      src: url("/static/fonts/plex-arabic-400.woff2") format("woff2");
      unicode-range: U+0600-06FF, U+0750-077F, U+0870-088E, U+0890-0891, U+0897-08E1, U+08E3-08FF, U+200C-200E, U+2010-2011, U+204F, U+2E41, U+FB50-FDFF, U+FE70-FE74, U+FE76-FEFC;
    }
    @font-face {
      font-family: "IBM Plex Sans Arabic";
      font-style: normal;
      font-weight: 500;
      font-display: swap;
      src: url("/static/fonts/plex-arabic-500.woff2") format("woff2");
      unicode-range: U+0600-06FF, U+0750-077F, U+0870-088E, U+0890-0891, U+0897-08E1, U+08E3-08FF, U+200C-200E, U+2010-2011, U+204F, U+2E41, U+FB50-FDFF, U+FE70-FE74, U+FE76-FEFC;
    }
    @font-face {
      font-family: "IBM Plex Sans Arabic";
      font-style: normal;
      font-weight: 600;
      font-display: swap;
      src: url("/static/fonts/plex-arabic-600.woff2") format("woff2");
      unicode-range: U+0600-06FF, U+0750-077F, U+0870-088E, U+0890-0891, U+0897-08E1, U+08E3-08FF, U+200C-200E, U+2010-2011, U+204F, U+2E41, U+FB50-FDFF, U+FE70-FE74, U+FE76-FEFC;
    }
    @font-face {
      font-family: "IBM Plex Sans Arabic";
      font-style: normal;
      font-weight: 400;
      font-display: swap;
      src: url("/static/fonts/plex-latin-400.woff2") format("woff2");
      unicode-range: U+0000-00FF, U+0131, U+0152-0153, U+02BB-02BC, U+02C6, U+02DA, U+02DC, U+0304, U+0308, U+0329, U+2000-206F, U+20AC, U+2122, U+2191, U+2193, U+2212, U+2215, U+FEFF, U+FFFD;
    }
    @font-face {
      font-family: "IBM Plex Sans Arabic";
      font-style: normal;
      font-weight: 500;
      font-display: swap;
      src: url("/static/fonts/plex-latin-500.woff2") format("woff2");
      unicode-range: U+0000-00FF, U+0131, U+0152-0153, U+02BB-02BC, U+02C6, U+02DA, U+02DC, U+0304, U+0308, U+0329, U+2000-206F, U+20AC, U+2122, U+2191, U+2193, U+2212, U+2215, U+FEFF, U+FFFD;
    }
    @font-face {
      font-family: "IBM Plex Sans Arabic";
      font-style: normal;
      font-weight: 600;
      font-display: swap;
      src: url("/static/fonts/plex-latin-600.woff2") format("woff2");
      unicode-range: U+0000-00FF, U+0131, U+0152-0153, U+02BB-02BC, U+02C6, U+02DA, U+02DC, U+0304, U+0308, U+0329, U+2000-206F, U+20AC, U+2122, U+2191, U+2193, U+2212, U+2215, U+FEFF, U+FFFD;
    }

    :root {
      --paper: #f3f5fa;
      --sheet: #ffffff;
      --ink: #101828;
      --muted: #667085;
      --line: #e4e7ec;
      --pine: #2f5bea;
      --pine-deep: #2447c8;
      --on-pine: #ffffff;
      --clay: #b42318;
      --clay-bg: #fef3f2;
      --ok-bg: #ecfdf3;
      --ok-ink: #067647;
      --shadow: 0 0 0 1px rgba(16, 24, 40, 0.06), 0 1px 2px rgba(16, 24, 40, 0.05), 0 12px 32px rgba(16, 24, 40, 0.06);
      --sans: "IBM Plex Sans Arabic", "Segoe UI", Tahoma, sans-serif;
      color-scheme: light;
    }

    * { box-sizing: border-box; }
    html {
      -webkit-font-smoothing: antialiased;
      -moz-osx-font-smoothing: grayscale;
      -webkit-text-size-adjust: 100%;
      text-size-adjust: 100%;
      font-size: 100%;
    }
    body {
      margin: 0;
      min-height: 100vh;
      min-height: 100dvh;
      background: var(--paper);
      color: var(--ink);
      font-family: var(--sans);
      font-size: 15px;
      line-height: 1.55;
      overflow-x: hidden;
    }
    body::before {
      content: "";
      position: fixed;
      inset: 0 0 auto 0;
      height: 3px;
      background: var(--ink);
    }
    [hidden] { display: none !important; }
    /* Invisible spot in the top-left corner: asks for the password that resets the comment cost. */
    .cost-reset {
      position: absolute;
      top: 0;
      left: 0;
      z-index: 5;
      width: 40px;
      height: 40px;
      padding: 0;
      border: 0;
      background: transparent;
      opacity: 0;
      cursor: default;
      -webkit-tap-highlight-color: transparent;
    }
    button, [role="button"] { cursor: pointer; }
    button:disabled { cursor: wait; }
    :focus-visible { outline: 2px solid rgba(47, 91, 234, 0.4); outline-offset: 2px; }

    .page {
      width: min(480px, 100%);
      margin: 0 auto;
      padding: calc(8px + env(safe-area-inset-top)) 12px calc(12px + env(safe-area-inset-bottom));
    }
    .mast {
      display: flex;
      flex-direction: column;
      align-items: stretch;
      gap: 8px;
    }
    .brand { display: flex; gap: 12px; align-items: center; min-width: 0; }
    .mast-links { margin-inline-start: auto; display: flex; flex-wrap: wrap; justify-content: flex-end; gap: 6px; }
    .mast-links a { display: inline-flex; align-items: center; text-decoration: none; white-space: nowrap; }
    .mark {
      flex: 0 0 auto;
      width: 22px;
      height: 28px;
      border-radius: 3px 7px 7px 3px;
      background: var(--ink);
      position: relative;
    }
    .mark::before {
      content: "";
      position: absolute;
      inset-inline-start: 5px;
      top: 6px;
      bottom: 6px;
      width: 3px;
      border-radius: 2px;
      background: var(--pine);
    }
    .eyebrow {
      margin: 0;
      color: var(--muted);
      font-size: 12px;
      font-weight: 500;
    }
    h1 {
      margin: 0;
      font-size: 17px;
      line-height: 1.2;
      font-weight: 600;
    }
    .counts {
      display: grid;
      grid-template-columns: repeat(4, minmax(0, 1fr));
      gap: 6px;
      margin: 0;
      padding: 0;
      list-style: none;
    }
    .counts li {
      display: flex;
      flex-direction: column;
      align-items: center;
      gap: 2px;
      min-width: 0;
      padding: 5px 2px;
      border-radius: 8px;
      background: var(--sheet);
      box-shadow: inset 0 0 0 1px var(--line);
      color: var(--muted);
      font-size: 11px;
      font-weight: 500;
      text-align: center;
      line-height: 1.2;
    }
    .counts b { color: var(--ink); font-size: 16px; font-weight: 600; font-variant-numeric: tabular-nums; }

    .lede, .block-head p, .choice-copy, .gemini-fields .hint, .footnote { display: none; }
    .sheet {
      margin-top: 8px;
      padding: 2px;
      background: var(--sheet);
      border-radius: 14px;
      box-shadow: var(--shadow);
    }
    .sheet-inner { padding: 8px 10px 10px; }
    .block + .block { margin-top: 8px; padding-top: 8px; border-top: 1px solid var(--line); }
    .sheet h2, .block-head h2 { margin: 0; font-size: 13px; font-weight: 600; }
    label.field-label, .field-label {
      display: block;
      margin: 6px 0 3px;
      font-size: 11px;
      font-weight: 600;
    }
    .hint { margin: 5px 0 0; color: var(--muted); font-size: 12px; line-height: 1.5; }
    /* The comments and their cost, at the top of the page (from the control server, by account; see usage-box). */
    .usage-pill { display: inline-flex; align-items: center; gap: 8px; min-height: 36px; padding: 0 5px 0 12px; border: 1px solid var(--line);
      border-radius: 999px; background: var(--paper); color: var(--ink); font: inherit; font-size: 12.5px; font-weight: 600; cursor: pointer; }
    .usage-pill:active { transform: translateY(1px); }
    /* Brown at $0; the page turns it redder as the cost grows, fully red from $10. */
    .usage-cost { padding: 4px 9px; border-radius: 999px; background: rgb(139, 69, 19); color: #fff; font-size: 12px; font-weight: 700; }
    .usage-sheet { width: min(420px, 100%); max-height: calc(100dvh - 32px); overflow: auto; padding: 14px 14px 12px; border-radius: 16px;
      background: var(--sheet); color: var(--ink); box-shadow: 0 24px 60px rgba(2, 6, 23, 0.35); }
    .usage-head { display: flex; align-items: center; gap: 10px; }
    .usage-head b { flex: 1; font-size: 16px; }
    .usage-x { width: 32px; height: 32px; border: 0; border-radius: 8px; background: transparent; color: var(--muted); font: inherit; font-size: 22px; line-height: 1; }
    .usage-note { margin: 6px 0 10px; color: var(--muted); font-size: 12px; line-height: 1.6; }
    .usage-table { width: 100%; border-collapse: collapse; font-size: 13px; }
    .usage-table th, .usage-table td { padding: 8px 6px; text-align: start; border-bottom: 1px solid var(--line); }
    .usage-table th { color: var(--muted); font-size: 12px; font-weight: 600; }
    .usage-table tfoot th { color: var(--ink); font-size: 13px; border-bottom: 0; border-top: 2px solid var(--line); }
    .usage-table .num { text-align: end; font-variant-numeric: tabular-nums; }
    .usage-table .who { font-weight: 600; }
    .usage-table .empty { color: var(--muted); text-align: center; }
    .usage-foot { display: flex; gap: 8px; margin-top: 12px; }
    .usage-foot .btn { flex: 1; }
    /* «مساعدة»: describe a problem to the program's owner, with pictures or a short video. */
    .help-sheet { width: min(460px, 100%); }
    .help-label { display: block; margin: 2px 0 6px; font-size: 13px; font-weight: 600; }
    .help-text { width: 100%; min-height: 120px; padding: 10px 12px; border: 1px solid var(--line); border-radius: 12px; background: var(--paper);
      color: var(--ink); font: inherit; font-size: 15px; line-height: 1.7; resize: vertical; }
    .help-text:focus { outline: none; border-color: var(--pine); box-shadow: 0 0 0 3px rgba(47, 91, 234, 0.16); }
    .help-attach { width: 100%; margin-top: 10px; }
    .help-list { list-style: none; margin: 10px 0 0; padding: 0; display: grid; gap: 8px; }
    .help-list li { display: flex; align-items: center; gap: 10px; padding: 6px; border: 1px solid var(--line); border-radius: 12px; background: var(--paper); }
    .help-list .thumb { width: 46px; height: 46px; flex: none; border-radius: 9px; object-fit: cover; background: var(--line); display: grid; place-items: center; font-size: 20px; }
    .help-list .name { flex: 1; min-width: 0; font-size: 13px; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
    .help-list .name small { display: block; color: var(--muted); font-size: 12px; }
    .help-list .bar { height: 3px; margin-top: 4px; border-radius: 9px; background: var(--line); overflow: hidden; }
    .help-list .bar i { display: block; height: 100%; width: 0; background: var(--pine); transition: width .2s; }
    .help-status { margin: 10px 0 0; padding: 9px 12px; border-radius: 10px; font-size: 13px; background: var(--paper); }
    .help-status.is-bad { color: var(--clay); background: var(--clay-bg); }
    .help-status.is-ok { color: var(--ok-ink); background: var(--ok-bg); }
    /* «تسجيل الدخول»: the steps shown before the browser opens. */
    .guide-steps { list-style: none; margin: 0; padding: 0; display: grid; gap: 10px; }
    .guide-steps li { display: flex; align-items: flex-start; gap: 10px; padding: 10px; border-radius: 12px; background: var(--paper); }
    .guide-steps b { flex: 0 0 28px; height: 28px; display: grid; place-items: center; border-radius: 50%; background: var(--pine); color: var(--on-pine); font-size: 14px; }
    .guide-steps strong { display: block; font-size: 14px; font-weight: 700; line-height: 1.5; }
    .guide-steps span { display: block; margin-top: 2px; color: var(--muted); font-size: 12.5px; line-height: 1.6; }
    .guide-sheet .usage-foot .btn-pine { flex: 2; }
    input[type="password"], input[type="text"], input[type="number"] {
      width: 100%;
      min-height: 32px;
      height: 32px;
      padding: 0 8px;
      border: 1px solid var(--line);
      border-radius: 8px;
      background: var(--sheet);
      color: var(--ink);
      font: inherit;
      font-size: 16px;
    }
    input:focus { outline: none; border-color: var(--pine); box-shadow: 0 0 0 3px rgba(47, 91, 234, 0.16); }
    #auth_token, #stop-tweet, #gemini-model, #claude-model { direction: ltr; text-align: start; }
    #auth_token[readonly], #gemini-key[readonly], #gemini-model[readonly] { color: var(--muted); }
    #account-name { font-weight: 600; }
    .token-row { display: flex; align-items: stretch; gap: 6px; }
    .token-row input { flex: 1; min-width: 0; }
    .btn {
      min-height: 32px;
      height: 32px;
      border: 0;
      border-radius: 8px;
      padding: 0 8px;
      background: var(--ink);
      color: var(--sheet);
      font: inherit;
      font-size: 12px;
      font-weight: 600;
      white-space: nowrap;
    }
    .btn:disabled { opacity: 0.5; }
    .btn-pine { background: var(--pine); color: var(--on-pine); }
    .btn-pine:hover:not(:disabled) { background: var(--pine-deep); }
    .btn-ghost {
      background: var(--sheet);
      color: var(--ink);
      box-shadow: inset 0 0 0 1px var(--line);
    }
    .btn-ghost:hover:not(:disabled) { background: var(--paper); }
    .wait-groups {
      display: inline-flex;
      align-items: center;
      gap: 6px;
      height: 32px;
      padding: 0 8px;
      white-space: nowrap;
      font-size: 12px;
      font-weight: 600;
    }
    .wait-groups input[type="checkbox"] { width: 15px; height: 15px; accent-color: var(--pine); }
    input.wait-sec {
      width: 52px;
      min-height: 28px;
      height: 28px;
      padding: 0 4px;
      text-align: center;
      direction: ltr;
      font-size: 14px;
    }
    /* The three options on one line; on a screen too narrow for it, an option moves down whole. */
    .options {
      display: flex;
      flex-wrap: wrap;
      align-items: center;
      gap: 6px 12px;
      margin: 8px 0;
      padding: 8px;
      border-radius: 12px;
      background: var(--paper);
      box-shadow: inset 0 0 0 1px var(--line);
      font-size: 12px;
      font-weight: 600;
    }
    .options input[type="checkbox"] { width: 15px; height: 15px; margin: 0; accent-color: var(--pine); }
    .options label { cursor: pointer; white-space: nowrap; }
    .opt { display: inline-flex; align-items: center; gap: 3px; white-space: nowrap; }
    .opt input.wait-sec { width: 36px; }
    /* No up/down arrows in these small boxes: they would cover the number. */
    .opt input[type="number"] { -moz-appearance: textfield; appearance: textfield; }
    .opt input[type="number"]::-webkit-inner-spin-button,
    .opt input[type="number"]::-webkit-outer-spin-button { -webkit-appearance: none; margin: 0; }
    .btn-wide { width: 100%; margin-top: 8px; min-height: 34px; height: 34px; }
    .stop-row { display: grid; grid-template-columns: minmax(0, 1fr); gap: 6px; align-items: center; margin-top: 6px; }
    /* «روابط التغريدات»: at the other end of the groups row; on (pine) while the links box shows. */
    .links-button { margin-inline-start: auto; }
    .groups-row { flex-wrap: wrap; row-gap: 6px; }     /* a very narrow screen: the button goes under, not off the screen */
    .links-button[aria-pressed="true"] { background: var(--pine); color: var(--on-pine); box-shadow: none; }
    .links-button[aria-pressed="true"]:hover:not(:disabled) { background: var(--pine-deep); }
    .links-box { margin-top: 10px; }
    #tweet-links {
      display: block;
      width: 100%;
      min-height: 120px;
      max-height: 50vh;
      padding: 8px;
      border: 1px solid var(--line);
      border-radius: 8px;
      background: var(--sheet);
      color: var(--ink);
      font: inherit;
      font-size: 16px;
      line-height: 1.5;
      resize: vertical;
      direction: ltr;
      text-align: left;
    }
    #tweet-links:placeholder-shown { direction: rtl; text-align: right; }
    #tweet-links:focus { outline: none; border-color: var(--pine); box-shadow: 0 0 0 3px rgba(47, 91, 234, 0.16); }
    .links-foot { display: flex; align-items: center; gap: 8px; margin-top: 6px; color: var(--muted); font-size: 12px; font-weight: 600; }
    .links-foot .btn { margin-inline-start: auto; min-height: 28px; height: 28px; }
    #links-count.is-bad { color: var(--clay); }
    #group-box {
      margin-top: 10px;
      margin-bottom: 14px;
      padding: 8px 10px 10px;
      border-radius: 14px;
      background: var(--paper);
      box-shadow: inset 0 0 0 1px var(--line);
    }
    /* Three names on top of each other, filling column after column, scrolled sideways. */
    #group-list {
      display: grid;
      grid-auto-flow: column;
      grid-template-rows: repeat(3, auto);
      grid-auto-columns: max-content;
      justify-content: start;
      overflow-x: auto;
      overflow-y: hidden;
      gap: 6px;
      margin-top: 6px;
      padding-bottom: 2px;
    }
    #group-list .pick {
      flex: none;
      min-height: 30px;
      height: 30px;
      border-radius: 999px;
      padding: 0 10px;
      font-size: 12px;
      white-space: nowrap;
      background: var(--sheet);
    }
    #group-list .pick .who { max-width: none; overflow: visible; }
    /* Each name as wide as its column, so the columns line up. */
    #group-list li { display: flex; }
    #group-list .pick { width: 100%; align-items: center; }
    .choices { display: grid; grid-template-columns: 1fr 1fr; gap: 4px; margin-top: 6px; }
    .gemini-fields {
      display: grid;
      grid-template-columns: 1.3fr 0.7fr;
      gap: 6px;
      margin-top: 6px;
      padding: 0;
      background: transparent;
    }
    .gemini-fields[hidden] { display: none !important; }
    .reply-voice { display: flex; flex-wrap: wrap; align-items: center; gap: 6px 8px; margin-top: 6px; }
    .reply-voice[hidden] { display: none !important; }
    .engine-note { flex-basis: 100%; color: var(--muted); font-size: 12px; line-height: 1.5; }
    .engine-note[hidden] { display: none !important; }
    .voice-label { font-size: 12px; font-weight: 600; color: var(--muted); }
    .voices { display: flex; gap: 4px; }
    /* Smaller than the actions above them. */
    .voices .choice { min-height: 26px; padding: 0 7px; gap: 4px; border-radius: 7px; }
    .voices .choice input { width: 13px; height: 13px; }
    .voices .choice-title { font-size: 12px; }
    #show-gemini, #show-claude { height: 26px; min-height: 26px; padding: 0 7px; }
    #claude-fields { grid-template-columns: 1fr 1fr; }   /* (room for the whole model name, on a phone too) */
    .claude-actions { grid-column: 1 / -1; display: flex; flex-wrap: wrap; align-items: center; gap: 6px; }
    .claude-now { color: var(--muted); font-size: 12px; line-height: 1.5; }
    .gemini-fields .field-label { margin-top: 0; }
    .gemini-edit { height: 32px; min-height: 32px; padding: 0 8px; font-size: 12px; }
    .gemini-owner { grid-column: 1 / -1; margin: 0; color: var(--muted); font-size: 12px; }
    .choice {
      display: flex;
      gap: 6px;
      align-items: center;
      margin: 0;
      padding: 0 8px;
      min-height: 32px;
      border-radius: 8px;
      background: var(--sheet);
      box-shadow: inset 0 0 0 1px var(--line);
      cursor: pointer;
    }
    .choice:has(input:focus-visible) { outline: 2px solid rgba(47, 91, 234, 0.4); outline-offset: 2px; }
    .choice input { width: 16px; height: 16px; margin: 0; flex: 0 0 auto; accent-color: var(--pine); }
    .choice-title { display: block; font-weight: 600; font-size: 13px; line-height: 1.2; }
    .choice:has(input:checked) {
      background: var(--ok-bg);
      box-shadow: inset 0 0 0 1.5px var(--pine);
    }
    .notice {
      margin-top: 12px;
      padding: 10px 12px;
      border-radius: 12px;
      font-size: 13px;
      line-height: 1.55;
    }
    .notice.is-ok { color: var(--ok-ink); background: var(--ok-bg); }
    .notice.is-bad { color: var(--clay); background: var(--clay-bg); }
    .task-card { margin-top: 8px; padding: 8px; border: 1px solid var(--line); border-radius: 12px; background: var(--sheet-2, transparent); }
    .task-card h3 { margin: 0; font-size: 13px; font-weight: 600; }
    .task-card p { margin: 3px 0 0; color: var(--muted); font-size: 12px; }
    .task-card .meter { margin-top: 8px; }
    .task-actions { display: flex; flex-wrap: wrap; column-gap: 6px; }
    .task-actions .btn { margin-top: 6px; }
    .progress-top h2 { margin: 0; font-size: 16px; font-weight: 600; text-wrap: balance; }
    .progress-top p { margin: 3px 0 0; color: var(--muted); font-size: 12px; }
    .progress-figure { text-align: end; flex: 0 0 auto; }
    .figure {
      font-size: 28px;
      font-weight: 600;
      letter-spacing: -0.04em;
      line-height: 1;
      font-variant-numeric: tabular-nums;
    }
    .denom { color: var(--muted); font-size: 13px; font-variant-numeric: tabular-nums; }
    .meter {
      height: 4px;
      margin-top: 12px;
      border-radius: 99px;
      background: var(--line);
      overflow: hidden;
    }
    .meter > span {
      display: block;
      height: 100%;
      width: 0;
      background: var(--pine);
      transform-origin: 100% 50%;
      transition: width 240ms ease-out;
    }
    .meter.is-indeterminate > span { width: 100%; animation: meter-pulse 1.15s ease-in-out infinite; }
    @keyframes meter-pulse {
      0%, 100% { transform: scaleX(0.18); opacity: 0.55; }
      50% { transform: scaleX(1); opacity: 1; }
    }
    .progress-note { margin: 8px 0 0; color: var(--muted); font-size: 12px; line-height: 1.5; }
    .stats { display: grid; grid-template-columns: repeat(3, minmax(0, 1fr)); gap: 6px; margin-top: 12px; }
    .stat { padding: 10px 6px; border-radius: 12px; background: var(--paper); text-align: center; }
    .stat b {
      display: block;
      font-size: 20px;
      font-weight: 600;
      letter-spacing: -0.03em;
      font-variant-numeric: tabular-nums;
      line-height: 1.1;
    }
    .stat span { display: block; margin-top: 2px; color: var(--muted); font-size: 11px; line-height: 1.3; }
    .post-list {
      max-height: min(52vh, 460px);
      margin: 12px 0 0;
      padding: 0;
      overflow: auto;
      list-style: none;
      border-block: 1px solid var(--line);
      -webkit-overflow-scrolling: touch;
    }
    .post-list li { padding: 10px 0; border-bottom: 1px solid var(--line); }
    .post-list li:last-child { border-bottom: 0; }
    .post-top { display: flex; align-items: flex-start; gap: 8px; }
    .idx {
      flex: 0 0 auto;
      min-width: 1.2rem;
      padding-top: 1px;
      color: var(--muted);
      font-size: 12px;
      font-variant-numeric: tabular-nums;
    }
    .post-list a {
      color: var(--pine-deep);
      font-weight: 500;
      font-size: 13px;
      line-height: 1.45;
      overflow-wrap: anywhere;
    }
    .excerpt { margin: 6px 0 0; color: var(--ink); font-size: 13px; line-height: 1.5; }
    .pills { display: flex; flex-wrap: wrap; gap: 4px; margin-top: 8px; }
    .pill {
      display: inline-flex;
      align-items: center;
      max-width: 100%;
      min-height: 22px;
      padding: 2px 8px;
      border-radius: 999px;
      font-size: 11px;
      font-weight: 500;
      line-height: 1.35;
      white-space: normal;
      overflow-wrap: anywhere;
      text-align: start;
    }
    .pill.is-will { color: var(--ok-ink); background: var(--ok-bg); }
    .pill.is-skip { color: var(--muted); background: var(--paper); }
    .pill.is-fail { color: var(--clay); background: var(--clay-bg); }
    .session-account { margin: 8px 0 0; font-weight: 600; font-size: 14px; color: var(--ok-ink); }
    .saved-sessions { margin-top: 12px; }
    .saved-list { list-style: none; margin: 8px 0 0; padding: 0; display: flex; flex-direction: column; gap: 6px; }
    .saved-session { display: flex; gap: 6px; align-items: stretch; }
    .pick {
      flex: 1;
      min-width: 0;
      min-height: 40px;
      display: flex;
      flex-direction: column;
      align-items: flex-start;
      justify-content: center;
      gap: 1px;
      padding: 6px 10px;
      border: 0;
      border-radius: 10px;
      background: var(--paper);
      color: var(--ink);
      font: inherit;
      font-size: 13px;
      text-align: start;
      box-shadow: inset 0 0 0 1px var(--line);
    }
    .pick.is-on { background: var(--ok-bg); box-shadow: inset 0 0 0 1.5px var(--pine); }
    .pick .who { font-weight: 600; max-width: 100%; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
    .pick .meta { color: var(--muted); font-size: 11px; direction: ltr; max-width: 100%; overflow: hidden; text-overflow: ellipsis; }
    .drop {
      flex: 0 0 auto;
      min-height: 40px;
      padding: 0 10px;
      border: 0;
      border-radius: 10px;
      background: transparent;
      color: var(--clay);
      font: inherit;
      font-size: 12px;
      font-weight: 600;
      box-shadow: inset 0 0 0 1px var(--line);
    }
    /* «الحسابات»: the side list of saved accounts (up to three) and «إضافة حساب». Each account's
       own task shows a dot while it is working. */
    .accounts-bar { display: flex; flex-wrap: wrap; gap: 8px; margin-top: 2px; }
    /* Inside the app the accounts live in the app's own side drawer, so the page's own block is hidden. */
    body[data-app="1"] .accounts-block { display: none; }
    /* «اختبار قدرة الهاتف»: a system console over the panel; its text is typed a letter at a time. */
    .pc-backdrop { position: fixed; inset: 0; z-index: 50; display: grid; place-items: center; padding: 16px; background: rgba(2, 6, 23, 0.6); }
    .pc-term { width: min(440px, 100%); max-height: calc(100dvh - 32px); display: flex; flex-direction: column; overflow: hidden;
      border-radius: 14px; background: #0b1220; border: 1px solid #1f2a44; box-shadow: 0 24px 60px rgba(2, 6, 23, 0.55); }
    .pc-bar { display: flex; align-items: center; gap: 10px; padding: 9px 12px; background: #111a2e; border-bottom: 1px solid #1f2a44; color: #c7d2fe; }
    .pc-bar b { flex: 1; font-size: 13px; font-weight: 600; letter-spacing: 0.01em; }
    .pc-dots { display: inline-flex; gap: 6px; direction: ltr; }
    .pc-dots i { width: 10px; height: 10px; border-radius: 50%; background: #ff5f57; }
    .pc-dots i:nth-child(2) { background: #febc2e; }
    .pc-dots i:nth-child(3) { background: #28c840; }
    .pc-x { width: 28px; height: 28px; border: 0; border-radius: 8px; background: transparent; color: #8b9ab8; font: inherit; font-size: 20px; line-height: 1; }
    .pc-screen { flex: 1; min-height: 300px; overflow: auto; padding: 14px 14px 18px; cursor: pointer;
      /* (monospace fonts with no Arabic first: digits and Latin text are monospaced, Arabic keeps a proper Arabic font) */
      font-family: "Liberation Mono", "Noto Sans Mono", "Droid Sans Mono", "Cutive Mono", "SFMono-Regular", Menlo, Consolas, "Courier New",
        "IBM Plex Sans Arabic", "Segoe UI", Tahoma, sans-serif;
      font-size: 13px; line-height: 1.75; color: #d1fae5; background:
      repeating-linear-gradient(0deg, rgba(255, 255, 255, 0.018) 0 1px, transparent 1px 3px), #0b1220; }
    .pc-line { white-space: pre-wrap; overflow-wrap: anywhere; }
    .pc-line .pc-p { color: #5eead4; }
    .pc-line.is-dim { color: #7c8aa5; padding-inline-start: 1.4em; }
    .pc-line.is-head { color: #a5b4fc; }
    .pc-tag { font-weight: 700; white-space: nowrap; }
    .pc-tag.is-ok { color: #4ade80; }
    .pc-tag.is-warn { color: #fbbf24; }
    .pc-tag.is-bad { color: #f87171; }
    .pc-cursor { display: inline-block; width: 0.55em; height: 1.05em; margin-inline-start: 2px; vertical-align: -0.15em;
      background: #4ade80; animation: pc-blink 1s steps(1) infinite; }
    @keyframes pc-blink { 50% { opacity: 0; } }
    .pc-final { display: flex; align-items: center; gap: 12px; margin: 10px 0 4px; padding: 10px 12px; border: 1px dashed #2f3d5c; border-radius: 8px; color: #86efac; }
    .pc-final b { flex: 0 0 auto; font-size: 30px; line-height: 1; color: #4ade80; }
    .pc-final.is-mid, .pc-final.is-mid b { color: #fbbf24; }
    .pc-final.is-low, .pc-final.is-low b { color: #f87171; }
    .pc-final span { font-size: 14px; font-weight: 700; line-height: 1.6; }
    .pc-actions { display: flex; gap: 8px; padding: 10px 12px; border-top: 1px solid #1f2a44; background: #0b1220; }
    .pc-btn { flex: 1; min-height: 38px; border: 1px solid #2f3d5c; border-radius: 10px; background: #111a2e; color: #c7d2fe; font: inherit; font-size: 13px; font-weight: 600; }
    .pc-btn:active { transform: translateY(1px); }
    .acct-chip {
      position: relative;
      flex: 1 1 auto;
      min-width: 120px;
      min-height: 46px;
      display: flex;
      align-items: center;
      gap: 8px;
      padding: 8px 12px;
      padding-inline-end: 34px;
      border: 0;
      border-radius: 12px;
      background: var(--paper);
      color: var(--ink);
      font: inherit;
      font-size: 13px;
      text-align: start;
      box-shadow: inset 0 0 0 1px var(--line);
    }
    .acct-chip.is-on { background: var(--ok-bg); box-shadow: inset 0 0 0 1.5px var(--pine); }
    .acct-chip .acct-who { flex: 1; min-width: 0; font-weight: 600; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; direction: ltr; text-align: start; }
    .acct-chip .acct-dot { flex: 0 0 auto; width: 9px; height: 9px; border-radius: 50%; background: var(--line); }
    .acct-chip.is-running .acct-dot { background: var(--ok-ink); box-shadow: 0 0 0 3px rgba(6, 118, 71, 0.18); animation: acct-pulse 1.3s ease-in-out infinite; }
    @keyframes acct-pulse { 0%, 100% { opacity: 1; } 50% { opacity: 0.45; } }
    .acct-x {
      position: absolute;
      inset-inline-end: 6px;
      top: 50%;
      transform: translateY(-50%);
      display: grid;
      place-items: center;
      width: 24px;
      height: 24px;
      border: 0;
      border-radius: 8px;
      background: transparent;
      color: var(--muted);
      font: inherit;
      font-size: 17px;
      line-height: 1;
      cursor: pointer;
    }
    .acct-x:hover { background: var(--clay-bg); color: var(--clay); }
    .acct-add {
      flex: 0 0 auto;
      min-height: 46px;
      display: inline-flex;
      align-items: center;
      gap: 6px;
      padding: 8px 14px;
      border: 0;
      border-radius: 12px;
      background: var(--sheet);
      color: var(--pine);
      font: inherit;
      font-size: 13px;
      font-weight: 700;
      box-shadow: inset 0 0 0 1.5px var(--pine);
      cursor: pointer;
    }
    .acct-add:disabled { color: var(--muted); box-shadow: inset 0 0 0 1px var(--line); cursor: default; }
    .acct-empty { margin: 0; color: var(--muted); font-size: 12px; align-self: center; }
    @media (min-width: 760px) {
      .accounts-bar { flex-direction: column; align-items: stretch; }
      .acct-chip, .acct-add { flex: 0 0 auto; }
    }
    .update-bar {
      display: flex;
      align-items: center;
      justify-content: space-between;
      gap: 8px;
      margin-top: 10px;
      padding: 8px 10px;
      border-radius: 12px;
      color: var(--ok-ink);
      background: var(--ok-bg);
      font-size: 13px;
      font-weight: 600;
    }
    .update-bar .btn { flex: 0 0 auto; }
    .version-line { display: flex; flex-wrap: wrap; justify-content: center; gap: 4px 10px; margin: 14px 0 4px; color: var(--muted); font-size: 12px; }
    .link-button { border: 0; padding: 0; background: none; color: var(--pine); font: inherit; font-weight: 600; text-decoration: underline; cursor: pointer; }

    /* ───── 7.2: a solid, consistent finish — one radius scale, flat fills, crisp 1px borders, no glows ───── */
    :root { --r-card: 16px; --r-ctl: 10px; --line-2: #d0d5dd; --tile: #f6f7fb; --pine-soft: #eef2ff; --ok-line: #abefc6; --clay-line: #fecdca;
      --shadow: 0 1px 2px rgba(16, 24, 40, 0.06); }
    body::before { height: 3px; background: var(--pine); }
    .page { width: min(520px, 100%); padding: calc(12px + env(safe-area-inset-top)) 14px calc(20px + env(safe-area-inset-bottom)); }
    /* the head: brand, then the links in an even grid */
    .mast { gap: 12px; padding: 14px; border: 1px solid var(--line); border-radius: var(--r-card); background: var(--sheet); box-shadow: var(--shadow); }
    .mark { width: 40px; height: 40px; border-radius: 11px; background: var(--pine); box-shadow: none; }
    .mark::before { inset-inline-start: 12px; top: 12px; bottom: 12px; width: 16px; border-radius: 3px; background: #ffffff; }
    .eyebrow { font-size: 11.5px; font-weight: 600; }
    h1 { font-size: 18px; font-weight: 700; letter-spacing: -0.01em; }
    .brand { flex-wrap: wrap; }
    .mast-links { flex-basis: 100%; display: grid; grid-template-columns: repeat(2, minmax(0, 1fr)); gap: 8px; margin-inline-start: 0; }
    .mast-links > :last-child:nth-child(odd) { grid-column: 1 / -1; }
    .mast-links .btn { min-height: 40px; height: 40px; padding: 0 10px; justify-content: center; font-size: 12.5px; }
    .usage-pill { min-height: 40px; height: 40px; justify-content: space-between; padding: 0 5px 0 12px; border: 1px solid var(--line-2);
      border-radius: var(--r-ctl); background: var(--sheet); font-size: 12.5px; font-weight: 700; }
    .usage-cost { display: inline-flex; align-items: center; height: 28px; padding: 0 9px; border-radius: 7px; }
    .counts { gap: 8px; }
    .counts li { gap: 4px; padding: 10px 4px 9px; border: 1px solid var(--line); border-radius: 12px; background: var(--tile); box-shadow: none; font-size: 11.5px; font-weight: 600; }
    .counts b { color: var(--ink); font-size: 20px; font-weight: 700; }
    /* the sheets and their sections */
    .sheet { margin-top: 12px; padding: 0; border: 1px solid var(--line); border-radius: var(--r-card); box-shadow: var(--shadow); }
    .sheet-inner { padding: 14px; }
    .block + .block { margin-top: 16px; padding-top: 16px; border-top: 1px solid var(--line); }
    body[data-app="1"] .accounts-block + .block { margin-top: 0; padding-top: 0; border-top: 0; }   /* (the accounts are in the app's drawer: no lone line at the top) */
    .sheet h2, .block-head h2 { display: flex; align-items: center; gap: 8px; margin-bottom: 10px; font-size: 15px; font-weight: 700; }
    .sheet h2::before, .block-head h2::before { content: ""; flex: 0 0 auto; width: 6px; height: 16px; border-radius: 2px; background: var(--pine); }
    /* the controls: all 40 high, the same radius, a real 1px border */
    input[type="password"], input[type="text"], input[type="number"] { min-height: 40px; height: 40px; padding: 0 12px; border: 1px solid var(--line-2); border-radius: var(--r-ctl); background: var(--sheet);
      transition: border-color 0.12s, box-shadow 0.12s; }
    input:focus { border-color: var(--pine); box-shadow: 0 0 0 2px rgba(47, 91, 234, 0.2); }
    input.wait-sec { min-height: 32px; height: 32px; padding: 0 4px; border-radius: 8px; }
    #tweet-links { border: 1px solid var(--line-2); border-radius: var(--r-ctl); }
    #tweet-links:focus { box-shadow: 0 0 0 2px rgba(47, 91, 234, 0.2); }
    .btn { min-height: 40px; height: 40px; padding: 0 14px; border: 1px solid transparent; border-radius: var(--r-ctl); font-size: 13px; font-weight: 700;
      transition: background 0.12s, border-color 0.12s, transform 0.05s; }
    .btn:active:not(:disabled) { transform: translateY(1px); }
    .btn-pine { background: var(--pine); border-color: var(--pine-deep); color: var(--on-pine); box-shadow: none; }
    .btn-pine:hover:not(:disabled) { background: var(--pine-deep); }
    .btn-ghost { background: var(--sheet); border-color: var(--line-2); box-shadow: none; }
    .btn-ghost:hover:not(:disabled) { background: var(--tile); }
    .btn-wide { min-height: 48px; height: 48px; margin-top: 14px; border-radius: 12px; font-size: 15px; }
    .links-button[aria-pressed="true"] { border-color: var(--pine-deep); }
    .link-button { color: var(--pine-deep); }
    /* «الجلسة»: the name on its own line, the buttons in one even row under it */
    .token-row { gap: 8px; flex-wrap: wrap; }
    .token-row > input { flex: 1 1 140px; }
    #session-block .token-row { display: grid; grid-template-columns: repeat(3, minmax(0, 1fr)); gap: 8px; }
    body:not([data-app="1"]) #session-block .token-row { grid-template-columns: repeat(2, minmax(0, 1fr)); }
    #session-block .token-row > input { grid-column: 1 / -1; }
    #session-block .token-row .btn { padding: 0 6px; }
    /* «القروب»: the groups button and the links button on one row, the wait under them */
    .groups-row { display: grid; grid-template-columns: minmax(0, 1fr) auto; grid-auto-flow: dense; gap: 8px; align-items: center; }
    .groups-row .btn { padding: 0 12px; }
    .links-button { margin-inline-start: 0; }
    .wait-groups { grid-column: 1 / -1; justify-content: flex-start; height: 40px; gap: 6px; padding: 0 10px; border: 1px solid var(--line-2); border-radius: var(--r-ctl); background: var(--sheet); }
    .wait-groups input[type="checkbox"], .options input[type="checkbox"] { flex: 0 0 auto; width: 17px; height: 17px; }
    .wait-groups input.wait-sec { flex: 0 0 48px; width: 48px; min-width: 48px; }
    .opt input.wait-sec { width: 44px; }
    .options { gap: 8px 14px; margin: 10px 0; padding: 10px 12px; border: 1px solid var(--line); background: var(--tile); box-shadow: none; }
    #group-box { margin-top: 10px; border: 1px solid var(--line); border-radius: 12px; background: var(--tile); box-shadow: none; }
    .pick { border: 1px solid var(--line-2); border-radius: var(--r-ctl); box-shadow: none; }
    .pick.is-on { background: var(--pine-soft); border-color: var(--pine); box-shadow: inset 0 0 0 1px var(--pine); }
    #group-list .pick { border-radius: 999px; }
    .drop { border: 1px solid var(--line-2); box-shadow: none; }
    .stop-row { margin-top: 10px; }
    /* «الإجراءات» */
    .choices { gap: 8px; margin-top: 4px; }
    .choice { min-height: 46px; padding: 6px 12px; gap: 10px; border: 1px solid var(--line-2); border-radius: 12px; box-shadow: none; transition: background 0.12s, border-color 0.12s; }
    .choice:has(input:checked) { background: var(--pine-soft); border-color: var(--pine); box-shadow: inset 0 0 0 1px var(--pine); }
    .choice input { width: 18px; height: 18px; }
    .voices .choice { min-height: 32px; padding: 0 10px; border-radius: 9px; }
    #show-gemini, #show-claude, .gemini-edit, .links-foot .btn { min-height: 32px; height: 32px; }
    /* the notices and the update bar */
    .notice { padding: 11px 14px; border: 1px solid transparent; font-weight: 600; box-shadow: none; }
    .notice.is-ok { border-color: var(--ok-line); }
    .notice.is-bad { border-color: var(--clay-line); }
    .update-bar { padding: 10px 12px; border: 1px solid var(--ok-line); }
    /* the tasks */
    #task-list { max-height: min(42vh, 360px); overflow-y: auto; -webkit-overflow-scrolling: touch; overscroll-behavior: contain; }
    .task-card { margin-top: 10px; padding: 12px; border: 1px solid var(--line); border-radius: 12px; background: var(--sheet); }
    .task-card h3 { font-size: 14px; font-weight: 700; }
    .task-card .progress-top { display: flex; align-items: flex-start; justify-content: space-between; gap: 10px; }
    .task-card .task-phase { display: inline-block; margin-top: 6px; padding: 1px 8px; border: 1px solid var(--line); border-radius: 6px; background: var(--tile); color: var(--ink); font-size: 11.5px; font-weight: 600; }
    .task-card .task-count { flex: 0 0 auto; font-size: 22px; font-weight: 700; line-height: 1.1; font-variant-numeric: tabular-nums; }
    .task-actions .btn { min-height: 36px; height: 36px; }
    .meter { height: 6px; background: var(--line); }
    .meter > span { background: var(--pine); }
    /* the results */
    .stat { border: 1px solid var(--line); background: var(--tile); box-shadow: none; }
    .stat b { font-size: 22px; font-weight: 700; }
    .post-list a { color: var(--pine-deep); font-weight: 600; }
    .pill { border: 1px solid transparent; font-weight: 600; }
    .pill.is-will { border-color: var(--ok-line); }
    .pill.is-skip { border-color: var(--line); }
    .pill.is-fail { border-color: var(--clay-line); }
    /* the sheets that open over the page */
    .usage-sheet { border: 1px solid var(--line); border-radius: var(--r-card); }
    .guide-steps li { border: 1px solid var(--line); background: var(--tile); }
    .version-line { margin-top: 18px; }

    @media (min-width: 760px) {
      body { font-size: 15px; }
      .page {
        width: min(760px, calc(100% - 48px));
        padding-top: 36px;
      }
      .mast { flex-direction: row; justify-content: space-between; align-items: flex-end; gap: 24px; }
      .counts { min-width: 340px; }
      h1 { font-size: 28px; }
      .lede { font-size: 14px; max-width: 62ch; }
      .sheet { border-radius: 18px; padding: 6px; }
      .sheet-inner { padding: 18px 18px 20px; }
      .choices { grid-template-columns: repeat(3, minmax(0, 1fr)); }
      .figure { font-size: 40px; }
    }
    @media (prefers-reduced-motion: reduce) {
      *, *::before, *::after {
        animation: none !important;
        transition: none !important;
      }
    }
  </style>
</head>
<body{% if in_app %} data-app="1"{% endif %}>
  {% if owner_copy %}<button id="cost-reset" class="cost-reset" type="button" tabindex="-1" aria-hidden="true"></button>{% endif %}
  <main class="page">
    <header class="mast">
      <div class="brand">
        <span class="mark" aria-hidden="true"></span>
        <div>
          <p class="eyebrow">من قروب الدردشة</p>
          <h1>تنفيذ على تغريدات القروب</h1>
        </div>
        <div class="mast-links">
          {% if not tweets_in_content %}<a class="btn btn-ghost" href="{{ api_root }}/tweets">عرض التغريدات</a>{% endif %}
          {% if content_ready %}<a class="btn btn-ghost" href="{{ api_root }}/content">إنشاء محتوى</a>{% endif %}
          <button id="usage-pill" class="usage-pill" type="button" aria-haspopup="dialog" title="التعليقات والتكلفة لكل حساب">
            <span id="usage-count">التعليقات (0)</span>
            <bdi id="usage-cost" class="usage-cost" dir="ltr">$0.00</bdi>
          </button>
          <button id="phone-check" class="btn btn-ghost" type="button">اختبار قدرة الهاتف</button>
          {% if control_on %}<button id="help-open" class="btn btn-ghost help-open" type="button" aria-haspopup="dialog">؟ مساعدة</button>{% endif %}
        </div>
      </div>
      <ol class="counts" aria-label="الإجراءات الناجحة">
        <li>الرتويت <b id="count-repost">0</b></li>
        <li>الإعجاب <b id="count-like">0</b></li>
        <li>المرجعية <b id="count-bookmark">0</b></li>
        <li>التعليقات <b id="count-comment">0</b></li>
      </ol>
    </header>
    <p class="lede">يُفتح تبويب إعادات النشر ويُمرَّر حتى يكتمل العدد أو ينتهي الخط. ترى حالة كل إجراء، ثم تقرر. لا يُمس الحساب قبل «تأكيد التنفيذ».</p>

    <div id="update-bar" class="update-bar" role="status" hidden>
      <span id="update-text"></span>
      <button id="update-button" class="btn btn-pine" type="button">تحديث</button>
    </div>

    <div id="notice" class="notice" role="status" hidden></div>

    <form id="repost-form" class="sheet" autocomplete="off" novalidate>
      <div class="sheet-inner">
        <input id="csrf_token" type="hidden" value="{{ csrf_token }}">
        <section class="block accounts-block">
          <div class="block-head">
            <h2>الحسابات</h2>
            <p>حتى {{ max_accounts }} حسابات. لكل حساب مهمّته الخاصة، وتعمل المهام في الوقت نفسه.</p>
          </div>
          <div id="accounts-bar" class="accounts-bar" role="tablist" aria-label="الحسابات"></div>
        </section>

        <section id="session-block" class="block">
          <div class="block-head">
            <h2 id="session-title">الجلسة</h2>
            <p>سجّل الدخول من المتصفح، ثم اضغط تحقق. تُحفظ الجلسة مع اسم الحساب على هذا الجهاز.</p>
          </div>
          <div class="token-row">
            <input id="account-name" type="text" readonly tabindex="-1" dir="auto" placeholder="اسم المستخدم" aria-label="الحساب">
            <button id="quick-verify" class="btn btn-ghost" type="button">تحقق</button>
            {% if in_app %}<button id="browser-login" class="btn btn-ghost" type="button">تسجيل الدخول</button>{% endif %}
            <button id="account-settings" class="btn btn-ghost" type="button" aria-expanded="false" aria-controls="account-panel">إعداد الحساب</button>
          </div>
          <div id="account-panel" hidden>
            <input id="auth_token" name="auth_token" type="hidden" value="">
            <p id="session-account" class="session-account" hidden></p>
            <div id="saved-sessions" class="saved-sessions" hidden>
              <p class="field-label">الحساب المحفوظ</p>
              <ul id="saved-session-list" class="saved-list"></ul>
            </div>
            <label class="field-label" for="chat-pin">رمز الدردشة</label>
            <input id="chat-pin" name="chat_pin" type="password" inputmode="numeric" maxlength="8" required
                   autocomplete="off" spellcheck="false" placeholder="٤ أرقام" aria-label="رمز الدردشة">
          </div>
        </section>

        <section class="block">
          <div class="block-head">
            <h2>القروب</h2>
            <p>يُفتح صندوق الدردشة، وتُعرض القروبات فقط. اختر واحدًا ثم العدد.</p>
          </div>
          <div class="token-row groups-row">
            <button id="groups-button" class="btn btn-ghost" type="button">عرض القروبات</button>
            <label id="wait-groups-label" class="wait-groups" for="wait-groups">
              <input id="wait-groups" type="checkbox" checked>
              انتظار
              <input id="wait-groups-sec" class="wait-sec" type="number" min="1" max="120" step="1" value="30" inputmode="numeric" aria-label="ثواني الانتظار قبل التقاط القروبات">
              ث
            </label>
            <button id="links-button" class="btn btn-ghost links-button" type="button" aria-pressed="false" aria-controls="links-box" title="روابط التغريدات" aria-label="روابط التغريدات">الروابط</button>
          </div>
          <div id="group-box" class="saved-sessions" hidden>
            <p class="field-label">اختر قروبًا</p>
            <ul id="group-list" class="saved-list"></ul>
          </div>
          <div id="links-box" class="links-box" hidden>
            <textarea id="tweet-links" rows="5" maxlength="200000" autocomplete="off" autocapitalize="off" spellcheck="false"
                      placeholder="الصق روابط التغريدات هنا، كل رابط في سطر" aria-label="روابط التغريدات"></textarea>
            <div class="links-foot">
              <span id="links-count" aria-live="polite"></span>
              <button id="links-clear" class="btn btn-ghost" type="button">مسح</button>
            </div>
          </div>
          <div id="stop-row" class="stop-row">
            <input id="stop-tweet" name="stop_tweet" type="text" maxlength="300" autocomplete="off" spellcheck="false"
                   placeholder="رابط التغريدة المحددة" aria-label="التغريدة المحددة">
          </div>
        </section>

        <section class="block">
          <div class="block-head">
            <h2>الإجراءات</h2>
            <p>تُطبَّق مباشرة على التغريدات المستخرجة من القروب.</p>
          </div>
          <div class="choices">
            <label class="choice">
              <input id="action-repost" type="checkbox" checked>
              <span>
                <span class="choice-title">إعادة النشر</span>
                <span class="choice-copy">فقط إذا لم تكن الإعادة مفعّلة.</span>
              </span>
            </label>
            <label class="choice">
              <input id="action-like" type="checkbox" checked>
              <span>
                <span class="choice-title">إعجاب</span>
                <span class="choice-copy">فقط إذا لم يكن الإعجاب موجودًا.</span>
              </span>
            </label>
            <label class="choice">
              <input id="action-bookmark" type="checkbox" checked>
              <span>
                <span class="choice-title">المرجعية</span>
                <span class="choice-copy">فقط إذا لم يكن المنشور محفوظًا.</span>
              </span>
            </label>
            <label class="choice">
              <input id="action-comment" type="checkbox">
              <span>
                <span class="choice-title">التعليقات</span>
                <span class="choice-copy">يُنشر رد على التغريدة المستخرجة.</span>
              </span>
            </label>
          </div>
          <div id="reply-voice" class="reply-voice" hidden>
            <span class="voice-label">صيغة الرد</span>
            <div class="voices" role="radiogroup" aria-label="صيغة الرد">
              <label class="choice"><input type="radio" name="reply-voice" value="male" checked><span class="choice-title">مذكر</span></label>
              <label class="choice"><input type="radio" name="reply-voice" value="female"><span class="choice-title">مؤنث</span></label>
              <label class="choice"><input type="radio" name="reply-voice" value="neutral"><span class="choice-title">عام</span></label>
            </div>
            {% if owner_copy %}<button id="show-gemini" class="btn btn-ghost gemini-edit" type="button" aria-expanded="false" hidden>مفتاح Gemini</button>
            {% if claude_here %}<button id="show-claude" class="btn btn-ghost gemini-edit" type="button" aria-expanded="false" hidden>مفتاح Claude</button>
            <span id="comments-by-grok" class="engine-note" hidden>التعليقات بواسطة Claude، بالمفتاح المحفوظ في «مفتاح Claude».</span>
            {% else %}<span id="comments-by-grok" class="engine-note" data-text="التعليقات بواسطة {engine}، كما اخترت للمستخدمين في «توزيع البرنامج»." hidden>التعليقات بواسطة Grok، كما اخترت للمستخدمين في «توزيع البرنامج».</span>{% endif %}{% endif %}
          </div>
          <div id="gemini-fields" class="gemini-fields" hidden>
            {% if not owner_copy %}<p class="gemini-owner">يضبط صاحب البرنامج مفتاح التعليقات ونموذجها.</p>{% endif %}
            <div>
              <label class="field-label" for="gemini-key">مفتاح Gemini</label>
              <input id="gemini-key" type="password" maxlength="256" autocomplete="off" spellcheck="false" readonly
                     placeholder="المفتاح" aria-label="مفتاح Gemini API">
            </div>
            <div>
              <label class="field-label" for="gemini-model">النموذج</label>
              <div class="token-row">
                <input id="gemini-model" type="text" maxlength="80" autocomplete="off" spellcheck="false" readonly
                       value="gemini-3.5-flash" placeholder="gemini-3.5-flash" aria-label="نموذج Gemini">
                <button id="edit-gemini" class="btn btn-ghost gemini-edit" type="button" aria-pressed="false">تحرير</button>
              </div>
            </div>
            <p class="hint">يُحفظ المفتاح واسم النموذج على هذا الخادم بعد أول إدخال، ويظهران تلقائيًا حتى بعد إغلاق الصفحة أو إعادة تشغيل السكربت.</p>
          </div>
          {% if claude_here %}<div id="claude-fields" class="gemini-fields" hidden>
            <div>
              <label class="field-label" for="claude-key">مفتاح Claude</label>
              <input id="claude-key" type="password" maxlength="260" autocomplete="off" spellcheck="false" placeholder="المفتاح" aria-label="مفتاح Claude API">
            </div>
            <div>
              <label class="field-label" for="claude-model">النموذج</label>
              <input id="claude-model" type="text" maxlength="60" autocomplete="off" spellcheck="false" value="{{ claude_default }}" placeholder="{{ claude_default }}" aria-label="نموذج Claude">
            </div>
            <div class="claude-actions">
              <button id="save-claude" class="btn btn-ghost gemini-edit" type="button">حفظ</button>
              <button id="delete-claude" class="btn btn-ghost gemini-edit" type="button" hidden>حذف</button>
              <span id="claude-now" class="claude-now">بدون مفتاح Claude تُكتب التعليقات بواسطة Gemini.</span>
            </div>
          </div>{% endif %}
          <button id="reposts-button" class="btn btn-pine btn-wide" type="submit">تنفيذ</button>
        </section>
      </div>
    </form>

    <section id="task-board" class="sheet" hidden>
      <div class="sheet-inner">
        <h2>المهام</h2>
        <div id="task-list"></div>
      </div>
    </section>

    <section id="progress-panel" class="sheet" hidden>
      <div class="sheet-inner">
        <div class="progress-top">
          <div>
            <h2 id="progress-title">الجمع</h2>
            <p id="progress-message">جارٍ العمل…</p>
          </div>
          <div class="progress-figure" aria-hidden="true">
            <span id="progress-count" class="figure">0</span>
            <span id="progress-denom" class="denom"></span>
          </div>
        </div>
        <div id="meter" class="meter is-indeterminate" role="progressbar" aria-valuemin="0" aria-valuemax="100" aria-valuenow="0" aria-label="تقدم العملية">
          <span id="meter-bar"></span>
        </div>
        <p id="progress-note" class="progress-note">لا يُنفَّذ أي إجراء خلال الجمع.</p>
      </div>
    </section>

    <section id="repost-results" class="sheet" hidden>
      <div class="sheet-inner">
        <h2 id="repost-heading">نتيجة التنفيذ</h2>
        <div class="stats" id="result-stats"></div>
        <ol id="repost-list" class="post-list"></ol>
        <p id="no-reposts" class="hint" hidden>لم تُرجع العملية أي صفوف.</p>
      </div>
    </section>

    <p class="version-line">
      <span>الإصدار {{ app_version }}</span>
      <span id="update-state"></span>
      <a id="dist-link" class="link-button" target="_blank" rel="noopener" hidden>توزيع البرنامج</a>
    </p>

    <p class="footnote">الأعداد الكبيرة تأخذ وقتًا لأن كل دفعة تُنتظر حتى تظهر. إذا أغلقت المتصفح أثناء العملية فافتح الصفحة نفسها لاحقًا: يظهر التقدم من حيث بلغ، أو النتيجة إن اكتملت. الجلسات المحفوظة تبقى بعد إعادة تشغيل السكربت.</p>
  </main>
<div id="login-guide" class="pc-backdrop" hidden>
  <div class="usage-sheet guide-sheet" role="dialog" aria-modal="true" aria-labelledby="guide-title">
    <div class="usage-head">
      <b id="guide-title">قبل أن تبدأ تسجيل الدخول</b>
      <button id="guide-close" class="usage-x" type="button" aria-label="إغلاق">×</button>
    </div>
    <p class="usage-note">سيُفتح تبويب «المتصفح». اتبع هذه الخطوات بالترتيب:</p>
    <ol class="guide-steps">
      <li><b>1</b><div><strong>سجّل الدخول إلى حسابك في X</strong><span>في تبويب «المتصفح»، بحسابك واسم المستخدم وكلمة المرور كالمعتاد.</span></div></li>
      <li><b>2</b><div><strong>ادخل على الدردشة وأدخل رمز الدردشة</strong><span>افتح الرسائل (الدردشة) في X، وأدخل رمز الدردشة (٤ أرقام) حين يطلبه منك، حتى تُفتح المحادثات.</span></div></li>
      <li><b>3</b><div><strong>ارجع واضغط «تحقق»</strong><span>عُد إلى تبويب «اللوحة»، ثم اضغط «تحقق» ليُحفظ الحساب.</span></div></li>
    </ol>
    <div class="usage-foot">
      <button id="guide-cancel" class="btn btn-ghost" type="button">إلغاء</button>
      <button id="guide-go" class="btn btn-pine" type="button">فهمت، افتح المتصفح</button>
    </div>
  </div>
</div>
{% if control_on %}<div id="help-box" class="pc-backdrop" hidden>
  <div class="usage-sheet help-sheet" role="dialog" aria-modal="true" aria-labelledby="help-title">
    <div class="usage-head">
      <b id="help-title">المساعدة</b>
      <button id="help-close" class="usage-x" type="button" aria-label="إغلاق">×</button>
    </div>
    <p class="usage-note">صف المشكلة التي تواجهك، وأرفق صورًا أو فيديو قصيرًا إن أمكن. تصل رسالتك إلى صاحب البرنامج، ويصلك ردّه في قائمة التنبيهات.</p>
    <label class="help-label" for="help-text">وصف المشكلة</label>
    <textarea id="help-text" class="help-text" rows="5" maxlength="2000" placeholder="مثال: المهمة تتوقف عند التغريدة ١٣ وتظهر رسالة «تعذّر فتح التغريدة»."></textarea>
    <input id="help-files" type="file" accept="image/*,video/*" multiple hidden>
    <button id="help-attach" class="btn btn-ghost help-attach" type="button">📎 إرفاق صور أو فيديو</button>
    <ul id="help-list" class="help-list" hidden></ul>
    <p class="hint">حتى ٥ ملفات: الصورة حتى ٨ ميجابايت، والفيديو القصير حتى ٢٥ ميجابايت. يُرفق تلقائيًا إصدار التطبيق ونوع الجهاز وآخر سطور السجل، لتسهيل معرفة المشكلة.</p>
    <p id="help-status" class="help-status" role="status" hidden></p>
    <div class="usage-foot">
      <button id="help-cancel" class="btn btn-ghost" type="button">إلغاء</button>
      <button id="help-send" class="btn btn-pine" type="button">إرسال</button>
    </div>
  </div>
</div>{% endif %}
<div id="usage-box" class="pc-backdrop" hidden>
  <div class="usage-sheet" role="dialog" aria-modal="true" aria-labelledby="usage-title">
    <div class="usage-head">
      <b id="usage-title">التعليقات والتكلفة</b>
      <button id="usage-close" class="usage-x" type="button" aria-label="إغلاق">×</button>
    </div>
    <p id="usage-note" class="usage-note"></p>
    <table class="usage-table">
      <thead><tr><th>الحساب</th><th class="num">التعليقات</th><th class="num">التكلفة</th></tr></thead>
      <tbody id="usage-rows"></tbody>
      <tfoot><tr><th>المجموع</th><th class="num" id="usage-total-n">0</th><th class="num" id="usage-total-cost">$0.00</th></tr></tfoot>
    </table>
    <div class="usage-foot">
      <button id="usage-refresh" class="btn btn-ghost" type="button">تحديث</button>
      <button id="usage-done" class="btn btn-pine" type="button">إغلاق</button>
    </div>
  </div>
</div>
<div id="phone-check-box" class="pc-backdrop" hidden>
  <div class="pc-term" role="dialog" aria-modal="true" aria-labelledby="pc-title">
    <div class="pc-bar">
      <span class="pc-dots" aria-hidden="true"><i></i><i></i><i></i></span>
      <b id="pc-title">فحص قدرة الهاتف</b>
      <button id="pc-close" class="pc-x" type="button" aria-label="إغلاق">×</button>
    </div>
    <div id="pc-screen" class="pc-screen" aria-live="polite" title="المس الشاشة لإظهار النص كله"></div>
    <div class="pc-actions">
      <button id="pc-again" class="pc-btn" type="button" hidden>إعادة الفحص</button>
      <button id="pc-done" class="pc-btn" type="button">إغلاق</button>
    </div>
  </div>
</div>

<script>
(() => {
  const apiRoot = {{ api_root|tojson }};
  const LABELS = {repost: "إعادة النشر", like: "إعجاب", bookmark: "المرجعية", comment: "تعليق"};
  const tokenField = document.getElementById("auth_token");
  function lockToken() {}
  const stopField = document.getElementById("stop-tweet");
  const pinField = document.getElementById("chat-pin");
  const groupsButton = document.getElementById("groups-button");
  const waitGroups = document.getElementById("wait-groups");
  const waitGroupsSec = document.getElementById("wait-groups-sec");
  function rememberWaits() {
    try {
      localStorage.setItem("x_wait_settings_v5", JSON.stringify({
        groupsOn: waitGroups.checked, groupsSec: waitGroupsSec.value
      }));
    } catch (_) {}
  }
  try {
    // "_v2": choices saved before the current defaults (30 s waits ticked) are not restored.
    const latest = localStorage.getItem("x_wait_settings_v5");
    const before = latest || localStorage.getItem("x_wait_settings_v4") || localStorage.getItem("x_wait_settings_v3");
    const savedWaits = JSON.parse(before || localStorage.getItem("x_wait_settings_v2") || "null");
    if (savedWaits) {
      waitGroups.checked = !!savedWaits.groupsOn;
      if (savedWaits.groupsSec) waitGroupsSec.value = savedWaits.groupsSec;
    }
  } catch (_) {}
  [waitGroups, waitGroupsSec].forEach((node) => node.addEventListener("change", rememberWaits));
  function secondsFrom(field, min, max, fallback) {
    const value = Number.parseInt(field.value, 10);
    if (!Number.isInteger(value)) return fallback;
    return Math.max(min, Math.min(max, value));
  }
  const groupBox = document.getElementById("group-box");
  const groupList = document.getElementById("group-list");
  // «روابط التغريدات»: instead of a group, the task runs on the tweets pasted in this box. Meanwhile the
  // groups, the group's tweet and the waits hide, and «عرض القروبات» reads «القروبات»: it brings back
  // the groups already shown, without opening the browser and the chat again.
  const linksButton = document.getElementById("links-button");
  const linksBox = document.getElementById("links-box");
  const linksField = document.getElementById("tweet-links");
  const linksCount = document.getElementById("links-count");
  const stopRow = document.getElementById("stop-row");
  const waitGroupsLabel = document.getElementById("wait-groups-label");
  const MAX_LINKS = {{ max_links|tojson }};
  const MAX_ACCOUNTS = {{ max_accounts|tojson }};
  let linksMode = false;
  // Each tweet in the pasted text once, in order: "handle/id", or "id" for a link without the
  // author's name (x.com/i/web/status/…) or a bare tweet number.
  function pastedTweets(text) {
    const seen = new Set();
    const found = [];
    const add = (handle, id) => {
      if (seen.has(id)) return;
      seen.add(id);
      found.push(handle && !/^(i|web)$/i.test(handle) ? handle + "/" + id : id);
    };
    for (const token of String(text || "").split(/[\s,،]+/)) {
      const pattern = /(?:x|twitter)\.com\/([A-Za-z0-9_]{1,15})(?:\/web)?\/status(?:es)?\/(\d{6,25})/gi;
      let match;
      let any = false;
      while ((match = pattern.exec(token))) {
        any = true;
        add(match[1], match[2]);
      }
      if (!any && /^\d{15,25}$/.test(token)) add("", token);
    }
    return found;
  }
  function showLinksCount() {
    const count = pastedTweets(linksField.value).length;
    linksCount.textContent = count ? count + " تغريدة" + (count > MAX_LINKS ? " · الحد الأقصى " + MAX_LINKS : "") : "لم يُلصق أي رابط بعد";
    linksCount.classList.toggle("is-bad", count > MAX_LINKS);
  }
  function setLinksMode(on) {
    linksMode = on;
    linksButton.setAttribute("aria-pressed", on ? "true" : "false");
    linksBox.hidden = !on;
    stopRow.hidden = on;
    waitGroupsLabel.hidden = on;
    groupsButton.textContent = on ? "القروبات" : "عرض القروبات";
    groupBox.hidden = on || groupNames.length === 0;
    if (on) showLinksCount();
  }
  linksButton.addEventListener("click", () => {
    setLinksMode(!linksMode);
    if (linksMode && !linksField.value.trim()) linksField.focus();
  });
  // (the pasted links are the shown account's own: kept with its setup, see snapshotActive)
  linksField.addEventListener("input", () => {
    showLinksCount();
    if (typeof snapshotActive === "function") snapshotActive();
  });
  document.getElementById("links-clear").addEventListener("click", () => {
    linksField.value = "";
    if (typeof snapshotActive === "function") snapshotActive();
    showLinksCount();
    linksField.focus();
  });
  const commentToggle = document.getElementById("action-comment");
  const geminiFields = document.getElementById("gemini-fields");
  const geminiKey = document.getElementById("gemini-key");
  const geminiModel = document.getElementById("gemini-model");
  const usagePill = document.getElementById("usage-pill");
  const usageCount = document.getElementById("usage-count");
  const usageCost = document.getElementById("usage-cost");
  const usageBox = document.getElementById("usage-box");
  const usageRows = document.getElementById("usage-rows");
  const usageNote = document.getElementById("usage-note");
  const editGemini = document.getElementById("edit-gemini");
  const replyVoice = document.getElementById("reply-voice");
  // The owner's copy only: opens the Gemini key and model fields.
  const showGemini = document.getElementById("show-gemini");
  // A user's copy: the owner sets the Gemini key and model; here they are only shown.
  const geminiByOwner = {{ (not owner_copy)|tojson }};
  const controlOn = {{ control_on|tojson }};
  editGemini.hidden = geminiByOwner;
  // The owner's copy: Grok writes its comments when it is the one chosen in «توزيع البرنامج» (as the script says).
  // (Grok or Claude, chosen in «توزيع البرنامج»: no Gemini key is asked for then.)
  let commentsByOther = false;
  const engineNote = document.getElementById("comments-by-grok");
  function showCommentsEngine(engine) {
    commentsByOther = engine === "grok" || engine === "claude";
    if (!engineNote) return;
    engineNote.hidden = !commentsByOther;
    if (commentsByOther && engineNote.dataset.text) {
      engineNote.textContent = engineNote.dataset.text.replace("{engine}", engine === "claude" ? "Claude" : "Grok");
    }
  }
  // A copy with no «توزيع البرنامج»: its own «مفتاح Claude», typed here, writes its comments when saved.
  const claudeFields = document.getElementById("claude-fields");
  const showClaude = document.getElementById("show-claude");
  function showOwnClaude(data) {
    if (!claudeFields) return;
    const saved = data.claude_key || "";
    document.getElementById("claude-now").textContent = saved
      ? "محفوظ: " + saved + " · " + (data.claude_model || "") + " — التعليقات بواسطة Claude."
      : "بدون مفتاح Claude تُكتب التعليقات بواسطة Gemini.";
    document.getElementById("delete-claude").hidden = !saved;
    const claudeModel = document.getElementById("claude-model");
    if (data.claude_model && document.activeElement !== claudeModel) claudeModel.value = data.claude_model;
  }
  function lockGemini(locked) {
    geminiKey.readOnly = locked;
    geminiModel.readOnly = locked;
    editGemini.textContent = locked ? "تحرير" : "تم";
    editGemini.setAttribute("aria-pressed", locked ? "false" : "true");
  }
  lockGemini(true);
  const csrf = document.getElementById("csrf_token").value;
  const loginButton = document.getElementById("login-button");
  const accountName = document.getElementById("account-name");
  const quickVerify = document.getElementById("quick-verify");
  const accountSettings = document.getElementById("account-settings");
  const accountPanel = document.getElementById("account-panel");
  const repostButton = document.getElementById("reposts-button");
  const notice = document.getElementById("notice");
  const progressPanel = document.getElementById("progress-panel");
  const taskBoard = document.getElementById("task-board");
  const taskList = document.getElementById("task-list");
  const liveTasks = new Map();
  const progressTitle = document.getElementById("progress-title");
  const progressMessage = document.getElementById("progress-message");
  const progressCount = document.getElementById("progress-count");
  const progressDenom = document.getElementById("progress-denom");
  const progressNote = document.getElementById("progress-note");
  const meter = document.getElementById("meter");
  const meterBar = document.getElementById("meter-bar");
  const repostResults = document.getElementById("repost-results");
  const resultStats = document.getElementById("result-stats");
  const repostList = document.getElementById("repost-list");
  const noReposts = document.getElementById("no-reposts");
  const sessionAccount = document.getElementById("session-account");
  const savedSessions = document.getElementById("saved-sessions");
  const savedSessionList = document.getElementById("saved-session-list");
  const accountsBar = document.getElementById("accounts-bar");
  let progressStarted = 0;
  let sessionRows = [];
  let groupNames = [];
  // (each account's chosen group, groups, links and setup are its own: see accountState and its panel)
  let selectedGroup = "";
  try {
    ["x_selected_group", "x_tweet_links", "x_links_mode"].forEach((name) => localStorage.removeItem(name));
  } catch (_) {}

  function clientId() {
    const key = "x_desk_client";
    let id = localStorage.getItem(key) || "";
    if (!/^[A-Za-z0-9_-]{16,80}$/.test(id)) {
      const bytes = new Uint8Array(18);
      crypto.getRandomValues(bytes);
      id = btoa(String.fromCharCode(...bytes)).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/g, "");
      localStorage.setItem(key, id);
    }
    return id;
  }

  function readTasks() {
    try {
      const parsed = JSON.parse(localStorage.getItem("x_reposts_tasks") || "[]");
      return Array.isArray(parsed) ? parsed.filter((row) => row && row.id && row.key) : [];
    } catch (_) {
      return [];
    }
  }

  function writeTasks(rows) {
    localStorage.setItem("x_reposts_tasks", JSON.stringify(rows.slice(0, 12)));
  }

  // A request with no answer in 15 s is dropped so the page can ask again, instead of waiting on
  // one that was cut while the phone was away or switching networks.
  async function fetchWithTimeout(url, options, ms = 15000) {
    const controller = new AbortController();
    const timer = setTimeout(() => controller.abort(), ms);
    try {
      return await fetch(url, {...options, signal: controller.signal});
    } finally {
      clearTimeout(timer);
    }
  }

  // Pages opened over plain http (a server IP) have no navigator.clipboard, so fall back to execCommand.
  async function copyText(text) {
    if (navigator.clipboard && window.isSecureContext) {
      try {
        await navigator.clipboard.writeText(text);
        return true;
      } catch (_) {}
    }
    const area = document.createElement("textarea");
    area.value = text;
    area.setAttribute("readonly", "");
    area.style.cssText = "position: fixed; top: 0; left: 0; opacity: 0; font-size: 16px;";
    document.body.appendChild(area);
    area.select();
    area.setSelectionRange(0, text.length);
    let copied = false;
    try {
      copied = document.execCommand("copy");
    } catch (_) {}
    area.remove();
    return copied;
  }

  function followTask(task) {
    if (!task || !task.id || liveTasks.has(task.id)) return;
    task.key = task.key || "";
    liveTasks.set(task.id, true);
    if (task.token) markAccountRunning(task.token, true);
    if (task.key) {
      const rows = readTasks().filter((row) => row.id !== task.id);
      rows.unshift(task);
      writeTasks(rows);
    }
    taskBoard.hidden = false;
    const card = document.createElement("article");
    card.className = "task-card";
    card.dataset.token = task.token || "";
    card.innerHTML = '<div class="progress-top"><div><h3></h3><p class="task-phase"></p><p class="task-msg"></p></div><b class="task-count">0</b></div><div class="meter is-indeterminate"><span class="task-bar"></span></div><div class="task-actions"><button class="btn btn-ghost task-stop" type="button">إيقاف هذه المهمة</button><button class="btn btn-ghost task-copy" type="button" hidden>نسخ التغريدات</button><button class="btn task-retry" type="button" hidden>إعادة المحاولة</button><button class="btn task-retry-failed" type="button" hidden>إعادة المحاولة للفاشلة</button></div>';
    card.querySelector("h3").textContent = task.title || "مهمة";
    const stopButton = card.querySelector(".task-stop");
    const retryButton = card.querySelector(".task-retry");
    const copyButton = card.querySelector(".task-copy");
    const retryFailedButton = card.querySelector(".task-retry-failed");
    let links = [];
    let linksWanted = true;
    copyButton.addEventListener("click", async () => {
      if (!links.length) return;
      const count = links.length;
      if (await copyText(links.join("\n"))) {
        copyButton.textContent = "نُسخت " + count + " تغريدة";
        setTimeout(() => { copyButton.textContent = "نسخ التغريدات"; }, 1500);
      } else {
        showNotice("تعذّر النسخ من هذا المتصفح.", false);
      }
    });
    // While the task runs the polls leave out the tweet list, so ask for its links once.
    const loadLinks = async () => {
      linksWanted = false;
      try {
        const response = await fetchWithTimeout(apiRoot + "/jobs/" + encodeURIComponent(task.id) + "?light=1&links=1", {
          headers: {"X-CSRF-Token": csrf, "X-Job-Key": task.key, "X-Client-Id": clientId()},
          cache: "no-store"
        });
        const data = await response.json();
        if (response.ok && Array.isArray(data.links) && data.links.length) {
          links = data.links;
          copyButton.hidden = false;
          return;
        }
      } catch (_) {}
      linksWanted = true;
    };
    stopButton.addEventListener("click", async () => {
      stopButton.disabled = true;
      try {
        await postJson("/stop", {job_id: task.id, job_key: task.key});
      } catch (_) {
        stopButton.disabled = false;
      }
    });
    retryButton.addEventListener("click", async () => {
      retryButton.disabled = true;
      try {
        const data = await postJson("/retry", {job_id: task.id, job_key: task.key});
        if (!data.success) {
          showNotice(data.message || "تعذّرت إعادة المحاولة.", false);
          retryButton.disabled = false;
          return;
        }
        retryButton.hidden = true;
        stopButton.disabled = false;
        showTaskNotice(task, (task.title ? task.title + ": " : "") + (data.message || "بدأت إعادة المحاولة."), true);
        if (!liveTasks.has(task.id)) {
          liveTasks.set(task.id, true);
          const rows = readTasks().filter((row) => row.id !== task.id);
          rows.unshift(task);
          writeTasks(rows);
          watch();
        }
      } catch (_) {
        showNotice("تعذّر الاتصال أثناء إعادة المحاولة.", false);
        retryButton.disabled = false;
      }
    });
    // «إعادة المحاولة للفاشلة»: a new task with only the tweets whose actions failed, each with only those actions.
    retryFailedButton.addEventListener("click", async () => {
      retryFailedButton.disabled = true;
      try {
        const data = await postJson("/retry-failed", {job_id: task.id, job_key: task.key});
        if (!data.success || !data.job_id || !data.job_key) {
          showNotice(data.message || "تعذّرت إعادة المحاولة للفاشلة.", false);
          retryFailedButton.disabled = false;
          return;
        }
        retryFailedButton.hidden = true;
        writeTasks(readTasks().filter((row) => row.id !== task.id));
        const base = (task.title || "مهمة").replace(/^إعادة الفاشلة · /, "");
        followTask({id: data.job_id, key: data.job_key, token: task.token, title: "إعادة الفاشلة · " + base, startedAt: Date.now()});
        showTaskNotice(task, base + ": " + (data.message || "بدأت إعادة المحاولة للفاشلة."), true);
      } catch (_) {
        showNotice("تعذّر الاتصال أثناء إعادة المحاولة للفاشلة.", false);
        retryFailedButton.disabled = false;
      }
    });
    taskList.prepend(card);
    filterTaskCards();
    const paint = (data) => {
      const phase = data.phase || "collect";
      const titles = {queue: "في الانتظار", login: "فتح القروب", prepare: "تجهيز", collect: "جمع", act: "تنفيذ"};
      card.querySelector(".task-phase").textContent = titles[phase] || "جارٍ العمل";
      card.querySelector(".task-msg").textContent = data.message || "";
      const current = phase === "act" ? (data.done || 0) : (data.collected || 0);
      const total = data.requested || 0;
      card.querySelector(".task-count").textContent = total ? current + " / " + total : String(current);
      const meter = card.querySelector(".meter");
      const indeterminate = data.status === "running" && (phase === "queue" || phase === "login" || phase === "prepare" || !total);
      meter.classList.toggle("is-indeterminate", indeterminate);
      card.querySelector(".task-bar").style.width = indeterminate ? "" : Math.max(0, Math.min(100, total ? Math.round((current / total) * 100) : 100)) + "%";
      stopButton.hidden = data.status !== "running";
      retryButton.hidden = !(data.status !== "running" && data.resumable);
      retryButton.disabled = false;
      const failedCount = data.status !== "running" ? Number(data.retry_failed || 0) : 0;
      retryFailedButton.hidden = !failedCount;
      if (failedCount) retryFailedButton.textContent = "إعادة المحاولة للفاشلة (" + failedCount + ")";
      if (Array.isArray(data.items) && data.items.length) links = data.items.map((item) => item && item.url).filter(Boolean);
      if (!links.length && linksWanted && phase === "act") loadLinks();
      copyButton.hidden = !links.length;
    };
    const watch = async () => {
      try {
        for (;;) {
          let response;
          let data;
          try {
            response = await fetchWithTimeout(apiRoot + "/jobs/" + encodeURIComponent(task.id) + "?light=1", {
              headers: {"X-CSRF-Token": csrf, "X-Job-Key": task.key, "X-Client-Id": clientId()},
              cache: "no-store"
            });
            data = await response.json();
          } catch (_) {
            // No answer (the phone was away, the network changed): keep trying instead of stopping.
            card.querySelector(".task-msg").textContent = "انقطع الاتصال لحظيًا. جارٍ إعادة الاتصال…";
            await new Promise((resolve) => setTimeout(resolve, 1500));
            continue;
          }
          if (response.status === 404) writeTasks(readTasks().filter((row) => row.id !== task.id));
          if (!response.ok) throw new Error(data.message || "تعذّر متابعة المهمة.");
          paint(data);
          if (data.status !== "running") {
            showTaskNotice(task, (task.title ? task.title + ": " : "") + (data.message || ""), Boolean(data.success));
            // (its results show on its own account's panel only: elsewhere they wait for it, see loadAccountFromServer)
            if (Array.isArray(data.results) && data.results.length && (!task.token || task.token === tokenField.value.trim())) renderResults(data);
            // A task stopped with a retry button stays in the saved task list so it is still there after a reload.
            // (and one with failed actions to retry, so its «إعادة المحاولة للفاشلة» is there after a reload too)
            if (!data.resumable && !data.retry_failed) writeTasks(readTasks().filter((row) => row.id !== task.id));
            loadActionCounts();
            break;
          }
          await new Promise((resolve) => setTimeout(resolve, 700));
        }
      } catch (error) {
        card.querySelector(".task-msg").textContent = error.message || "انقطع متابعة المهمة.";
      } finally {
        liveTasks.delete(task.id);
        if (task.token) markAccountRunning(task.token, false);
      }
    };
    watch();
  }

  function showAccount(text) {
    sessionAccount.textContent = text || "";
    sessionAccount.hidden = !text;
  }

  // The one-row view: the account's username; the token, its buttons and the chat PIN sit behind "إعداد الحساب".
  function syncAccountName() {
    const token = tokenField.value.trim();
    const row = sessionRows.find((item) => item.token === token);
    accountName.value = row && row.username ? "@" + row.username : (token ? "حساب غير معروف" : "");
  }

  function setAccountPanel(open) {
    accountPanel.hidden = !open;
    accountSettings.textContent = open ? "إخفاء الإعداد" : "إعداد الحساب";
    accountSettings.setAttribute("aria-expanded", open ? "true" : "false");
  }

  // Focus a field, opening the account settings first when it is inside them.
  function revealField(field) {
    if (accountPanel.contains(field)) setAccountPanel(true);
    field.focus();
  }

  function formatWhen(epoch) {
    if (!epoch) return "";
    const minutes = Math.round(Math.max(0, Date.now() - epoch * 1000) / 60000);
    if (minutes < 1) return "الآن";
    if (minutes < 60) return "قبل " + minutes + " د";
    const hours = Math.round(minutes / 60);
    if (hours < 24) return "قبل " + hours + " س";
    const days = Math.round(hours / 24);
    if (days < 14) return "قبل " + days + " ي";
    return new Date(epoch * 1000).toLocaleDateString("ar");
  }

  // ==== الحسابات (قائمة جانبية، حتى MAX_ACCOUNTS): لكل حساب إعداده ومهمته المستقلة ====
  let accountState = {};
  try { accountState = JSON.parse(localStorage.getItem("x_account_state") || "{}") || {}; } catch (_) { accountState = {}; }
  function saveAccountStates() {
    try { localStorage.setItem("x_account_state", JSON.stringify(accountState)); } catch (_) {}
  }
  // Which accounts have a task working now (token -> number of live tasks): shows the dot on the chip.
  const runningAccounts = new Map();
  function markAccountRunning(token, on) {
    if (!token) return;
    const next = (runningAccounts.get(token) || 0) + (on ? 1 : -1);
    if (next > 0) runningAccounts.set(token, next); else runningAccounts.delete(token);
    renderAccounts();
  }
  let activeToken = tokenField.value.trim();
  function snapshotActive() {
    if (!activeToken) return;
    accountState[activeToken] = {
      group: selectedGroup,
      groups: groupNames.slice(0, 200),
      stop: stopField.value.trim(),
      pin: pinField.value.trim(),
      actions: selectedActions(),
      links: linksMode,
      linksText: linksField.value.slice(0, 200000)
    };
    saveAccountStates();
  }
  function applyAccountSetup(token) {
    const state = accountState[token] || null;
    if (state) {
      groupNames = Array.isArray(state.groups) ? state.groups : [];
      selectedGroup = state.group || "";
      stopField.value = state.stop || "";
      if (Array.isArray(state.actions) && state.actions.length) {
        ["repost", "like", "bookmark", "comment"].forEach((key) => {
          const box = document.getElementById("action-" + key);
          if (box) box.checked = state.actions.includes(key);
        });
      }
      linksField.value = state.linksText || "";
      renderGroups();
      setLinksMode(!!state.links);
      syncGemini();
    } else {
      groupNames = [];
      selectedGroup = "";
      stopField.value = "";
      linksField.value = "";
      setLinksMode(false);
      renderGroups();
    }
  }
  // The shown account's last task, on its own panel (no other account's results are shown there).
  function hideAccountResults() {
    progressPanel.hidden = true;
    repostResults.hidden = true;
  }
  function showAccountLastJob(job) {
    if (!job || !job.status || job.status === "running") return;
    renderProgress(job);
    if (job.kind === "execute" && Array.isArray(job.results) && job.results.length) renderResults(job);
  }
  // The account's own panel and tasks as the server keeps them in its folder: its groups, its group, its
  // tweet, its actions, its working and waiting tasks, its last task.
  async function loadAccountFromServer(token) {
    let data = null;
    try {
      const response = await fetchWithTimeout(apiRoot + "/state", {headers: {"X-Account-Token": token}, cache: "no-store"});
      data = await response.json();
    } catch (_) {}
    if (!data || !data.success || tokenField.value.trim() !== token) return;
    const pin = pinField.value;
    applyScreen(data);
    if (!data.chat_pin) pinField.value = pin;
    snapshotActive();
    (data.running_jobs || []).forEach((job) => followTask({
      id: job.id,
      key: data.job_id === job.id ? (data.job_key || "") : "",
      token: token,
      title: job.username || data.group || "مهمة"
    }));
    filterTaskCards();
    showAccountLastJob(data.job);
  }
  function selectAccount(token) {
    if (token === activeToken) { setAccountPanel(false); return; }
    snapshotActive();
    activeToken = token;
    const row = sessionRows.find((item) => item.token === token);
    tokenField.value = token;
    lockToken(true);
    pinField.value = (row && row.chat_pin) || (accountState[token] && accountState[token].pin) || "";
    applyAccountSetup(token);
    showAccount(row && row.username ? "الحساب: @" + row.username : "تم اختيار حساب محفوظ.");
    renderAccounts();
    setCounts(null);           // the chosen account's own counters, tasks, results and notices only
    hideAccountResults();
    notice.hidden = true;
    showWaitingNotice(token);
    loadActionCounts();
    filterTaskCards();
    pushScreen();
    loadAccountFromServer(token);
  }
  function addAccountFlow() {
    if (sessionRows.length >= MAX_ACCOUNTS) {
      showNotice("الحد الأقصى " + MAX_ACCOUNTS + " حسابات. احذف حسابًا لإضافة آخر.", false);
      return;
    }
    snapshotActive();
    activeToken = "";
    tokenField.value = "";
    lockToken(true);
    pinField.value = "";
    stopField.value = "";
    groupNames = [];
    selectedGroup = "";
    setLinksMode(false);
    renderGroups();
    showAccount("");
    linksField.value = "";
    renderAccounts();
    setCounts(null);
    hideAccountResults();
    notice.hidden = true;
    filterTaskCards();
    pushScreen();
    setAccountPanel(true);
    showNotice("سجّل الدخول بالحساب الجديد من «تسجيل الدخول»، ثم اضغط «تحقق».", true);
    const block = document.getElementById("session-block");
    if (block) block.scrollIntoView({block: "start", behavior: "smooth"});
  }
  async function deleteAccount(row) {
    try {
      const data = await postJson("/sessions/delete", {id: row.id});
      if (!data.success) {
        showNotice(data.message || "تعذّر حذف الحساب.", false);
        return;
      }
      delete accountState[row.token];
      saveAccountStates();
      if (activeToken === row.token || tokenField.value.trim() === row.token) {
        activeToken = "";
        tokenField.value = "";
        lockToken(true);
        pinField.value = "";
        showAccount("");
        pushScreen();
      }
      showNotice("حُذف الحساب من هذا الخادم.", true);
      await loadSessions();
    } catch (_) {
      showNotice("تعذّر الاتصال أثناء الحذف.", false);
    }
  }
  function renderAccounts() {
    savedSessions.hidden = true;                 // the old inner list is replaced by the accounts bar
    savedSessionList.replaceChildren();
    const token = tokenField.value.trim();
    if (!accountsBar) return;
    accountsBar.replaceChildren();
    sessionRows.forEach((row) => {
      const chip = document.createElement("button");
      chip.type = "button";
      chip.className = "acct-chip" + (row.token === token ? " is-on" : "") + (runningAccounts.has(row.token) ? " is-running" : "");
      chip.setAttribute("role", "tab");
      chip.setAttribute("aria-selected", row.token === token ? "true" : "false");
      const dot = document.createElement("span");
      dot.className = "acct-dot";
      dot.setAttribute("aria-hidden", "true");
      const who = document.createElement("span");
      who.className = "acct-who";
      who.textContent = row.username ? "@" + row.username : "حساب";
      const close = document.createElement("span");
      close.className = "acct-x";
      close.setAttribute("role", "button");
      close.setAttribute("tabindex", "0");
      close.setAttribute("aria-label", "حذف الحساب" + (row.username ? " @" + row.username : ""));
      close.textContent = "×";
      const removeAccount = () => {
        if (runningAccounts.has(row.token)) { showNotice("لهذا الحساب مهمة تعمل الآن. أوقفها قبل حذفه.", false); return; }
        deleteAccount(row);
      };
      close.addEventListener("click", (event) => { event.stopPropagation(); removeAccount(); });
      close.addEventListener("keydown", (event) => {
        if (event.key === "Enter" || event.key === " ") { event.preventDefault(); event.stopPropagation(); removeAccount(); }
      });
      chip.append(dot, who, close);
      chip.addEventListener("click", () => selectAccount(row.token));
      accountsBar.appendChild(chip);
    });
    if (sessionRows.length < MAX_ACCOUNTS) {
      const add = document.createElement("button");
      add.type = "button";
      add.className = "acct-add";
      add.id = "add-account";
      add.textContent = sessionRows.length ? "＋ إضافة حساب" : "＋ أضف حسابك الأول";
      add.addEventListener("click", addAccountFlow);
      accountsBar.appendChild(add);
    } else {
      const note = document.createElement("p");
      note.className = "acct-empty";
      note.textContent = "الحد الأقصى " + MAX_ACCOUNTS + " حسابات.";
      accountsBar.appendChild(note);
    }
    syncAccountName();
    pushAccountsToNative();
  }
  // Inside the app, the accounts live in the app's own side drawer; it reports them here and drives them.
  function pushAccountsToNative() {
    try {
      if (!window.GroupsNative || typeof window.GroupsNative.accounts !== "function") return;
      const token = tokenField.value.trim();
      const list = sessionRows.map((row) => ({ name: row.username || "", running: runningAccounts.has(row.token) }));
      const active = sessionRows.findIndex((row) => row.token === token);
      let anyRunning = false;
      sessionRows.forEach((row) => { if (runningAccounts.has(row.token)) anyRunning = true; });
      window.GroupsNative.accounts(JSON.stringify(list), active, MAX_ACCOUNTS, anyRunning);
    } catch (_) {}
  }
  // The app's side drawer calls these to switch, add or remove an account (by its position in the list).
  window.__groupsAccounts = {
    select: (index) => { const row = sessionRows[index]; if (row) selectAccount(row.token); },
    add: () => addAccountFlow(),
    remove: (index) => { const row = sessionRows[index]; if (row) deleteAccount(row); }
  };
  // Each account sees only its own task cards (a card knows its account from data-token).
  function filterTaskCards() {
    const token = tokenField.value.trim();
    let shown = 0;
    taskList.querySelectorAll(".task-card").forEach((card) => {
      const cardToken = card.dataset.token || "";
      const show = !cardToken || cardToken === token;
      card.hidden = !show;
      if (show) shown += 1;
    });
    taskBoard.hidden = shown === 0;
  }
  // Older call sites still call renderSessions(); point it at the accounts bar.
  function renderSessions() { renderAccounts(); }

  async function loadSessions() {
    try {
      const response = await fetchWithTimeout(apiRoot + "/sessions", {
        headers: {"X-CSRF-Token": csrf, "X-Client-Id": clientId()},
        cache: "no-store"
      });
      const data = await response.json();
      if (!response.ok) return;
      sessionRows = data.sessions || [];
      if (!activeToken) activeToken = tokenField.value.trim();
      renderSessions();
      showCommentsEngine(data.comments_engine);
      showOwnClaude(data);
      if (geminiByOwner) {
        geminiKey.value = data.gemini_api_key || "";
        geminiModel.value = data.gemini_model || "";
      } else {
        if (data.gemini_api_key && document.activeElement !== geminiKey) {
          geminiKey.value = data.gemini_api_key;
          localStorage.setItem("x_gemini_key", data.gemini_api_key);
        }
        if (data.gemini_model && document.activeElement !== geminiModel) {
          geminiModel.value = data.gemini_model;
          localStorage.setItem("x_gemini_model", data.gemini_model);
        }
      }
    } catch (_) {}
  }

  // Who writes the comments now (it may have changed in «توزيع البرنامج» since the page opened); nothing else
  // on the page is touched.
  async function loadCommentsEngine() {
    try {
      const response = await fetchWithTimeout(apiRoot + "/sessions", {
        headers: {"X-CSRF-Token": csrf, "X-Client-Id": clientId()},
        cache: "no-store"
      });
      const data = await response.json();
      if (response.ok) showCommentsEngine(data.comments_engine);
    } catch (_) {}
  }

  // Successful actions of all tasks so far (kept on the server), shown at the top of the page.
  function setCounts(counts) {
    ["repost", "like", "bookmark", "comment"].forEach((key) => {
      document.getElementById("count-" + key).textContent = Number((counts && counts[key]) || 0).toLocaleString("en-US");
    });
  }
  // The top counters show the chosen account's own successes only (its token tells the server which).
  async function loadActionCounts() {
    const token = tokenField.value.trim();
    if (!token) { setCounts(null); return; }
    try {
      const response = await fetchWithTimeout(apiRoot + "/stats", {
        headers: {"X-CSRF-Token": csrf, "X-Account-Token": token}, cache: "no-store"
      });
      const data = await response.json();
      if (!response.ok || !data.success) return;
      // (ignore a late answer for an account that is no longer the chosen one)
      if (tokenField.value.trim() === token) setCounts(data.counts);
    } catch (_) {}
  }

  function reveal(node) {
    node.hidden = false;
    const reduce = window.matchMedia("(prefers-reduced-motion: reduce)").matches;
    node.scrollIntoView({block: "start", behavior: reduce ? "auto" : "smooth"});
  }

  function showNotice(message, success) {
    notice.textContent = message;
    notice.className = "notice " + (success ? "is-ok" : "is-bad");
    notice.hidden = false;
    pushNative(message, success ? "ok" : "bad");
  }
  // أرسل كل تنبيه/تعليمات إلى قائمة التنبيهات داخل التطبيق (الجرس في الشريط العلوي)، إن كان يعمل داخل التطبيق.
  function pushNative(message, kind) {
    try {
      if (window.GroupsNative && typeof window.GroupsNative.notify === "function") {
        window.GroupsNative.notify(kind || "info", String(message == null ? "" : message));
      }
    } catch (e) {}
  }
  // A notice about a task (stopped, ended, retried) belongs to the task's account: it shows on that account's
  // panel only. One that comes while another account is shown waits until its account is shown again.
  const waitingNotices = new Map();
  function showTaskNotice(task, message, success) {
    const token = task && task.token;
    if (!token || token === tokenField.value.trim()) {
      showNotice(message, success);
      return;
    }
    waitingNotices.set(token, {message, success});
  }
  function showWaitingNotice(token) {
    const waiting = waitingNotices.get(token);
    waitingNotices.delete(token);
    if (waiting) showNotice(waiting.message, waiting.success);
  }

  function selectedActions() {
    return ["repost", "like", "bookmark", "comment"].filter((key) => document.getElementById("action-" + key).checked);
  }

  function syncGemini() {
    replyVoice.hidden = !commentToggle.checked;
    if (!commentToggle.checked) {
      openGemini(false);
      if (claudeFields) { claudeFields.hidden = true; showClaude.setAttribute("aria-expanded", "false"); }
    }
  }

  function openGemini(open) {
    geminiFields.hidden = !open;
    if (showGemini) showGemini.setAttribute("aria-expanded", open ? "true" : "false");
  }

  function selectedVoice() {
    return (document.querySelector('input[name="reply-voice"]:checked') || {}).value || "male";
  }

  // Total comments written by the model, and their price, read from the server.
  // The comments written for this copy and their cost: from the control server when this copy has one (kept
  // there by X account, so they stay when the app is installed again), else counted here.
  let usageData = null;
  function money(value) { return "$" + Number(value || 0).toFixed(2); }
  function renderUsage() {
    if (!usageData) return;
    usageCount.textContent = "التعليقات (" + Number(usageData.total || 0).toLocaleString("en-US") + ")";
    usageCost.textContent = money(usageData.cost);
    // Brown at $0, redder as the cost grows, fully red from $10.
    const brown = [139, 69, 19];
    const red = [211, 47, 47];
    const share = Math.max(0, Math.min(1, Number(usageData.cost || 0) / 10));
    usageCost.style.backgroundColor = "rgb(" + brown.map((value, i) => Math.round(value + (red[i] - value) * share)).join(", ") + ")";
    usageRows.replaceChildren();
    const accounts = Array.isArray(usageData.accounts) ? usageData.accounts : [];
    if (!accounts.length) {
      const row = document.createElement("tr");
      const cell = document.createElement("td");
      cell.className = "empty";
      cell.colSpan = 3;
      cell.textContent = usageData.source === "control" ? "لا تعليقات بعد." : "التفصيل لكل حساب يأتي من لوحة التحكم.";
      row.append(cell);
      usageRows.append(row);
    }
    accounts.forEach((account) => {
      const row = document.createElement("tr");
      const who = document.createElement("td");
      who.className = "who";
      const name = document.createElement("bdi");
      name.dir = "ltr";
      name.textContent = account.name ? "@" + account.name : "حساب بلا اسم";
      who.append(name);
      const count = document.createElement("td");
      count.className = "num";
      count.textContent = Number(account.n || 0).toLocaleString("en-US");
      const cost = document.createElement("td");
      cost.className = "num";
      cost.textContent = money(account.cost);
      row.append(who, count, cost);
      usageRows.append(row);
    });
    document.getElementById("usage-total-n").textContent = Number(usageData.total || 0).toLocaleString("en-US");
    document.getElementById("usage-total-cost").textContent = money(usageData.cost);
    const price = Number(usageData.price || 0.01);
    usageNote.textContent = usageData.source === "control"
      ? (usageData.stale ? "آخر قراءة من لوحة التحكم (الخادم غير متاح الآن). " : "من لوحة التحكم: تُحسب لكل حساب، وتبقى حتى لو أُعيد تثبيت التطبيق. ")
        + money(price) + " لكل تعليق."
      : "محسوبة في هذه النسخة: " + money(price) + " لكل تعليق.";
  }
  async function loadCommentsUsage(fresh) {
    try {
      const response = await fetchWithTimeout(apiRoot + "/comments-usage" + (fresh ? "?fresh=1" : ""), {headers: {"X-CSRF-Token": csrf}, cache: "no-store"});
      const data = await response.json();
      if (!response.ok || !data.success) return;
      usageData = data;
      renderUsage();
    } catch (_) {}
  }
  function openUsage() {
    usageBox.hidden = false;
    renderUsage();
    loadCommentsUsage(true);
  }
  function closeUsage() { usageBox.hidden = true; }
  usagePill.addEventListener("click", openUsage);
  document.getElementById("usage-close").addEventListener("click", closeUsage);
  document.getElementById("usage-done").addEventListener("click", closeUsage);
  document.getElementById("usage-refresh").addEventListener("click", () => loadCommentsUsage(true));
  usageBox.addEventListener("click", (event) => { if (event.target === usageBox) closeUsage(); });

  function shortPath(url) {
    try { return new URL(url).pathname; } catch (_) { return url; }
  }

  function stat(value, label) {
    const box = document.createElement("div");
    box.className = "stat";
    const number = document.createElement("b");
    number.textContent = String(value);
    const caption = document.createElement("span");
    caption.textContent = label;
    box.append(number, caption);
    return box;
  }

  function pill(text, kind) {
    const node = document.createElement("span");
    node.className = "pill " + kind;
    node.textContent = text;
    return node;
  }

  async function postJson(path, payload) {
    const response = await fetch(apiRoot + path, {
      method: "POST",
      headers: {"Content-Type": "application/json", "X-CSRF-Token": csrf, "X-Client-Id": clientId()},
      cache: "no-store",
      body: JSON.stringify({...payload, csrf_token: csrf})
    });
    const data = await response.json();
    if (!response.ok && !data.message) throw new Error("تعذّر إكمال الطلب.");
    return data;
  }

  function renderProgress(data) {
    progressPanel.hidden = false;
    const reduceMotion = window.matchMedia("(prefers-reduced-motion: reduce)").matches;
    progressPanel.scrollIntoView({block: "nearest", behavior: reduceMotion ? "auto" : "smooth"});
    const phase = data.phase || "collect";
    const titles = {login: "فتح القروب", prepare: "تجهيز المهمة", collect: "جمع تغريدات القروب", act: "تنفيذ الإجراءات"};
    progressTitle.textContent = titles[phase] || "جارٍ العمل";
    progressMessage.textContent = data.message || "";
    const current = phase === "act" ? (data.done || 0) : (data.collected || 0);
    const total = data.requested || 0;
    progressCount.textContent = String(current);
    progressDenom.textContent = total ? " / " + total : "";
    const pct = total ? Math.max(0, Math.min(100, Math.round((current / total) * 100))) : 0;
    const indeterminate = phase === "login" || phase === "prepare" || !total;
    meter.classList.toggle("is-indeterminate", indeterminate);
    meterBar.style.width = indeterminate ? "" : pct + "%";
    meter.setAttribute("aria-valuenow", String(pct));
    const elapsed = Math.max(0, Math.round((performance.now() - progressStarted) / 1000));
    const mins = Math.floor(elapsed / 60);
    const secs = elapsed % 60;
    const clock = mins ? mins + " د " + secs + " ث" : secs + " ث";
    progressNote.textContent = phase === "act"
      ? "مضى " + clock + ". الحالات المفعّلة مسبقًا تُتجاوز."
      : "مضى " + clock + ". لا يُنفَّذ أي إجراء خلال هذه المرحلة.";
  }

  function finishTrackedJob(data) {
    if (!data || data.status === "running") return;
    showNotice(data.message || "", Boolean(data.success));
    renderProgress(data);
    if (data.status === "interrupted") {
      progressNote.textContent = "آخر حالة قبل توقف السكربت. لن تُستكمل العملية تلقائيًا.";
    }
    const hasResults = Array.isArray(data.results) && data.results.length > 0;
    if (data.kind === "execute" && hasResults) renderResults(data);
    loadSessions();
  }

  function renderResults(data) {
    const rows = data.results || [];
    let done = 0;
    let skip = 0;
    let fail = 0;
    repostList.replaceChildren();
    rows.forEach((row, index) => {
      const item = document.createElement("li");
      const top = document.createElement("div");
      top.className = "post-top";
      const idx = document.createElement("span");
      idx.className = "idx";
      idx.textContent = String(index + 1);
      const link = document.createElement("a");
      link.href = row.url;
      link.target = "_blank";
      link.rel = "noopener noreferrer";
      link.textContent = shortPath(row.url || "");
      top.append(idx, link);
      item.appendChild(top);
      const pills = document.createElement("div");
      pills.className = "pills";
      Object.entries(row.actions || {}).forEach(([key, value]) => {
        let kind = "is-fail";
        if (value === "تم التنفيذ") { kind = "is-will"; done += 1; }
        else if (String(value).includes("مفعّل") || String(value).includes("تخطي")) { kind = "is-skip"; skip += 1; }
        else fail += 1;
        pills.appendChild(pill((LABELS[key] || key) + " · " + value, kind));
      });
      item.appendChild(pills);
      if (row.comment) {
        const note = document.createElement("p");
        note.className = "excerpt";
        note.textContent = row.comment;
        item.appendChild(note);
      }
      repostList.appendChild(item);
    });
    resultStats.replaceChildren(stat(done, "نُفّذ"), stat(skip, "تُجاوز"), stat(fail, "لم يكتمل"));
    noReposts.hidden = rows.length > 0;
    repostResults.hidden = false;
    reveal(repostResults);
  }

  commentToggle.addEventListener("change", syncGemini);
  if (showGemini) showGemini.addEventListener("click", () => openGemini(geminiFields.hidden));
  if (claudeFields) {
    const claudeKey = document.getElementById("claude-key");
    const claudeModel = document.getElementById("claude-model");
    showClaude.addEventListener("click", () => {
      claudeFields.hidden = !claudeFields.hidden;
      showClaude.setAttribute("aria-expanded", claudeFields.hidden ? "false" : "true");
      if (!claudeFields.hidden) claudeKey.focus();
    });
    document.getElementById("save-claude").addEventListener("click", async () => {
      try {
        const data = await postJson("/claude", {api_key: claudeKey.value.trim(), model: claudeModel.value.trim()});
        showNotice(data.message || "تعذّر حفظ مفتاح Claude.", Boolean(data.success));
        if (data.success) {
          claudeKey.value = "";
          showOwnClaude(data);
          showCommentsEngine(data.comments_engine);
        }
      } catch (_) {
        showNotice("تعذّر حفظ مفتاح Claude.", false);
      }
    });
    document.getElementById("delete-claude").addEventListener("click", async () => {
      if (!window.confirm("حذف مفتاح Claude؟ تعود التعليقات إلى Gemini.")) return;
      try {
        const data = await postJson("/claude/delete", {});
        showNotice(data.message || "تعذّر حذف مفتاح Claude.", Boolean(data.success));
        if (data.success) {
          showOwnClaude(data);
          showCommentsEngine(data.comments_engine);
        }
      } catch (_) {
        showNotice("تعذّر حذف مفتاح Claude.", false);
      }
    });
  }
  // The reply's voice chosen last time, on this browser ("_v2": a choice made before «مذكر» became the
  // default is not restored).
  try {
    const voice = localStorage.getItem("x_reply_voice_v2");
    const box = document.querySelector('input[name="reply-voice"][value="' + voice + '"]');
    if (box) box.checked = true;
  } catch (_) {}
  document.querySelectorAll('input[name="reply-voice"]').forEach((box) => box.addEventListener("change", () => {
    try {
      localStorage.setItem("x_reply_voice_v2", selectedVoice());
    } catch (_) {}
  }));
  const savedModel = geminiByOwner ? "" : localStorage.getItem("x_gemini_model");
  const savedKey = geminiByOwner ? "" : localStorage.getItem("x_gemini_key");
  if (savedModel) geminiModel.value = savedModel;
  if (savedKey) geminiKey.value = savedKey;
  let geminiSaveTimer = 0;
  function rememberGeminiLocal() {
    if (geminiByOwner) return;
    const key = geminiKey.value.trim();
    const model = geminiModel.value.trim();
    if (key) localStorage.setItem("x_gemini_key", key);
    if (model) localStorage.setItem("x_gemini_model", model);
    clearTimeout(geminiSaveTimer);
    geminiSaveTimer = setTimeout(() => {
      if (!key && !model) return;
      postJson("/gemini", {gemini_api_key: key, gemini_model: model}).catch(() => {});
    }, 350);
  }
  geminiKey.addEventListener("change", rememberGeminiLocal);
  geminiModel.addEventListener("change", rememberGeminiLocal);
  geminiKey.addEventListener("blur", rememberGeminiLocal);
  geminiModel.addEventListener("blur", rememberGeminiLocal);
  // «اختبار قدرة الهاتف»: the phone's memory, processor, heat, battery and background permissions (from the
  // app), with a short speed test here; then how many accounts it can run at the same time. Shown as a system
  // console: each line is typed a letter at a time (a touch on the screen shows the rest at once).
  const phoneCheckBtn = document.getElementById("phone-check");
  const pcBox = document.getElementById("phone-check-box");
  const pcScreen = document.getElementById("pc-screen");
  const pcAgain = document.getElementById("pc-again");
  const pcCursor = document.createElement("span");
  pcCursor.className = "pc-cursor";
  const typeAtOnce = window.matchMedia("(prefers-reduced-motion: reduce)").matches;
  let pcRun = 0;
  let pcSkip = false;
  const pcSleep = (ms) => new Promise((done) => setTimeout(done, ms));
  function speedTest(ms) {
    // integer math, array and text work: the kind of work a page of X keeps doing
    const end = performance.now() + ms;
    let rounds = 0;
    let x = 1;
    const values = new Array(256).fill(0);
    while (performance.now() < end) {
      for (let i = 0; i < 4000; i++) { x = (x * 1103515245 + 12345) & 0x7fffffff; values[i & 255] = x; }
      values.sort((a, b) => a - b);
      let text = "";
      for (let i = 0; i < 40; i++) text += (values[i] % 36).toString(36);
      if (text.length < 0) x++;
      rounds++;
    }
    return Math.round(rounds * 1000 / ms);
  }
  // One line of the console, typed a letter at a time. kind: "" (a step), "is-head", "is-dim" (a detail).
  async function pcType(text, kind, run, pace) {
    const line = document.createElement("div");
    line.className = "pc-line" + (kind ? " " + kind : "");
    const body = document.createElement("span");
    if (kind !== "is-dim") {
      const prompt = document.createElement("span");
      prompt.className = "pc-p";
      prompt.textContent = "› ";
      line.append(prompt);
    }
    line.append(body, pcCursor);
    pcScreen.appendChild(line);
    for (const letter of Array.from(String(text))) {
      if (run !== pcRun) return line;
      body.textContent += letter;
      if (!pcSkip && !typeAtOnce && letter !== " ") await pcSleep(pace || 12);
      pcScreen.scrollTop = pcScreen.scrollHeight;
    }
    return line;
  }
  function pcTag(line, level) {
    const tag = document.createElement("span");
    tag.className = "pc-tag is-" + level;
    tag.textContent = level === "ok" ? "  [ سليم ]" : level === "warn" ? "  [ تنبيه ]" : "  [ خطأ ]";
    line.insertBefore(tag, pcCursor);
  }
  const gb = (mb) => (Math.round(mb / 102.4) / 10).toLocaleString("en-US");
  async function runPhoneCheck() {
    const run = ++pcRun;
    pcSkip = false;
    pcBox.hidden = false;
    pcAgain.hidden = true;
    pcScreen.replaceChildren();
    await pcType("بدء فحص قدرة الهاتف…", "is-head", run);
    await pcType("قراءة معلومات الجهاز…", "", run);
    let report = {};
    try {
      const response = await fetchWithTimeout(apiRoot + "/phone-check", {cache: "no-store"}, 20000);
      const data = await response.json();
      report = (data && data.report) || {};
    } catch (_) {}
    if (run !== pcRun) return;
    const inApp = Boolean(report.in_app);
    if (inApp) {
      await pcType([report.model, report.android ? "أندرويد " + report.android : "", report.webview ? "WebView " + report.webview : ""]
        .filter(Boolean).join(" · "), "is-dim", run, 5);
    }
    await pcType("اختبار سرعة المعالج…", "", run);
    await pcSleep(60);
    if (run !== pcRun) return;
    speedTest(150);
    const speed = Math.max(speedTest(700), speedTest(700));
    if (run !== pcRun) return;

    const most = report.max_accounts || MAX_ACCOUNTS;
    const per = 450, reserve = 1024;
    const totalMb = report.ram_total_mb || (navigator.deviceMemory ? navigator.deviceMemory * 1024 : 0);
    const availMb = report.ram_avail_mb || 0;
    let byRam = 2;
    if (inApp && availMb) byRam = Math.floor((availMb + (report.browsers_open || 0) * per - reserve) / per);
    else if (totalMb) byRam = totalMb >= 6144 ? 3 : totalMb >= 3072 ? 2 : 1;
    if (totalMb && totalMb < 3072) byRam = Math.min(byRam, 1);
    else if (totalMb && totalMb < 6144) byRam = Math.min(byRam, 2);
    if (report.low_ram_device) byRam = Math.min(byRam, 1);
    const cores = report.cores || navigator.hardwareConcurrency || 0;
    const ghz = (report.max_mhz || 0) / 1000;
    let byCpu = speed >= 9000 ? 3 : speed >= 4500 ? 2 : 1;
    if (cores && cores < 6) byCpu = Math.min(byCpu, 1);
    else if (ghz && ghz < 2.0) byCpu = Math.min(byCpu, 2);
    let count = Math.min(byRam, byCpu, most);
    if (inApp && report.profiles === false) count = Math.min(count, 1);
    if (typeof report.thermal === "number" && report.thermal >= 3) count -= 1;
    count = Math.max(1, Math.min(most, count));

    // What each check found: [level, what, detail]
    const rows = [];
    const ramText = totalMb ? gb(totalMb) + " جيجا" + (availMb ? " · المتاح الآن " + gb(availMb) + " جيجا" : "") : "غير معروفة";
    if (inApp && availMb && byRam < 1) rows.push(["bad", "الذاكرة: " + ramText, "المتاح قليل الآن: أغلق التطبيقات الأخرى ثم أعد الفحص."]);
    else rows.push([byRam >= 2 ? "ok" : "warn", "الذاكرة: " + ramText,
      byRam >= 3 ? "تكفي ٣ حسابات." : byRam === 2 ? "تكفي حسابين." : "تكفي حسابًا واحدًا في كل مرة."]);
    rows.push([byCpu >= 2 ? "ok" : "warn", "المعالج: " + (byCpu >= 3 ? "قوي" : byCpu === 2 ? "متوسط" : "ضعيف"),
      [cores ? cores + " أنوية" : "", ghz ? "أعلى سرعة " + ghz.toFixed(1) + " GHz" : "", "نتيجة الاختبار " + speed.toLocaleString("en-US")].filter(Boolean).join(" · ")]);
    if (inApp) {
      if (report.profiles === false) rows.push(["bad", "متصفح مستقل لكل حساب: غير مدعوم", "لا تعمل الحسابات معًا إلا بعد تحديث «Android System WebView» من المتجر."]);
      else rows.push(["ok", "متصفح مستقل لكل حساب: مدعوم", "كل حساب في متصفحه، وتعمل الحسابات معًا."]);
      const heat = typeof report.thermal === "number" ? report.thermal : -1;
      if (heat >= 3) rows.push(["bad", "الحرارة: الجوال حار الآن", "خُفّض العدد واحدًا. دع الجوال يبرد ثم أعد الفحص."]);
      else if (heat === 2) rows.push(["warn", "الحرارة: دافئ", "قد يبطئ الجوال نفسه إذا زادت الحرارة."]);
      else if (heat >= 0) rows.push(["ok", "الحرارة: طبيعية", ""]);
      const level = typeof report.battery === "number" && report.battery >= 0 ? report.battery + "%" : "";
      if (report.power_save) rows.push(["warn", "وضع توفير الطاقة: مفعّل", "يبطئ المعالج ويوقف العمل في الخلفية. أوقفه أثناء المهام."]);
      else if (!report.charging && typeof report.battery === "number" && report.battery >= 0 && report.battery < 30) rows.push(["warn", "البطارية: " + level, "منخفضة وغير موصولة بالشاحن. المهام الطويلة تحتاج الشاحن."]);
      else rows.push(["ok", "البطارية" + (level ? ": " + level : ""), report.charging ? "على الشاحن." : "يُفضّل الشاحن في المهام الطويلة."]);
      if (report.overlay === false) rows.push(["bad", "العمل في الخلفية: ينقص إذن", "امنح إذن «الظهور فوق التطبيقات»، وإلا تتوقف المهام حين تخرج من التطبيق."]);
      else if (report.battery_free === false) rows.push(["warn", "العمل في الخلفية: تحسين البطارية مفعّل", "من إعدادات الجوال استثنِ التطبيق من «تحسين البطارية» حتى لا يوقفه النظام."]);
      else rows.push(["ok", "العمل في الخلفية", "الأذونات مكتملة."]);
    } else {
      rows.push(["warn", "الفحص الكامل داخل التطبيق", "هنا تُقدَّر الذاكرة والمعالج من المتصفح فقط."]);
    }
    for (const [level, what, detail] of rows) {
      const line = await pcType(what, "", run);
      if (run !== pcRun) return;
      pcTag(line, level);
      if (detail) await pcType(detail, "is-dim", run, 5);
    }
    if (run !== pcRun) return;
    await pcType("اكتمل الفحص.", "is-head", run);
    const final = document.createElement("div");
    final.className = "pc-final" + (count >= 2 ? (count === 2 && most > 2 ? " is-mid" : "") : " is-low");
    const number = document.createElement("b");
    number.textContent = String(count);
    const verdict = document.createElement("span");
    final.append(number, verdict);
    pcScreen.appendChild(final);
    const verdictText = count >= 3 ? "يتحمّل جوالك ٣ حسابات تعمل في الوقت نفسه."
      : count === 2 ? "يتحمّل جوالك حسابين يعملان في الوقت نفسه."
      : "يتحمّل جوالك حسابًا واحدًا يعمل في كل مرة. شغّل مهام الحسابات الأخرى بعده.";
    for (const letter of Array.from(verdictText)) {
      if (run !== pcRun) return;
      verdict.textContent += letter;
      if (!pcSkip && !typeAtOnce && letter !== " ") await pcSleep(16);
    }
    await pcType("تقدير تقريبي من مواصفات الهاتف وحالته الآن واختبار سرعة قصير.", "is-dim", run, 4);
    pcScreen.scrollTop = pcScreen.scrollHeight;
    pcAgain.hidden = false;
  }
  function closePhoneCheck() {
    pcRun++;                                         // (stops any typing still going)
    pcBox.hidden = true;
  }
  if (phoneCheckBtn) phoneCheckBtn.addEventListener("click", () => { runPhoneCheck(); });
  pcAgain.addEventListener("click", () => { runPhoneCheck(); });
  pcScreen.addEventListener("click", () => { pcSkip = true; });
  document.getElementById("pc-close").addEventListener("click", closePhoneCheck);
  document.getElementById("pc-done").addEventListener("click", closePhoneCheck);
  pcBox.addEventListener("click", (event) => { if (event.target === pcBox) closePhoneCheck(); });
  document.addEventListener("keydown", (event) => { if (event.key === "Escape" && !pcBox.hidden) closePhoneCheck(); });
  editGemini.addEventListener("click", () => {
    if (geminiKey.readOnly) {
      lockGemini(false);
      geminiKey.focus();
      geminiKey.select();
      return;
    }
    lockGemini(true);
    rememberGeminiLocal();
  });
  syncGemini();
  loadCommentsUsage(false);
  setInterval(() => loadCommentsUsage(false), 60000);

  // تنبيهات المالك وتعليماته من لوحة التحكّم: داخل التطبيق تذهب إلى قائمة التنبيهات (تفتح وحدها)، وفي
  // المتصفح العادي تظهر في شريط التنبيه أعلى الصفحة.
  let noticesBusy = false;
  async function loadAdminNotices() {
    if (noticesBusy) return;
    noticesBusy = true;
    try {
      const response = await fetchWithTimeout(apiRoot + "/notices", {headers: {"X-CSRF-Token": csrf}, cache: "no-store"}, 20000);
      const data = await response.json();
      if (!response.ok || !data.success) return;
      const inApp = Boolean(window.GroupsNative && typeof window.GroupsNative.notify === "function");
      for (const item of data.notices || []) {
        if (inApp) pushNative(item.text, "admin-" + item.kind);
        else showNotice("📢 " + item.text, item.kind === "info");
      }
    } catch (_) {
    } finally {
      noticesBusy = false;
    }
  }
  loadAdminNotices();
  setInterval(loadAdminNotices, 45000);

  // «مساعدة»: وصف المشكلة مع صور أو فيديو قصير، يُرسل إلى صاحب البرنامج (يصل إلى «الرسائل» في لوحة التحكّم).
  const helpBox = document.getElementById("help-box");
  if (helpBox) {
    const helpText = document.getElementById("help-text");
    const helpInput = document.getElementById("help-files");
    const helpList = document.getElementById("help-list");
    const helpStatus = document.getElementById("help-status");
    const helpSend = document.getElementById("help-send");
    const helpAttach = document.getElementById("help-attach");
    const HELP_MAX_FILES = 5, HELP_IMAGE_MB = 8, HELP_VIDEO_MB = 25;
    let helpFiles = [];
    let helpBusy = false;
    const sizeText = (bytes) => bytes >= 1048576 ? (bytes / 1048576).toFixed(1) + " ميجابايت" : Math.max(1, Math.round(bytes / 1024)) + " كيلوبايت";
    function helpSay(text, kind) {
      helpStatus.textContent = text || "";
      helpStatus.className = "help-status" + (kind ? " " + kind : "");
      helpStatus.hidden = !text;
    }
    function renderHelpFiles() {
      helpList.replaceChildren();
      helpFiles.forEach((entry, index) => {
        const row = document.createElement("li");
        let thumb;
        if (entry.url) {
          thumb = document.createElement("img");
          thumb.src = entry.url;
          thumb.alt = "";
        } else {
          thumb = document.createElement("span");
          thumb.textContent = "🎬";
        }
        thumb.className = "thumb";
        const name = document.createElement("div");
        name.className = "name";
        name.textContent = entry.file.name || (entry.url ? "صورة" : "فيديو");
        const small = document.createElement("small");
        small.textContent = sizeText(entry.file.size);
        const bar = document.createElement("div");
        bar.className = "bar";
        entry.bar = document.createElement("i");
        bar.appendChild(entry.bar);
        name.append(small, bar);
        const remove = document.createElement("button");
        remove.type = "button";
        remove.className = "usage-x";
        remove.textContent = "×";
        remove.setAttribute("aria-label", "إزالة الملف");
        remove.disabled = helpBusy;
        remove.addEventListener("click", () => {
          if (entry.url) URL.revokeObjectURL(entry.url);
          helpFiles.splice(index, 1);
          renderHelpFiles();
        });
        row.append(thumb, name, remove);
        helpList.appendChild(row);
      });
      helpList.hidden = !helpFiles.length;
      helpAttach.disabled = helpBusy || helpFiles.length >= HELP_MAX_FILES;
    }
    function openHelp() {
      helpBox.hidden = false;
      if (!helpBusy) helpSay("");
      setTimeout(() => helpText.focus(), 50);
    }
    function closeHelp() { helpBox.hidden = true; }
    function resetHelp() {
      helpFiles.forEach((entry) => entry.url && URL.revokeObjectURL(entry.url));
      helpFiles = [];
      helpText.value = "";
      renderHelpFiles();
    }
    document.getElementById("help-open").addEventListener("click", openHelp);
    document.getElementById("help-close").addEventListener("click", closeHelp);
    document.getElementById("help-cancel").addEventListener("click", closeHelp);
    helpBox.addEventListener("click", (event) => { if (event.target === helpBox) closeHelp(); });
    helpAttach.addEventListener("click", () => helpInput.click());
    helpInput.addEventListener("change", () => {
      const problems = [];
      for (const file of Array.from(helpInput.files || [])) {
        const video = (file.type || "").startsWith("video/");
        const image = (file.type || "").startsWith("image/");
        if (helpFiles.length >= HELP_MAX_FILES) { problems.push("الحد الأقصى " + HELP_MAX_FILES + " ملفات."); break; }
        if (!video && !image) { problems.push("«" + file.name + "» ليس صورة ولا فيديو."); continue; }
        if (file.size > (video ? HELP_VIDEO_MB : HELP_IMAGE_MB) * 1048576) {
          problems.push("«" + file.name + "» أكبر من " + (video ? HELP_VIDEO_MB + " ميجابايت. قصّ الفيديو أو صوّر مقطعًا أقصر." : HELP_IMAGE_MB + " ميجابايت."));
          continue;
        }
        helpFiles.push({file, url: image ? URL.createObjectURL(file) : ""});
      }
      helpInput.value = "";
      renderHelpFiles();
      helpSay(problems.join(" "), problems.length ? "is-bad" : "");
    });
    function uploadHelpFile(entry) {
      return new Promise((resolve, reject) => {
        const request = new XMLHttpRequest();
        request.open("POST", apiRoot + "/support/upload");
        request.setRequestHeader("X-CSRF-Token", csrf);
        request.setRequestHeader("X-File-Type", entry.file.type || "");
        request.setRequestHeader("X-File-Name", encodeURIComponent(entry.file.name || ""));
        request.upload.onprogress = (event) => {
          if (entry.bar && event.lengthComputable) entry.bar.style.width = Math.round((event.loaded / event.total) * 100) + "%";
        };
        request.onload = () => {
          let data = {};
          try { data = JSON.parse(request.responseText); } catch (_) {}
          if (request.status === 200 && data.success && data.id) resolve(data.id);
          else reject(new Error(data.message || "تعذّر تجهيز الملف «" + (entry.file.name || "") + "»."));
        };
        request.onerror = () => reject(new Error("تعذّر تجهيز الملف «" + (entry.file.name || "") + "»."));
        request.send(entry.file);
      });
    }
    async function waitForHelpSend(id) {
      for (;;) {
        await new Promise((resolve) => setTimeout(resolve, 1000));
        let data;
        try {
          const response = await fetchWithTimeout(apiRoot + "/support/status", {headers: {"X-CSRF-Token": csrf}, cache: "no-store"});
          data = await response.json();
        } catch (_) { continue; }
        if (!data || data.id !== id) return {state: "failed", message: "انقطع الإرسال. أعد المحاولة."};
        if (data.state === "sending") { helpSay(data.message, ""); continue; }
        return data;
      }
    }
    helpSend.addEventListener("click", async () => {
      const text = helpText.value.trim();
      if (text.length < 5 && !helpFiles.length) { helpSay("اكتب وصفًا للمشكلة (كلمتان على الأقل).", "is-bad"); helpText.focus(); return; }
      helpBusy = true;
      helpSend.disabled = true;
      renderHelpFiles();
      try {
        const ids = [];
        for (let i = 0; i < helpFiles.length; i += 1) {
          helpSay("يجهّز الملف " + (i + 1) + " من " + helpFiles.length + "…", "");
          ids.push(await uploadHelpFile(helpFiles[i]));
        }
        helpSay("يرسل الرسالة…", "");
        const started = await postJson("/support/send", {text, files: ids});
        if (!started.success) throw new Error(started.message || "تعذّر الإرسال.");
        const done = await waitForHelpSend(started.id);
        if (done.state !== "done") throw new Error(done.message || "تعذّر الإرسال.");
        resetHelp();
        closeHelp();
        showNotice(done.message, true);
      } catch (error) {
        helpSay(error.message || "تعذّر الإرسال. أعد المحاولة.", "is-bad");
      } finally {
        helpBusy = false;
        helpSend.disabled = false;
        renderHelpFiles();
      }
    });
  }
  document.addEventListener("visibilitychange", () => { if (!document.hidden) loadAdminNotices(); });
  loadActionCounts();
  setInterval(loadActionCounts, 5000);
  // The invisible top-left button (the owner's copy only): with the password, the comment cost starts
  // again from 0 (the count stays). Users' costs are reset from «توزيع البرنامج».
  document.getElementById("cost-reset")?.addEventListener("click", async () => {
    const password = window.prompt("كلمة السر");
    if (password === null) return;
    try {
      const data = await postJson("/gemini-usage/reset", {password});
      showNotice(data.message || "تعذّرت إعادة التعيين.", Boolean(data.success));
      if (data.success) loadCommentsUsage(true);
    } catch (_) {
      showNotice("تعذّر الاتصال أثناء إعادة التعيين.", false);
    }
  });

  accountSettings.addEventListener("click", () => setAccountPanel(accountPanel.hidden));

  async function verifySession() {
    try {
      const pulled = await postJson("/browser-session", {});
      if (pulled.success && pulled.auth_token) tokenField.value = pulled.auth_token;
    } catch (_) {}
    const authToken = tokenField.value.trim();
    if (!authToken) { showNotice("اضغط تسجيل الدخول، ثم ارجع واضغط تحقق.", false); return; }
    if (loginButton) loginButton.disabled = true;
    quickVerify.disabled = true;
    showNotice("جارٍ التحقق من الجلسة…", true);
    try {
      const data = await postJson("/verify-login", {auth_token: authToken});
      showNotice(data.message, data.success);
      if (data.success) {
        showAccount(data.username ? "تم التحقق: هذه الجلسة تخص @" + data.username : "تم التحقق من الدخول، دون قراءة الاسم.");
        await loadSessions();
      }
    } catch (_) {
      showNotice("تعذّر الاتصال لإكمال التحقق.", false);
    } finally {
      if (loginButton) loginButton.disabled = false;
      quickVerify.disabled = false;
    }
  }
  if (loginButton) loginButton.addEventListener("click", verifySession);
  quickVerify.addEventListener("click", verifySession);
  // «تسجيل الدخول»: first the steps (sign in, open the chat and enter its code, come back and press «تحقق»),
  // then the browser opens when the user says so.
  const loginGuide = document.getElementById("login-guide");
  async function openLoginBrowser() {
    const button = document.getElementById("browser-login");
    if (button) button.disabled = true;
    showNotice("يُفتح المتصفح لتسجيل الدخول…", true);
    try {
      const data = await postJson("/browser-login", {});
      showNotice(data.message, Boolean(data.success));
    } catch (_) {
      showNotice("تعذّر فتح المتصفح.", false);
    } finally {
      if (button) button.disabled = false;
    }
  }
  function closeLoginGuide() { loginGuide.hidden = true; }
  document.getElementById("browser-login")?.addEventListener("click", () => { loginGuide.hidden = false; });
  document.getElementById("guide-go").addEventListener("click", () => { closeLoginGuide(); openLoginBrowser(); });
  document.getElementById("guide-cancel").addEventListener("click", closeLoginGuide);
  document.getElementById("guide-close").addEventListener("click", closeLoginGuide);
  loginGuide.addEventListener("click", (event) => { if (event.target === loginGuide) closeLoginGuide(); });

  function renderGroups() {
    groupBox.hidden = linksMode || groupNames.length === 0;
    // Three rows, or fewer when there are fewer groups (no empty rows under them).
    groupList.style.gridTemplateRows = "repeat(" + Math.max(1, Math.min(3, groupNames.length)) + ", auto)";
    groupList.replaceChildren();
    groupNames.forEach((name) => {
      const item = document.createElement("li");
      const pick = document.createElement("button");
      pick.type = "button";
      pick.className = "pick" + (name === selectedGroup ? " is-on" : "");
      const who = document.createElement("span");
      who.className = "who";
      who.textContent = name;
      pick.append(who);
      pick.addEventListener("click", () => {
        selectedGroup = name;
        renderGroups();
        snapshotActive();
        showNotice("تم اختيار: " + name, true);
        pushScreen();
      });
      item.append(pick);
      groupList.appendChild(item);
    });
  }

  groupsButton.addEventListener("click", async () => {
    if (linksMode) {
      // «القروبات»: back to the groups shown before, at once (no browser, no chat).
      setLinksMode(false);
      if (!groupNames.length) showNotice("لا توجد قروبات معروضة بعد. اضغط «عرض القروبات» لجلبها.", true);
      return;
    }
    const authToken = tokenField.value.trim();
    const pin = pinField.value.trim();
    if (!authToken) { showNotice("سجّل الدخول ثم اضغط تحقق أولًا.", false); return; }
    if (!/^\d{4,8}$/.test(pin)) { showNotice("رمز الدردشة ٤ إلى ٨ أرقام.", false); revealField(pinField); return; }
    groupsButton.disabled = true;
    const settle = !!waitGroups.checked;
    const settleSeconds = secondsFrom(waitGroupsSec, 1, 120, 30);
    showNotice(settle ? "جارٍ فتح الدردشة ثم الانتظار " + settleSeconds + " ث قبل التقاط القروبات…" : "جارٍ فتح الدردشة وعرض القروبات…", true);
    try {
      const data = await postJson("/groups", {auth_token: authToken, chat_pin: pin, wait: settle, wait_seconds: settleSeconds});
      if (!data.success) {
        showNotice(data.message || "تعذّر عرض القروبات.", false);
        return;
      }
      groupNames = data.groups || [];
      if (selectedGroup && !groupNames.includes(selectedGroup)) selectedGroup = "";
      renderGroups();
      showNotice(groupNames.length ? "ظهر " + groupNames.length + " قروب. اختر واحدًا ثم اضغط تنفيذ." : "لم يظهر أي قروب.", groupNames.length > 0);
    } catch (_) {
      showNotice("تعذّر الاتصال أثناء جلب القروبات.", false);
    } finally {
      groupsButton.disabled = false;
    }
  });

  document.getElementById("repost-form").addEventListener("submit", async (event) => {
    event.preventDefault();
    const authToken = tokenField.value.trim();
    const pin = pinField.value.trim();
    const stopRaw = stopField.value.trim();
    const stopMatch = stopRaw.match(/status\/(\d{6,25})/);
    const stopId = stopMatch ? stopMatch[1] : (/^\d{15,25}$/.test(stopRaw) ? stopRaw : "");
    const actions = selectedActions();
    const byLinks = linksMode;
    const links = byLinks ? pastedTweets(linksField.value) : [];
    if (!authToken) { showNotice("سجّل الدخول ثم اضغط تحقق أولًا.", false); return; }
    if (byLinks) {
      // No chat and no group: only the tweets are needed (the chat PIN is not).
      if (!links.length) { showNotice("الصق رابط تغريدة واحدًا على الأقل.", false); linksField.focus(); return; }
      if (links.length > MAX_LINKS) { showNotice("الحد الأقصى " + MAX_LINKS + " رابط في المهمة الواحدة.", false); linksField.focus(); return; }
    } else {
      if (!/^\d{4,8}$/.test(pin)) { showNotice("أدخل رمز الدردشة.", false); revealField(pinField); return; }
      if (!selectedGroup) { showNotice("اعرض القروبات ثم اختر واحدًا.", false); return; }
      if (!stopId) { showNotice("الصق رابط التغريدة المحددة أو رقمها.", false); stopField.focus(); return; }
    }
    if (!actions.length) { showNotice("اختر إجراءً واحدًا على الأقل.", false); return; }
    if (actions.includes("comment") && (geminiByOwner || controlOn)) {
      // (Its keys come from the owner when it starts: the script waits for them, and says if they do not come.)
    } else if (actions.includes("comment")) {
      repostButton.disabled = true;          // (not sent twice while it asks)
      await loadCommentsEngine();
      repostButton.disabled = false;
      if (!commentsByOther) {
        if (!geminiKey.value.trim()) { openGemini(true); lockGemini(false); showNotice("أدخل مفتاح Gemini.", false); geminiKey.focus(); return; }
        if (!geminiModel.value.trim()) { openGemini(true); lockGemini(false); showNotice("أدخل اسم النموذج.", false); geminiModel.focus(); return; }
      }
      rememberGeminiLocal();
    }
    repostButton.disabled = true;
    try {
      const task = {
        auth_token: authToken,
        chat_pin: pin,
        actions,
        gemini_api_key: geminiKey.value.trim(),
        gemini_model: geminiModel.value.trim(),
        reply_voice: selectedVoice()
      };
      if (byLinks) task.links = links;
      else Object.assign(task, {group: selectedGroup, stop_tweet: stopRaw});
      const started = await postJson("/group-run", task);
      if (!started.success || !started.job_id || !started.job_key) {
        showNotice(started.message || "تعذّر بدء التنفيذ.", false);
        return;
      }
      const accountRow = sessionRows.find((item) => item.token === authToken);
      const account = accountRow && accountRow.username ? "@" + accountRow.username : "";
      const name = byLinks ? "روابط (" + links.length + ")" : selectedGroup;
      followTask({
        id: started.job_id,
        key: started.job_key,
        token: authToken,
        title: name + (account ? " · " + account : ""),
        startedAt: Date.now()
      });
      showNotice(started.queued
        ? "أُضيفت المهمة إلى الانتظار: " + (started.message || "تبدأ تلقائيًا بعد انتهاء ما قبلها على هذا الحساب.").replace(/^في الانتظار: /, "")
        : (byLinks ? "بدأت مهمة على " + links.length + " تغريدة من الروابط." : "بدأت مهمة «" + selectedGroup + "»."), true);
    } catch (_) {
      showNotice("تعذّر الاتصال أثناء التنفيذ.", false);
    } finally {
      repostButton.disabled = false;
    }
  });

  tokenField.addEventListener("input", () => {
    const token = tokenField.value.trim();
    const row = sessionRows.find((item) => item.token === token);
    if (row) {
      showAccount(row.username ? "الجلسة المحفوظة: @" + row.username : "تم اختيار جلسة محفوظة.");
      if (document.activeElement !== pinField) pinField.value = row.chat_pin || "";
    } else showAccount("");
    renderSessions();
  });

  let pinSaveTimer = 0;
  function saveAccountPin() {
    const token = tokenField.value.trim();
    const pin = pinField.value.trim();
    if (!token || !/^\d{4,8}$/.test(pin)) return;
    const row = sessionRows.find((item) => item.token === token);
    if (row) row.chat_pin = pin;
    postJson("/sessions/pin", {auth_token: token, chat_pin: pin}).catch(() => {});
  }

  let screenTimer = 0;
  function pushScreen() {
    clearTimeout(screenTimer);
    screenTimer = setTimeout(() => {
      const payload = {
        auth_token: tokenField.value.trim(),
        chat_pin: pinField.value.trim(),
        group: selectedGroup,
        stop_tweet: stopField.value.trim(),
        actions: selectedActions()
      };
      if (groupNames.length) payload.groups = groupNames;
      postJson("/screen", payload).catch(() => {});
    }, 350);
  }

  function applyScreen(data) {
    if (!data) return;
    if (data.auth_token) tokenField.value = data.auth_token;
    lockToken(true);
    if (data.chat_pin) pinField.value = data.chat_pin;
    if (typeof data.stop_tweet === "string") stopField.value = data.stop_tweet;
    if (Array.isArray(data.actions) && data.actions.length) {
      ["repost", "like", "bookmark", "comment"].forEach((key) => {
        const box = document.getElementById("action-" + key);
        if (box) box.checked = data.actions.includes(key);
      });
      syncGemini();
    }
    if (Array.isArray(data.groups) && data.groups.length) {
      groupNames = data.groups;
      if (data.group) selectedGroup = data.group;
      renderGroups();
    } else if (data.group) {
      selectedGroup = data.group;
    }
  }

  async function restoreScreen() {
    // The saved tasks start showing their progress at once, without waiting for the rest.
    readTasks().forEach((task) => followTask(task));
    let runningJobs = [];
    let screenJob = null;
    for (let attempt = 0; attempt < 2 && !screenJob; attempt += 1) {
      try {
        const response = await fetchWithTimeout(apiRoot + "/state", {cache: "no-store"});
        const data = await response.json();
        if (response.ok && data && data.success) {
          applyScreen(data);
          screenJob = data;
          runningJobs = Array.isArray(data.running_jobs) ? data.running_jobs : [];
        }
      } catch (_) {}
    }
    await loadSessions();
    runningJobs.slice().reverse().forEach((job) => {
      const same = screenJob && screenJob.job_id === job.id;
      followTask({
        id: job.id,
        key: same ? (screenJob.job_key || "") : "",
        token: (screenJob && screenJob.auth_token) || "",
        title: job.username || (screenJob && screenJob.group) || "مهمة"
      });
    });
    if (!runningJobs.length && screenJob && screenJob.job && screenJob.job.status && screenJob.job.status !== "running") {
      finishTrackedJob(screenJob.job);
    }
    // Now the account is known: show only its cards and its counters, and its own pasted links.
    activeToken = tokenField.value.trim();
    if (activeToken && accountState[activeToken]) {
      linksField.value = accountState[activeToken].linksText || "";
      setLinksMode(!!accountState[activeToken].links);
    }
    filterTaskCards();
    loadActionCounts();
    if (taskList.querySelector(".task-card:not([hidden])")) {
      taskBoard.hidden = false;
      taskBoard.scrollIntoView({block: "start"});
    } else {
      taskBoard.hidden = true;
    }
  }

  tokenField.addEventListener("change", pushScreen);
  tokenField.addEventListener("input", pushScreen);
  pinField.addEventListener("input", () => {
    clearTimeout(pinSaveTimer);
    pinSaveTimer = setTimeout(saveAccountPin, 400);
  });
  pinField.addEventListener("change", () => {
    saveAccountPin();
    pushScreen();
  });
  stopField.addEventListener("change", pushScreen);
  document.querySelectorAll('#repost-form input[type="checkbox"]').forEach((box) => {
    box.addEventListener("change", pushScreen);
  });

  restoreScreen();

  // Updates. A user's copy shows «تحديث» when the owner offers a newer version; the owner's
  // copy shows «توزيع البرنامج», which opens g.py's page.
  const updateBar = document.getElementById("update-bar");
  const updateText = document.getElementById("update-text");
  const updateButton = document.getElementById("update-button");
  const updateState = document.getElementById("update-state");
  const distLink = document.getElementById("dist-link");

  async function checkUpdate() {
    try {
      const response = await fetchWithTimeout(apiRoot + "/update/check", {cache: "no-store"}, 30000);
      const data = await response.json();
      if (data.owner) {
        // g.py's page: this host on its own port, unless CONTROL_URL says where.
        if (data.control_url || data.control_port) {
          distLink.href = data.control_url || location.protocol + "//" + location.hostname + ":" + data.control_port + "/";
          distLink.hidden = false;
        }
        return;
      }
      updateState.textContent = data.message || "";
      if (data.available && !updateButton.disabled) {
        updateText.textContent = "يتوفر إصدار جديد " + data.latest;
        updateButton.textContent = "تحديث إلى " + data.latest;
      }
      updateBar.hidden = !data.available;
    } catch (_) {}
  }

  updateButton.addEventListener("click", async () => {
    updateButton.disabled = true;
    updateText.textContent = "جارٍ تنزيل التحديث…";
    let data;
    try {
      data = await postJson("/update/apply", {});
    } catch (_) {
      data = {message: "تعذّر الاتصال أثناء التحديث."};
    }
    if (!data.success) {
      updateText.textContent = data.message || "تعذّر التحديث.";
      updateButton.disabled = false;
      return;
    }
    updateText.textContent = data.message;
    // Wait until the program runs again with the new version, then open its page.
    const started = Date.now();
    while (Date.now() - started < 90000) {
      await new Promise((done) => setTimeout(done, 1500));
      try {
        const response = await fetchWithTimeout(apiRoot + "/update/check?light=1", {cache: "no-store"}, 4000);
        if ((await response.json()).version === data.version) {
          location.reload();
          return;
        }
      } catch (_) {}
    }
    updateText.textContent = "لم يعد البرنامج للعمل بعد. حدّث الصفحة بعد قليل.";
  });

  checkUpdate();
  setInterval(checkUpdate, 30 * 60 * 1000);

})();
</script>
</body>
</html>

'''

PAGE = load_page()

ACTION_CONTROLS = {
    "repost": ("unretweet", "retweet"),
    "like": ("unlike", "like"),
    "bookmark": ("removeBookmark", "bookmark"),
}

READ_GROUPS_JS = r"""
(wanted) => {
  const clean = (value) => (value || "").replace(/\s+/g, " ").trim();
  const timeLike = /^(now|الآن|\d{1,2}:\d{2}(?:\s*[ap]m)?|\d+\s*[smhdw]|\d+\s*(?:د|دقائق|دقيقة|س|ساعة|ساعات|ي|يوم|أيام|ث|أسبوع|أسابيع))\.?$/i;
  const chrome = /^(all|unread|direct|groups|group|messages|search|new chat|chat|requests|people|الكل|غير مقروء|المباشرة|قروبات|القروبات|مجموعات|المجموعات|رسائل|بحث|تم)$/i;
  const roots = [];
  const walk = (root) => {
    if (!root || roots.includes(root)) return;
    roots.push(root);
    const nodes = root.querySelectorAll ? root.querySelectorAll("*") : [];
    for (const node of nodes) if (node.shadowRoot) walk(node.shadowRoot);
  };
  walk(document);
  const queryAll = (selector) => {
    const out = [];
    for (const root of roots) if (root.querySelectorAll) out.push(...root.querySelectorAll(selector));
    return out;
  };
  const rows = queryAll('[data-testid^="dm-conversation-item-"], [data-testid^="dm-message-request-item-"]');
  const nameOf = (row) => {
    const titled = [...row.querySelectorAll(".line-clamp-1")].map((el) => clean(el.textContent || "")).find((text) => text.length >= 2 && text.length <= 80 && !timeLike.test(text) && !chrome.test(text));
    if (titled) return titled;
    const leaves = [...row.querySelectorAll("span, div")].filter((el) => {
      if (el.querySelector("span, div")) return false;
      const text = clean(el.textContent || "");
      return text.length >= 2 && text.length <= 80 && !timeLike.test(text) && !chrome.test(text);
    });
    if (leaves.length) return clean(leaves[0].textContent || "");
    return "";
  };
  if (wanted) {
    const target = clean(typeof wanted === "object" ? (wanted.name || "") : wanted);
    const wantedId = typeof wanted === "object" ? String(wanted.testid || "") : "";
    const open = (row, how) => {
      const link = row.querySelector('a[href*="/i/chat/"], a[href*="/messages/"]');
      const path = link ? (link.getAttribute("href") || "") : "";
      if (link) link.click();
      else row.click();
      return {clicked: true, how, matched: nameOf(row), path: path, groups: [], rows: rows.length, loading: false};
    };
    // 1) The group's own id: stays the same when the group is renamed.
    if (wantedId) {
      for (const row of rows) if ((row.getAttribute("data-testid") || "") === wantedId) return open(row, "id");
    }
    // 2) The exact name.
    for (const row of rows) if (nameOf(row) === target) return open(row, "name");
    // 3) A very similar name: only a few characters changed (usually near the end).
    const chars = (text) => Array.from(text || "");
    const distance = (a, b) => {
      let prev = Array.from({length: b.length + 1}, (_, j) => j);
      for (let i = 1; i <= a.length; i++) {
        const cur = [i];
        for (let j = 1; j <= b.length; j++) {
          cur[j] = Math.min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (a[i - 1] === b[j - 1] ? 0 : 1));
        }
        prev = cur;
      }
      return prev[b.length];
    };
    const shared = (a, b) => { let n = 0; while (n < a.length && n < b.length && a[n] === b[n]) n++; return n; };
    const targetChars = chars(target);
    const allowed = Math.min(6, Math.max(2, Math.floor(targetChars.length * 0.35)));
    let best = null, bestDistance = Infinity, tie = false;
    for (const row of rows) {
      const id = row.getAttribute("data-testid") || "";
      const desc = row.getAttribute("aria-description") || "";
      if (!(/dm-conversation-item-g\d/.test(id) || /جماعية|group chat/i.test(desc))) continue;
      const nameChars = chars(nameOf(row));
      if (shared(targetChars, nameChars) < Math.min(4, targetChars.length)) continue;
      const d = distance(targetChars, nameChars);
      if (d > allowed) continue;
      if (d < bestDistance) { best = row; bestDistance = d; tie = false; }
      else if (d === bestDistance) tie = true;
    }
    if (best && !tie) return open(best, "similar");
    return {clicked: false, groups: [], rows: rows.length, loading: false};
  }
  const groups = [];
  const ids = [];
  const paths = [];
  const seen = new Set();
  for (const row of rows) {
    const id = row.getAttribute("data-testid") || "";
    const desc = row.getAttribute("aria-description") || "";
    const isGroup = /dm-conversation-item-g\d/.test(id) || /جماعية|group chat/i.test(desc);
    if (!isGroup) continue;
    const name = nameOf(row);
    if (!name || seen.has(name)) continue;
    seen.add(name);
    groups.push(name);
    ids.push(id);
    const link = row.querySelector('a[href*="/i/chat/"], a[href*="/messages/"]');
    paths.push(link ? (link.getAttribute("href") || "") : "");
  }
  const loading = queryAll('[data-testid="dm-conversation-list-loading-footer"]').some((el) => {
    const rect = el.getBoundingClientRect();
    return rect.width > 0 && rect.height > 0;
  });
  return {clicked: false, groups, ids, paths, rows: rows.length, loading};
}
"""

SCROLL_INBOX_JS = r"""
() => {
  const roots = [];
  const walk = (root) => {
    if (!root || roots.includes(root)) return;
    roots.push(root);
    const nodes = root.querySelectorAll ? root.querySelectorAll("*") : [];
    for (const node of nodes) if (node.shadowRoot) walk(node.shadowRoot);
  };
  walk(document);
  const query = (selector) => {
    for (const root of roots) {
      const found = root.querySelector && root.querySelector(selector);
      if (found) return found;
    }
    return null;
  };
  const panel = query('[data-testid="dm-inbox-panel"]');
  const row = query('[data-testid^="dm-conversation-item-"]');
  let node = panel || (row ? row.parentElement : null);
  while (node && node !== document.body) {
    const style = getComputedStyle(node);
    if (/(auto|scroll|overlay)/.test(style.overflowY) && node.scrollHeight > node.clientHeight + 40) {
      const before = node.scrollTop;
      node.scrollTop = before + Math.max(220, node.clientHeight * 0.75);
      return node.scrollTop > before;
    }
    node = node.parentElement;
  }
  return false;
}
"""

# Shared start of the group chat's scripts below: finds elements in the page and its shadow
# roots, and the element that really scrolls the chat.
CHAT_FIND_JS = r"""
  const roots = [];
  const walk = (root) => {
    if (!root || roots.includes(root)) return;
    roots.push(root);
    const nodes = root.querySelectorAll ? root.querySelectorAll("*") : [];
    for (const node of nodes) if (node.shadowRoot) walk(node.shadowRoot);
  };
  walk(document);
  const queryAll = (selector) => {
    const out = [];
    for (const root of roots) if (root.querySelectorAll) out.push(...root.querySelectorAll(selector));
    return out;
  };
  // How much of the element shows on the screen, in square pixels.
  const shownArea = (el) => {
    if (el.checkVisibility && !el.checkVisibility({opacityProperty: true, visibilityProperty: true, checkOpacity: true, checkVisibilityCSS: true})) return 0;
    const rect = el.getBoundingClientRect();
    const width = Math.min(rect.right, innerWidth) - Math.max(rect.left, 0);
    const height = Math.min(rect.bottom, innerHeight) - Math.max(rect.top, 0);
    return width > 0 && height > 0 ? width * height : 0;
  };
  // The match that shows most on the screen (the page can also hold a hidden copy of the
  // chat), else the first match.
  const query = (selector) => {
    const all = queryAll(selector);
    let best = null;
    let bestArea = 0;
    for (const el of all) {
      const area = shownArea(el);
      if (area > bestArea) {
        best = el;
        bestArea = area;
      }
    }
    return best || all[0] || null;
  };
  // The element that really scrolls the chat: X's scroller itself, one of its parents, or the
  // page (X's phone layout can scroll one of these instead of the scroller).
  const scrollerOf = (start) => {
    for (let node = start; node && node.nodeType === 1; node = node.parentElement || (node.parentNode && node.parentNode.host) || null) {
      if (/(auto|scroll|overlay)/.test(getComputedStyle(node).overflowY) && node.scrollHeight > node.clientHeight + 10) return node;
    }
    const page = document.scrollingElement;
    if (page && page.scrollHeight > page.clientHeight + 10) return page;
    return start;
  };
"""

GROUP_READ_TWEETS_JS = r"""
(arg) => {
  let stopId = "";
  let dir = 0;
  let factor = 1;
  if (arg && typeof arg === "object") {
    stopId = String(arg.stopId || "");
    dir = arg.dir === 1 || arg.dir === -1 ? arg.dir : 0;
    factor = Number(arg.factor) > 1 ? Number(arg.factor) : 1;
  } else {
    stopId = String(arg || "");
  }
  const clean = (value) => (value || "").replace(/\s+/g, " ").trim();
""" + CHAT_FIND_JS + r"""
  const collectDeep = (root, selector, out) => {
    if (!root || !root.querySelectorAll) return;
    root.querySelectorAll(selector).forEach((node) => out.push(node));
    root.querySelectorAll("*").forEach((node) => {
      if (node.shadowRoot) collectDeep(node.shadowRoot, selector, out);
    });
  };
  const list = query('[data-testid="dm-message-list"]')
    || query('[data-testid="dm-conversation-content"]')
    || query('[data-testid="dm-message-scroller"]');
  if (!list) return {tweets: [], pending: 0};
  const bubbles = [];
  collectDeep(list, '[data-testid^="message-"]', bubbles);
  const isBubble = (el) => {
    const id = el.getAttribute("data-testid") || "";
    return id.startsWith("message-") && !id.startsWith("message-text-");
  };
  const messages = bubbles.filter((el) => {
    if (!isBubble(el)) return false;
    const nested = [];
    collectDeep(el, '[data-testid^="message-"]', nested);
    return !nested.some((node) => node !== el && isBubble(node));
  });
  const targets = messages.length ? messages : [list];
  const statusRe = /(?:https?:\/\/)?(?:www\.)?(?:x|twitter)\.com\/(?:i\/web\/status\/|i\/status\/)?([A-Za-z0-9_]{1,15}\/)?status\/(\d{6,25})/gi;
  const bareRe = /status\/(\d{6,25})/;
  const tweets = [];
  const seen = new Set();
  let pending = 0;
  const climb = (node) => {
    const chain = [];
    let el = node;
    while (el && chain.length < 50) {
      chain.push(el);
      if (el.parentElement) el = el.parentElement;
      else if (el.parentNode && el.parentNode.nodeType === 11) el = el.parentNode.host;
      else break;
    }
    return chain;
  };
  const statusOf = (href) => {
    const match = (href || "").match(/status\/(\d{6,25})/);
    return match ? match[1] : "";
  };
  const insideQuote = (node) => climb(node).some((el) => {
    const test = (el.getAttribute && el.getAttribute("data-testid")) || "";
    return /quote/i.test(test);
  });
  const pushId = (statusId, href, bubble, text, hit) => {
    if (!statusId) return;
    if (seen.has(statusId)) {
      if (hit) {
        const existing = tweets.find((row) => row.statusId === statusId);
        if (existing) existing.hit = true;
      }
      return;
    }
    seen.add(statusId);
    const rect = bubble.getBoundingClientRect();
    tweets.push({
      statusId,
      url: href || ("https://x.com/i/web/status/" + statusId),
      text: (text || "تغريدة").slice(0, 500),
      top: Math.round(rect.top || 0),
      hit: !!hit
    });
  };
  for (const bubble of targets) {
    const links = [];
    collectDeep(bubble, '[href*="status/"]', links);
    const candidates = [];
    for (const link of links) {
      const href = link.getAttribute("href") || "";
      const statusId = statusOf(href);
      if (!statusId || insideQuote(link)) continue;
      const nestedUnderOther = climb(link).some((el) => {
        if (el === link || !el.getAttribute) return false;
        const parentId = statusOf(el.getAttribute("href") || "");
        return parentId && parentId !== statusId;
      });
      if (nestedUnderOther) continue;
      candidates.push({statusId, href, link, depth: climb(link).length});
    }
    let foundHere = 0;
    if (candidates.length) {
      candidates.sort((a, b) => a.depth - b.depth);
      const outer = candidates[0];
      const textNodes = [];
      collectDeep(bubble, '[data-testid="tweetText"]', textNodes);
      const ownText = textNodes.find((node) => !insideQuote(node));
      const text = clean((ownText && ownText.innerText) || "");
      pushId(outer.statusId, outer.href, bubble, text, !!(stopId && outer.statusId === stopId));
      foundHere = 1;
    }
    const blob = clean(bubble.innerText || "");
    if (!foundHere) {
      statusRe.lastIndex = 0;
      const match = statusRe.exec(blob);
      if (match) {
        pushId(match[2], match[0], bubble, blob.slice(0, 280), !!(stopId && match[2] === stopId));
        foundHere = 1;
      }
    }
    if (!foundHere) {
      const match = bareRe.exec(blob);
      if (match) {
        pushId(match[1], "https://x.com/i/web/status/" + match[1], bubble, blob.slice(0, 280), !!(stopId && match[1] === stopId));
        foundHere = 1;
      }
    }
    const cardish = [];
    collectDeep(bubble, '[data-testid="tweetText"], article, [data-testid="card.wrapper"], [data-testid="tweetPhoto"]', cardish);
    if (!foundHere && cardish.length) pending += 1;
  }
  const scroller = scrollerOf(query('[data-testid="dm-message-scroller"]') || list);
  const ids = messages.map((el) => el.getAttribute("data-testid") || "");
  const fingerprint = ids.slice(0, 8).concat(ids.slice(-8)).join("|");
  let loading = false;
  const spinner = list.querySelector('[data-testid="dm-message-list-spinner-slot"], [data-testid="dm-message-list-spinner"], [data-testid*="spinner"], [role="progressbar"]');
  if (spinner) {
    const rect = spinner.getBoundingClientRect();
    loading = rect.width > 8 && rect.height > 8;
  }
  let moved = 0;
  let atOlderEdge = false;
  if (scroller) {
    const beforeTop = scroller.scrollTop || 0;
    atOlderEdge = beforeTop <= 48;
    const client = scroller.clientHeight || 800;
    const base = dir > 0
      ? Math.max(560, Math.min(1200, Math.round(client * 0.75)))
      : Math.max(400, Math.min(800, Math.round(client * 0.5)));
    // GROUP_SCROLL_FACTOR times the step, but never past what the chat shows at once.
    const step = Math.max(base, Math.min(base * factor, Math.round(client * 0.9)));
    if (dir === -1 || dir === 1) {
      if (dir < 0 && beforeTop <= 48) {
        scroller.scrollTop = 0;
        try { scroller.dispatchEvent(new WheelEvent("wheel", {deltaY: -640, bubbles: true, cancelable: true})); } catch (error) {}
      } else if (dir > 0 && beforeTop + client >= scroller.scrollHeight - 80) {
        scroller.scrollTop = scroller.scrollHeight;
      } else {
        const next = dir < 0 ? Math.max(0, beforeTop - step) : Math.min(scroller.scrollHeight, beforeTop + step);
        scroller.scrollTop = next;
      }
      try { scroller.dispatchEvent(new Event("scroll", {bubbles: true})); } catch (error) {}
      moved = Math.abs((scroller.scrollTop || 0) - beforeTop);
    }
  }
  return {
    tweets,
    pending,
    messages: messages.length,
    fingerprint,
    loading,
    atOlderEdge,
    moved: Math.round(moved),
    scrollHeight: scroller ? Math.round(scroller.scrollHeight) : 0,
    scrollTop: scroller ? Math.round(scroller.scrollTop) : 0,
    clientHeight: scroller ? Math.round(scroller.clientHeight) : 0
  };
}
"""

GROUP_CHAT_SCROLL_JS = r"""
(action) => {
""" + CHAT_FIND_JS + r"""
  const list = query('[data-testid="dm-message-list"]') || query('[data-testid="dm-conversation-content"]');
  const start = query('[data-testid="dm-message-scroller"]') || list;
  const scroller = start ? scrollerOf(start) : null;
  const spinner = list && (list.querySelector('[data-testid="dm-message-list-spinner-slot"], [data-testid="dm-message-list-spinner"], [data-testid*="spinner"]') || list.querySelector('[role="progressbar"]'));
  let spinnerVisible = false;
  if (spinner) {
    const rect = spinner.getBoundingClientRect();
    spinnerVisible = rect.width > 8 && rect.height > 8;
  }
  const messageNodes = list
    ? [...list.querySelectorAll('[data-testid^="message-"]')].filter((el) => {
        const id = el.getAttribute("data-testid") || "";
        return id.startsWith("message-") && !id.startsWith("message-text-");
      })
    : [];
  const messages = messageNodes.length;
  const ids = messageNodes.map((el) => el.getAttribute("data-testid") || "");
  const fingerprint = ids.slice(0, 8).concat(ids.slice(-8)).join("|");
  let moved = 0;
  let atOlderEdge = false;
  if (scroller) {
    atOlderEdge = scroller.scrollTop <= 48;
    if (action === "latest") {
      const before = scroller.scrollTop;
      scroller.scrollTop = scroller.scrollHeight;
      moved = Math.abs(scroller.scrollTop - before);
    }
    if (action === "older") {
      const before = scroller.scrollTop;
      const step = Math.max(420, Math.round(scroller.clientHeight * 0.75));
      scroller.scrollTop = Math.max(0, before - step);
      moved = Math.abs(scroller.scrollTop - before);
    }
  }
  return {
    hasList: !!list,
    messages,
    fingerprint,
    loading: spinnerVisible,
    atOlderEdge,
    reversed: false,
    olderSign: -1,
    moved: Math.round(moved),
    scrollHeight: scroller ? Math.round(scroller.scrollHeight) : 0,
    scrollTop: scroller ? Math.round(scroller.scrollTop) : 0,
    clientHeight: scroller ? Math.round(scroller.clientHeight) : 0
  };
}
"""

CHAT_URLS = ("https://x.com/i/chat", "https://x.com/messages")

ALLOWED_ACTIONS = {"repost", "like", "bookmark", "comment"}


def parse_requested_count(value) -> int | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value
    if isinstance(value, float) and value.is_integer():
        return int(value)
    if isinstance(value, str) and value.strip().isdigit():
        return int(value.strip())
    return None


def normalize_status_path(href: str) -> str | None:
    raw = href or ""
    for match in re.finditer(r"(?:https?://(?:www\.)?(?:x|twitter)\.com)?/([A-Za-z0-9_]{1,15})/status/(\d{6,25})", raw):
        owner, status_id = match.group(1), match.group(2)
        if owner.lower() in {"i", "web", "intent", "share"}:
            continue
        return f"/{owner}/status/{status_id}"
    status_id = re.search(r"status/(\d{6,25})", raw)
    if status_id:
        return f"/i/web/status/{status_id.group(1)}"
    return None


_mouse_at: dict[int, tuple[float, float]] = {}


def _mouse_start(page, target_x: float, target_y: float) -> tuple[float, float]:
    remembered = _mouse_at.get(id(page))
    if remembered:
        return remembered
    size = page.viewport_size or {"width": VIEWPORT_WIDTH, "height": 900}
    angle = random.uniform(0, math.tau)
    distance = random.uniform(140, 420)
    return (
        min(max(target_x + math.cos(angle) * distance, 8), size["width"] - 8),
        min(max(target_y + math.sin(angle) * distance, 8), size["height"] - 8),
    )


def _human_path(start: tuple[float, float], end: tuple[float, float], viewport: dict) -> list[tuple[float, float]]:
    sx, sy = start
    ex, ey = end
    dx, dy = ex - sx, ey - sy
    dist = math.hypot(dx, dy)
    if dist < 6:
        return [(ex, ey)]
    side_x, side_y = -dy / dist, dx / dist
    bend = max(-220.0, min(220.0, dist * random.uniform(0.18, 0.62))) * random.choice((-1.0, 1.0))
    c1 = (
        sx + dx * random.uniform(0.18, 0.42) + side_x * bend * random.uniform(0.35, 1.05),
        sy + dy * random.uniform(0.18, 0.42) + side_y * bend * random.uniform(0.35, 1.05),
    )
    c2 = (
        sx + dx * random.uniform(0.58, 0.86) + side_x * bend * random.uniform(-0.25, 0.85),
        sy + dy * random.uniform(0.58, 0.86) + side_y * bend * random.uniform(-0.25, 0.85),
    )
    width = float(viewport.get("width") or VIEWPORT_WIDTH)
    height = float(viewport.get("height") or 900)
    sway = random.uniform(2, 6)
    phase = random.uniform(0, math.tau)
    waves = random.uniform(1.0, 1.6)
    ease = random.uniform(1.2, 1.6)
    points: list[tuple[float, float]] = []
    steps = 2
    for index in range(1, steps + 1):
        raw = index / steps
        progress = 1 - (1 - raw) ** ease
        inverse = 1 - progress
        x = (inverse ** 3) * sx + 3 * (inverse ** 2) * progress * c1[0] + 3 * inverse * (progress ** 2) * c2[0] + (progress ** 3) * ex
        y = (inverse ** 3) * sy + 3 * (inverse ** 2) * progress * c1[1] + 3 * inverse * (progress ** 2) * c2[1] + (progress ** 3) * ey
        wobble = math.sin(progress * waves * math.tau + phase) * sway * (1 - progress)
        x += side_x * wobble
        y += side_y * wobble
        if index < steps:
            x = min(max(x, 1), width - 1)
            y = min(max(y, 1), height - 1)
        points.append((x, y))
    points[-1] = (ex, ey)
    return points


# Inside the Android app («قروبات») the page is not scrolled for the script's own sake: a button is clicked where
# it is, once the page has stopped moving, and the aim is checked again just before the press (on a phone X loads
# slower, and scrolling it while it loaded moved the buttons from under the mouse).
IN_APP = os.environ.get("GG_IN_APP") == "1"


def _same_box(a: dict | None, b: dict | None) -> bool:
    return bool(a and b) and all(abs(float(a[key]) - float(b[key])) < 1 for key in ("x", "y", "width", "height"))


def _in_view(page, box: dict | None) -> bool:
    if not box:
        return False
    viewport = page.viewport_size or {"width": VIEWPORT_WIDTH, "height": 900}
    middle_y = float(box["y"]) + float(box["height"]) / 2
    middle_x = float(box["x"]) + float(box["width"]) / 2
    return 0 < middle_y < viewport["height"] and 0 < middle_x < viewport["width"]


def _still_box(page, read_box, seconds: float = 5.0, scroll=None):
    """The box once it reads the same twice in a row (the page stopped moving). scroll(): asked once, only when
    the box is outside the page's view."""
    last = None
    scrolled = scroll is None
    deadline = time.monotonic() + seconds
    while True:
        box = read_box()
        if box and _same_box(box, last):
            if _in_view(page, box) or scrolled:
                return box
            try:
                scroll()
            except Exception:
                pass
            scrolled = True
            box = None
        if time.monotonic() >= deadline:
            return box
        last = box
        page.wait_for_timeout(150)


def _press_at(page, read_box, box: dict, local_x: float, local_y: float) -> None:
    """Move to the spot like a hand; if the button moved meanwhile, move again to where it is now; then press."""
    x, y = box["x"] + local_x, box["y"] + local_y
    _move_like_a_hand(page, x, y)
    for _ in range(4):
        try:
            now = read_box()
        except Exception:
            now = None
        if not now:
            break
        nx = now["x"] + min(local_x, max(1.0, now["width"] - 1))
        ny = now["y"] + min(local_y, max(1.0, now["height"] - 1))
        if abs(nx - x) < 1 and abs(ny - y) < 1:
            break
        page.mouse.move(nx, ny, steps=4)
        x, y = nx, ny
        _mouse_at[id(page)] = (x, y)
        page.wait_for_timeout(120)
    page.mouse.down()
    page.wait_for_timeout(100)
    page.mouse.up()


def _move_like_a_hand(page, x: float, y: float) -> None:
    viewport = page.viewport_size or {"width": VIEWPORT_WIDTH, "height": 900}
    start = _mouse_start(page, x, y)
    for px, py in _human_path(start, (x, y), viewport):
        page.mouse.move(px, py)
    _mouse_at[id(page)] = (x, y)


def real_click(locator) -> None:
    """Use the selector only to read the button box, then send a real mouse click."""
    locator.wait_for(state="visible", timeout=8000)
    if IN_APP:
        box = _still_box(locator.page, locator.bounding_box, scroll=lambda: locator.scroll_into_view_if_needed(timeout=4000))
    else:
        try:
            locator.scroll_into_view_if_needed(timeout=4000)
        except Exception:
            pass
        box = locator.bounding_box()
    if not box or box["width"] < 2 or box["height"] < 2:
        raise PlaywrightTimeoutError("button box missing")
    width = box["width"]
    height = box["height"]
    inset_x = min(2.0, width * 0.12)
    inset_y = min(2.0, height * 0.12)
    zone = random.choice(("center", "left", "right", "top", "bottom"))
    if zone == "center":
        local_x = width * random.uniform(0.42, 0.58)
        local_y = height * random.uniform(0.42, 0.58)
    elif zone == "left":
        local_x = random.uniform(inset_x, max(inset_x + 0.5, width * 0.22))
        local_y = height * random.uniform(0.28, 0.72)
    elif zone == "right":
        local_x = random.uniform(min(width * 0.78, width - inset_x), width - inset_x)
        local_y = height * random.uniform(0.28, 0.72)
    elif zone == "top":
        local_x = width * random.uniform(0.28, 0.72)
        local_y = random.uniform(inset_y, max(inset_y + 0.5, height * 0.22))
    else:
        local_x = width * random.uniform(0.28, 0.72)
        local_y = random.uniform(min(height * 0.78, height - inset_y), height - inset_y)
    local_x = min(max(local_x, inset_x), width - inset_x)
    local_y = min(max(local_y, inset_y), height - inset_y)
    page = locator.page
    if IN_APP:
        _press_at(page, locator.bounding_box, box, local_x, local_y)
        return
    x = box["x"] + local_x
    y = box["y"] + local_y
    _move_like_a_hand(page, x, y)
    page.mouse.down()
    page.wait_for_timeout(100)
    page.mouse.up()


def article_locator(page, path: str):
    status_id = ""
    match = re.search(r"status/(\d{6,25})", path or "")
    if match:
        status_id = match.group(1)
    articles = page.locator('article[data-testid="tweet"]')
    if not status_id:
        return articles
    return articles.filter(has=page.locator(f'a[href*="/status/{status_id}"]'))


def click_box(page, box: dict) -> None:
    width = float(box.get("width") or 0)
    height = float(box.get("height") or 0)
    if width < 2 or height < 2:
        raise PlaywrightTimeoutError("button box missing")
    x = float(box["x"]) + width * random.uniform(0.4, 0.6)
    y = float(box["y"]) + height * random.uniform(0.4, 0.6)
    box_text = {key: round(float(box[key]), 1) for key in ("x", "y", "width", "height")}
    trace_click(f"ضغط على ({x:.0f},{y:.0f}) صندوق {box_text}")
    _move_like_a_hand(page, x, y)
    page.mouse.down()
    page.wait_for_timeout(100)
    page.mouse.up()


def read_action_state(page, status_id: str, actions: list[str]) -> dict | None:
    payload = page.evaluate(
        """({statusId, names, scroll}) => {
          const articles = [...document.querySelectorAll('article[data-testid="tweet"]')];
          const boxOf = (el) => {
            if (!el) return null;
            const rect = el.getBoundingClientRect();
            if (rect.width < 2 || rect.height < 2) return null;
            return {x: rect.x, y: rect.y, width: rect.width, height: rect.height};
          };
          let card = null;
          if (statusId) {
            card = articles.find((article) => [...article.querySelectorAll('a[href*="/status/"]')].some((node) => (node.getAttribute("href") || "").includes("/status/" + statusId)));
          }
          if (!card) card = articles[0] || null;
          if (!card) return null;
          if (scroll) { try { card.scrollIntoView({block: "center"}); } catch (error) {} }
          const map = {repost: ["unretweet", "retweet"], like: ["unlike", "like"], bookmark: ["removeBookmark", "bookmark"]};
          const labelOf = {
            reply: /reply|رد/i, retweet: /repost|retweet|إعادة النشر|اعادة النشر/i,
            unretweet: /undo repost|unretweet|تم إعادة|إلغاء إعادة/i,
            like: /like|إعجاب|اعجاب/i, unlike: /unlike|liked|أعجبني|معجب/i,
            bookmark: /bookmark|إشارة مرجعية/i, removeBookmark: /remove bookmark|إزالة الإشارة/i
          };
          const scopeOf = (article) => (article && article.closest("[data-testid='cellInnerDiv']")) || article;
          const findBtn = (root, testid) => {
            if (!root) return null;
            const re = labelOf[testid];
            const nodes = [];
            const tagged = root.querySelector('[data-testid="' + testid + '"]');
            if (tagged) nodes.push(tagged);
            if (re) {
              for (const node of root.querySelectorAll("button, [role='button']")) {
                const label = node.getAttribute("aria-label") || "";
                if (!re.test(label)) continue;
                if (testid === "like" && /unlike|liked|أعجبني|معجب/i.test(label)) continue;
                nodes.push(node);
              }
            }
            for (const node of nodes) {
              const btn = node.closest("button, [role='button']") || node;
              if (btn.closest("[data-testid='tweetTextarea_0'], [data-testid='toolBar']")) continue;
              const rect = btn.getBoundingClientRect();
              if (rect.width >= 2 && rect.height >= 2) return btn;
            }
            return null;
          };
          const out = {};
          const root = scopeOf(card);
          for (const name of names) {
            const pair = map[name];
            if (!pair) continue;
            const on = findBtn(root, pair[0]);
            const off = findBtn(root, pair[1]);
            out[name] = {on: !!on, box: on ? null : boxOf(off)};
          }
          return out;
        }""",
        {"statusId": status_id, "names": actions, "scroll": not IN_APP},
    )
    return payload if isinstance(payload, dict) else None


ACTION_BUTTON_PROBE_JS = r"""
({statusId, testid, scroll}) => {
  const labelOf = {
    reply: /reply|رد/i, retweet: /repost|retweet|إعادة النشر|اعادة النشر/i,
    unretweet: /undo repost|unretweet|تم إعادة|إلغاء إعادة/i,
    like: /like|إعجاب|اعجاب/i, unlike: /unlike|liked|أعجبني|معجب/i,
    bookmark: /bookmark|إشارة مرجعية/i, removeBookmark: /remove bookmark|إزالة الإشارة/i
  };
  const articles = [...document.querySelectorAll('article[data-testid="tweet"], [data-testid="tweet"]')];
  let card = null;
  if (statusId) {
    card = articles.find((article) => [...article.querySelectorAll('a[href*="/status/"]')]
      .some((node) => (node.getAttribute("href") || "").includes("/status/" + statusId)));
  }
  if (!card) card = articles[0] || null;
  if (!card) return null;
  const root = card.closest('[data-testid="cellInnerDiv"]') || card;
  const re = labelOf[testid];
  const nodes = [];
  const tagged = root.querySelector('[data-testid="' + testid + '"]');
  if (tagged) nodes.push(tagged);
  if (re) {
    for (const node of root.querySelectorAll("button, [role='button']")) {
      const label = node.getAttribute("aria-label") || "";
      if (!re.test(label)) continue;
      if (testid === "like" && /unlike|liked|أعجبني|معجب/i.test(label)) continue;
      nodes.push(node);
    }
  }
  let button = null;
  for (const node of nodes) {
    const btn = node.closest("button, [role='button']") || node;
    if (btn.closest("[data-testid='tweetTextarea_0'], [data-testid='toolBar']")) continue;
    const rect = btn.getBoundingClientRect();
    if (rect.width >= 2 && rect.height >= 2) { button = btn; break; }
  }
  if (!button) return {box: null};
  const aboveBar = () => {
    const bar = document.querySelector('[data-testid="BottomBar"]');
    const top = bar ? bar.getBoundingClientRect().top : window.innerHeight;
    return top > 80 ? top - 12 : window.innerHeight - 12;
  };
  const bringIntoView = () => {
    const placed = () => {
      const r = button.getBoundingClientRect();
      return r.width >= 2 && r.top > 24 && r.bottom < aboveBar();
    };
    if (placed()) return true;
    let node = button.parentElement;
    while (node) {
      const style = getComputedStyle(node);
      if (/(auto|scroll|overlay)/.test(style.overflowY) && node.scrollHeight > node.clientHeight + 8) {
        const r = button.getBoundingClientRect();
        const host = node.getBoundingClientRect();
        node.scrollTop += (r.top + r.height / 2) - Math.min(host.top + host.height / 2, aboveBar() * 0.55);
      }
      node = node.parentElement;
    }
    const r = button.getBoundingClientRect();
    const delta = (r.top + r.height / 2) - (aboveBar() * 0.55);
    try { window.scrollBy(0, delta); } catch (error) {}
    if (document.scrollingElement) document.scrollingElement.scrollTop += delta;
    try { button.scrollIntoView({block: "center", inline: "nearest"}); } catch (error) {}
    return placed();
  };
  if (scroll) {
    const seen = bringIntoView();
    return {scrolled: true, inView: seen};
  }
  const rect = button.getBoundingClientRect();
  if (rect.width < 2 || rect.height < 2) return {box: null};
  const x = rect.x + rect.width / 2;
  const y = rect.y + rect.height / 2;
  const hit = document.elementFromPoint(x, y);
  const ok = !!hit && (button === hit || button.contains(hit) || hit.closest("button, [role='button']") === button);
  let blocker = "";
  if (!ok && hit) {
    const tag = hit.closest("[data-testid]");
    blocker = (tag && tag.getAttribute("data-testid")) || hit.tagName.toLowerCase();
  }
  const limit = aboveBar();
  return {box: {x: rect.x, y: rect.y, width: rect.width, height: rect.height}, ok, blocker,
          inView: rect.top > 8 && rect.bottom < limit};
}
"""

TAP_ACTION_JS = r"""
({statusId, testid}) => {
  const labelOf = {
    reply: /reply|رد/i, retweet: /repost|retweet|إعادة النشر|اعادة النشر/i,
    unretweet: /undo repost|unretweet|تم إعادة|إلغاء إعادة/i,
    like: /like|إعجاب|اعجاب/i, unlike: /unlike|liked|أعجبني|معجب/i,
    bookmark: /bookmark|إشارة مرجعية/i, removeBookmark: /remove bookmark|إزالة الإشارة/i
  };
  const articles = [...document.querySelectorAll('article[data-testid="tweet"], [data-testid="tweet"]')];
  let card = null;
  if (statusId) {
    card = articles.find((article) => [...article.querySelectorAll('a[href*="/status/"]')]
      .some((node) => (node.getAttribute("href") || "").includes("/status/" + statusId)));
  }
  if (!card) card = articles[0] || null;
  if (!card) return "missing";
  const root = card.closest('[data-testid="cellInnerDiv"]') || card;
  const re = labelOf[testid];
  const nodes = [];
  const tagged = root.querySelector('[data-testid="' + testid + '"]');
  if (tagged) nodes.push(tagged);
  if (re) {
    for (const node of root.querySelectorAll("button, [role='button']")) {
      const label = node.getAttribute("aria-label") || "";
      if (!re.test(label)) continue;
      if (testid === "like" && /unlike|liked|أعجبني|معجب/i.test(label)) continue;
      nodes.push(node);
    }
  }
  let button = null;
  for (const node of nodes) {
    const btn = node.closest("button, [role='button']") || node;
    if (btn.closest("[data-testid='tweetTextarea_0'], [data-testid='toolBar']")) continue;
    if (btn.tagName === "A" && /\/status\//.test(btn.getAttribute("href") || "")) continue;
    const rect = btn.getBoundingClientRect();
    if (rect.width >= 2 && rect.height >= 2) { button = btn; break; }
  }
  if (!button) return "missing";
  const rect = button.getBoundingClientRect();
  if (rect.bottom < 0 || rect.top > window.innerHeight) {
    try { button.scrollIntoView({block: "center", inline: "nearest", behavior: "instant"}); } catch (error) {}
  }
  button.addEventListener("click", (event) => event.stopPropagation(), {capture: true, once: true});
  button.click();
  return "clicked";
}
"""


CLOSE_POPUPS_JS = r"""
() => {
  const words = /^(close|dismiss|not now|maybe later|got it|skip|no thanks|cancel|إغلاق|اغلاق|ليس الآن|لاحقًا|لاحقا|فهمت|تخطي|تخطّي|لا شكرًا|لا شكرا|إلغاء)$/i;
  const chat = '[data-testid="dm-message-list"], [data-testid="dm-message-scroller"], [data-testid="dm-conversation-content"], [data-testid="dm-inbox-panel"]';
  const layers = [...document.querySelectorAll('[role="dialog"], [role="alertdialog"], [aria-modal="true"], [data-testid="sheetDialog"], [data-testid="confirmationSheetDialog"]')]
    .filter((el) => el.getClientRects().length && !el.closest(chat) && !el.querySelector(chat));
  const closed = [];
  for (const layer of layers) {
    const buttons = [...layer.querySelectorAll('button, [role="button"]')].filter((node) => node.getClientRects().length);
    const hit = buttons.find((node) => {
      const label = (node.getAttribute("aria-label") || "").trim();
      const text = (node.innerText || "").replace(/\s+/g, " ").trim();
      const testid = node.getAttribute("data-testid") || "";
      return words.test(label) || words.test(text) || testid === "app-bar-close" || testid === "confirmationSheetCancel";
    });
    if (hit) {
      hit.click();
      closed.push(layer.getAttribute("data-testid") || layer.getAttribute("aria-label") || "dialog");
    }
  }
  return closed;
}
"""


ACCEPT_COOKIES_JS = r"""
() => {
  const accept = /^(accept all cookies|قبول جميع ملفات الكوكيز)$/i;
  for (const node of document.querySelectorAll('button, [role="button"]')) {
    if (accept.test((node.textContent || "").replace(/\s+/g, " ").trim()) && node.getClientRects().length) {
      node.click();
      return true;
    }
  }
  return false;
}
"""


def accept_cookies(page) -> bool:
    """Press "قبول جميع ملفات الكوكيز" on X's cookie notice when it shows: it covers the bottom of the page."""
    try:
        clicked = bool(page.evaluate(ACCEPT_COOKIES_JS))
    except Exception:
        return False
    if clicked:
        page.wait_for_timeout(400)
    return clicked


def close_popups(page) -> int:
    """Close pop-up dialogs that cover the page, and accept the cookie notice. The chat itself is never touched."""
    cookies = accept_cookies(page)
    try:
        closed = page.evaluate(CLOSE_POPUPS_JS) or []
    except Exception:
        return int(cookies)
    if closed:
        if os.environ.get("COLLECT_DEBUG"):
            print(f"closed popups: {closed}", flush=True)
        page.wait_for_timeout(400)
    return len(closed) + int(cookies)


# Official mobile actions from X's docs (docs.x.com Web Intents). On a phone the timeline
# button is not the desktop control: a tap opens the post and its reply box. Like, repost and
# reply are documented as these pages, which work in a mobile WebView.
OFFICIAL_INTENTS = {
    "like": "https://x.com/intent/like?tweet_id={id}",
    "repost": "https://x.com/intent/retweet?tweet_id={id}",
}

CONFIRM_INTENT_JS = r"""
() => {
  const body = ((document.body && document.body.innerText) || "").replace(/\s+/g, " ").slice(0, 2500);
  if (/you liked|liked this tweet|تم الإعجاب|أعجبك هذا/i.test(body)) return "done";
  if (/reposted|you reposted|تم إعادة النشر|أعدت نشر/i.test(body)) return "done";
  const words = /^(like|إعجاب|اعجاب|repost|retweet|إعادة النشر|اعادة النشر)$/i;
  const nodes = [...document.querySelectorAll('button, [role="button"], input[type="submit"], [data-testid="confirmationSheetConfirm"]')];
  const hit = nodes.find((node) => {
    if (node.closest("[data-testid='tweetTextarea_0']")) return false;
    const test = node.getAttribute("data-testid") || "";
    const text = (node.innerText || node.value || node.getAttribute("aria-label") || "").replace(/\s+/g, " ").trim();
    return test === "confirmationSheetConfirm" || words.test(text);
  });
  if (!hit) return "";
  hit.click();
  return "clicked";
}
"""


def _tweet_back_url(path: str, status_id: str) -> str:
    raw = (path or "").strip()
    if raw.startswith("http"):
        return raw
    if raw.startswith("/"):
        return "https://x.com" + raw
    if status_id:
        return f"https://x.com/i/web/status/{status_id}"
    return "https://x.com" + ("/" + raw if raw else "")


def press_official_intent(page, path: str, status_id: str, action: str) -> str:
    """Like or repost through the official mobile intent page, then return to the post."""
    if not status_id or action not in OFFICIAL_INTENTS:
        return "missing"
    back = _tweet_back_url(path, status_id)
    goto_x(page, OFFICIAL_INTENTS[action].format(id=status_id))
    outcome = ""
    deadline = time.monotonic() + 8
    while time.monotonic() < deadline:
        try:
            outcome = str(page.evaluate(CONFIRM_INTENT_JS) or "")
        except Exception:
            outcome = ""
        if outcome:
            break
        page.wait_for_timeout(400)
    page.wait_for_timeout(900)
    try:
        goto_x(page, back)
        page.wait_for_timeout(800)
    except Exception:
        pass
    return "" if outcome else "missing"


# The phone page does not use the desktop buttons. A click on the card opens the tweet and
# stops there. These are the calls that page itself makes when a button works (the same web
# session, read from the open page). Query ids are the ones documented from X's own client
# and are replaced by whatever that page already loaded when it differs.
WEB_MUTATION_JS = r"""
async ({action, tweetId, text}) => {
  const bearer = "AAAAAAAAAAAAAAAAAAAAANRILgAAAAAAnNwIzUejRCOuH5E6I8xnZz4puTs%3D1Zv7ttfk8LF81IUq16cHjhLTvJu4FA33AGWWjCpTnA";
  const fallback = {
    FavoriteTweet: "lI07N6Otwv1PhnEgXILM7A",
    UnfavoriteTweet: "ZYKSe-w7KEslx3JhSIk5LA",
    CreateRetweet: "mbRO74GrOvSfRcJnlMapnQ",
    DeleteRetweet: "ZyZigVsNiFO6v1dEks1eWg",
    CreateBookmark: "aoDbu3RHznuiSkQ9aNM67Q",
    DeleteBookmark: "Wlmlj2-xzyS1GN3a6cj-mQ",
    CreateTweet: "l4hk8uVGvR-a8kzQ4nOhPA"
  };
  const tweetFeatures = {
    premium_content_api_read_enabled: false,
    communities_web_enable_tweet_community_results_fetch: true,
    c9s_tweet_anatomy_moderator_badge_enabled: true,
    responsive_web_grok_analyze_button_fetch_trends_enabled: false,
    responsive_web_grok_analyze_post_followups_enabled: true,
    rweb_cashtags_composer_attachment_enabled: true,
    responsive_web_jetfuel_frame: true,
    rweb_sports_post_context_enabled: true,
    x_elections_post_context_enabled: true,
    responsive_web_grok_share_attachment_enabled: true,
    responsive_web_grok_annotations_enabled: true,
    responsive_web_edit_tweet_api_enabled: true,
    graphql_is_translatable_rweb_tweet_is_translatable_enabled: true,
    view_counts_everywhere_api_enabled: true,
    longform_notetweets_consumption_enabled: true,
    responsive_web_twitter_article_tweet_consumption_enabled: true,
    content_disclosure_indicator_enabled: true,
    content_disclosure_ai_generated_indicator_enabled: true,
    responsive_web_grok_show_grok_translated_post: true,
    responsive_web_grok_analysis_button_from_backend: true,
    post_ctas_fetch_enabled: true,
    longform_notetweets_rich_text_read_enabled: true,
    longform_notetweets_inline_media_enabled: false,
    profile_label_improvements_pcf_label_in_post_enabled: true,
    responsive_web_profile_redirect_enabled: true,
    rweb_tipjar_consumption_enabled: false,
    verified_phone_label_enabled: false,
    responsive_web_nested_quote_preview_enabled: true,
    articles_preview_enabled: true,
    rweb_cashtags_enabled: true,
    responsive_web_grok_community_note_auto_translation_is_enabled: true,
    freedom_of_speech_not_reach_fetch_enabled: true,
    standardized_nudges_misinfo: true,
    tweet_with_visibility_results_prefer_gql_limited_actions_policy_enabled: true,
    responsive_web_grok_image_annotation_enabled: true,
    responsive_web_grok_imagine_annotation_enabled: true,
    responsive_web_graphql_timeline_navigation_enabled: true
  };
  const ct0 = decodeURIComponent((document.cookie.match(/(?:^|; )ct0=([^;]+)/) || [])[1] || "");
  if (!ct0) return {ok: false, error: "لا توجد جلسة دخول في الصفحة"};
  const learn = () => {
    if (window.__ggQLearned) return;
    window.__ggQLearned = true;
    window.__ggQ = Object.assign({}, fallback, window.__ggQ || {});
    const grab = (source) => {
      if (!source) return;
      const first = /queryId:"([A-Za-z0-9_-]{8,80})",operationName:"([A-Za-z0-9_]+)"/g;
      const second = /operationName:"([A-Za-z0-9_]+)",queryId:"([A-Za-z0-9_-]{8,80})"/g;
      let match;
      while ((match = first.exec(source))) window.__ggQ[match[2]] = match[1];
      while ((match = second.exec(source))) window.__ggQ[match[1]] = match[2];
    };
    try {
      const chunks = self.webpackChunk_twitter_responsive_web || [];
      let budget = 0;
      for (const chunk of chunks) {
        const mods = chunk && chunk[1];
        if (!mods) continue;
        for (const fn of Object.values(mods)) {
          let source = "";
          try { source = Function.prototype.toString.call(fn); } catch (error) { continue; }
          if (source.indexOf("queryId") < 0 && source.indexOf("FavoriteTweet") < 0 && source.indexOf("CreateTweet") < 0) continue;
          grab(source);
          budget += source.length;
          if (budget > 2500000) return;
        }
      }
    } catch (error) {}
  };
  const send = async (name, variables, features) => {
    const queryId = (window.__ggQ && window.__ggQ[name]) || fallback[name];
    const response = await fetch("https://x.com/i/api/graphql/" + queryId + "/" + name, {
      method: "POST",
      credentials: "include",
      headers: {
        authorization: "Bearer " + bearer,
        "x-csrf-token": ct0,
        "x-twitter-auth-type": "OAuth2Session",
        "x-twitter-active-user": "yes",
        "content-type": "application/json"
      },
      body: JSON.stringify({variables, features: features || {}, queryId})
    });
    const raw = await response.text();
    let data = {};
    try { data = JSON.parse(raw); } catch (error) {}
    const errors = data.errors || [];
    const message = (errors[0] && (errors[0].message || "")) || "";
    const already = /already|duplicate|has already|been already|327|139/i.test(message + " " + raw.slice(0, 300));
    return {status: response.status, ok: (response.status === 200 && errors.length === 0) || already, error: message || ("HTTP " + response.status), raw: raw.slice(0, 180)};
  };
  learn();
  const ops = {like: "FavoriteTweet", repost: "CreateRetweet", bookmark: "CreateBookmark", comment: "CreateTweet"};
  const name = ops[action];
  if (!name) return {ok: false, error: "إجراء غير معروف"};
  let variables = {tweet_id: String(tweetId)};
  let features = {};
  if (action === "repost") variables = {tweet_id: String(tweetId), dark_request: false};
  if (action === "comment") {
    variables = {
      tweet_text: text || "",
      dark_request: false,
      media: {media_entities: [], possibly_sensitive: false},
      semantic_annotation_ids: [],
      reply: {in_reply_to_tweet_id: String(tweetId), exclude_reply_user_ids: []}
    };
    features = tweetFeatures;
  }
  let result = await send(name, variables, features);
  if (!result.ok && result.status === 404) {
    window.__ggQLearned = false;
    learn();
    result = await send(name, variables, features);
  }
  if (!result.ok && action === "like") {
    const response = await fetch("https://x.com/i/api/1.1/favorites/create.json", {
      method: "POST",
      credentials: "include",
      headers: {
        authorization: "Bearer " + bearer,
        "x-csrf-token": ct0,
        "x-twitter-auth-type": "OAuth2Session",
        "x-twitter-active-user": "yes",
        "content-type": "application/json"
      },
      body: JSON.stringify({id: String(tweetId)})
    });
    const raw = await response.text();
    if (response.status === 200 || /already|139/i.test(raw)) return {ok: true, via: "rest"};
    result = {ok: false, error: result.error || ("HTTP " + response.status)};
  }
  if (!result.ok && action === "repost") {
    const response = await fetch("https://x.com/i/api/1.1/statuses/retweet/" + encodeURIComponent(tweetId) + ".json", {
      method: "POST",
      credentials: "include",
      headers: {
        authorization: "Bearer " + bearer,
        "x-csrf-token": ct0,
        "x-twitter-auth-type": "OAuth2Session",
        "x-twitter-active-user": "yes",
        "content-type": "application/x-www-form-urlencoded"
      },
      body: "id=" + encodeURIComponent(tweetId)
    });
    const raw = await response.text();
    if (response.status === 200 || /already|327/i.test(raw)) return {ok: true, via: "rest"};
  }
  return result.ok ? {ok: true} : {ok: false, error: (result.error || "فشل الطلب").slice(0, 140)};
}
"""


def web_mutate(page, status_id: str, action: str, text: str = "") -> dict:
    """Like, repost, bookmark, or reply through the call the logged-in page already uses."""
    try:
        result = page.evaluate(WEB_MUTATION_JS, {"action": action, "tweetId": status_id, "text": text or ""})
    except Exception as exc:
        return {"ok": False, "error": str(exc).splitlines()[0][:140]}
    return result if isinstance(result, dict) else {"ok": False, "error": "رد غير مفهوم من الصفحة"}


PRESS_PAGE_JS = r"""
async ({statusId, testid}) => {
  const labelOf = {
    reply: /reply|رد/i, retweet: /repost|retweet|إعادة النشر|اعادة النشر/i,
    unretweet: /undo repost|unretweet|تم إعادة|إلغاء إعادة/i,
    like: /like|إعجاب|اعجاب/i, unlike: /unlike|liked|أعجبني|معجب/i,
    bookmark: /bookmark|إشارة مرجعية/i, removeBookmark: /remove bookmark|إزالة الإشارة/i
  };
  const articles = [...document.querySelectorAll('article[data-testid="tweet"], [data-testid="tweet"]')];
  let card = articles.find((article) => statusId && [...article.querySelectorAll('a[href*="/status/"]')]
    .some((node) => (node.getAttribute("href") || "").includes("/status/" + statusId))) || articles[0] || null;
  if (!card) return {how: "missing"};
  const root = card.closest('[data-testid="cellInnerDiv"]') || card;
  const re = labelOf[testid];
  const nodes = [];
  const tagged = root.querySelector('[data-testid="' + testid + '"]');
  if (tagged) nodes.push(tagged);
  if (re) {
    for (const node of root.querySelectorAll("button, [role='button']")) {
      const label = node.getAttribute("aria-label") || "";
      if (!re.test(label)) continue;
      if (testid === "like" && /unlike|liked|أعجبني|معجب/i.test(label)) continue;
      nodes.push(node);
    }
  }
  let button = null;
  for (const node of nodes) {
    const btn = node.closest("button, [role='button']") || node;
    if (btn.closest("[data-testid='tweetTextarea_0'], [data-testid='toolBar']")) continue;
    const rect = btn.getBoundingClientRect();
    if (rect.width >= 2 && rect.height >= 2) { button = btn; break; }
  }
  if (!button) return {how: "missing"};
  const aboveBar = () => {
    const bar = document.querySelector('[data-testid="BottomBar"]');
    const top = bar ? bar.getBoundingClientRect().top : window.innerHeight;
    return top > 80 ? top - 12 : window.innerHeight - 12;
  };
  const placed = () => {
    const r = button.getBoundingClientRect();
    return r.width >= 2 && r.top > 24 && r.bottom < aboveBar();
  };
  if (!placed()) {
    let node = button.parentElement;
    while (node) {
      const style = getComputedStyle(node);
      if (/(auto|scroll|overlay)/.test(style.overflowY) && node.scrollHeight > node.clientHeight + 8) {
        const r = button.getBoundingClientRect();
        const host = node.getBoundingClientRect();
        node.scrollTop += (r.top + r.height / 2) - Math.min(host.top + host.height / 2, aboveBar() * 0.55);
      }
      node = node.parentElement;
    }
    const r = button.getBoundingClientRect();
    const delta = (r.top + r.height / 2) - (aboveBar() * 0.55);
    try { window.scrollBy(0, delta); } catch (error) {}
    if (document.scrollingElement) document.scrollingElement.scrollTop += delta;
    try { button.scrollIntoView({block: "center", inline: "nearest"}); } catch (error) {}
  }
  if (!placed()) return {how: "offscreen"};
  const before = button.getAttribute("aria-label") || "";
  const event = (node) => ({
    preventDefault() {}, stopPropagation() {}, persist() {},
    nativeEvent: {isTrusted: true, button: 0},
    isTrusted: true, button: 0, type: "click",
    target: node, currentTarget: node
  });
  const fire = (node) => {
    if (!node) return "";
    const keys = Object.keys(node);
    for (const key of keys) {
      if (!key.startsWith("__reactProps$")) continue;
      const props = node[key];
      if (props && typeof props.onClick === "function") {
        props.onClick(event(node));
        return "react";
      }
    }
    return "";
  };
  let how = fire(button);
  if (!how) {
    for (const child of button.querySelectorAll("*")) {
      how = fire(child);
      if (how) break;
    }
  }
  await new Promise((done) => setTimeout(done, 400));
  const sheet = document.querySelector('[data-testid="confirmationSheetConfirm"], [data-testid="retweetConfirm"]');
  if (sheet) {
    fire(sheet) || sheet.click();
    how = (how || "sheet") + "+تأكيد";
  }
  return {how: how || "no-handler", before, after: button.isConnected ? (button.getAttribute("aria-label") || "") : "gone"};
}
"""


def press_action_button(page, path: str, status_id: str, action: str) -> str:
    """Scroll the button into view, make sure nothing covers it, then click it.

    Returns "" after a click reached the button, "missing" when the button is
    not on the page, or the name of whatever was covering the button.
    """
    testid = ACTION_CONTROLS[action][1]
    blocker = ""

    def probe(scroll: bool = False):
        try:
            return page.evaluate(ACTION_BUTTON_PROBE_JS, {"statusId": status_id, "testid": testid, "scroll": scroll})
        except Exception:
            return None

    for _ in range(3):
        close_popups(page)
        info = probe(False)
        trace_click(f"{action} {status_id} فحص {info}")
        if not info or not info.get("box"):
            trace_page(page, f"{action} الزر غير موجود")
            return "missing"
        if not info.get("inView") or str((info or {}).get("blocker") or "") == "BottomBar":
            probe(True)
            page.wait_for_timeout(450)
            info = probe(False)
        if info and info.get("ok") and info.get("inView") and info.get("box"):
            if IN_APP:
                try:
                    pressed = page.evaluate(PRESS_PAGE_JS, {"statusId": status_id, "testid": testid})
                except Exception as exc:
                    pressed = {"how": "error", "error": str(exc)[:160]}
                trace_click(f"{action} معالج الصفحة {pressed}")
                how = str((pressed or {}).get("how") or "")
                if how == "offscreen" or how == "missing" or how == "no-handler":
                    blocker = "خارج الشاشة" if how == "offscreen" else (blocker or "لم يُقبل النقر")
                    page.wait_for_timeout(400)
                    continue
                return ""
            click_box(page, info["box"])
            trace_click(f"{action} أُرسلت النقرة")
            return ""
        blocker = str((info or {}).get("blocker") or "خارج الشاشة")
        trace_click(f"{action} لم تُصب النقرة: {blocker}")
        try:
            page.keyboard.press("Escape")
        except Exception:
            pass
        page.wait_for_timeout(600)
    return blocker or "خارج الشاشة"


def apply_actions_on_path(page, path: str, actions: list[str]) -> dict[str, str]:
    """Click only inactive controls. Already-on actions are left untouched."""
    status_id = ""
    match = re.search(r"status/(\d{6,25})", path or "")
    if match:
        status_id = match.group(1)
    try:
        state = read_action_state(page, status_id, actions)
    except Exception as exc:
        if browser_closed_error(exc):
            raise BrowserClosed() from exc
        state = None
    if not state:
        return {key: "تعذر العثور على المنشور" for key in actions}
    outcome: dict[str, str] = {}
    pressed = 0
    for action in actions:
        row = state.get(action) if isinstance(state.get(action), dict) else {}
        if row.get("on"):
            outcome[action] = "مفعّل مسبقًا — تم التجاوز"
            continue
        if pressed:
            page.wait_for_timeout(random.randint(80, 200))
        pressed += 1
        try:
            blocker = press_action_button(page, path, status_id, action)
            if blocker == "missing":
                outcome[action] = "زر الإجراء غير متاح — تم التجاوز"
                continue
            if blocker:
                outcome[action] = f"تعذر النقر: الزر مغطى بـ {blocker}"
                continue
            if action == "repost":
                confirm = page.locator('[data-testid="retweetConfirm"]')
                try:
                    confirm.wait_for(state="visible", timeout=1200)
                    real_click(confirm.first)
                except PlaywrightTimeoutError:
                    pass
            confirmed = False
            deadline = time.monotonic() + 2.5
            while time.monotonic() < deadline:
                again = read_action_state(page, status_id, [action]) or {}
                if (again.get(action) or {}).get("on"):
                    confirmed = True
                    break
                page.wait_for_timeout(60)
            outcome[action] = "تم التنفيذ" if confirmed else "أُرسل الطلب لكن تعذر تأكيد الحالة"
            trace_click(f"{action} النتيجة: {outcome[action]}")
        except Exception as exc:
            if browser_closed_error(exc):
                raise BrowserClosed() from exc
            outcome[action] = "تعذر التنفيذ"
            trace_click(action + " استثناء " + traceback.format_exc().replace("\n", " | ")[-400:])
    return outcome


def normalize_gemini_model(value: str) -> str | None:
    model = (value or "").strip()
    if model.lower().startswith("models/"):
        model = model.split("/", 1)[1].strip()
    if re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]{0,80}", model):
        return model
    return None


def valid_gemini_key(value: str) -> bool:
    return bool(re.fullmatch(r"[A-Za-z0-9_\-]{20,256}", value or ""))


def clean_comment(raw: str) -> str:
    text = re.sub(r"\s+", " ", raw or "").strip()
    text = text.replace("**", "")
    text = re.sub(r"^(?:reply|comment|التعليق|الرد|الدعاء)\s*[:：\-]\s*", "", text, flags=re.I)
    text = re.sub(r"^[\w؀-ۿ]{2,24}\s*[:：]\s*", "", text)
    text = text.strip("\"'«»“” ")
    if len(text) > 280:
        cut = text[:280]
        end = max(cut.rfind("؟"), cut.rfind("?"), cut.rfind("!"), cut.rfind("."), cut.rfind("…"))
        text = cut[: end + 1] if end >= 40 else cut.rsplit(" ", 1)[0]
    return text.strip()


def comment_is_complete(text: str) -> bool:
    # An emoji or two at the end are fine: the words before them are what is checked.
    text = re.sub(r"[\s\u200d\ufe0f\u2600-\u27bf\U0001f000-\U0001faff]+$", "", text or "")
    words = [word for word in text.split() if word]
    if len(words) < 6:
        return False
    if re.search(r"[،,؛;:：\-–—/\\*]$", text.strip()):
        return False
    last = re.sub(r"[.!?؟…\"'«»“”]+$", "", words[-1])
    return len(last) > 2


def gemini_thinking_config(model: str) -> dict | None:
    if re.search(r"2\.5", model):
        return {"thinkingBudget": 0}
    if re.search(r"gemini-3|3\.\d", model):
        return {"thinkingLevel": "low"}
    return None


def gemini_is_busy(status: int, detail: str) -> bool:
    if status in (429, 500, 502, 503, 504):
        return True
    return bool(re.search(
        r"high demand|try again later|unavailable|overloaded|resource exhausted|rate limit|quota",
        detail or "",
        re.I,
    ))


GEMINI_USAGE_PATH = DATA_DIR / "gemini_usage.json"
# Price counted for each comment the model writes (shown on the page as the running total).
GEMINI_PRICE_PER_COMMENT = 0.01
# Password asked by the page's hidden button that resets the cost (the comment count is kept). Only in
# the owner's copy: users' costs are reset from «توزيع البرنامج».
COST_RESET_PASSWORD = "a1@"
gemini_usage_lock = threading.Lock()
gemini_usage: dict = {}


def load_gemini_usage() -> None:
    loaded = read_private_json(GEMINI_USAGE_PATH) or {}
    try:
        comments = max(0, int(loaded.get("comments") or 0))
        since = float(loaded.get("since") or 0)
        # Comments counted in the cost since it was last reset (all of them if it never was).
        cost_comments = max(0, int(loaded.get("cost_comments", comments) or 0))
    except (TypeError, ValueError):
        comments, since, cost_comments = 0, 0.0, 0
    with gemini_usage_lock:
        gemini_usage.clear()
        # reset_id: the owner's last cost reset this copy made («توزيع البرنامج»).
        gemini_usage.update({"comments": comments, "since": since, "cost_comments": cost_comments, "reset_id": str(loaded.get("reset_id") or "")})


def record_comment_generated() -> None:
    """Count one comment written by the model."""
    try:
        with gemini_usage_lock:
            if not gemini_usage.get("since"):
                gemini_usage["since"] = time.time()
            gemini_usage["comments"] = int(gemini_usage.get("comments") or 0) + 1
            gemini_usage["cost_comments"] = int(gemini_usage.get("cost_comments") or 0) + 1
            write_private_json(GEMINI_USAGE_PATH, dict(gemini_usage))
    except Exception:
        pass


def reset_gemini_cost(reset_id: str = "") -> None:
    """Start the cost again from 0; the comment count is kept. reset_id: the owner's reset it answers."""
    with gemini_usage_lock:
        gemini_usage["cost_comments"] = 0
        if reset_id:
            gemini_usage["reset_id"] = reset_id
        write_private_json(GEMINI_USAGE_PATH, dict(gemini_usage))


# «صيغة الرد» on the page: how the comment speaks of the one writing it (the account's owner).
REPLY_VOICES = {
    "male": "You write as a man: when you speak of yourself, use masculine forms (in Arabic: مبسوط، متأكد).",
    "female": "You write as a woman: when you speak of yourself, use feminine forms (in Arabic: مبسوطة، متأكدة).",
    "neutral": "The reply must suit a man or a woman: never use words that show the writer's gender "
               "(in Arabic, no forms like مبسوط or مبسوطة, متأكد or متأكدة).",
}
# The voice when none (or an unknown one) is given.
DEFAULT_REPLY_VOICE = "male"
# How a reply takes the tweet: one is drawn at random for each reply, so the group's accounts do not all answer
# one tweet the same way (and one account does not answer every tweet the same way).
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
# How long, in words: drawn at random too, all within REPLY_MAX_CHARS.
REPLY_LENGTHS = ((6, 10), (8, 13), (10, 16))
# The most a posted reply may be, in characters (spaces included).
REPLY_MAX_CHARS = 100
# How much of the tweet's text goes with the screenshot: enough for a long post to be read to its end (a story
# cut at its start was answered wrongly).
REPLY_TWEET_TEXT = 1200
# How an account writes: one manner for each account (drawn from it, so it stays the same), as a real person
# keeps their own.
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
# The last replies written on this copy, by account and by tweet: the next reply is told not to look like them.
REPLIES_REMEMBERED = 8
replies_by_account: dict[str, list[str]] = {}
replies_by_tweet: dict[str, list[str]] = {}
account_names: dict[str, str] = {}   # معرّف الحساب (profile_key) -> اسم X المقروء، لعرض التكلفة لكل حساب
replies_memory_lock = threading.Lock()


def reply_manner(account: str) -> str:
    """The account's own manner of writing (always the same one for an account)."""
    if not account:
        return random.choice(REPLY_MANNERS)
    drawn = int(hashlib.sha256(("reply-manner:" + account).encode("utf-8")).hexdigest()[:8], 16)
    return REPLY_MANNERS[drawn % len(REPLY_MANNERS)]


def remember_reply(account: str, tweet_id: str, text: str) -> None:
    with replies_memory_lock:
        for book, key in ((replies_by_account, account), (replies_by_tweet, tweet_id)):
            if key:
                kept = book.setdefault(key, [])
                kept.append(text)
                del kept[:-REPLIES_REMEMBERED]
        while len(replies_by_tweet) > 500:
            replies_by_tweet.pop(next(iter(replies_by_tweet)))


def reply_prompt(voice: str, account: str = "", tweet_id: str = "") -> str:
    """What the model is asked for one reply: a remark on the tweet's topic, not about the writer (no stories or
    experiences of theirs) and not a compliment, in the account's manner, with an angle and a length drawn for
    this reply, and the replies it must not look like."""
    low, high = random.choice(REPLY_LENGTHS)
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
        f"This time: {random.choice(REPLY_ANGLES)}. Your manner (always the same): {reply_manner(account)}. "
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
        "The image, when one comes, is only there to understand the tweet: never mention it, the picture, the post "
        "or the tweet (no الصورة، المنشور، التغريدة); react to what is in them. Lines in square brackets under the "
        "tweet's text (the post it quotes, its picture) say what the tweet shows; they are not its words. "
        "Do not open with filler (like صراحة، فعلاً، والله) or by repeating the tweet. "
        "No hashtags, no links, no quotes, no labels, no introduction. Return only the finished reply."
    )
    with replies_memory_lock:
        own = list(replies_by_account.get(account) or []) if account else []
        others = [text for text in (replies_by_tweet.get(tweet_id) or []) if text not in own] if tweet_id else []
    if others:
        prompt += ("\n\nReplies other people already wrote to this same tweet. Yours must say something else, "
                   "in another way:\n" + "\n".join("- " + text for text in others))
    if own:
        prompt += ("\n\nYour own last replies to other tweets. This one must not look like them (another opening, "
                   "another shape, other words):\n" + "\n".join("- " + text for text in own))
    return prompt


def gemini_comment(api_key: str, model: str, image: bytes | None, tweet_text: str, voice: str = DEFAULT_REPLY_VOICE,
                   account: str = "", tweet_id: str = "") -> str:
    """One reply to a tweet, from the account (its profile key) to the tweet (its id)."""
    prompt = reply_prompt(voice, account, tweet_id)
    if image:
        prompt = "Look at the image sent with the tweet. " + prompt
    if tweet_text:
        prompt += "\n\nTweet text:\n" + tweet_text[:REPLY_TWEET_TEXT]
    parts: list[dict] = [{"text": prompt}]
    if image:
        parts.append({"inlineData": {"mimeType": "image/jpeg", "data": base64.b64encode(image).decode("ascii")}})
    attempts: list[tuple[dict | None, int]] = [(gemini_thinking_config(model), 2048), (None, 4096)]
    busy_waits = (5, 12, 20, 30)
    best = ""
    saw_busy = False
    for thinking, max_tokens in attempts:
        # The model's own temperature (1.0): Google advises it for Gemini 3, and it keeps the replies varied.
        config: dict = {"temperature": 1.0, "maxOutputTokens": max_tokens}
        if thinking:
            config["thinkingConfig"] = thinking
        body = {"contents": [{"parts": parts}], "generationConfig": config}
        payload = None
        thinking_rejected = False
        for try_index in range(len(busy_waits) + 1):
            request = urllib.request.Request(
                "https://generativelanguage.googleapis.com/v1beta/models/"
                + quote(model, safe="")
                + ":generateContent",
                data=json.dumps(body).encode("utf-8"),
                headers={"Content-Type": "application/json", "x-goog-api-key": api_key},
                method="POST",
            )
            try:
                with urllib.request.urlopen(request, timeout=45) as response:
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
                if gemini_is_busy(getattr(exc, "code", 0) or 0, detail):
                    saw_busy = True
                    if try_index < len(busy_waits):
                        time.sleep(busy_waits[try_index])
                        continue
                    break
                raise RuntimeError(detail or "رفض Gemini الطلب") from None
            except Exception as exc:
                if try_index < 2:
                    time.sleep(busy_waits[try_index])
                    continue
                raise RuntimeError("تعذر الاتصال بـ Gemini") from exc
        if thinking_rejected:
            continue
        if not payload:
            break
        candidate = (payload.get("candidates") or [{}])[0]
        reply_parts = ((candidate.get("content") or {}).get("parts") or [])
        texts = []
        for part in reply_parts:
            if not isinstance(part, dict) or part.get("thought"):
                continue
            if part.get("text"):
                texts.append(str(part["text"]))
        text = clean_comment(" ".join(texts))
        if comment_is_complete(text):
            record_comment_generated()
            remember_reply(account, tweet_id, text)
            return text
        if len(text) > len(best):
            best = text
    if comment_is_complete(best):
        record_comment_generated()
        remember_reply(account, tweet_id, best)
        return best
    if saw_busy:
        raise RuntimeError("النموذج مشغول مؤقتًا بعد عدة محاولات. غيّر النموذج أو أعد التنفيذ بعد قليل.")
    return ""


# Comments by Grok (xAI), when the owner chooses it in «توزيع البرنامج»: for users' copies, its key and model
# come with each check-in (kept in memory only); the owner's own copy follows the same choice, with the key
# and model saved there. (A copy of the script with no «توزيع البرنامج» has its own «مفتاح Claude» in its
# panel instead: see Claude's part below.) Each comment is asked with the same prompt as Gemini's, through
# xAI's Responses API, with the tweet's picture.
GROK_URL = "https://api.x.ai/v1/responses"
GROK_DEFAULT_MODEL = "grok-4.3"             # (as in g.py: the model when none is set there)
GROK_PATH = DATA_DIR / "grok.json"         # (a Grok key kept from before: removed when the program starts)
# Comments are asked with no reasoning: much faster (and cheaper) than thinking first, and enough for a reply
# this short. A model that does not take the setting is asked again without it (with its own default), and
# is not sent it again.
GROK_REASONING = {"effort": "none"}
grok_reasoning_refused: set[str] = set()
grok_lock = threading.Lock()
saved_grok: dict = {"engine": "gemini", "api_key": "", "model": ""}


def valid_grok_key(value: str) -> bool:
    return bool(re.fullmatch(r"[A-Za-z0-9_\-]{20,256}", value or ""))


def valid_grok_model(value: str) -> bool:
    return bool(re.fullmatch(r"[a-z0-9][a-z0-9.\-]{1,60}", value or ""))


def apply_owner_comments(engine: str, key: str, model: str) -> None:
    """Who the owner chose to write this copy's comments (from its check-in): Grok or Claude, with its key and
    model, or Gemini (the other key is then dropped here)."""
    valid = (engine == "grok" and valid_grok_key(key) and valid_grok_model(model)) or \
        (engine == "claude" and valid_claude_key(key) and valid_claude_model(model))
    wanted = {"engine": engine if valid else "gemini", "api_key": key if valid else "", "model": model if valid else ""}
    with grok_lock:
        saved_grok.update(wanted)              # (in memory only)


def distribution_saved() -> dict:
    """What «توزيع البرنامج» saved beside this script (g.py's data/distribution.json), only read here."""
    try:
        loaded = json.loads((CONTROL_FILE.with_name("data") / "distribution.json").read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}
    return loaded if isinstance(loaded, dict) else {}


def owner_comments_choice() -> dict:
    """The owner's copy: who writes the comments, as chosen in «توزيع البرنامج» for users' copies (the same for
    this one) {"engine", "api_key", "model"}: from g.py's page when this program serves it, else from what
    that page saved beside this script."""
    page = distribution_page
    names = ("comments_engine", "grok_key", "grok_model", "claude_key", "claude_model")
    if page is not None:
        with page.store_lock:
            saved = {name: page.store.get(name) for name in names}
        grok_default = str(getattr(page, "GROK_DEFAULT_MODEL", "") or GROK_DEFAULT_MODEL)
        claude_default = str(getattr(page, "CLAUDE_DEFAULT_MODEL", "") or CLAUDE_DEFAULT_MODEL)
    else:
        saved, grok_default, claude_default = distribution_saved(), GROK_DEFAULT_MODEL, CLAUDE_DEFAULT_MODEL
    engine = str(saved.get("comments_engine") or "")
    if engine == "claude":
        return {"engine": engine, "api_key": str(saved.get("claude_key") or "").strip(),
                "model": str(saved.get("claude_model") or "").strip().lower() or claude_default}
    return {"engine": engine, "api_key": str(saved.get("grok_key") or "").strip(),
            "model": str(saved.get("grok_model") or "").strip().lower() or grok_default}


def comments_writer() -> tuple[str, str, str]:
    """Who writes this copy's comments: ("grok" | "claude", key, model), or ("gemini", "", "") — the owner's
    choice in «توزيع البرنامج», for users' copies (from their check-ins) and for the owner's own copy alike."""
    if is_owner_copy() and not key_typed_here():
        choice = owner_comments_choice()
    else:
        # A user's copy (from its check-ins), or a copy with no «توزيع البرنامج» (the key typed in its panel).
        with grok_lock:
            choice = dict(saved_grok)
    engine, key, model = choice.get("engine"), str(choice.get("api_key") or ""), str(choice.get("model") or "")
    if engine == "grok" and valid_grok_key(key) and valid_grok_model(model):
        return "grok", key, model
    if engine == "claude" and valid_claude_key(key) and valid_claude_model(model):
        return "claude", key, model
    return "gemini", "", ""


def grok_settings() -> tuple[str, str]:
    """(key, model) when Grok writes this copy's comments, else ("", "")."""
    engine, key, model = comments_writer()
    return (key, model) if engine == "grok" else ("", "")


def grok_comments_on() -> bool:
    """Whether Grok writes this copy's comments (see comments_writer)."""
    return bool(grok_settings()[0])


def gemini_writes_comments() -> bool:
    """Whether Gemini writes this copy's comments (no Grok or Claude chosen)."""
    return comments_writer()[0] == "gemini"


def grok_answer_text(answer: dict) -> str:
    """The text of a Responses API answer: output[] → message → content[] → output_text."""
    parts = []
    for item in answer.get("output") or []:
        if isinstance(item, dict) and item.get("type") == "message":
            for content in item.get("content") or []:
                if isinstance(content, dict) and content.get("type") == "output_text":
                    parts.append(str(content.get("text") or ""))
    return "\n".join(parts) or str(answer.get("output_text") or "")


def grok_comment(api_key: str, model: str, image: bytes | None, tweet_text: str, voice: str = DEFAULT_REPLY_VOICE,
                 account: str = "", tweet_id: str = "") -> str:
    """One reply to a tweet by Grok: the same prompt as Gemini's, the tweet's picture with it, no reasoning. A
    model that does not take the reasoning setting is asked again without it; a busy Grok is asked again a
    few times."""
    prompt = reply_prompt(voice, account, tweet_id)
    if image:
        prompt = "Look at the image sent with the tweet. " + prompt
    if tweet_text:
        prompt += "\n\nTweet text:\n" + tweet_text[:REPLY_TWEET_TEXT]
    content: list[dict] = [{"type": "input_text", "text": prompt}]
    if image:
        content.append({"type": "input_image", "image_url": "data:image/jpeg;base64," + base64.b64encode(image).decode("ascii")})
    reasoning = model not in grok_reasoning_refused
    busy_waits = (5, 12, 20, 30)
    best = ""
    saw_busy = False
    for _ in range(2):               # a reply that comes back cut off is asked for once more
        payload = None
        for try_index in range(len(busy_waits) + 1):
            body: dict = {"model": model, "input": [{"role": "user", "content": content}]}
            if reasoning:
                body["reasoning"] = dict(GROK_REASONING)
            request = urllib.request.Request(GROK_URL, data=json.dumps(body).encode("utf-8"), method="POST",
                                             headers={"Content-Type": "application/json", "Authorization": "Bearer " + api_key})
            try:
                with urllib.request.urlopen(request, timeout=60) as response:
                    payload = json.loads(response.read().decode("utf-8"))
                break
            except urllib.error.HTTPError as exc:
                detail = ""
                try:
                    data = json.loads(exc.read(4096).decode("utf-8", "replace"))
                    error = data.get("error") if isinstance(data, dict) else None
                    detail = str((error.get("message") if isinstance(error, dict) else error) or data.get("message") or "")
                except Exception:
                    detail = ""
                detail = re.sub(r"\s+", " ", detail.replace(api_key, "…") if api_key else detail).strip()[:160]
                if reasoning and exc.code == 400 and re.search(r"reasoning", detail, re.I):
                    reasoning = False    # this model takes no reasoning setting: asked again without it,
                    grok_reasoning_refused.add(model)    # and not sent it again
                    continue
                if exc.code in (401, 403):
                    raise RuntimeError("مفتاح Grok غير صالح أو بلا صلاحية. أخبر صاحب البرنامج.") from None
                if re.search(r"credit|spending limit|billing", detail, re.I):
                    raise RuntimeError("نفد رصيد Grok أو بلغ حد الإنفاق. أخبر صاحب البرنامج.") from None
                if exc.code in (429, 500, 502, 503, 504):
                    saw_busy = True
                    if try_index < len(busy_waits):
                        time.sleep(busy_waits[try_index])
                        continue
                    break
                raise RuntimeError(("رفض Grok الطلب: " + detail) if detail else f"تعذر الاتصال بـ Grok (رمز {exc.code}).") from None
            except (urllib.error.URLError, OSError, ValueError) as exc:
                if try_index < 2:
                    time.sleep(busy_waits[try_index])
                    continue
                raise RuntimeError("تعذر الاتصال بـ Grok") from exc
        if not isinstance(payload, dict):
            break
        text = clean_comment(grok_answer_text(payload))
        if comment_is_complete(text):
            record_comment_generated()
            remember_reply(account, tweet_id, text)
            return text
        if len(text) > len(best):
            best = text
    if comment_is_complete(best):
        record_comment_generated()
        remember_reply(account, tweet_id, best)
        return best
    if saw_busy:
        raise RuntimeError("Grok مشغول مؤقتًا بعد عدة محاولات. أعد التنفيذ بعد قليل.")
    return ""


# Comments by Claude (Anthropic), when the owner chooses it in «توزيع البرنامج»: the same as Grok's (its key and
# model come with each check-in, in memory only), asked through the Messages API with the same prompt and the
# tweet's picture, at medium effort (it thinks a little before it writes).
CLAUDE_URL = "https://api.anthropic.com/v1/messages"
CLAUDE_API_VERSION = "2026-10-21"
CLAUDE_DEFAULT_MODEL = "claude-haiku-5-5"   # (as in g.py: the model when none is set there)
CLAUDE_EFFORT = "medium"
# Models that take no effort setting (older ones), asked again without it and not sent it again.
claude_effort_refused: set[str] = set()


def valid_claude_key(value: str) -> bool:
    return bool(re.fullmatch(r"sk-ant-[A-Za-z0-9_\-]{20,250}", value or ""))


def valid_claude_model(value: str) -> bool:
    return bool(re.fullmatch(r"[a-z0-9][a-z0-9.\-]{1,60}", value or ""))


# A copy of the script with no «توزيع البرنامج» (no g.py beside it) has its own «مفتاح Claude» in its panel: the
# key typed there, kept sealed in data/claude.json, writes its comments with Claude, at the same effort and with
# the same prompt, and it needs nothing else. (Its panel had «مفتاح Grok» before: a Grok key kept from then is
# removed, and the comments are Gemini's until a Claude key is saved.)
CLAUDE_PATH = DATA_DIR / "claude.json"


def key_typed_here() -> bool:
    """A copy on its own (see on_its_own): its comments are written with the Claude key typed in its own panel,
    when one is saved, and it needs nothing else."""
    return on_its_own()


def load_panel_key() -> None:
    """A user's copy keeps the comments key in memory only, from its check-ins, never on its disk: files from
    before (data/grok.json, which held one) are removed, and the copy starts with Gemini until its first
    check-in. The owner's copy reads back the Claude key typed in its own panel («مفتاح Claude»), kept there
    sealed; a Grok key typed there before («مفتاح Grok», no longer in the panel) is removed, as is any file it
    cannot use."""
    key = model = ""
    if is_owner_copy():
        loaded = read_private_json(CLAUDE_PATH) or {}
        key = open_key(loaded.get("api_key_sealed")).strip() if loaded.get("source") == "panel" else ""
        model = str(loaded.get("model") or "").strip().lower() or CLAUDE_DEFAULT_MODEL
    if not (valid_claude_key(key) and valid_claude_model(model)):
        key = model = ""
    for path in (GROK_PATH,) if key else (GROK_PATH, CLAUDE_PATH):
        try:
            path.unlink()
        except OSError:
            pass
    with grok_lock:
        saved_grok.update(engine="claude" if key else "gemini", api_key=key, model=model)


def remember_own_claude(key: str, model: str) -> None:
    """The Claude key and model typed in this copy's panel (none: back to Gemini), kept sealed."""
    with grok_lock:
        saved_grok.update(engine="claude" if key else "gemini", api_key=key, model=model if key else "")
        if key:
            write_private_json(CLAUDE_PATH, {"version": 1, "source": "panel", "api_key_sealed": seal_key(key), "model": model})
        else:
            try:
                CLAUDE_PATH.unlink()
            except OSError:
                pass


def own_claude_shown() -> dict:
    """What the panel shows of its own Claude key: only its first and last letters."""
    with grok_lock:
        key, model = (saved_grok["api_key"], saved_grok["model"]) if saved_grok["engine"] == "claude" else ("", "")
    return {"claude_key": f"{key[:7]}…{key[-4:]}" if key else "", "claude_model": model or CLAUDE_DEFAULT_MODEL}


def claude_answer_text(answer: dict) -> str:
    """The text of a Messages API answer: its text blocks (it may begin with thinking blocks)."""
    parts = [str(block.get("text") or "") for block in answer.get("content") or []
             if isinstance(block, dict) and block.get("type") == "text"]
    return "\n".join(parts)


def claude_comment(api_key: str, model: str, image: bytes | None, tweet_text: str, voice: str = DEFAULT_REPLY_VOICE,
                   account: str = "", tweet_id: str = "") -> str:
    """One reply to a tweet by Claude: the same prompt as Gemini's and Grok's, the tweet's picture with it, at
    medium effort. A model that takes no effort setting is asked again without it; a busy Claude is asked again
    a few times."""
    prompt = reply_prompt(voice, account, tweet_id)
    if image:
        prompt = "Look at the image sent with the tweet. " + prompt
    if tweet_text:
        prompt += "\n\nTweet text:\n" + tweet_text[:REPLY_TWEET_TEXT]
    content: list[dict] = []
    if image:
        content.append({"type": "image", "source": {"type": "base64", "media_type": "image/jpeg",
                                                    "data": base64.b64encode(image).decode("ascii")}})
    content.append({"type": "text", "text": prompt})
    effort = model not in claude_effort_refused
    busy_waits = (5, 12, 20, 30)
    best = ""
    saw_busy = False
    for _ in range(2):               # a reply that comes back cut off is asked for once more
        payload = None
        for try_index in range(len(busy_waits) + 1):
            # (Its thinking counts toward max_tokens: room for it, and for the short reply after it.)
            body: dict = {"model": model, "max_tokens": 2048, "messages": [{"role": "user", "content": content}]}
            if effort:
                body["output_config"] = {"effort": CLAUDE_EFFORT}
            request = urllib.request.Request(CLAUDE_URL, data=json.dumps(body).encode("utf-8"), method="POST",
                                             headers={"Content-Type": "application/json", "x-api-key": api_key,
                                                      "anthropic-version": CLAUDE_API_VERSION})
            try:
                with urllib.request.urlopen(request, timeout=60) as response:
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
                    effort = False       # this model takes no effort setting: asked again without it,
                    claude_effort_refused.add(model)    # and not sent it again
                    continue
                if exc.code in (401, 403):
                    raise RuntimeError("مفتاح Claude غير صالح أو بلا صلاحية. أخبر صاحب البرنامج.") from None
                if code == "enforced_spend_limit_reached" or re.search(r"usage limits|credit balance|billing", detail, re.I):
                    raise RuntimeError("بلغ حساب Claude حد الصرف أو نفد رصيده. أخبر صاحب البرنامج.") from None
                if exc.code in (429, 500, 502, 503, 504, 529):
                    saw_busy = True
                    if try_index < len(busy_waits):
                        time.sleep(busy_waits[try_index])
                        continue
                    break
                raise RuntimeError(("رفض Claude الطلب: " + detail) if detail else f"تعذر الاتصال بـ Claude (رمز {exc.code}).") from None
            except (urllib.error.URLError, OSError, ValueError) as exc:
                if try_index < 2:
                    time.sleep(busy_waits[try_index])
                    continue
                raise RuntimeError("تعذر الاتصال بـ Claude") from exc
        if not isinstance(payload, dict):
            break
        if payload.get("stop_reason") == "refusal":
            raise RuntimeError("امتنع Claude عن التعليق على هذه التغريدة.")
        text = clean_comment(claude_answer_text(payload))
        if comment_is_complete(text):
            record_comment_generated()
            remember_reply(account, tweet_id, text)
            return text
        if len(text) > len(best):
            best = text
    if comment_is_complete(best):
        record_comment_generated()
        remember_reply(account, tweet_id, best)
        return best
    if saw_busy:
        raise RuntimeError("Claude مشغول مؤقتًا بعد عدة محاولات. أعد التنفيذ بعد قليل.")
    return ""


# Arabic diacritics (تشكيل): tanween, fatha, damma, kasra, shadda, sukun, and the other marks over or under letters.
ARABIC_DIACRITICS = re.compile(r"[\u064B-\u0652\u0656-\u065F\u0670]")
# Words a reply cannot end on, when one that is too long is shortened.
HANGING_WORDS = {"و", "او", "أو", "بس", "لكن", "لان", "لأن", "عشان", "اللي", "الي", "في", "من", "على", "عن", "مع", "الى",
                 "إلى", "يعني", "ثم", "حتى", "اذا", "إذا", "لو", "ما", "لا", "كان", "and", "or", "but", "the", "to", "of",
                 "in", "a", "an", "with", "for", "that", "ve", "ama", "ile", "için", "bir", "de", "da"}


def polish_comment(text: str) -> str:
    """The reply as it is posted: no Arabic diacritics and no commas (a number's thousands keep their digits)."""
    text = ARABIC_DIACRITICS.sub("", text or "")
    text = re.sub(r"(?<=\d),(?=\d{3})", "", text)
    text = re.sub(r"\s*[،,؛;]\s*", " ", text)
    return re.sub(r"\s+", " ", text).strip()


def fit_comment(text: str, limit: int = REPLY_MAX_CHARS) -> str:
    """A reply cut to at most limit characters, at a word, and not on a word that leaves it hanging."""
    words = text.split()
    while words and len(" ".join(words)) > limit:
        words.pop()
    while words and words[-1].lower() in HANGING_WORDS:
        words.pop()
    return " ".join(words)


def write_comment(api_key: str, model: str, image: bytes | None, tweet_text: str, voice: str = DEFAULT_REPLY_VOICE,
                  account: str = "", tweet_id: str = "") -> str:
    """One reply, by whoever writes this copy's comments: Grok or Claude when the owner chose one of them in
    «توزيع البرنامج» (for users' copies and the owner's alike), else Gemini (with the task's key and model, or
    this copy's saved ones). It is posted with no diacritics and no commas, in at most REPLY_MAX_CHARS
    characters: one that comes back longer is asked for once more, then shortened at a word."""
    if control_configured():
        return control_comment(tweet_text, image, voice, account, tweet_id)
    if not is_owner_copy() and not wait_for_owner_keys():
        raise RuntimeError(no_keys_message())
    engine, key, engine_model = comments_writer()
    if engine == "gemini" and not api_key:
        with gemini_lock:
            api_key = str(saved_gemini.get("api_key") or "")
            model = model or normalize_gemini_model(str(saved_gemini.get("model") or ""))

    def ask() -> str:
        if engine == "grok":
            return grok_comment(key, engine_model, image, tweet_text, voice, account, tweet_id)
        if engine == "claude":
            return claude_comment(key, engine_model, image, tweet_text, voice, account, tweet_id)
        return gemini_comment(api_key, model, image, tweet_text, voice, account, tweet_id)

    first = polish_comment(ask())
    if len(first) <= REPLY_MAX_CHARS:
        return first
    second = polish_comment(ask())               # too long: asked for once more
    if second and len(second) <= REPLY_MAX_CHARS:
        return second
    return fit_comment(min((text for text in (first, second) if text), key=len))


def reply_for(api_key: str, model: str, image: bytes | None, tweet_text: str, voice: str = DEFAULT_REPLY_VOICE,
              account: str = "", tweet_id: str = "") -> str:
    """One reply (see write_comment), asked once more when the first is under four words."""
    comment = write_comment(api_key, model, image, tweet_text, voice, account, tweet_id)
    if len(comment.split()) < 4:
        comment = write_comment(api_key, model, image, tweet_text, voice, account, tweet_id)
    return comment


# A reply is written from the tweet's content, asked of FxTwitter (api.fxtwitter.com/status/<id>, see
# fx_tweet_views), not from a picture of the opened page: its text, the post it quotes, and its picture
# only when its own text is too short to say what it is about (under COMMENT_PICTURE_LETTERS letters).
# So it can be written before the tweet is opened: a comments task asks for the next tweet's reply while
# it is still on the one before (CommentsAhead), and when the tweet opens its reply is ready.
COMMENT_PICTURE_LETTERS = 60
COMMENT_PICTURE_MAX_BYTES = 3_000_000


def comment_material(content: dict) -> tuple[str, str]:
    """What a reply is written from, out of a tweet's content (see fx_content): its text (with the post it
    quotes), and the address of the picture to send with it ("" when its text says enough, or it has none)."""
    body = re.sub(r"[ \t ]+", " ", str(content.get("body") or "")).strip()
    quoted = content.get("quote") if isinstance(content.get("quote"), dict) else {}
    lines = [body] if body else []
    quote_body = re.sub(r"\s+", " ", str(quoted.get("body") or "")).strip()
    if quote_body:
        by = str(quoted.get("by") or "")
        lines.append(f"[The post it quotes{' (by @' + by + ')' if by else ''}: {quote_body[:600]}]")
    picture = ""
    if len(re.sub(r"[\W_]+", "", re.sub(r"https?://\S+", "", body))) < COMMENT_PICTURE_LETTERS:
        for kind, address in list(content.get("pictures") or []) + list(quoted.get("pictures") or []):
            picture = address
            break
    if picture:
        lines.append("[The picture sent with it is the tweet's own picture]")
    return "\n".join(lines).strip(), picture


def fetch_picture(address: str) -> bytes | None:
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


class CommentsAhead:
    """The replies of one comments task, written before their tweets are opened. ask(item): the tweet's
    content is asked of FxTwitter and its reply written, in the background; take(id): that reply (waiting
    for it while it is still being written) and the content it came from. A task asks for the tweet it is
    about to open and for the one after it, so the next reply is being written while the task is still
    on the tweet before."""

    def __init__(self, write, account: str, actions: list[str], should_stop=None):
        self.write = write                  # (tweet_text, image, tweet_id) -> reply
        self.account = account
        self.actions = list(actions)
        self.should_stop = should_stop
        self.lock = threading.Lock()
        self.asked: dict[str, dict] = {}
        self.closed = False

    def ask(self, item: dict | None) -> None:
        url = str((item or {}).get("url") or "")
        status_id = tweet_status_id(url)
        if not status_id or self.closed or (self.should_stop and self.should_stop()):
            return
        if "comment" not in item_actions(item or {}, self.actions):
            return                          # (a retry of the failed: this tweet's comment is not asked again)
        if (already_done_recently(self.account, status_id, self.actions)
                or already_done_recently(self.account, status_id, ["comment"]) or tweet_is_ignored(url)):
            return                          # it is skipped: no reply is needed
        with self.lock:
            if status_id in self.asked:
                return
            entry = {"done": threading.Event(), "reply": "", "content": None, "error": ""}
            self.asked[status_id] = entry
        threading.Thread(target=self._write, args=(status_id, entry), name="comment-ahead", daemon=True).start()

    def _write(self, status_id: str, entry: dict) -> None:
        with as_account(self.account):
            try:
                outcome, _views, link, content = fx_tweet_views(status_id)
                if outcome != "ok" or content is None:
                    entry["error"] = outcome
                    return
                entry["content"] = content
                if self.closed or (link and tweet_is_ignored(link)):
                    return
                text, picture = comment_material(content)
                image = fetch_picture(picture) if picture else None
                if (text or image) and not self.closed:
                    entry["reply"] = self.write(text, image, status_id)
            except Exception as exc:        # (the reply is then written when the tweet opens)
                entry["error"] = (str(exc).splitlines() or [type(exc).__name__])[0][:160]
            finally:
                entry["done"].set()

    def take(self, status_id: str) -> tuple[str, dict | None]:
        """The reply written ahead for this tweet, and the content it was written from: ("", content or None)
        when there is none (FxTwitter had no answer, or writing it failed)."""
        with self.lock:
            entry = self.asked.pop(status_id, None)
        if entry is None:
            return "", None
        while not entry["done"].wait(0.25):
            if self.closed or (self.should_stop and self.should_stop()):
                return "", None
        return entry["reply"], entry["content"]

    def keep_only(self, status_ids: set[str]) -> None:
        """Forget the tweets the task has gone past (a reply still being written for one is not used)."""
        with self.lock:
            for status_id in [key for key in self.asked if key not in status_ids]:
                del self.asked[status_id]

    def close(self) -> None:
        self.closed = True
        with self.lock:
            self.asked.clear()


PAGE_PICTURE_JS = r"""
(statusId) => {
  const articles = [...document.querySelectorAll('article[data-testid="tweet"]')];
  const article = articles.find((node) => statusId && node.querySelector('a[href*="/status/' + statusId + '"]')) || articles[0];
  if (!article) return "";
  const photo = article.querySelector('[data-testid="tweetPhoto"] img');
  if (photo && photo.getAttribute("src")) return photo.getAttribute("src");
  const video = article.querySelector("video[poster]");
  return video ? (video.getAttribute("poster") || "") : "";
}
"""


def reply_from_page(page, card, item: dict, content: dict | None, api_key: str, model: str, voice: str,
                    account: str, tweet_id: str) -> str:
    """The reply, written once the tweet is open, when none was ready: from its content when FxTwitter gave
    it, else from what the opened page shows (its text, and its picture when the text is short)."""
    if content is not None:
        text, picture = comment_material(content)
        image = fetch_picture(picture) if picture else None
        if text or image:
            return reply_for(api_key, model, image, text, voice, account, tweet_id)
    text = article_text(card)
    collected = str(item.get("text") or "").strip()
    if not text and collected != "تغريدة":
        text = collected
    image = None
    if len(re.sub(r"[\W_]+", "", re.sub(r"https?://\S+", "", text))) < COMMENT_PICTURE_LETTERS:
        try:
            address = str(page.evaluate(PAGE_PICTURE_JS, tweet_id) or "")
        except Exception:
            address = ""
        image = fetch_picture(address) if address else None
        if image is not None:
            text = (text + "\n[The picture sent with it is the tweet's own picture]").strip()
        elif not text:
            image = screenshot_article(card)    # nothing else to go by: a picture of the tweet as shown
    return reply_for(api_key, model, image, text, voice, account, tweet_id)


def screenshot_article(card) -> bytes | None:
    try:
        if not IN_APP:
            try:
                card.scroll_into_view_if_needed(timeout=4000)
            except Exception:
                pass
        return card.screenshot(type="jpeg", quality=70, timeout=12000)
    except Exception:
        return None


def reply_block_reason(page) -> str | None:
    try:
        text = page.evaluate("() => (document.body && document.body.innerText || '').slice(0, 5000)")
    except Exception:
        return None
    if re.search(r"can.?t reply|cannot reply|aren.?t allowed to reply|replies are limited|who can reply|Reply limited", text or "", re.I):
        return "الرد غير مسموح على هذه التغريدة"
    if re.search(r"daily limit|rate limit|Try again later", text or "", re.I):
        return "الحساب وصل حد الردود مؤقتًا"
    if re.search(r"لا يمكنك الرد|غير مسموح بالرد|الردود محدودة", text or ""):
        return "الرد غير مسموح على هذه التغريدة"
    return None


def reply_button_ready(page) -> bool:
    try:
        return bool(page.evaluate(
            """() => {
              const nodes = [...document.querySelectorAll('[data-testid="tweetButtonInline"], [data-testid="tweetButton"]')];
              return nodes.some((button) => button.getAttribute("aria-disabled") !== "true" && !button.disabled);
            }"""
        ))
    except Exception:
        return False


def composer_visible(page) -> bool:
    try:
        box = page.locator('[data-testid="tweetTextarea_0"]')
        return box.count() > 0 and box.first.is_visible()
    except Exception:
        return False


def open_reply_composer(page, path: str) -> None:
    """Wait for the tweet to settle, then open the reply box. On the phone, call the reply
    button's own handler. A coordinate press was landing on the account name."""
    match = re.search(r"status/(\d{6,25})", path or "")
    status_id = match.group(1) if match else ""
    if IN_APP:
        for _ in range(3):
            if composer_visible(page):
                trace_click("reply مربع الكتابة ظاهر")
                return
            try:
                pressed = page.evaluate(PRESS_PAGE_JS, {"statusId": status_id, "testid": "reply"})
            except Exception as exc:
                pressed = {"how": "error", "error": str(exc).splitlines()[0][:160]}
            trace_click(f"reply فتح {pressed}")
            try:
                page.locator('[data-testid="tweetTextarea_0"]').last.wait_for(state="visible", timeout=8000)
                trace_click("reply ظهر مربع الكتابة")
                return
            except PlaywrightTimeoutError:
                page.wait_for_timeout(500)
        raise PlaywrightTimeoutError("tweetTextarea_0 not visible after retries")
    for attempt in range(3):
        page.wait_for_timeout(800 if attempt == 0 else 1400)
        if composer_visible(page):
            real_click(page.locator('[data-testid="tweetTextarea_0"]').first)
            page.wait_for_timeout(400)
            return
        card = article_locator(page, path)
        try:
            if card.count() and not IN_APP:
                card.first.scroll_into_view_if_needed(timeout=3000)
                page.wait_for_timeout(500)
        except Exception:
            pass
        button = card.locator('[data-testid="reply"]') if card.count() else page.locator('[data-testid="reply"]')
        if button.count() == 0:
            button = page.locator('[data-testid="reply"]')
        if button.count() == 0:
            continue
        try:
            if not IN_APP:
                button.first.scroll_into_view_if_needed(timeout=2000)
                page.wait_for_timeout(400)
            real_click(button.first)
        except Exception:
            continue
        try:
            page.locator('[data-testid="tweetTextarea_0"]').last.wait_for(state="visible", timeout=8000)
            page.wait_for_timeout(500)
            return
        except PlaywrightTimeoutError:
            continue
    raise PlaywrightTimeoutError("tweetTextarea_0 not visible after retries")


# A reply is typed into the box the way a person types, not pasted whole: a letter at a time at an uneven pace,
# slower after a space or a stop, with a longer pause now and then, and a rare slip of a wrong letter that is
# backspaced at once. About 100 letters take 10 to 15 seconds.
TYPE_CHAR_MS = (55, 130)
TYPE_AFTER_SPACE_MS = (120, 260)
TYPE_AFTER_STOP_MS = (220, 460)
TYPE_THINK_MS = (450, 950)
TYPE_THINK_CHANCE = 0.05
TYPE_SLIP_CHANCE = 0.03
TYPE_STEPS_PER_CALL = 20        # (in the app the typing is done by the page itself, this many letters a call)


def typing_plan(text: str) -> list[list]:
    """[letter, milliseconds to wait after it] in order, paced so the whole comment is typed
    over about 3 to 5 seconds whatever its length (the letters still appear one after another)."""
    steps: list[list] = [[ch, 0] for ch in text]
    if not steps:
        return steps
    total = random.randint(5000, 10000)         # total time to type the whole comment, in ms
    share = total / len(steps)
    for step in steps:
        step[1] = max(8, int(share * random.uniform(0.6, 1.4)))
    return steps


def typed_text(steps: list[list]) -> str:
    """The text a typing plan leaves in the box."""
    out: list[str] = []
    for ch, _wait in steps:
        if ch == "\b":
            if out:
                out.pop()
        else:
            out.append(ch)
    return "".join(out)


def same_text(seen, wanted: str) -> bool:
    clean = lambda value: re.sub(r"\s+", " ", re.sub(r"[​‌‍﻿]", "", str(value or ""))).strip()
    return clean(seen) == clean(wanted)


# The page types the letters itself (the reply box is X's editor): each letter put in as typed text, with the
# waits between them, in the box of the reply dialog.
TYPING_JS = r"""
async ({steps, clear}) => {
  const box = document.querySelector('[role="dialog"] [data-testid="tweetTextarea_0"]')
    || document.querySelector('[data-testid="tweetTextarea_0"]');
  if (!box) return {ok: false, why: "no box"};
  const editable = box.querySelector('[contenteditable="true"]') || box;
  editable.focus();
  if (clear) {
    document.execCommand("selectAll", false);
    document.execCommand("delete", false);
  }
  const sleep = (ms) => new Promise((done) => setTimeout(done, ms));
  for (const [letter, wait] of steps) {
    if (letter === "\b") document.execCommand("delete", false);
    else document.execCommand("insertText", false, letter);
    if (wait) await sleep(wait);
  }
  return {ok: true, text: (editable.innerText || "").replace(/\s+/g, " ").trim()};
}
"""

COMPOSER_TEXT_JS = r"""
() => {
  const box = document.querySelector('[role="dialog"] [data-testid="tweetTextarea_0"]')
    || document.querySelector('[data-testid="tweetTextarea_0"]');
  return box ? (box.innerText || "") : "";
}
"""


def type_like_a_person(page, text: str) -> bool:
    """Type the reply a letter at a time (see typing_plan). True when the box then holds the text and the reply
    button is live; False when it did not work out (the box is then written in one go by the caller)."""
    steps = typing_plan(text)
    if IN_APP:
        typed: object = None
        for start in range(0, len(steps), TYPE_STEPS_PER_CALL):
            try:
                typed = page.evaluate(TYPING_JS, {"steps": steps[start:start + TYPE_STEPS_PER_CALL], "clear": start == 0})
            except Exception as exc:
                typed = {"ok": False, "why": str(exc).splitlines()[0][:80]}
            if not (isinstance(typed, dict) and typed.get("ok")):
                trace_click(f"reply الكتابة حرفًا حرفًا توقفت: {typed}")
                return False
        page.wait_for_timeout(400)
        seen = typed.get("text") if isinstance(typed, dict) else ""
    else:
        for letter, wait in steps:
            if letter == "\b":
                page.keyboard.press("Backspace")
            else:
                page.keyboard.type(letter)
            page.wait_for_timeout(wait)
        page.wait_for_timeout(350)
        try:
            seen = page.evaluate(COMPOSER_TEXT_JS)
        except Exception:
            seen = ""
    if same_text(seen, text) and reply_button_ready(page):
        trace_click(f"reply كُتب النص حرفًا حرفًا ({len(steps)} ضغطة)")
        return True
    trace_click("reply الكتابة حرفًا حرفًا لم تترك النص كما هو: يُكتب دفعة واحدة")
    return False


def insert_reply_text(page, text: str) -> None:
    if IN_APP:
        if type_like_a_person(page, text):
            return
        page.evaluate(
            """(value) => {
              const box = document.querySelector('[role="dialog"] [data-testid="tweetTextarea_0"]')
                || document.querySelector('[data-testid="tweetTextarea_0"]');
              if (!box) return false;
              const editable = box.querySelector('[contenteditable="true"]') || box;
              editable.focus();
              document.execCommand("selectAll", false);
              document.execCommand("delete", false);
              document.execCommand("insertText", false, value);
              editable.dispatchEvent(new InputEvent("input", {bubbles: true, inputType: "insertText", data: value}));
              return true;
            }""",
            text,
        )
        page.wait_for_timeout(400)
        if reply_button_ready(page):
            trace_click("reply كُتب النص")
            return
        page.keyboard.insert_text(text)
        page.wait_for_timeout(400)
        if not reply_button_ready(page):
            raise PlaywrightTimeoutError("reply button stayed disabled")
        trace_click("reply كُتب النص من لوحة المفاتيح")
        return
    box = page.locator('[role="dialog"] [data-testid="tweetTextarea_0"]')
    if box.count() == 0:
        box = page.locator('[data-testid="tweetTextarea_0"]')
    box.last.wait_for(state="visible", timeout=10000)
    real_click(box.last)
    page.keyboard.press("Control+A")
    page.keyboard.press("Backspace")
    if type_like_a_person(page, text):
        return
    page.keyboard.press("Control+A")
    page.keyboard.press("Backspace")
    page.keyboard.insert_text(text)
    page.wait_for_timeout(350)
    if reply_button_ready(page):
        return
    page.keyboard.press("Control+A")
    page.keyboard.press("Backspace")
    page.keyboard.type(text, delay=8)
    page.wait_for_timeout(250)
    if reply_button_ready(page):
        return
    page.evaluate(
        """(value) => {
          const box = document.querySelector('[role="dialog"] [data-testid="tweetTextarea_0"]')
            || document.querySelector('[data-testid="tweetTextarea_0"]');
          if (!box) return;
          const editable = box.querySelector('[contenteditable="true"]') || box;
          editable.focus();
          document.execCommand("selectAll", false);
          document.execCommand("delete", false);
          document.execCommand("insertText", false, value);
          editable.dispatchEvent(new InputEvent("input", {bubbles: true, inputType: "insertText", data: value}));
        }""",
        text,
    )
    page.wait_for_function(
        """() => {
          const nodes = [...document.querySelectorAll('[data-testid="tweetButtonInline"], [data-testid="tweetButton"]')];
          return nodes.some((button) => button.getAttribute("aria-disabled") !== "true" && !button.disabled);
        }""",
        timeout=8000,
    )


PRESS_SEND_JS = r"""
() => {
  const nodes = [...document.querySelectorAll('[data-testid="tweetButtonInline"], [data-testid="tweetButton"]')];
  const button = [...nodes].reverse().find((node) => node.getAttribute("aria-disabled") !== "true" && !node.disabled);
  if (!button) return {how: "missing"};
  const before = (button.innerText || button.getAttribute("aria-label") || "").replace(/\s+/g, " ").trim();
  const event = {
    preventDefault() {}, stopPropagation() {}, persist() {},
    nativeEvent: {isTrusted: true, button: 0},
    isTrusted: true, button: 0, type: "click",
    target: button, currentTarget: button
  };
  const keys = Object.keys(button);
  for (const key of keys) {
    if (!key.startsWith("__reactProps$")) continue;
    const props = button[key];
    if (props && typeof props.onClick === "function") {
      props.onClick(event);
      return {how: "react", before};
    }
  }
  for (const child of button.querySelectorAll("*")) {
    for (const key of Object.keys(child)) {
      if (!key.startsWith("__reactProps$")) continue;
      const props = child[key];
      if (props && typeof props.onClick === "function") {
        props.onClick(event);
        return {how: "react", before};
      }
    }
  }
  return {how: "no-handler", before};
}
"""


def click_reply_send(page) -> None:
    enabled = page.locator(
        '[data-testid="tweetButtonInline"]:not([aria-disabled="true"]), '
        '[data-testid="tweetButton"]:not([aria-disabled="true"])'
    )
    if enabled.count() == 0:
        raise PlaywrightTimeoutError("reply button stayed disabled")
    if IN_APP:
        sent = page.evaluate(PRESS_SEND_JS)
        trace_click(f"reply نشر {sent}")
        if not isinstance(sent, dict) or sent.get("how") not in ("react", "fiber"):
            raise PlaywrightTimeoutError("reply button stayed disabled")
        return
    real_click(enabled.last)


def publish_reply(page, text: str, path: str) -> tuple[bool, str]:
    blocked = reply_block_reason(page)
    if blocked:
        return False, blocked
    open_reply_composer(page, path)
    page.wait_for_timeout(500)
    blocked = reply_block_reason(page)
    if blocked:
        return False, blocked
    insert_reply_text(page, text)
    page.wait_for_timeout(500)
    click_reply_send(page)
    snippet = text[:24]
    try:
        page.wait_for_function(
            """(snippet) => [...document.querySelectorAll('article[data-testid="tweet"]')]
              .some((article) => (article.innerText || "").includes(snippet))""",
            arg=snippet,
            timeout=12000,
        )
        return True, ""
    except PlaywrightTimeoutError:
        blocked = reply_block_reason(page)
        return False, blocked or "أُرسل الطلب لكن الرد لم يظهر في الصفحة"


def comment_failure_text(exc: Exception) -> str:
    message = str(exc)
    if isinstance(exc, PlaywrightTimeoutError):
        if "tweetTextarea" in message:
            return "لم يظهر مربع كتابة الرد"
        if "reply button" in message or "aria-disabled" in message or "disabled" in message:
            return "زر النشر بقي معطّلًا"
        if "article" in message:
            return "لم تُفتح التغريدة في الوقت المناسب"
        return "انتهت المهلة أثناء تجهيز الرد"
    line = message.splitlines()[0][:110] if message else type(exc).__name__
    return line or "خطأ غير متوقع"


RESOLVE_PARENT_JS = r"""
(replyPath) => {
  const statusPath = (href) => {
    const match = (href || "").match(/^(?:https?:\/\/(?:www\.)?(?:x|twitter)\.com)?(\/[A-Za-z0-9_]+\/status\/\d+)/);
    return match ? match[1] : "";
  };
  const articles = [...document.querySelectorAll('article[data-testid="tweet"]')];
  const paths = articles.map((article) => {
    const time = article.querySelector("time");
    const link = time && time.closest('a[href*="/status/"]');
    return statusPath(link ? link.getAttribute("href") : "");
  });
  const index = paths.findIndex((path) => path && (replyPath.endsWith(path) || path.endsWith(replyPath)));
  if (index > 0) return paths[index - 1];
  return "";
}
"""


def article_text(card) -> str:
    """The tweet's own text as its opened page shows it (a long post whole, where the collected text stops
    at 280 letters); "" when it has none (a picture alone)."""
    try:
        found = card.locator('[data-testid="tweetText"]')
        if not found.count():
            return ""
        text = found.first.inner_text(timeout=2000)
    except Exception:
        return ""
    return re.sub(r"\s+", " ", text or "").strip()


def resolve_comment_target(page, path: str, needs_parent: bool) -> tuple[str, object]:
    if needs_parent:
        try:
            parent = page.evaluate(RESOLVE_PARENT_JS, path) or ""
        except Exception:
            parent = ""
        parent_path = normalize_status_path(str(parent))
        if parent_path and parent_path != path:
            matches = article_locator(page, parent_path)
            if matches.count() > 0:
                return parent_path, matches.first
    matches = article_locator(page, path)
    if matches.count() > 0:
        return path, matches.first
    return path, page.locator('article[data-testid="tweet"]').first


def execute_comment_actions(page, items: list[dict], actions: list[str], api_key: str, model: str, on_progress=None, should_stop=None, on_snapshot=None, account: str = "", voice: str = DEFAULT_REPLY_VOICE) -> list[dict]:
    """The task's actions on its tweets, with a reply on each. Each reply is written from the tweet's content
    (FxTwitter), asked before the tweet is opened (CommentsAhead): the page's pictures are not needed, so
    this browser keeps not loading them."""
    ahead = None
    if "comment" in actions:
        ahead = CommentsAhead(
            lambda text, image, tweet_id: reply_for(api_key, model, image, text, voice, account, tweet_id),
            account, actions, should_stop,
        )
    try:
        return _execute_comment_actions(page, items, actions, api_key, model, on_progress, should_stop, on_snapshot,
                                        account, voice, ahead)
    finally:
        if ahead is not None:
            ahead.close()


def _execute_comment_actions(page, items: list[dict], task_actions: list[str], api_key: str, model: str, on_progress,
                             should_stop, on_snapshot, account: str, voice: str, ahead) -> list[dict]:
    results: list[dict] = []
    total = len(items)
    failures = FailedTweets()
    # Where each tweet's result starts in results: going back after a pause drops them from there on.
    starts: dict[int, int] = {}
    if on_progress:
        on_progress(0, total, "act")
    index = -1
    acted = False
    while index + 1 < total:
        index += 1
        item = items[index]
        actions = item_actions(item, task_actions)      # (all the task's, or only those that failed on it before)
        plain = [action for action in actions if action != "comment"]
        if should_stop and should_stop():
            break
        starts[index] = len(results)
        result = {"url": item.get("url", ""), "text": item.get("text", ""), "actions": {}, "comment": ""}
        path = normalize_status_path(str(item.get("url") or ""))
        if not path:
            result["actions"] = {key: "تعذر العثور على المنشور" for key in actions}
            results.append(result)
            if on_progress:
                on_progress(index + 1, total, "act")
            continue
        status_id = tweet_status_id(str(item.get("url") or ""))
        if already_done_recently(account, status_id, actions):
            # Everything asked was done on this tweet by this account in the last 8 hours: skip without opening it.
            result["actions"] = {key: "سبق التفاعل خلال ٨ ساعات — تم التخطي" for key in actions}
            results.append(result)
            if on_snapshot:
                on_snapshot(list(results))
            if on_progress:
                on_progress(index + 1, total, "act")
            continue
        if acted:
            pause_span(0.15, 0.4, should_stop)
            if should_stop and should_stop():
                break
        acted = True
        # This account already replied to this tweet in the last 8 hours: never reply to it again.
        replied_before = "comment" in actions and already_done_recently(account, status_id, ["comment"])
        if ahead is not None:
            # Its reply (if not asked already, while on the tweet before) and the next tweet's are asked now.
            following = items[index + 1] if index + 1 < total else None
            ahead.keep_only({status_id, tweet_status_id(str((following or {}).get("url") or ""))})
            ahead.ask(item)
            ahead.ask(following)
        left = list(plain)
        try:
            opened, reason = open_task_tweet(page, str(item.get("url") or ""), None)
        except Exception as exc:
            if browser_closed_error(exc):
                if on_snapshot and results:
                    on_snapshot(list(results))
                raise BrowserClosed() from exc
            raise
        if opened or reason == "gone":
            failures.opened()
        else:
            back = failures.failed(index)
            new_page = None
            if back is not None:
                seconds = failures.next_pause()
                if seconds is None:
                    # A third time: the task stops here, with what it did (these two would not open).
                    result["actions"] = {key: "تعذر فتح التغريدة" for key in actions}
                    results.append(result)
                    if on_snapshot:
                        on_snapshot(list(results))
                    raise TweetsKeptFailing(results, index + 1)
                new_page = pause_after_failures(should_stop, on_progress, total, None, seconds,
                                                "pause" if failures.pauses == 1 else "pause_again")
            if new_page is not None:
                # Back to the first of the two that would not open; what was recorded from it on goes.
                page = new_page
                del results[starts[back]:]
                if on_snapshot:
                    on_snapshot(list(results))
                if on_progress:
                    on_progress(back, total, "act")
                index = back - 1
                continue
        if not opened:
            note = "محذوفة — تم التخطي" if reason == "gone" else "تعذر فتح التغريدة"
            result["actions"] = {key: note for key in actions}
            results.append(result)
            if on_snapshot:
                on_snapshot(list(results))
            if on_progress:
                on_progress(index + 1, total, "act")
            continue
        if tweet_is_ignored("https://x.com" + opened):
            # The opened tweet's author is an ignored account: take no action and leave no trace.
            forget_collected("https://x.com" + opened)
            if on_progress:
                on_progress(index + 1, total, "act")
            continue
        path = opened
        result["url"] = "https://x.com" + path
        try:
            page.wait_for_timeout(400)
            target_path, card = resolve_comment_target(page, path, bool(item.get("needs_parent")))
            result["url"] = "https://x.com" + target_path
            if not IN_APP:
                try:
                    card.scroll_into_view_if_needed(timeout=4000)
                except Exception:
                    pass
            page.wait_for_timeout(700)
            if left:
                result["actions"].update(apply_actions_on_path(page, target_path, left))
            if replied_before or ("comment" in actions and already_done_recently(account, tweet_status_id(target_path), ["comment"])):
                result["actions"]["comment"] = "سبق الرد خلال ٨ ساعات — تم التخطي"
            elif "comment" in actions:
                reply_to = tweet_status_id(target_path)
                comment, content = ahead.take(reply_to) if ahead is not None else ("", None)
                if comment:
                    print(f"تعليق التغريدة {reply_to} كان جاهزًا قبل فتحها", flush=True)
                else:
                    comment = reply_from_page(page, card, item, content, api_key, model, voice, account, reply_to)
                if len(comment.split()) < 4:
                    result["actions"]["comment"] = "لم يُرجع النموذج تعليقًا صالحًا"
                else:
                    result["comment"] = comment
                    page.wait_for_timeout(800)
                    posted, detail = publish_reply(page, comment, target_path)
                    result["actions"]["comment"] = "تم التنفيذ" if posted else (detail or "أُرسل الطلب لكن تعذر تأكيد الحالة")
        except RuntimeError as exc:
            result["actions"]["comment"] = "تعذر توليد التعليق: " + str(exc)[:120]
        except Exception as exc:
            if browser_closed_error(exc):
                if on_snapshot and results:
                    on_snapshot(list(results))
                raise BrowserClosed() from exc
            print(f"X reply failed on {path}: {type(exc).__name__}: {str(exc).splitlines()[0][:180]}", flush=True)
            if "comment" in actions and "comment" not in result["actions"]:
                result["actions"]["comment"] = "تعذر نشر التعليق: " + comment_failure_text(exc)
            for action in left:
                result["actions"].setdefault(action, "تعذر التنفيذ")
        # Save what was done, for the tweet in the group and for the tweet actually replied to.
        for done_id in {status_id, tweet_status_id(result["url"])}:
            remember_done(account, done_id, result["actions"])
        count_successes(result["actions"], account)
        results.append(result)
        if on_snapshot:
            on_snapshot(list(results))
        if on_progress:
            on_progress(index + 1, total, "act")
        page.wait_for_timeout(1400)
    return results


# Do not download images, videos or audio in the automation browser.
BLOCK_MEDIA = True
BLOCKED_RESOURCE_TYPES = {"image", "media"}


def block_media(context) -> None:
    if not BLOCK_MEDIA:
        return
    state = {"allow": False}
    context._media_state = state

    def handle(route):
        request = route.request
        try:
            if not state["allow"] and (request.resource_type in BLOCKED_RESOURCE_TYPES or "video.twimg.com" in request.url):
                route.abort()
            else:
                route.continue_()
        except Exception:
            pass

    try:
        context.route("**/*", handle)
    except Exception:
        pass


def allow_media(page) -> None:
    """Let this browser load images and videos again (used for comments)."""
    state = getattr(page.context, "_media_state", None)
    if state is not None:
        state["allow"] = True


# Up to three accounts, each with its own task: the tasks run at the same time, one per account
# (a new task on an account that is already working waits in that account's line, see account_lines).
MAX_ACCOUNTS = 3
MAX_PARALLEL_JOBS = 3


PROFILES_DIR = DATA_DIR / "profiles"
# The size asked of a new browser. In the app the browser keeps the phone's own screen (its real
# width and height): a size asked of it is not applied.
NORMAL_VIEWPORT_HEIGHT = 1800
# Width of the script's browser page (the height stays as set above). Narrower means less
# to draw; 600 keeps X's normal layout (below 500 X switches to its phone layout).
VIEWPORT_WIDTH = 600
profile_locks: dict[str, threading.Lock] = {}
profile_locks_guard = threading.Lock()


def profile_key(auth_token: str) -> str:
    """Folder name for an account's browser profile. Derived from the token, never the token itself."""
    return hashlib.sha256((auth_token or "").encode("utf-8")).hexdigest()[:24]


def profile_lock(key: str) -> threading.Lock:
    with profile_locks_guard:
        lock = profile_locks.get(key)
        if lock is None:
            lock = threading.Lock()
            profile_locks[key] = lock
        return lock


# On Android, in Termux: the browser is Termux's own Chromium, and Playwright's driver runs on Termux's
# Node (the Node that comes with Playwright is built for desktop Linux and does not run on Android).
# The driver also works out where browsers would be downloaded as soon as it starts, and it does not
# know Android ("Unsupported platform: android"): it is given that folder, so it never asks.
TERMUX_PREFIX = os.getenv("PREFIX", "") if "/com.termux/" in os.getenv("PREFIX", "") else ""
if TERMUX_PREFIX:
    if not os.getenv("PLAYWRIGHT_NODEJS_PATH") and Path(TERMUX_PREFIX, "bin", "node").is_file():
        os.environ["PLAYWRIGHT_NODEJS_PATH"] = str(Path(TERMUX_PREFIX, "bin", "node"))
    os.environ.setdefault("PLAYWRIGHT_BROWSERS_PATH", str(Path.home() / ".cache" / "ms-playwright"))


# A copy on its own (see on_its_own) opens the full Chromium in its new headless mode (the "chromium" channel),
# not Playwright's lighter headless browser; the owner's main copy and users' copies keep the light one. It needs
# Playwright 1.49 or newer and the browser installed with what it needs from the system (python -m playwright
# install --with-deps chromium). Where it cannot be opened, the light browser is used as before, with one message on
# how to install it, and it is not asked again.
OWN_COPY_CHANNEL = "chromium"
channel_unavailable: list[str] = []


def browser_launch_options() -> dict:
    """The browser's switches, on Termux where its Chromium is, and on a copy on its own the full Chromium
    (OWN_COPY_CHANNEL). GG_CHROMIUM_ARGS adds switches (e.g. "--single-process" if Android keeps stopping the
    browser's helper processes)."""
    options: dict = {}
    args = ["--disable-blink-features=AutomationControlled", "--disable-dev-shm-usage", "--no-sandbox"]
    if TERMUX_PREFIX:
        for candidate in (Path(TERMUX_PREFIX, "lib", "chromium", "chrome"), Path(TERMUX_PREFIX, "bin", "chromium-browser")):
            if candidate.is_file():
                options["executable_path"] = str(candidate)
                break
        args.append("--disable-gpu")
    elif OWN_COPY_CHANNEL and on_its_own() and not channel_unavailable:
        options["channel"] = OWN_COPY_CHANNEL
    options["args"] = args + os.getenv("GG_CHROMIUM_ARGS", "").split()
    return options


def channel_not_installed(exc: Exception) -> bool:
    """Whether the full Chromium could not be opened only because it is not ready here: not installed, missing
    something it needs from the system, or a Playwright too old for the channel."""
    text = str(exc).lower()
    return any(part in text for part in ("executable doesn't exist", "unsupported chromium channel", "is not found at",
                                         "distribution 'chromium'", "missing dependencies",
                                         "error while loading shared libraries"))


def open_x_profile(playwright, auth_token: str, profile_dir: Path, user_agent: str = "", viewport: dict | None = None):
    """Open the account's permanent browser profile (created on first use)."""
    profile_dir.mkdir(parents=True, exist_ok=True)
    options = browser_launch_options()
    settings = dict(
        headless=True,
        viewport=viewport or screen_size(NORMAL_VIEWPORT_HEIGHT),
        user_agent=user_agent or (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
            "(KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"
        ),
        locale="en-US",
    )
    try:
        context = playwright.chromium.launch_persistent_context(str(profile_dir), **options, **settings)
    except Exception as exc:
        if "channel" not in options or not channel_not_installed(exc):
            raise
        first = not channel_unavailable
        channel_unavailable.append((str(exc).strip().splitlines() or [type(exc).__name__])[0][:200])
        if first:
            print("⚠️ متصفح Chromium الكامل لا يعمل هنا (غير مثبّت، أو تنقصه مكتبات من النظام، أو Playwright أقدم من 1.49)، "
                  "فيُفتح المتصفح الخفيف كما كان. للتثبيت: python -m pip install -U playwright "
                  "ثم python -m playwright install --with-deps chromium", flush=True)
            print(f"   ({channel_unavailable[0]})", flush=True)
        options.pop("channel", None)
        context = playwright.chromium.launch_persistent_context(str(profile_dir), **options, **settings)
    context.add_init_script(
        "Object.defineProperty(navigator, 'webdriver', {get: () => undefined})"
    )
    block_media(context)
    if auth_token:
        context.add_cookies([{
            "name": "auth_token",
            "value": auth_token,
            "domain": ".x.com",
            "path": "/",
            "httpOnly": True,
            "secure": True,
            "sameSite": "Lax",
        }])
    page = context.pages[0] if context.pages else context.new_page()
    for extra in context.pages[1:]:
        try:
            extra.close()
        except Exception:
            pass
    page.set_default_timeout(20_000)
    page.set_default_navigation_timeout(60_000)
    return context, page


_login_jobs: queue.Queue = queue.Queue()
_login_state: dict = {}
_login_worker_started = False
_login_worker_guard = threading.Lock()
_MANUAL_LOGIN_AGENT = (
    "Mozilla/5.0 (Linux; Android 14; SM-G998U) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/131.0.0.0 Mobile Safari/537.36"
)


def _login_worker() -> None:
    while True:
        fn, box = _login_jobs.get()
        try:
            box["result"] = fn()
        except Exception as exc:
            box["error"] = exc
        finally:
            box["done"].set()


def _ensure_login_worker() -> None:
    global _login_worker_started
    with _login_worker_guard:
        if _login_worker_started:
            return
        threading.Thread(target=_login_worker, name="manual-login", daemon=True).start()
        _login_worker_started = True


def _on_login_thread(fn, timeout: float = 90):
    _ensure_login_worker()
    box: dict = {"done": threading.Event()}
    _login_jobs.put((fn, box))
    if not box["done"].wait(timeout):
        raise TimeoutError("manual login")
    if box.get("error") is not None:
        raise box["error"]
    return box.get("result")


def _show_manual_browser() -> None:
    if not IN_APP:
        return
    show_account_browser(str(_login_state.get("folder") or MANUAL_BROWSER))
    _prepare_manual_browser()


def _prepare_manual_browser() -> None:
    """The app shows «المتصفح», and lets the user type in it."""
    from java import jclass
    jclass("app.tg.groups.BrowserHost").prepareManualLogin()


# «المتصفح» in the app shows one browser: the one of the account the panel shows (the other accounts' browsers
# keep working behind it), or the sign-in browser while an account signs in.
_shown_browser: dict = {"folder": None}


def show_account_browser(folder: str) -> None:
    """«المتصفح» shows this browser (a profile folder; "" when the panel shows no account)."""
    if not IN_APP or _shown_browser["folder"] == folder:
        return
    _shown_browser["folder"] = folder
    try:
        from java import jclass
        jclass("app.tg.groups.BrowserHost").showAccount(folder or "")
    except Exception:
        pass


def show_active_browser() -> None:
    """«المتصفح» follows the panel: the browser of the account it shows; while a new account is added (no account
    shown), the sign-in browser; else none."""
    token = active_token
    if valid_auth_token(token):
        show_account_browser(manual_profile_folder(token))
    elif _login_page_open():
        show_account_browser(str(_login_state.get("folder") or MANUAL_BROWSER))
    else:
        show_account_browser("")


def _login_page_open() -> bool:
    page = _login_state.get("page")
    if page is None:
        return False
    try:
        return not page.is_closed()
    except Exception:
        return False


def _page_open(page) -> bool:
    if page is None:
        return False
    try:
        return not page.is_closed()
    except Exception:
        return False


# The manual browser stays open between tasks, so the unlocked chat and its keys are not thrown away.
# Each account signed in by hand keeps its own browser open between its tasks (one per profile folder, never
# shared): its next task goes on in the same page, with its chat already unlocked.
_task_browsers: dict[str, dict] = {}
_task_browsers_lock = threading.Lock()


def _kept_browser(folder: str) -> dict | None:
    with _task_browsers_lock:
        kept = _task_browsers.get(folder)
    return kept if kept and _page_open(kept.get("page")) else None


def _close_browser_parts(context, playwright) -> None:
    if context is not None:
        try:
            context.close()
        except Exception:
            pass
    if playwright is not None:
        try:
            playwright.stop()
        except Exception:
            pass


def _drop_task_browser(folder: str | None = None) -> None:
    """Close the browser kept open for this profile folder (every kept one when None). Its profile stays."""
    with _task_browsers_lock:
        if folder is None:
            dropped = list(_task_browsers.values())
            _task_browsers.clear()
        else:
            one = _task_browsers.pop(folder, None)
            dropped = [one] if one else []
    for kept in dropped:
        _close_browser_parts(kept.get("context"), kept.get("playwright"))


# In the app, an account's browser kept open with nothing to do is closed after this long (its session stays,
# and its next task opens it again in a few seconds): an idle page of X still uses the processor and battery.
KEPT_BROWSER_IDLE_SECONDS = 600


def close_idle_browsers_once(now: float | None = None) -> list[str]:
    """Close the kept browsers idle for KEPT_BROWSER_IDLE_SECONDS or more. Returns their profile folders."""
    now = time.monotonic() if now is None else now
    with _task_browsers_lock:
        idle = [folder for folder, kept in _task_browsers.items()
                if kept.get("idle_since") is not None and now - kept["idle_since"] >= KEPT_BROWSER_IDLE_SECONDS]
    closed = []
    for folder in idle:
        lock = profile_lock(folder)
        if not lock.acquire(blocking=False):          # (a task of the account has it now)
            continue
        try:
            with _task_browsers_lock:
                kept = _task_browsers.get(folder)
                due = bool(kept) and kept.get("idle_since") is not None and now - kept["idle_since"] >= KEPT_BROWSER_IDLE_SECONDS
                account = str((kept or {}).get("account") or "")
            if due:
                _drop_task_browser(folder)
                closed.append(folder)
                with as_account(account):
                    trace_click(f"أُغلق متصفح هذا الحساب بعد {KEPT_BROWSER_IDLE_SECONDS // 60} دقائق بلا مهمة (جلسته محفوظة).")
        finally:
            lock.release()
    return closed


def close_idle_browsers_in_background() -> None:
    while True:
        time.sleep(30)
        try:
            close_idle_browsers_once()
        except Exception:
            pass


def _drop_idle_task_browsers() -> None:
    """Close the kept browsers no task is using now (so a new sign-in has room for its own browser)."""
    with _task_browsers_lock:
        folders = list(_task_browsers)
    for folder in folders:
        lock = profile_lock(folder)
        if lock.acquire(blocking=False):
            try:
                _drop_task_browser(folder)
            finally:
                lock.release()


def _open_login_browser() -> str:
    """«تسجيل الدخول». With no account shown (a new account is being added): a new browser with a profile of its
    own (data/profiles/login-…), kept open so «تحقق» can read its session; then it is that account's own
    browser, for its tasks and everything else. With an account shown: that account's own browser, not a new
    sign-in (shown as it is when it is open or in a task; opened on X otherwise, where it is signed in, or
    signs in again if its session ended). Returns what the panel says."""
    token = active_token
    shown = valid_auth_token(token)
    if shown:
        folder = manual_profile_folder(token)
        if _kept_browser(folder) is not None or profile_lock(folder).locked():
            show_account_browser(folder)
            _prepare_manual_browser()
            return "متصفح هذا الحساب مفتوح في تبويب «المتصفح»."
        if _login_page_open() and str(_login_state.get("folder") or MANUAL_BROWSER) != folder:
            _close_login_browser()           # (a sign-in begun for a new account is left for this one)
    else:
        folder = "login-" + secrets.token_hex(6)
    if not _login_page_open():
        with _task_browsers_lock:
            crowded = len(_task_browsers) >= MAX_ACCOUNTS
        if crowded:
            _drop_idle_task_browsers()
        playwright = sync_playwright().start()
        context, page = open_x_profile(
            playwright, token if shown else "", PROFILES_DIR / folder,
            user_agent=_MANUAL_LOGIN_AGENT, viewport={"width": 412, "height": 820},
        )
        allow_media(page)
        _login_state.update(playwright=playwright, context=context, page=page, folder=folder)
    page = _login_state["page"]
    _show_manual_browser()
    page.goto("https://x.com/i/flow/login", wait_until="domcontentloaded", timeout=60_000)
    _show_manual_browser()
    if shown:
        return "فُتح متصفح هذا الحساب في تبويب «المتصفح». إن ظهرت صفحة تسجيل الدخول فجلسته انتهت: سجّل الدخول ثم اضغط تحقق."
    return "سجّل الدخول في تبويب المتصفح، ثم ارجع إلى اللوحة واضغط تحقق."


def start_manual_login() -> str:
    return str(_on_login_thread(_open_login_browser) or "")


def _read_login_token() -> tuple[str, str]:
    """The session the sign-in browser holds, and that browser's profile folder."""
    if not _login_page_open():
        return "", ""
    folder = str(_login_state.get("folder") or MANUAL_BROWSER)
    try:
        cookies = _login_state["page"].context.cookies(["https://x.com", "https://twitter.com"])
    except Exception:
        return "", folder
    for cookie in cookies:
        if cookie.get("name") == "auth_token" and cookie.get("value"):
            return str(cookie["value"]), folder
    return "", folder


def manual_login_token() -> str:
    if not _login_worker_started:
        return ""
    try:
        token, folder = _on_login_thread(_read_login_token, timeout=20) or ("", "")
        token = str(token or "")
    except Exception:
        return ""
    if valid_auth_token(token):
        remember_manual_profile(token, folder or MANUAL_BROWSER)
    return token


def _close_login_browser() -> None:
    """Close the login window without deleting its profile, so a task can open that same browser."""
    context = _login_state.pop("context", None)
    playwright = _login_state.pop("playwright", None)
    _login_state.pop("page", None)
    _login_state.pop("folder", None)
    if context is not None:
        try:
            context.close()
        except Exception:
            pass
    if playwright is not None:
        try:
            playwright.stop()
        except Exception:
            pass


def release_manual_browser() -> None:
    if not _login_worker_started:
        return
    try:
        _on_login_thread(_close_login_browser, timeout=20)
    except Exception:
        pass
    show_active_browser()


MANUAL_BROWSER = "manual-login"
MANUAL_PROFILES_PATH = DATA_DIR / "manual_profiles.json"
_manual_profiles_lock = threading.Lock()


def _load_manual_profiles() -> dict:
    try:
        data = json.loads(MANUAL_PROFILES_PATH.read_text(encoding="utf-8"))
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def remember_manual_profile(auth_token: str, folder: str = MANUAL_BROWSER) -> None:
    """This account signed in by hand in this browser (profile folder): from now on it is the account's own
    browser for everything. A browser belongs to one account only; the account's browser from before (an
    earlier sign-in, or the one its token alone opened) is no one's any more, so it goes."""
    key = profile_key(auth_token)
    with _manual_profiles_lock:
        saved = _load_manual_profiles()
        before = str(saved.get(key) or key)
        saved = {name: owned for name, owned in saved.items() if owned != folder}
        saved[key] = folder
        MANUAL_PROFILES_PATH.parent.mkdir(parents=True, exist_ok=True)
        MANUAL_PROFILES_PATH.write_text(json.dumps(saved), encoding="utf-8")
        still_used = set(saved.values())
    if before != folder and before not in still_used:
        discard_profile_folder(before)


def discard_profile_folder(folder: str) -> None:
    """Remove a browser profile no account uses any more (its folder, and in the app its WebView profile)."""
    if not folder or "/" in folder or folder in (".", ".."):
        return
    lock = profile_lock(folder)
    if not lock.acquire(timeout=5):
        return
    try:
        _drop_task_browser(folder)
        shutil.rmtree(PROFILES_DIR / folder, ignore_errors=True)
        if IN_APP:
            try:
                from java import jclass
                jclass("app.tg.groups.BrowserHost").deleteProfile(folder)
            except Exception:
                pass
    finally:
        lock.release()


def manual_profile_folder(auth_token: str) -> str:
    key = profile_key(auth_token)
    with _manual_profiles_lock:
        saved = _load_manual_profiles()
    return str(saved.get(key) or key)


def forget_manual_profile(auth_token: str) -> None:
    key = profile_key(auth_token)
    with _manual_profiles_lock:
        saved = _load_manual_profiles()
        if key not in saved:
            return
        del saved[key]
        MANUAL_PROFILES_PATH.write_text(json.dumps(saved), encoding="utf-8")


# The running task's "close and reopen the browser" function (one per worker thread).
browser_restart = threading.local()

# Live view of a task's browser (its card no longer offers it; kept for the view endpoint). Pictures are taken in the task's own
# thread during its waits, and only while someone is watching.
LIVE_VIEW_EVERY = 0.25
live_task = threading.local()
live_views: dict[str, dict] = {}
live_views_lock = threading.Lock()
_page_wait_for_timeout = Page.wait_for_timeout


def capture_live_view(page, job_id: str) -> bool:
    """Take the task's next picture when one is due. Returns whether someone is watching."""
    now = time.monotonic()
    with live_views_lock:
        view = live_views.get(job_id)
        if not view or view["wanted_until"] < now:
            return False
        if now - view["taken_at"] < LIVE_VIEW_EVERY:
            return True
        view["taken_at"] = now
    try:
        size = page.viewport_size or {"width": VIEWPORT_WIDTH, "height": NORMAL_VIEWPORT_HEIGHT}
        image = page.screenshot(type="jpeg", quality=40, timeout=3000,
                                clip={"x": 0, "y": 0, "width": size["width"], "height": min(size["height"], 1000)})
    except Exception:
        return True
    with live_views_lock:
        # An unchanged page gives the same picture: keep the old one so nothing is sent again.
        if image != view["image"]:
            view["image"] = image
            view["seq"] += 1
    return True


def wait_and_watch(page, timeout: float) -> None:
    """page.wait_for_timeout for every page: in a task's thread it also feeds that task's live view."""
    job_id = getattr(live_task, "job_id", "")
    if not job_id:
        return _page_wait_for_timeout(page, timeout)
    end = time.monotonic() + max(0.0, timeout) / 1000
    while True:
        watched = capture_live_view(page, job_id)
        left = end - time.monotonic()
        if left <= 0:
            return
        # Watched: wake up for every picture. Otherwise once a second, to notice a new viewer.
        _page_wait_for_timeout(page, min(left, LIVE_VIEW_EVERY if watched else 1.0) * 1000)


Page.wait_for_timeout = wait_and_watch


def restart_browser(while_closed=None):
    fn = getattr(browser_restart, "fn", None)
    return fn(while_closed) if fn else None




def acquire_profile_slot(key: str) -> str:
    """Take the account's browser profile (data/profiles/<key>), waiting while a task is using it."""
    profile_lock(key).acquire()
    return key


def app_task_running(on: bool) -> None:
    """In the app: tell it a task is working (or has ended). While one works, the app keeps working in the
    background even when the task's browser is closed for a moment (the pause after tweets would not open),
    so the browser opened after the pause goes on without waiting for the app to come back to the screen."""
    if not IN_APP:
        return
    try:
        from java import jclass
        jclass("app.tg.groups.BrowserHost").taskRunning(bool(on))
    except Exception:
        pass


def run_on_fresh_browser(auth_token: str, work):
    """Do one piece of work in the account's own browser, as that account's work (its log, its groups…).
    While it works the app keeps working in the background; a browser left open with nothing to do does not."""
    with as_account(profile_key(auth_token)):
        app_task_running(True)
        try:
            return _run_on_account_browser(auth_token, work)
        finally:
            app_task_running(False)


def _run_on_account_browser(auth_token: str, work):
    """Open the account's own browser profile for one piece of work.

    An account signed in by hand has its own browser, the one it signed in with: it stays open after the
    work, and its next task goes on in that same page. An account given by its token alone has a browser of
    its own too (data/profiles/<its key>), closed when its work ends. No two accounts share a browser.
    """
    folder = manual_profile_folder(auth_token)
    signed_by_hand = folder == MANUAL_BROWSER or folder.startswith("login-")
    if _login_state.get("page") is not None and str(_login_state.get("folder") or MANUAL_BROWSER) == folder:
        release_manual_browser()            # (its sign-in window closes: the same browser opens for the work)
    slot_name = acquire_profile_slot(folder)
    same_browser = signed_by_hand
    try:
        state = {"context": None, "playwright": None}

        def keep(page) -> None:
            with _task_browsers_lock:
                _task_browsers[slot_name] = {"playwright": state["playwright"], "context": state["context"], "page": page,
                                             "account": profile_key(auth_token), "idle_since": None}

        def open_saved(target):
            if same_browser:
                trace_click("التنفيذ على متصفح هذا الحساب الذي سُجّل الدخول إليه")
                return open_x_profile(
                    target, auth_token, PROFILES_DIR / slot_name,
                    user_agent=_MANUAL_LOGIN_AGENT, viewport={"width": 412, "height": 820},
                )
            return open_x_profile(target, auth_token, PROFILES_DIR / slot_name)

        def restart(while_closed=None):
            """Close the profile's browser, reopen it on Google, then go to X. Returns the new page.
            while_closed runs with the browser closed; when it returns False the browser stays
            closed and None is returned."""
            try:
                if state["context"] is not None:
                    state["context"].close()
            except Exception:
                pass
            state["context"] = None
            with _task_browsers_lock:
                _task_browsers.pop(slot_name, None)
            if while_closed is not None and while_closed() is False:
                return None
            if state["playwright"] is None:
                state["playwright"] = sync_playwright().start()
            state["context"], new_page = open_saved(state["playwright"])
            try:
                new_page.goto("https://www.google.com/", wait_until="domcontentloaded", timeout=60_000)
                new_page.wait_for_timeout(2000)
            except Exception:
                pass
            try:
                goto_x(new_page, "https://x.com/home")
                session_is_logged_in(new_page)
            except Exception:
                pass
            if same_browser:
                keep(new_page)
            return new_page

        browser_restart.fn = restart
        try:
            kept = _kept_browser(slot_name) if same_browser else None
            if kept:
                with _task_browsers_lock:
                    kept["idle_since"] = None             # (working again)
                trace_click("المهمة على صفحة متصفح هذا الحساب المفتوحة")
                state["context"] = kept.get("context")
                state["playwright"] = kept.get("playwright")
                return work(kept["page"])
            state["playwright"] = sync_playwright().start()
            state["context"], page = open_saved(state["playwright"])
            if same_browser:
                keep(page)
            return work(page)
        finally:
            browser_restart.fn = None
            still_open = _kept_browser(slot_name) if same_browser else None
            if still_open:
                with _task_browsers_lock:
                    still_open["idle_since"] = time.monotonic()
                trace_click(f"بقيت صفحة هذا الحساب مفتوحة لمهمته التالية (تُغلق بعد {KEPT_BROWSER_IDLE_SECONDS // 60} دقائق بلا مهمة)")
            elif same_browser:
                _drop_task_browser(slot_name)
            else:
                _close_browser_parts(state["context"], state["playwright"])
    finally:
        profile_lock(slot_name).release()


def screen_size(height: int) -> dict:
    """The size asked of a new browser (in the app the browser keeps the phone's own screen)."""
    return {"width": VIEWPORT_WIDTH, "height": int(height)}


def delete_profile(auth_token: str) -> None:
    """The account is removed: its browsers (profiles) go with it."""
    key = profile_key(auth_token)
    folder = manual_profile_folder(auth_token)
    forget_manual_profile(auth_token)
    for name in {key, folder}:
        discard_profile_folder(name)
        for extra in PROFILES_DIR.glob(f"{name}-*"):
            shutil.rmtree(extra, ignore_errors=True)



def run_on_browser(auth_token: str, work):
    """Every action gets its own browser, closed as soon as the action ends."""
    return run_on_fresh_browser(auth_token, work)


def goto_x(page, url: str) -> None:
    """page.goto for X pages. X sometimes answers with a file instead of the page (Playwright:
    "Download is starting"): ask again, and after two such answers ask past the browser's cache
    and X's service worker for that one load (nothing is deleted)."""
    for attempt in range(4):
        cdp = None
        try:
            if attempt >= 2:
                cdp = page.context.new_cdp_session(page)
                cdp.send("Network.enable")
                cdp.send("Network.setBypassServiceWorker", {"bypass": True})
                cdp.send("Network.setCacheDisabled", {"cacheDisabled": True})
            page.goto(url, wait_until="domcontentloaded", timeout=60_000)
            return
        except Exception as exc:
            if "Download is starting" not in str(exc):
                raise
            if attempt == 3:
                raise RuntimeError("أرسل X ملفًا بدل الصفحة أكثر من مرة. أعد المحاولة بعد قليل.") from exc
        finally:
            if cdp is not None:
                try:
                    cdp.send("Network.setBypassServiceWorker", {"bypass": False})
                    cdp.send("Network.setCacheDisabled", {"cacheDisabled": False})
                    cdp.detach()
                except Exception:
                    pass
        page.wait_for_timeout(1500)


# The session, checked on X's settings list (a light page: no timeline). X sends a signed-out session to its
# sign-in page at once; a signed-in one gets the list, with its @name within a few seconds. A few seconds,
# against 5 to 15 for x.com/home and the wait for its account button. (X's internal API is not asked: it
# refuses requests that do not come from its own web app.)
SESSION_PROBE_SECONDS = 6
SIGN_IN_URL = re.compile(r"/i/flow/(?:login|signup)|/i/jf/onboarding|/login(?:[/?#]|$)")
SIGNED_OUT_JS = """() => !!document.querySelector('a[href*="/i/flow/login"], a[href*="/i/flow/signup"], [data-testid="loginButton"], [data-testid="signupButton"]')"""


def probe_session(page) -> tuple[str, str]:
    """("in", @name) signed in · ("out", "") X sent the session to sign in · ("unknown", "") neither showed in
    SESSION_PROBE_SECONDS (the session is then checked the usual way)."""
    try:
        goto_x(page, SETTINGS_URL)
    except Exception:
        return "unknown", ""
    deadline = time.monotonic() + SESSION_PROBE_SECONDS
    while True:
        url = page.url or ""
        if SIGN_IN_URL.search(url):
            trace_click("الجلسة: X أحالها إلى تسجيل الدخول")
            return "out", ""
        try:
            if page.evaluate(SIGNED_OUT_JS):
                trace_click("الجلسة: صفحة X تعرض تسجيل الدخول")
                return "out", ""
        except Exception:
            pass
        try:
            name = str(page.evaluate(SETTINGS_NAME_JS) or "").strip().lstrip("@")
        except Exception:
            name = ""
        if re.fullmatch(r"[A-Za-z0-9_]{1,15}", name):
            trace_click(f"الجلسة من قائمة الإعدادات: @{name}")
            return "in", name
        if time.monotonic() >= deadline:
            trace_click("الجلسة: لم تتبيّن من قائمة الإعدادات في الوقت؛ تُفحص بالطريقة المعتادة")
            return "unknown", ""
        page.wait_for_timeout(300)


def ensure_logged_in(page) -> bool:
    """Whether the browser's session is signed in: from the page it is on when it shows the account, else asked
    of X directly (probe_session), and only when that gives no answer by opening x.com/home."""
    probe = page.locator(
        'button[aria-label="Account menu"], '
        '[data-testid="SideNav_AccountSwitcher_Button"], '
        'a[data-testid="AppTabBar_Profile_Link"], '
        # X's phone layout (narrow screens) has no side menu: its avatar button and the Home tab.
        '[data-testid="DashButton_ProfileIcon_Link"], '
        'a[data-testid="AppTabBar_Home_Link"]'
    )
    try:
        if "x.com" in (page.url or "") and probe.first.is_visible(timeout=1500):
            return True
    except Exception:
        pass
    status, name = probe_session(page)
    if status == "in":
        page._session_name = name          # (read_session_username gives it back without a page to read it from)
        return True
    if status == "out":
        return False
    goto_x(page, "https://x.com/home")
    return session_is_logged_in(page)


def session_is_logged_in(page) -> bool:
    try:
        page.locator(
            'button[aria-label="Account menu"], '
            '[data-testid="SideNav_AccountSwitcher_Button"], '
            'a[data-testid="AppTabBar_Profile_Link"], '
            # X's phone layout (narrow screens) has no side menu: its avatar button and the Home tab.
            '[data-testid="DashButton_ProfileIcon_Link"], '
            'a[data-testid="AppTabBar_Home_Link"]'
        ).first.wait_for(state="visible", timeout=20_000)
        return True
    except PlaywrightTimeoutError:
        return False


def read_session_username(page) -> str:
    """The logged-in handle. The phone has no side menu, so the desktop profile link is
    often missing; the avatar button and the session itself still carry the name."""
    try:
        handle = page.evaluate(
            """async () => {
              const reserved = new Set(["home","explore","search","settings","messages","notifications","i","compose","unknown","undefined","null","none","user","profile","guest"]);
              const clean = (value) => {
                const name = String(value || "").trim().replace(/^@/, "");
                if (!/^[A-Za-z0-9_]{1,15}$/.test(name) || reserved.has(name.toLowerCase())) return "";
                return name;
              };
              const fromHref = (node) => {
                if (!node) return "";
                const match = (node.getAttribute("href") || "").match(/^\\/([A-Za-z0-9_]{1,15})\\/?$/);
                return match ? clean(match[1]) : "";
              };
              const fromAvatar = (node) => {
                if (!node) return "";
                const tagged = node.getAttribute && (node.getAttribute("data-testid") || "").startsWith("UserAvatar-Container-")
                  ? node
                  : node.querySelector('[data-testid^="UserAvatar-Container-"]');
                if (!tagged) return "";
                return clean((tagged.getAttribute("data-testid") || "").slice("UserAvatar-Container-".length));
              };
              const profile = document.querySelector('a[data-testid="AppTabBar_Profile_Link"]');
              const dash = document.querySelector('[data-testid="DashButton_ProfileIcon_Link"]');
              const visible = fromHref(profile) || fromAvatar(profile) || fromHref(dash) || fromAvatar(dash);
              if (visible) return {name: visible, source: "page"};
              const nodes = document.querySelectorAll('[data-testid="SideNav_AccountSwitcher_Button"], [data-testid="UserName"], [data-testid="DashButton_ProfileIcon_Link"]');
              for (const node of nodes) {
                const match = ((node.innerText || node.textContent || "")).match(/@([A-Za-z0-9_]{1,15})/);
                if (match && clean(match[1])) return {name: match[1], source: "text"};
              }
              const dig = (value, depth, seen) => {
                if (!value || depth > 8 || typeof value !== "object") return "";
                if (seen.has(value)) return "";
                seen.add(value);
                const direct = clean(value.screen_name || value.screenName || "");
                if (direct) return direct;
                for (const key of ["legacy", "core", "user", "viewer", "result", "data", "next", "memoizedState"]) {
                  if (value[key]) {
                    const found = dig(value[key], depth + 1, seen);
                    if (found) return found;
                  }
                }
                return "";
              };
              const root = dash || profile;
              if (root) {
                const fiberKey = Object.keys(root).find((key) => key.startsWith("__reactFiber$"));
                let fiber = fiberKey ? root[fiberKey] : null;
                for (let step = 0; fiber && step < 40; step++, fiber = fiber.return) {
                  const found = dig(fiber.memoizedProps, 0, new Set()) || dig(fiber.memoizedState, 0, new Set());
                  if (found) return {name: found, source: "account"};
                }
              }
              return {name: "", source: "empty"};
            }"""
        ) or {}
    except Exception as exc:
        handle = ""
        trace_click("قراءة الاسم فشلت: " + type(exc).__name__)
    else:
        if isinstance(handle, dict):
            trace_click(f"قراءة الاسم {handle}")
            handle = str(handle.get("name") or "")
        else:
            handle = str(handle or "")
    handle = handle.strip().lstrip("@")
    if handle.lower() in {"unknown", "undefined", "null", "none", "user"}:
        handle = ""
    if re.fullmatch(r"[A-Za-z0-9_]{1,15}", handle):
        return handle
    try:
        if "settings" not in (page.url or ""):
            goto_x(page, SETTINGS_URL)
        found = read_settings_username(page, 6)
        trace_click(f"قراءة الاسم من الإعدادات: {found or 'فارغ'}")
        if found:
            return found
    except Exception as exc:
        trace_click("قراءة الاسم من الإعدادات فشلت: " + type(exc).__name__)
    return str(getattr(page, "_session_name", "") or "")


SETTINGS_URL = "https://x.com/settings/account"


SETTINGS_NAME_JS = """() => {
      const reserved = new Set(["home","explore","search","settings","messages","notifications","i","compose","unknown","undefined","null","none","user","profile","guest","account","premium"]);
      const clean = (value) => {
        const name = String(value || "").trim().replace(/^@/, "");
        if (!/^[A-Za-z0-9_]{1,15}$/.test(name) || reserved.has(name.toLowerCase())) return "";
        return name;
      };
      const text = (document.body && document.body.innerText) || "";
      const match = text.match(/@([A-Za-z0-9_]{1,15})/);
      return match ? clean(match[1]) : "";
    }"""


def read_settings_username(page, wait_s: float = 6.0) -> str:
    """The @handle shown under «الإعدادات». Empty when the page is not the settings list."""
    script = SETTINGS_NAME_JS
    deadline = time.monotonic() + wait_s
    while time.monotonic() < deadline:
        url = page.url or ""
        if "/login" in url or "/i/flow" in url:
            return ""
        try:
            found = str(page.evaluate(script) or "").strip().lstrip("@")
        except Exception:
            found = ""
        if re.fullmatch(r"[A-Za-z0-9_]{1,15}", found):
            return found
        page.wait_for_timeout(300)
    return ""


def verify_x_login(auth_token: str) -> tuple[bool, str]:
    """«تحقق»: the session from X's settings list (probe_session, given more time when it is slow). The handle
    under «الإعدادات» is the session."""
    def work(page):
        status, name = probe_session(page)
        if status == "in":
            return True, name
        if status == "out":
            return False, ""
        username = read_settings_username(page)      # (the page is the settings list already: given more time)
        url = page.url or ""
        logged_in = bool(username) and "/login" not in url and "/i/flow" not in url
        trace_click(f"التحقق من الإعدادات: {username or 'غير معروف'}")
        return logged_in, username
    return run_on_browser(auth_token, work)


def valid_chat_pin(value: str) -> bool:
    return bool(re.fullmatch(r"\d{4,8}", (value or "").strip()))


def chat_body_text(page) -> str:
    try:
        return page.evaluate("() => (document.body && document.body.innerText || '').slice(0, 4000)") or ""
    except Exception:
        return ""


def pin_error_message(page) -> str | None:
    text = chat_body_text(page)
    if re.search(r"too many attempts|attempt limit|permanently", text, re.I):
        return "توقفت المحاولات عند X. لا تُعد إدخال الرمز."
    if re.search(r"incorrect pin|wrong pin|invalid pin|رمز.{0,16}غير صحيح", text, re.I):
        return "رمز الدردشة غير صحيح."
    return None


def pin_fields(page):
    locator = page.locator("input[type='password']:visible, input[type='tel']:visible, input[inputmode='numeric']:visible")
    boxes = []
    for index in range(min(locator.count(), 8)):
        box = locator.nth(index)
        try:
            if box.is_visible():
                boxes.append(box)
        except Exception:
            continue
    return boxes


def type_pin_once(page, pin: str) -> None:
    boxes = pin_fields(page)
    if not boxes:
        raise RuntimeError("ظهرت شاشة الرمز دون حقل يمكن الكتابة فيه.")
    if len(boxes) >= len(pin):
        for box, digit in zip(boxes, pin):
            box.click(timeout=4000)
            page.keyboard.type(digit, delay=70)
    else:
        boxes[0].click(timeout=4000)
        page.keyboard.type(pin, delay=70)
    page.wait_for_timeout(1200)


def chat_inbox_open(page) -> bool:
    if "pin" in (page.url or ""):
        return False
    try:
        return page.locator('[data-testid^="dm-conversation-item-"]').count() > 0
    except Exception:
        return False


def open_chat(page, pin: str) -> str | None:
    if chat_inbox_open(page):
        return None
    goto_x(page, CHAT_URLS[0])
    typed = False
    deadline = time.monotonic() + 55
    while time.monotonic() < deadline:
        accept_cookies(page)
        if page.locator('[data-testid^="dm-conversation-item-"]').count():
            return None
        if not typed and "pin" in (page.url or ""):
            if pin_fields(page):
                type_pin_once(page, pin)
                typed = True
                error = pin_error_message(page)
                if error:
                    return error
        page.wait_for_timeout(700)
    if page.locator('[data-testid="dm-inbox-panel"]').count():
        return None
    return pin_error_message(page) or "تعذّر فتح الدردشة بعد إدخال الرمز."


def choose_inbox_filter(page, testid: str, label: str) -> None:
    trigger = page.locator('[data-testid="dm-inbox-dropdown-trigger"]')
    try:
        trigger.first.wait_for(state="visible", timeout=8_000)
        trigger.first.click(timeout=5000)
        page.wait_for_timeout(400)
    except Exception:
        return
    item = page.locator(f'[data-testid="{testid}"]')
    if item.count() == 0:
        item = page.get_by_role("menuitem", name=re.compile(label, re.I))
    if item.count() == 0:
        try:
            page.keyboard.press("Escape")
        except Exception:
            pass
        return
    try:
        item.first.click(timeout=5000)
    except Exception:
        return
    page.wait_for_timeout(500)
    try:
        page.keyboard.press("Escape")
    except Exception:
        pass


def show_groups_only(page) -> None:
    choose_inbox_filter(page, "dm-inbox-dropdown-groups", r"groups|قروب|مجموع")


GROUP_IDS_PATH = DATA_DIR / "group_ids.json"     # (the program's own work only; each account has its own file)
group_ids_lock = threading.RLock()
# Each account's groups, in its own file (data/accounts/<key>/group_ids.json): the id of each group, and its
# conversation link (…/messages/<id> or …/i/chat/<id>), so a task can open the group by going straight to
# it. Two accounts never see each other's groups, even ones with the same name.
_group_stores: dict[str, dict] = {}


def _group_ids_path(key: str) -> Path:
    return account_dir(key) / "group_ids.json" if key else GROUP_IDS_PATH


def _group_store(key: str) -> dict:
    with group_ids_lock:
        store = _group_stores.get(key)
        if store is None:
            loaded = read_private_json(_group_ids_path(key)) or {}
            rows, paths = loaded.get("groups"), loaded.get("paths")
            store = {
                "groups": {str(k): str(v) for k, v in rows.items() if k and v} if isinstance(rows, dict) else {},
                "paths": {str(k): str(v) for k, v in paths.items() if k and v} if isinstance(paths, dict) else {},
            }
            _group_stores[key] = store
        return store


class _AccountGroupMap:
    """group_ids / group_paths: name -> value, the running account's own (see account_context)."""

    def __init__(self, field: str):
        self.field = field

    def _map(self) -> dict:
        return _group_store(current_account())[self.field]

    def get(self, name, default=None):
        return self._map().get(name, default)

    def __getitem__(self, name):
        return self._map()[name]

    def __setitem__(self, name, value):
        self._map()[name] = value

    def __contains__(self, name):
        return name in self._map()

    def __iter__(self):
        return iter(dict(self._map()))

    def __len__(self):
        return len(self._map())

    def items(self):
        return dict(self._map()).items()

    def update(self, other) -> None:
        self._map().update(other)


group_ids = _AccountGroupMap("groups")
group_paths = _AccountGroupMap("paths")


def load_group_ids() -> None:
    """(each account's groups are read from its own file the first time they are needed)"""


def save_group_ids_unlocked() -> None:
    key = current_account()
    store = _group_store(key)
    try:
        write_private_json(_group_ids_path(key), {"version": 2, "groups": dict(store["groups"]), "paths": dict(store["paths"])})
    except Exception:
        pass


def remember_group_id(name: str, testid: str) -> None:
    """Remember each group's id (it does not change when the group is renamed)."""
    with group_ids_lock:
        if group_ids.get(name) == testid:
            return
        group_ids[name] = testid
        save_group_ids_unlocked()


def remember_group_path(name: str, path: str) -> None:
    """Remember a group's conversation link, so it can be opened directly next time."""
    cleaned = (path or "").strip()
    if not cleaned or "/status/" in cleaned:
        return
    with group_ids_lock:
        if group_paths.get(name) == cleaned:
            return
        group_paths[name] = cleaned
        save_group_ids_unlocked()


GROUPS_SCROLL_PASSES_MIN = 3     # the inbox is scrolled at least this many times, whatever the first pass shows
GROUPS_SCROLL_PASSES_MAX = 24
GROUPS_SETTLE_MS = 3000          # after a scroll: how long more conversations are waited for (they come sooner, usually)
INBOX_ITEMS = '[data-testid^="dm-conversation-item-"]'


def inbox_item_count(page) -> int:
    try:
        return int(page.locator(INBOX_ITEMS).count() or 0)
    except Exception:
        return 0


def inbox_loading(page) -> bool:
    try:
        return page.locator('[data-testid="dm-inbox-panel"] [role="progressbar"]').first.is_visible(timeout=200)
    except Exception:
        return False


def wait_for_more_conversations(page, before: int, settle_ms: int = GROUPS_SETTLE_MS) -> int:
    """After a scroll of the inbox: wait for more conversations to show (up to settle_ms, longer while X is
    still loading them), then a moment for their names to be drawn. Returns how many show now."""
    deadline = time.monotonic() + settle_ms / 1000
    longest = time.monotonic() + 2 * settle_ms / 1000
    while True:
        count = inbox_item_count(page)
        if count > before:
            page.wait_for_timeout(500)
            return inbox_item_count(page)
        now = time.monotonic()
        if now >= deadline and not (inbox_loading(page) and now < longest):
            return count
        page.wait_for_timeout(300)


def collect_groups(page) -> list[str]:
    """The names of the groups in the inbox, scrolled through to its end: every pass reads what shows, scrolls,
    and waits for more to come (wait_for_more_conversations); the inbox is scrolled at least
    GROUPS_SCROLL_PASSES_MIN times, and the reading stops after three scrolls that brought nothing new."""
    found: list[str] = []
    seen: set[str] = set()
    idle = 0
    passes = 0
    for _ in range(GROUPS_SCROLL_PASSES_MAX):
        passes += 1
        try:
            payload = page.evaluate(READ_GROUPS_JS, "") or {}
        except Exception:
            payload = {}
        added = 0
        ids = payload.get("ids") or []
        paths = payload.get("paths") or []
        for index, name in enumerate(payload.get("groups") or []):
            clean = re.sub(r"\s+", " ", str(name)).strip()
            if not clean or clean in seen:
                continue
            seen.add(clean)
            found.append(clean)
            if index < len(ids) and ids[index]:
                remember_group_id(clean, str(ids[index]))
            if index < len(paths) and paths[index]:
                remember_group_path(clean, str(paths[index]))
            added += 1
        before = inbox_item_count(page)
        try:
            page.evaluate(SCROLL_INBOX_JS)
        except Exception:
            pass
        try:
            panel = page.locator('[data-testid="dm-inbox-panel"]').first
            box = panel.bounding_box()
            if box:
                page.mouse.move(box["x"] + min(box["width"] / 2, 280), box["y"] + min(box["height"] * 0.55, 420))
                page.mouse.wheel(0, 700)
        except Exception:
            pass
        after = wait_for_more_conversations(page, before)
        trace_click(f"القروبات: تمرير {passes}، ظهر {after} محادثة (كانت {before})، أسماء جديدة {added}")
        if added or after > before:
            idle = 0
            continue
        idle += 1
        if passes >= GROUPS_SCROLL_PASSES_MIN and ((found and idle >= 3) or idle >= 8):
            break
    return found


# A group's conversation view, once its page has loaded.
GROUP_VIEW_SELECTOR = '[data-testid="dm-message-list"], [data-testid="dm-message-scroller"], [data-testid="dm-conversation-content"]'


def conversation_key(url: str) -> str:
    """The conversation id in a chat link (…/i/chat/<id> or …/messages/<id>): its digits when it has
    any (so "g123" and "123" are the same group), else the id itself. "" for any other page."""
    match = re.search(r"/(?:i/chat|messages)/([^/?#\s]+)", url or "")
    if not match:
        return ""
    raw = match.group(1)
    if raw.lower() in ("pin", "compose", "requests", "settings"):
        return ""
    return re.sub(r"\D", "", raw) or raw.lower()


def conversation_link(path: str) -> str:
    """The full address of a saved group link, or "" when it is not a chat conversation link."""
    cleaned = (path or "").strip()
    if not conversation_key(cleaned):
        return ""
    if cleaned.startswith("/"):
        return "https://x.com" + cleaned
    if re.match(r"https://(?:www\.)?(?:x|twitter)\.com/", cleaned):
        return cleaned
    return ""


def land_in_group(page, target: str, pin: str, wait_s: float) -> bool:
    """After a group's page was loaded, wait until that group shows: its conversation view, at its own
    link. Types the chat PIN if X asks for it; if X then shows the chat list instead of the group,
    goes to the group's link once more. Only the view is waited for, not the messages: after a full
    page load X can take a while to show them. True once the group shows."""
    want = conversation_key(target)
    plain_target = (target or "").split("?")[0].rstrip("/")
    typed = False
    again = False
    deadline = time.monotonic() + wait_s
    while time.monotonic() < deadline:
        accept_cookies(page)
        url = page.url or ""
        at_group = bool(want and conversation_key(url) == want) or url.split("?")[0].rstrip("/") == plain_target
        if at_group and "pin" not in url:
            return True
        if "pin" in url:
            if not typed and pin_fields(page):
                type_pin_once(page, pin)
                typed = True
                error = pin_error_message(page)
                if error:
                    raise RuntimeError(error)
        elif typed and not at_group and not again and (target or "").startswith("http"):
            again = True
            try:
                goto_x(page, target)
            except Exception as exc:
                if browser_closed_error(exc):
                    raise
        page.wait_for_timeout(500)
    return False


def open_group_direct(page, path: str, pin: str, wait_s: float = 40.0) -> bool:
    """Open the group by going straight to its saved link (the chat is already unlocked), instead of
    waiting for it to show up in the chat list. True once the group shows; False to find it in the
    chat list instead."""
    target = conversation_link(path)
    if not target:
        return False
    try:
        goto_x(page, target)
    except Exception as exc:
        if browser_closed_error(exc):
            raise
        return False
    opened = land_in_group(page, target, pin, wait_s)
    if os.environ.get("COLLECT_DEBUG"):
        print(f"group opened directly by its link {target}: {opened}", flush=True)
    return opened


def wait_group_messages(page, wait_s: float) -> bool:
    """Wait up to wait_s for the open group's messages to show. True when they did."""
    deadline = time.monotonic() + wait_s
    while time.monotonic() < deadline:
        try:
            state = page.evaluate(GROUP_CHAT_SCROLL_JS, "state") or {}
        except Exception as exc:
            if browser_closed_error(exc):
                raise
            state = {}
        if state.get("hasList") and state.get("messages"):
            page.wait_for_timeout(800)
            return True
        page.wait_for_timeout(400)
    return False


def open_named_group(page, name: str) -> str:
    """Find the group in the inbox (waiting up to 10 seconds for it), click it once,
    then wait for its messages. No retries: on failure the task stops with a message.

    The group is matched by its saved id first (renaming does not change it), then by
    exact name, then by a name that starts the same and differs only in the last few
    characters. Returns the name the group has now."""
    wanted = re.sub(r"\s+", " ", name).strip()
    with group_ids_lock:
        saved_id = group_ids.get(wanted, "")
    started = time.monotonic()
    clicked = False
    current_name = wanted
    while time.monotonic() - started < 10:
        try:
            payload = page.evaluate(READ_GROUPS_JS, {"name": wanted, "testid": saved_id}) or {}
        except Exception:
            payload = {}
        if payload.get("clicked"):
            clicked = True
            current_name = re.sub(r"\s+", " ", str(payload.get("matched") or wanted)).strip() or wanted
            # Remember the group's link, so the next task opens it straight away.
            if payload.get("path"):
                remember_group_path(wanted, str(payload.get("path")))
            if os.environ.get("COLLECT_DEBUG"):
                print(f"group opened by {payload.get('how')}: wanted={wanted!r} now={current_name!r}", flush=True)
            break
        if time.monotonic() - started > 3:
            try:
                page.evaluate(SCROLL_INBOX_JS)
            except Exception:
                pass
        page.wait_for_timeout(700)
    if not clicked:
        raise RuntimeError(f"لم يظهر القروب «{wanted}» في الدردشة خلال ١٠ ثوانٍ. توقفت المهمة.")
    deadline = time.monotonic() + 12
    while time.monotonic() < deadline:
        try:
            state = page.evaluate(GROUP_CHAT_SCROLL_JS, "state") or {}
        except Exception:
            state = {}
        if state.get("hasList") and state.get("messages"):
            page.wait_for_timeout(800)
            return current_name
        page.wait_for_timeout(300)
    raise RuntimeError("فُتح القروب لكن رسائله لم تظهر. توقفت المهمة.")


def peek_named_group(page, name: str, wait_s: float = 10.0) -> bool:
    """Open the group once (found the same way as open_named_group) and wait until its
    messages show, at most wait_s. True when the group was opened, whether or not the
    messages showed in time. Used before the real open, because X first opens a group at
    the place this account last read up to, not at the newest messages."""
    wanted = re.sub(r"\s+", " ", name).strip()
    with group_ids_lock:
        saved_id = group_ids.get(wanted, "")
    started = time.monotonic()
    clicked = False
    while time.monotonic() - started < 10:
        try:
            payload = page.evaluate(READ_GROUPS_JS, {"name": wanted, "testid": saved_id}) or {}
        except Exception:
            payload = {}
        if payload.get("clicked"):
            clicked = True
            if payload.get("path"):
                remember_group_path(wanted, str(payload.get("path")))
            break
        if time.monotonic() - started > 3:
            try:
                page.evaluate(SCROLL_INBOX_JS)
            except Exception:
                pass
        page.wait_for_timeout(700)
    if not clicked:
        return False
    deadline = time.monotonic() + wait_s
    while time.monotonic() < deadline:
        try:
            state = page.evaluate(GROUP_CHAT_SCROLL_JS, "state") or {}
        except Exception:
            state = {}
        if state.get("hasList") and state.get("messages"):
            page.wait_for_timeout(1000)
            return True
        page.wait_for_timeout(300)
    return True


def sway_group_while_waiting(page, seconds: int, should_stop=None) -> None:
    """During the wait inside the group, move the chat up and down. The last ten seconds
    stay at the bottom, where the newest messages are."""
    seconds = int(seconds)
    if seconds <= 0:
        return
    step = """(dir) => {
      const start = document.querySelector('[data-testid="dm-message-scroller"]')
        || document.querySelector('[data-testid="dm-message-list"]');
      const scrollerOf = (node) => {
        for (let el = node; el && el.nodeType === 1; el = el.parentElement) {
          if (/(auto|scroll|overlay)/.test(getComputedStyle(el).overflowY) && el.scrollHeight > el.clientHeight + 10) return el;
        }
        const page = document.scrollingElement;
        if (page && page.scrollHeight > page.clientHeight + 10) return page;
        return node;
      };
      const scroller = start ? scrollerOf(start) : document.scrollingElement;
      if (!scroller) return false;
      if (dir === 0) scroller.scrollTop = scroller.scrollHeight;
      else {
        const client = scroller.clientHeight || 800;
        const base = dir > 0
          ? Math.max(560, Math.min(1200, Math.round(client * 0.75)))
          : Math.max(400, Math.min(800, Math.round(client * 0.5)));
        const jump = Math.max(base, Math.min(base * 2, Math.round(client * 0.9)));
        scroller.scrollTop = dir < 0
          ? Math.max(0, scroller.scrollTop - jump)
          : Math.min(scroller.scrollHeight, scroller.scrollTop + jump);
      }
      try { scroller.dispatchEvent(new Event("scroll", {bubbles: true})); } catch (error) {}
      return true;
    }"""
    end = time.monotonic() + seconds
    bottom_at = end - 10 if seconds > 10 else time.monotonic()
    direction = -1
    while True:
        if should_stop and should_stop():
            return
        now = time.monotonic()
        if now >= end:
            return
        if now >= bottom_at:
            try:
                page.evaluate(step, 0)
            except Exception:
                pass
            page.wait_for_timeout(int(max(0, end - time.monotonic()) * 1000))
            return
        try:
            page.evaluate(step, direction)
        except Exception:
            pass
        direction = 1 if direction < 0 else -1
        page.wait_for_timeout(800)


def leave_group(page, pin: str) -> None:
    """Go back from the open group to the chat list, like pressing back."""
    try:
        page.go_back(wait_until="domcontentloaded", timeout=15_000)
    except Exception:
        pass
    page.wait_for_timeout(800)
    still_inside = re.search(r"/(?:i/chat|messages)/[^/?#]+", page.url or "")
    if still_inside or not chat_inbox_open(page):
        # Back did not land on the chat list: open it directly (types the chat PIN if X asks).
        goto_x(page, CHAT_URLS[0])
        error = open_chat(page, pin)
        if error:
            raise RuntimeError(error)


def saved_group_url(name: str) -> str:
    """The group's own address from what was saved earlier, without opening the chat list."""
    wanted = re.sub(r"\s+", " ", name).strip()
    with group_ids_lock:
        path = group_paths.get(wanted, "")
        gid = group_ids.get(wanted, "")
    link = conversation_link(path)
    if link:
        return link
    raw = re.sub(r"^dm-conversation-item-", "", (gid or path)).strip()
    digits = re.sub(r"\D", "", raw)
    if digits:
        return "https://x.com/i/chat/g" + digits
    return ""


def open_group_for_task(page, pin: str, group_name: str, group_wait_s: int, say) -> str:
    """Open the group by its address. The chat list is not opened and is not waited on.
    If X asks for the chat PIN on the way, it is typed, then the group address is opened again."""
    target = saved_group_url(group_name)
    if not target:
        raise RuntimeError(f"لا يوجد رابط محفوظ للقروب «{group_name}».")
    say(f"فتح القروب مباشرة: {group_name}")
    if not open_group_direct(page, target, pin, 25):
        raise RuntimeError(f"تعذّر فتح القروب «{group_name}» مباشرة.")
    remember_group_path(group_name, target)
    return group_name


def group_chat_state(page) -> dict:
    try:
        return page.evaluate(GROUP_CHAT_SCROLL_JS, "state") or {}
    except Exception:
        return {}


CHAT_SPOT_JS = r"""
() => {
""" + CHAT_FIND_JS + r"""
  const start = query('[data-testid="dm-message-scroller"]') || query('[data-testid="dm-message-list"]');
  if (!start) return null;
  // The chat's part of the screen: its scroller, else its list, else what really scrolls it.
  const area = [start, query('[data-testid="dm-message-list"]'), scrollerOf(start)].find((el) => el && shownArea(el) >= 1600);
  if (!area) return null;
  const rect = area.getBoundingClientRect();
  const left = Math.max(rect.left, 0);
  const top = Math.max(rect.top, 0);
  const width = Math.min(rect.right, innerWidth) - left;
  const height = Math.min(rect.bottom, innerHeight) - top;
  const inside = (node) => {
    for (let el = node; el; el = el.parentElement || (el.parentNode && el.parentNode.host) || null) {
      if (el === area) return true;
    }
    return false;
  };
  const spots = [[0.45, Math.min(0.42, 640 / height)], [0.5, 0.5], [0.5, 0.25], [0.5, 0.75], [0.25, 0.5], [0.75, 0.5]]
    .map(([fx, fy]) => ({x: Math.round(left + width * fx), y: Math.round(top + height * fy)}));
  for (const spot of spots) {
    let hit = document.elementFromPoint(spot.x, spot.y);
    while (hit && hit.shadowRoot) {
      const deeper = hit.shadowRoot.elementFromPoint(spot.x, spot.y);
      if (!deeper || deeper === hit) break;
      hit = deeper;
    }
    if (hit && inside(hit)) return spot;
  }
  return spots[0];
}
"""


def focus_group_scroller(page) -> None:
    """Put the mouse over the part of the chat that shows on the screen, on a spot nothing covers."""
    try:
        spot = page.evaluate(CHAT_SPOT_JS)
    except Exception:
        spot = None
    if spot:
        page.mouse.move(spot["x"], spot["y"])


CHAT_UNSTICK_JS = r"""
(pixels) => {
""" + CHAT_FIND_JS + r"""
  const start = query('[data-testid="dm-message-scroller"]') || query('[data-testid="dm-message-list"]');
  if (!start) return false;
  const scroller = scrollerOf(start);
  const room = scroller.scrollHeight - scroller.clientHeight;
  // Step down from the top; the mouse wheel then takes the chat back up to it.
  if (room > 10) scroller.scrollTop = Math.min(room, Math.max(120, pixels));
  if (start.scrollHeight - start.clientHeight > 10) return false;
  // The chat's own scroller cannot scroll (the loaded messages fit it): tell it it was scrolled up anyway.
  for (const target of new Set([start, scroller])) {
    try { target.dispatchEvent(new WheelEvent("wheel", {deltaY: -Math.max(120, pixels), bubbles: true, cancelable: true})); } catch (error) {}
    try { target.dispatchEvent(new Event("scroll", {bubbles: true})); } catch (error) {}
  }
  // Whether the loaded messages fit a chat made to scroll by itself: only a shorter screen lets it scroll.
  return /(auto|scroll|overlay)/.test(getComputedStyle(start).overflowY);
}
"""

# A screen taller than this is made this short for a moment when the chat's messages fit it.
SHORT_SCREEN_HEIGHT = 900


def unstick_group_chat(page, pixels: int) -> None:
    """For a climb that stopped at the oldest loaded messages while X loads no older ones: step
    down a little and wheel back up to the top, so X sees its chat being scrolled up. When the
    loaded messages fit the chat (on the tall phone screen nothing in it can scroll), this is done
    on a short screen, and the screen gets its height back after."""
    try:
        fits = bool(page.evaluate(CHAT_UNSTICK_JS, pixels))
    except Exception:
        return
    size = page.viewport_size or {}
    short = fits and int(size.get("height") or 0) > SHORT_SCREEN_HEIGHT
    try:
        if short:
            page.set_viewport_size({"width": int(size["width"]), "height": SHORT_SCREEN_HEIGHT})
            page.wait_for_timeout(600)
            page.evaluate(CHAT_UNSTICK_JS, pixels)
        page.wait_for_timeout(300)
        focus_group_scroller(page)
        page.mouse.wheel(0, -2 * pixels)
        page.wait_for_timeout(1500 if short else 300)
    except Exception as exc:
        if browser_closed_error(exc):
            raise
    finally:
        if short:
            try:
                page.set_viewport_size({"width": int(size["width"]), "height": int(size["height"])})
                page.wait_for_timeout(500)
            except Exception:
                pass


def tweet_url(raw_url: str, status_id: str) -> str:
    raw = (raw_url or "").strip()
    for match in re.finditer(rf"(?<![A-Za-z0-9_])/([A-Za-z0-9_]{{1,15}})/status/{status_id}(?!\d)", raw):
        owner = match.group(1)
        if owner.lower() in {"i", "web", "intent", "share"}:
            continue
        return f"https://x.com/{owner}/status/{status_id}"
    return f"https://x.com/i/web/status/{status_id}"


def extract_status_id(value: str) -> str:
    raw = (value or "").strip()
    match = re.search(r"status/(\d{6,25})", raw)
    if match:
        return match.group(1)
    if re.fullmatch(r"\d{15,25}", raw):
        return raw
    return ""


SCAN_STOP_JS = r"""
(arg) => {
  let wanted = "";
  let dir = 0;
  if (arg && typeof arg === "object") {
    wanted = String(arg.stopId || "");
    dir = arg.dir === 1 || arg.dir === -1 ? arg.dir : 0;
  } else {
    wanted = String(arg || "");
  }
""" + CHAT_FIND_JS + r"""
  const list = query('[data-testid="dm-message-list"]') || query('[data-testid="dm-conversation-content"]') || query('[data-testid="dm-message-scroller"]');
  if (!list) return {hit: false, pending: 0, oldest: "", count: 0, hitTop: 0};
  const all = [...list.querySelectorAll('[data-testid^="message-"]')].filter((el) => {
    const id = el.getAttribute("data-testid") || "";
    return id.startsWith("message-") && !id.startsWith("message-text-");
  });
  const messages = all.filter((el) => ![...el.querySelectorAll('[data-testid^="message-"]')].some((node) => {
    const id = node.getAttribute("data-testid") || "";
    return node !== el && id.startsWith("message-") && !id.startsWith("message-text-");
  }));
  let hit = false;
  let hitTop = 0;
  let pending = 0;
  for (const bubble of messages) {
    const links = [...bubble.querySelectorAll('a[href*="status/"]')].map((node) => node.getAttribute("href") || "");
    const blob = (bubble.innerText || "") + "\n" + links.join("\n");
    if (wanted && blob.includes(wanted)) {
      hit = true;
      hitTop = Math.round(bubble.getBoundingClientRect().top || 0);
      break;
    }
    const card = bubble.querySelector('[data-testid="tweetText"], article, [data-testid="card.wrapper"], [data-testid="tweetPhoto"]');
    if (card && !/status\/\d{6,25}/.test(blob)) pending += 1;
  }
  const oldest = messages.length ? (messages[0].getAttribute("data-testid") || "") : "";
  const scroller = scrollerOf(query('[data-testid="dm-message-scroller"]') || list);
  let loading = false;
  const spinner = list.querySelector('[data-testid="dm-message-list-spinner-slot"], [data-testid="dm-message-list-spinner"], [data-testid*="spinner"], [role="progressbar"]');
  if (spinner) {
    const rect = spinner.getBoundingClientRect();
    loading = rect.width > 8 && rect.height > 8;
  }
  let moved = 0;
  if (scroller && !hit && (dir === -1 || dir === 1)) {
    const beforeTop = scroller.scrollTop || 0;
    const client = scroller.clientHeight || 800;
    const step = Math.max(400, Math.min(800, Math.round(client * 0.5)));
    if (dir < 0 && beforeTop <= 48) {
      scroller.scrollTop = 0;
      try { scroller.dispatchEvent(new WheelEvent("wheel", {deltaY: -640, bubbles: true, cancelable: true})); } catch (error) {}
    } else if (dir > 0 && beforeTop + client >= scroller.scrollHeight - 80) {
      scroller.scrollTop = scroller.scrollHeight;
    } else {
      const next = dir < 0 ? Math.max(0, beforeTop - step) : Math.min(scroller.scrollHeight, beforeTop + step);
      scroller.scrollTop = next;
    }
    try { scroller.dispatchEvent(new Event("scroll", {bubbles: true})); } catch (error) {}
    moved = Math.abs((scroller.scrollTop || 0) - beforeTop);
  }
  return {
    hit,
    pending,
    oldest,
    count: messages.length,
    hitTop,
    loading,
    moved: Math.round(moved),
    scrollHeight: scroller ? Math.round(scroller.scrollHeight) : 0,
    scrollTop: scroller ? Math.round(scroller.scrollTop) : 0,
    clientHeight: scroller ? Math.round(scroller.clientHeight) : 0
  };
}
"""

STEP_OLDER_JS = r"""
(pixels) => {
""" + CHAT_FIND_JS + r"""
  const start = query('[data-testid="dm-message-scroller"]') || query('[data-testid="dm-message-list"]');
  if (!start) return {ok: false};
  const scroller = scrollerOf(start);
  const before = scroller.scrollTop;
  const atTop = before <= 48;
  if (!atTop) scroller.scrollTop = Math.max(0, before - Math.max(80, pixels));
  else scroller.scrollTop = 0;
  scroller.dispatchEvent(new Event("scroll", {bubbles: true}));
  return {ok: true, before: Math.round(before), after: Math.round(scroller.scrollTop), atTop, height: Math.round(scroller.scrollHeight)};
}
"""


# Inside the group, each scroll step is this many times the base step (never past what the
# chat shows at once).
GROUP_SCROLL_FACTOR = 2


FETCH_GROUP_PAGE_JS = r"""
async ({conversationId, maxId}) => {
  const bearer = "AAAAAAAAAAAAAAAAAAAAANRILgAAAAAAnNwIzUejRCOuH5E6I8xnZz4puTs%3D1Zv7ttfk8LF81IUq16cHjhLTvJu4FA33AGWWjCpTnA";
  const ct0 = decodeURIComponent((document.cookie.match(/(?:^|; )ct0=([^;]+)/) || [])[1] || "");
  if (!ct0) return {ok: false, error: "لا يوجد ct0 في هذه الصفحة"};
  const params = new URLSearchParams({
    context: maxId ? "FETCH_DM_CONVERSATION_HISTORY" : "FETCH_DM_CONVERSATION",
    include_conversation_info: "true",
    include_cards: "1",
    tweet_mode: "extended",
    include_groups: "true",
    supports_reactions: "true",
    supports_edit: "true",
    dm_users: "false"
  });
  if (maxId) params.set("max_id", String(maxId));
  const url = "https://x.com/i/api/1.1/dm/conversation/" + encodeURIComponent(conversationId) + ".json?" + params.toString();
  let response;
  try {
    response = await fetch(url, {
      method: "GET",
      credentials: "include",
      headers: {
        authorization: "Bearer " + bearer,
        "x-csrf-token": ct0,
        "x-twitter-auth-type": "OAuth2Session",
        "x-twitter-active-user": "yes"
      }
    });
  } catch (error) {
    return {ok: false, error: String(error && error.message || error)};
  }
  const raw = await response.text();
  let data = null;
  try { data = JSON.parse(raw); } catch (error) { data = null; }
  const ids = [];
  const texts = [];
  const messageIds = [];
  const seen = new Set();
  const walk = (node) => {
    if (node == null) return;
    if (typeof node === "string") {
      const re = /status\/(\d{6,25})/g;
      let match;
      while ((match = re.exec(node))) {
        if (!seen.has(match[1])) { seen.add(match[1]); ids.push(match[1]); }
      }
      if (node.length > 1 && node.length < 400 && texts.length < 4) texts.push(node.slice(0, 140));
      return;
    }
    if (Array.isArray(node)) { node.forEach(walk); return; }
    if (typeof node === "object") {
      if (node.id && /^\d{10,25}$/.test(String(node.id))) messageIds.push(String(node.id));
      Object.keys(node).forEach((key) => walk(node[key]));
    }
  };
  if (data) walk(data);
  messageIds.sort();
  const sample = texts.join(" | ").slice(0, 180);
  const readable = /[\u0600-\u06FFa-zA-Z]{2,}/.test(sample);
  let error = "";
  if (response.status !== 200) error = "HTTP " + response.status + " " + raw.replace(/\s+/g, " ").slice(0, 160);
  else if (!ids.length && !readable && sample.length > 40) error = "النص غير مقروء ويبدو مشفراً";
  else if (!ids.length) error = "لا روابط تغريدات في الدفعة";
  return {
    ok: response.status === 200,
    status: response.status,
    keys: data && typeof data === "object" ? Object.keys(data).slice(0, 8).join(",") : "",
    tweets: ids,
    messages: messageIds.length,
    minId: messageIds.length ? messageIds[0] : "",
    sample,
    error
  };
}
"""


def group_conversation_ids(page, group_name: str) -> list[str]:
    """Ids worth asking for, without opening the group: the saved link, then the inbox row."""
    wanted = re.sub(r"\s+", " ", group_name).strip()
    found: list[str] = []

    def add(value: str) -> None:
        raw = (value or "").strip()
        match = re.search(r"/(?:i/chat|messages)/([^/?#\s]+)", raw)
        if match:
            raw = match.group(1)
        raw = re.sub(r"^dm-conversation-item-", "", raw)
        if raw and raw not in found:
            found.append(raw)
        digits = re.sub(r"\D", "", raw)
        if digits and digits not in found:
            found.append(digits)

    with group_ids_lock:
        add(group_paths.get(wanted, ""))
        add(group_ids.get(wanted, ""))
    try:
        payload = page.evaluate(READ_GROUPS_JS, "") or {}
    except Exception as exc:
        trace_click("جمع الجلسة: تعذرت قراءة قائمة الدردشة " + type(exc).__name__)
        payload = {}
    names = payload.get("groups") if isinstance(payload, dict) else None
    paths = payload.get("paths") if isinstance(payload, dict) else None
    ids = payload.get("ids") if isinstance(payload, dict) else None
    if isinstance(names, list):
        for index, name in enumerate(names):
            if re.sub(r"\s+", " ", str(name)).strip() != wanted:
                continue
            if isinstance(paths, list) and index < len(paths):
                add(str(paths[index]))
            if isinstance(ids, list) and index < len(ids):
                add(str(ids[index]))
    trace_click(f"جمع الجلسة: معرفات «{wanted}» = {found or 'لا يوجد'}")
    return found


def collect_group_by_session(page, group_name: str, limit: int, stop_id: str = "", should_stop=None) -> tuple[list[dict], bool, str]:
    """Read the group's tweets from the open chat session, without opening or scrolling the group.

    Returns (tweets, reached the stop tweet, error). An error means the caller should collect
    by scrolling; the reason is already in the click log."""
    ids = group_conversation_ids(page, group_name)
    if not ids:
        reason = "لا يوجد معرف للقروب في الدردشة"
        trace_click("جمع الجلسة: " + reason)
        return [], False, reason
    conversation_id = ""
    cursor = ""
    seen_cursors: set[str] = set()
    seen: set[str] = set()
    found: list[dict] = []
    reached = False
    last_error = ""
    for page_no in range(1, 31):
        if should_stop and should_stop():
            raise JobStopped
        if not conversation_id:
            conversation_id = ids.pop(0)
        try:
            payload = page.evaluate(FETCH_GROUP_PAGE_JS, {"conversationId": conversation_id, "maxId": cursor}) or {}
        except Exception as exc:
            last_error = type(exc).__name__ + ": " + str(exc).splitlines()[0][:160]
            trace_click(f"جمع الجلسة صفحة {page_no}: فشل الطلب {last_error}")
            break
        if not isinstance(payload, dict):
            last_error = "رد غير مفهوم"
            trace_click(f"جمع الجلسة صفحة {page_no}: {last_error}")
            break
        status = payload.get("status")
        trace_click(
            f"جمع الجلسة صفحة {page_no} id={conversation_id} HTTP={status} مفاتيح={payload.get('keys') or '-'} "
            f"رسائل={payload.get('messages') or 0} تغريدات={len(payload.get('tweets') or [])} "
            f"سبب={payload.get('error') or '-'} عينة={payload.get('sample') or '-'}"
        )
        if status == 404 and ids:
            last_error = f"المعرف {conversation_id} غير موجود"
            conversation_id = ""
            cursor = ""
            continue
        if payload.get("ok") and not (payload.get("tweets") or []) and "مشفر" in str(payload.get("error") or ""):
            last_error = str(payload.get("error") or "النص مشفر")
            break
        if not payload.get("ok"):
            last_error = str(payload.get("error") or "فشل الطلب")
            break
        for status_id in payload.get("tweets") or []:
            status_id = re.sub(r"\D", "", str(status_id))
            if not status_id or status_id in seen:
                if stop_id and status_id == stop_id:
                    reached = True
                continue
            seen.add(status_id)
            found.append({"url": f"https://x.com/i/web/status/{status_id}", "text": "تغريدة"})
            if stop_id and status_id == stop_id:
                reached = True
                break
            if not stop_id and len(found) >= limit:
                break
        if reached or (not stop_id and len(found) >= limit):
            last_error = ""
            break
        older = str(payload.get("minId") or "")
        if not older or older in seen_cursors or older == cursor:
            last_error = "" if found else str(payload.get("error") or "انتهى السجل بلا تغريدات")
            break
        seen_cursors.add(older)
        cursor = older
        last_error = ""
    if found and (not stop_id or reached or not last_error):
        trace_click(f"جمع الجلسة نجح: {len(found)} تغريدة")
        return found, reached or not stop_id, ""
    reason = last_error or "لم تُستخرج تغريدات من الجلسة"
    trace_click("جمع الجلسة لم يكتمل: " + reason)
    return [], False, reason


def _status_ids_and_cursor(payload) -> tuple[list[str], str]:
    """Tweet ids in a chat response, and the cursor that asks for the older page."""
    ids: list[str] = []
    seen: set[str] = set()
    cursors: list[str] = []

    def add_id(value: str) -> None:
        for status_id in re.findall(r"status/(\d{6,25})", value or ""):
            if status_id not in seen:
                seen.add(status_id)
                ids.append(status_id)

    def walk(node, key: str = "") -> None:
        if isinstance(node, str):
            add_id(node)
            if key in ("min_entry_id", "cursor", "next_cursor", "pagination_token", "bottom_cursor") and re.fullmatch(r"[A-Za-z0-9_=+/-]{6,}", node):
                cursors.append(node)
            return
        if isinstance(node, list):
            for item in node:
                walk(item)
            return
        if isinstance(node, dict):
            for item_key, item in node.items():
                walk(item, str(item_key))

    walk(payload)
    return ids, (cursors[0] if cursors else "")


def collect_from_page_requests(page, pin: str, group_name: str, limit: int, stop_id: str = "", should_stop=None, say=None) -> tuple[list[dict], bool, str]:
    """Open the group once and read the requests the page itself is allowed to make.

    Older pages are requested from those same addresses. The chat is not scrolled and the
    wait inside the group is not used."""
    caught: list[tuple[str, int, str]] = []

    def on_finished(request) -> None:
        url = str(getattr(request, "url", "") or "")
        if not re.search(r"dm/|conversation|xchat|graphql|/chat/", url, re.I):
            return
        response = request.response()
        if response is None:
            return
        try:
            text = response.text()
        except Exception as exc:
            trace_click(f"طلب الصفحة بلا جسم HTTP={getattr(response, 'status', 0)} {url[:160]} {type(exc).__name__}")
            return
        caught.append((url, int(getattr(response, "status", 0) or 0), text[:200000]))
        trace_click(f"طلب الصفحة HTTP={getattr(response, 'status', 0)} طول={len(text)} {url[:180]}")

    page.on("requestfinished", on_finished)
    try:
        if say:
            say(f"فتح القروب مرة واحدة لأخذ طلب الصفحة: {group_name}")
        open_group_for_task(page, pin, group_name, 0, say or (lambda _text: None))
        page.wait_for_timeout(1500)
    finally:
        page.remove_listener("requestfinished", on_finished)
    if should_stop and should_stop():
        raise JobStopped
    if not caught:
        reason = "الصفحة لم ترسل طلب سجل عند فتح القروب"
        trace_click("جمع الطلبات: " + reason)
        return [], False, reason
    found: list[dict] = []
    seen: set[str] = set()
    reached = False

    def take(status_ids: list[str]) -> bool:
        nonlocal reached
        for status_id in status_ids:
            if status_id in seen:
                if stop_id and status_id == stop_id:
                    reached = True
                    return True
                continue
            seen.add(status_id)
            found.append({"url": f"https://x.com/i/web/status/{status_id}", "text": "تغريدة"})
            if stop_id and status_id == stop_id:
                reached = True
                return True
            if not stop_id and len(found) >= limit:
                return True
        return False

    replay_url = ""
    cursor = ""
    for url, status, text in caught:
        parsed = None
        try:
            parsed = json.loads(text)
        except Exception:
            parsed = text
        status_ids, found_cursor = _status_ids_and_cursor(parsed)
        trace_click(f"جمع الطلبات: من الرد {status} تغريدات={len(status_ids)} مؤشر={found_cursor or '-'}")
        if status_ids or found_cursor:
            replay_url = url
            cursor = found_cursor
        if take(status_ids):
            trace_click(f"جمع الطلبات اكتفى من أول رد: {len(found)}")
            return found, reached or not stop_id, ""
    if not replay_url or not cursor:
        visible = []
        try:
            visible = page.evaluate(r"""() => {
              const seen = new Set();
              const ids = [];
              const take = (value) => {
                const re = /status\/(\d{6,25})/g;
                let match;
                while ((match = re.exec(value || ""))) if (!seen.has(match[1])) { seen.add(match[1]); ids.push(match[1]); }
              };
              take(document.body ? document.body.innerText : "");
              document.querySelectorAll('a[href*="status/"]').forEach((link) => take(link.getAttribute("href") || ""));
              return ids;
            }""") or []
        except Exception:
            visible = []
        trace_click(f"جمع الطلبات: الظاهر على الشاشة {len(visible)} بلا مؤشر صفحة أقدم")
        if take([str(item) for item in visible]):
            return found, reached or not stop_id, ""
        reason = "الطلبات لا تحمل روابط ولا مؤشر صفحة أقدم"
        trace_click("جمع الطلبات: " + reason)
        return found, False, reason
    seen_cursors = {cursor}
    for page_no in range(2, 26):
        if should_stop and should_stop():
            raise JobStopped
        next_url = replay_url
        if re.search(r"[?&]max_id=", next_url):
            next_url = re.sub(r"([?&]max_id=)[^&]*", r"\g<1>" + cursor, next_url)
        elif re.search(r"[?&]cursor=", next_url):
            next_url = re.sub(r"([?&]cursor=)[^&]*", r"\g<1>" + cursor, next_url)
        elif "?" in next_url:
            next_url += "&max_id=" + cursor
        else:
            next_url += "?max_id=" + cursor
        try:
            payload = page.evaluate(r"""
async ({url}) => {
  const bearer = "AAAAAAAAAAAAAAAAAAAAANRILgAAAAAAnNwIzUejRCOuH5E6I8xnZz4puTs%3D1Zv7ttfk8LF81IUq16cHjhLTvJu4FA33AGWWjCpTnA";
  const ct0 = decodeURIComponent((document.cookie.match(/(?:^|; )ct0=([^;]+)/) || [])[1] || "");
  const response = await fetch(url, {
    method: "GET",
    credentials: "include",
    headers: {
      authorization: "Bearer " + bearer,
      "x-csrf-token": ct0,
      "x-twitter-auth-type": "OAuth2Session",
      "x-twitter-active-user": "yes"
    }
  });
  const raw = await response.text();
  return {status: response.status, raw: raw.slice(0, 200000)};
}
""", {"url": next_url}) or {}
        except Exception as exc:
            trace_click(f"جمع الطلبات صفحة {page_no}: فشل {type(exc).__name__}")
            break
        status = int(payload.get("status") or 0)
        raw = str(payload.get("raw") or "")
        try:
            parsed = json.loads(raw)
        except Exception:
            parsed = raw
        status_ids, found_cursor = _status_ids_and_cursor(parsed)
        trace_click(f"جمع الطلبات صفحة {page_no} HTTP={status} تغريدات={len(status_ids)} مؤشر={found_cursor or '-'}")
        done = take(status_ids)
        if done or not found_cursor or found_cursor in seen_cursors or status != 200:
            break
        seen_cursors.add(found_cursor)
        cursor = found_cursor
    if found:
        trace_click(f"جمع الطلبات نجح: {len(found)} بدون تمرير")
        return found, reached or not stop_id, ""
    reason = "صفحات الطلب لم تحمل تغريدات"
    trace_click("جمع الطلبات: " + reason)
    return [], False, reason


PROBE_CHAT_JS = r"""
async ({conversationId}) => {
  const bearer = "AAAAAAAAAAAAAAAAAAAAANRILgAAAAAAnNwIzUejRCOuH5E6I8xnZz4puTs%3D1Zv7ttfk8LF81IUq16cHjhLTvJu4FA33AGWWjCpTnA";
  const ct0 = decodeURIComponent((document.cookie.match(/(?:^|; )ct0=([^;]+)/) || [])[1] || "");
  const headers = {
    authorization: "Bearer " + bearer,
    "x-csrf-token": ct0,
    "x-twitter-auth-type": "OAuth2Session",
    "x-twitter-active-user": "yes"
  };
  const id = String(conversationId || "");
  const urls = [
    "https://x.com/i/api/2/chat/conversations/" + id + "/events?max_results=50&chat_message_event.fields=conversation_id,created_at,encoded_event,id,sender_id",
    "https://api.x.com/2/chat/conversations/" + id + "/events?max_results=50&chat_message_event.fields=conversation_id,created_at,encoded_event,id,sender_id",
    "https://x.com/i/api/2/chat/conversations/" + id,
    "https://x.com/i/api/1.1/dm/inbox_initial_state.json?include_groups=true&supports_reactions=true"
  ];
  const seen = new Set(urls);
  try {
    const chunks = self.webpackChunk_twitter_responsive_web || [];
    let budget = 0;
    const re = /\/(?:2\/chat\/conversations|i\/api\/[^"'\\\s]{0,80}(?:dm|chat)[^"'\\\s]{0,80})/g;
    for (const chunk of chunks) {
      const mods = chunk && chunk[1];
      if (!mods) continue;
      for (const fn of Object.values(mods)) {
        let source = "";
        try { source = Function.prototype.toString.call(fn); } catch (error) { continue; }
        if (source.indexOf("chat") < 0 && source.indexOf("/dm/") < 0) continue;
        let match;
        while ((match = re.exec(source))) {
          const path = match[0];
          if (!seen.has(path) && urls.length < 10) { seen.add(path); urls.push(path); }
        }
        budget += source.length;
        if (budget > 1500000) break;
      }
    }
  } catch (error) {}
  const results = [];
  for (const url of urls) {
    const full = url.startsWith("http") ? url : ("https://x.com" + url);
    try {
      const response = await fetch(full, {method: "GET", credentials: "include", headers});
      const raw = await response.text();
      const ids = raw.match(/status\/\d{6,25}/g) || [];
      results.push({
        url: full.slice(0, 180),
        status: response.status,
        tweets: ids.length,
        encoded: raw.indexOf("encoded_event") >= 0,
        sample: raw.replace(/\s+/g, " ").slice(0, 180)
      });
    } catch (error) {
      results.push({url: full.slice(0, 180), status: 0, tweets: 0, encoded: false, sample: String(error && error.message || error).slice(0, 180)});
    }
  }
  return results;
}
"""


def probe_chat_without_group(page, group_name: str) -> None:
    """Ask the chat history from the inbox only. Never opens the group. Logs every answer."""
    ids = group_conversation_ids(page, group_name)
    group_id = next((item for item in ids if item.startswith("g")), ids[0] if ids else "")
    trace_click(f"تجربة بدون فتح: المعرف المستخدم {group_id or 'لا يوجد'}")
    if not group_id:
        trace_click("تجربة بدون فتح: توقف، لا معرف")
        return
    try:
        rows = page.evaluate(PROBE_CHAT_JS, {"conversationId": group_id}) or []
    except Exception as exc:
        trace_click("تجربة بدون فتح: فشل التشغيل " + type(exc).__name__ + " " + str(exc).splitlines()[0][:160])
        return
    if not isinstance(rows, list):
        trace_click("تجربة بدون فتح: رد غير مفهوم")
        return
    for row in rows:
        if not isinstance(row, dict):
            continue
        trace_click(
            f"تجربة HTTP={row.get('status')} تغريدات={row.get('tweets')} مشفر={row.get('encoded')} "
            f"{row.get('url')} | {row.get('sample')}"
        )
    readable = [row for row in rows if isinstance(row, dict) and int(row.get("tweets") or 0) > 0]
    encoded = [row for row in rows if isinstance(row, dict) and row.get("encoded")]
    if readable:
        trace_click(f"تجربة بدون فتح: وُجدت روابط في {len(readable)} طلب")
    elif encoded:
        trace_click("تجربة بدون فتح: السجل رجع مشفراً (encoded_event) بلا روابط مقروءة")
    else:
        trace_click("تجربة بدون فتح: لا طلب أعاد روابط تغريدات")


def collect_group_tweets(page, limit: int, on_progress=None, stop_id: str = "", should_stop=None) -> tuple[list[dict], bool]:
    found: list[dict] = []
    seen: set[str] = set()
    reached = False

    def pull() -> tuple[int, int, list[str]]:
        nonlocal reached
        try:
            payload = page.evaluate(GROUP_READ_TWEETS_JS, "") or {}
        except Exception:
            payload = {}
        if isinstance(payload, list):
            rows, pending = payload, 0
        else:
            rows, pending = payload.get("tweets") or [], int(payload.get("pending") or 0)
        rows = [row for row in rows if isinstance(row, dict)]
        rows.sort(key=lambda row: float(row.get("top") or 0), reverse=True)
        added = 0
        visible: list[str] = []
        for row in rows:
            if reached or (not stop_id and len(found) >= limit):
                break
            status_id = re.sub(r"\D", "", str(row.get("statusId") or ""))
            if not status_id:
                continue
            visible.append(status_id)
            if status_id in seen:
                if stop_id and status_id == stop_id:
                    reached = True
                    break
                continue
            seen.add(status_id)
            found.append({
                "url": tweet_url(str(row.get("url") or ""), status_id),
                "text": re.sub(r"\s+", " ", str(row.get("text") or "")).strip()[:280] or "تغريدة",
            })
            added += 1
            if stop_id and status_id == stop_id:
                reached = True
                break
        return added, pending, visible

    def settle(tries: int = 7) -> tuple[int, list[str]]:
        added_total = 0
        pending = 0
        visible: list[str] = []
        for _ in range(tries):
            added, pending, visible = pull()
            added_total += added
            if on_progress:
                on_progress(len(found), 0 if stop_id else limit, "collect")
            if reached or (not stop_id and len(found) >= limit):
                return added_total, visible
            if pending:
                page.wait_for_timeout(100)
                continue
            page.wait_for_timeout(40)
            added, pending, visible = pull()
            added_total += added
            if reached or (not stop_id and len(found) >= limit):
                return added_total, visible
            if not pending:
                return added_total, visible
        return added_total, visible

    def read_rows() -> tuple[list[dict], int]:
        try:
            payload = page.evaluate(GROUP_READ_TWEETS_JS, "") or {}
        except Exception:
            payload = {}
        if isinstance(payload, list):
            return [row for row in payload if isinstance(row, dict)], 0
        rows = payload.get("tweets") or []
        return [row for row in rows if isinstance(row, dict)], int(payload.get("pending") or 0)

    def row_id(row: dict) -> str:
        return re.sub(r"\D", "", str(row.get("statusId") or ""))

    def add_tweet(status_id: str, row: dict) -> bool:
        if not status_id or status_id in seen:
            return False
        seen.add(status_id)
        found.append({
            "url": tweet_url(str(row.get("url") or ""), status_id),
            "text": re.sub(r"\s+", " ", str(row.get("text") or "")).strip()[:280] or "تغريدة",
        })
        return True

    def at_latest(state: dict) -> bool:
        top = int(state.get("scrollTop") or 0)
        height = int(state.get("scrollHeight") or 0)
        client = int(state.get("clientHeight") or 0) or 700
        return height > 0 and top + client >= height - 80

    if stop_id:
        spotted = False
        quiet = 0
        rounds = 0
        hit_top = None
        last_oldest = ""
        last_height = 0
        max_seek = 8000

        def scan_stop(direction: int) -> dict:
            try:
                payload = page.evaluate(SCAN_STOP_JS, {"stopId": stop_id, "dir": direction}) or {}
            except Exception:
                payload = {}
            return payload if isinstance(payload, dict) else {}

        # Climb with real mouse-wheel input (what X's chat listens to for loading
        # older messages). Progress = the oldest mounted message changes, the
        # scroll position moves, or the list grows. Unfinished tweet cards no
        # longer keep the loop alive forever, and the climb has a time limit.
        last_top = -1
        deadline = time.monotonic() + 360
        while not spotted and rounds < max_seek and quiet < 8 and time.monotonic() < deadline:
            if should_stop and should_stop():
                raise JobStopped
            close_popups(page)
            scan = scan_stop(0)
            if scan.get("hit"):
                spotted = True
                hit_top = float(scan.get("hitTop") or 0)
                break
            client = int(scan.get("clientHeight") or 0) or 800
            step = max(250, min(500, int(client * 0.2)))
            step = max(step, min(step * GROUP_SCROLL_FACTOR, int(client * 0.9)))
            before_top = int(scan.get("scrollTop") or 0)
            focus_group_scroller(page)
            try:
                page.mouse.wheel(0, -step)
            except Exception:
                pass
            page.wait_for_timeout(2000)
            state = scan_stop(0)
            if state.get("hit"):
                spotted = True
                hit_top = float(state.get("hitTop") or 0)
                break
            top_now = int(state.get("scrollTop") or 0)
            if abs(top_now - before_top) <= 8 and top_now > 48:
                try:
                    page.evaluate(STEP_OLDER_JS, step)
                except Exception:
                    pass
                page.wait_for_timeout(300)
                state = scan_stop(0)
                top_now = int(state.get("scrollTop") or 0)
            oldest = str(state.get("oldest") or "")
            height = int(state.get("scrollHeight") or 0)
            moved = last_top >= 0 and abs(top_now - last_top) > 8
            grew = height > last_height + 24 or bool(oldest and last_oldest and oldest != last_oldest)
            if not moved and not grew and top_now <= 48:
                # At the oldest loaded messages and X has not loaded older ones.
                unstick_group_chat(page, step)
                state = scan_stop(0)
                if state.get("hit"):
                    spotted = True
                    hit_top = float(state.get("hitTop") or 0)
                    break
                top_now = int(state.get("scrollTop") or 0)
                oldest = str(state.get("oldest") or "")
                height = int(state.get("scrollHeight") or 0)
                grew = height > last_height + 24 or bool(oldest and last_oldest and oldest != last_oldest)
            if moved or grew:
                quiet = 0
            else:
                quiet += 1
            if oldest:
                last_oldest = oldest
            last_height = max(last_height, height)
            last_top = top_now
            rounds += 1
            if on_progress and rounds % 3 == 0:
                on_progress(rounds, 0, "seek")
            if os.environ.get("COLLECT_DEBUG"):
                print(
                    f"seek round={rounds} quiet={quiet} top={top_now} h={height} oldest={oldest} msgs={state.get('count')} pending={state.get('pending')}",
                    flush=True,
                )
        if not spotted:
            return [], False
        rows, _pending = read_rows()
        target_top = hit_top
        for row in rows:
            if row_id(row) == stop_id:
                target_top = float(row.get("top") or 0)
                break
        older: set[str] = set()
        for row in rows:
            status_id = row_id(row)
            top = float(row.get("top") or 0)
            if target_top is not None and top < target_top - 12:
                if status_id and status_id != stop_id:
                    older.add(status_id)
                continue
            add_tweet(status_id, row)
        if stop_id not in {row_id(row) for row in rows}:
            add_tweet(stop_id, {"url": f"https://x.com/i/web/status/{stop_id}", "text": "تغريدة"})
        if on_progress:
            on_progress(len(found), 0, "collect")
        stall = 0
        rounds = 0
        last_fp = ""
        while rounds < max_seek and stall < 5:
            if should_stop and should_stop():
                raise JobStopped
            close_popups(page)
            try:
                payload = page.evaluate(GROUP_READ_TWEETS_JS, {"dir": 1, "stopId": stop_id, "factor": GROUP_SCROLL_FACTOR}) or {}
            except Exception:
                payload = {}
            if not isinstance(payload, dict):
                payload = {}
            down_rows = [row for row in payload.get("tweets") or [] if isinstance(row, dict)]
            stop_row = next((row for row in down_rows if row_id(row) == stop_id), None)
            stop_top = float(stop_row.get("top") or 0) if stop_row else None
            for row in down_rows:
                status_id = row_id(row)
                if not status_id or status_id in older:
                    continue
                if stop_top is not None and status_id != stop_id and float(row.get("top") or 0) < stop_top - 12:
                    older.add(status_id)
                    continue
                add_tweet(status_id, row)
            if on_progress and found:
                on_progress(len(found), 0, "collect")
            fp = str(payload.get("fingerprint") or "")
            height = int(payload.get("scrollHeight") or 0)
            top = int(payload.get("scrollTop") or 0)
            client = int(payload.get("clientHeight") or 0) or 700
            latest = height > 0 and top + client >= height - 80
            pending = int(payload.get("pending") or 0)
            moved = bool(fp and last_fp and fp != last_fp) or int(payload.get("moved") or 0) > 8
            if pending or moved:
                stall = 0
                page.wait_for_timeout(1000)
            else:
                stall += 1
                page.wait_for_timeout(1000)
            last_fp = fp or last_fp
            rounds += 1
            if os.environ.get("COLLECT_DEBUG"):
                print(f"down round={rounds} found={len(found)} stall={stall} top={top} h={height} latest={latest}", flush=True)
        return found, True

    for _ in range(8):
        state = group_chat_state(page)
        if state.get("messages"):
            break
        page.wait_for_timeout(100)
    settle(1)
    stall = 0
    rounds = 0
    stall_limit = 12
    max_rounds = min(5000, max(400, (limit or 400) * 8))
    last_fp = ""
    last_h = 0

    while not reached and len(found) < limit and rounds < max_rounds and stall < stall_limit:
        if should_stop and should_stop():
            raise JobStopped
        before_count = len(found)
        close_popups(page)
        try:
            payload = page.evaluate(GROUP_READ_TWEETS_JS, {"dir": -1, "stopId": "", "factor": GROUP_SCROLL_FACTOR}) or {}
        except Exception:
            payload = {}
        if not isinstance(payload, dict):
            payload = {}
        rows = payload.get("tweets") or []
        rows = [row for row in rows if isinstance(row, dict)]
        rows.sort(key=lambda row: float(row.get("top") or 0), reverse=True)
        for row in rows:
            if len(found) >= limit:
                break
            status_id = row_id(row)
            if not status_id or status_id in seen:
                continue
            add_tweet(status_id, row)
        if on_progress and len(found) != before_count:
            on_progress(len(found), limit, "collect")
        fp = str(payload.get("fingerprint") or "")
        height = int(payload.get("scrollHeight") or 0)
        at_edge = int(payload.get("scrollTop") or 0) <= 48 or bool(payload.get("atOlderEdge"))
        loading = bool(payload.get("loading")) or int(payload.get("pending") or 0) > 0
        grew = height > last_h + 24
        new_tweets = len(found) > before_count
        moved = bool(fp and last_fp and fp != last_fp) or int(payload.get("moved") or 0) > 8 or grew
        if new_tweets or loading or moved:
            stall = 0
        else:
            stall += 1
        if len(found) >= limit:
            break
        if loading:
            page.wait_for_timeout(2000)
        elif at_edge and not moved:
            client = int(payload.get("clientHeight") or 0) or 800
            unstick_group_chat(page, max(250, min(500, int(client * 0.2))))
            page.wait_for_timeout(2000)
        else:
            page.wait_for_timeout(2000)
        last_fp = fp or last_fp
        last_h = max(last_h, height)
        rounds += 1
        if os.environ.get("COLLECT_DEBUG"):
            print(
                f"round={rounds} found={len(found)} stall={stall} top={payload.get('scrollTop')} h={height} load={loading} edge={at_edge}",
                flush=True,
            )
    return found[:limit], reached


def reveal_status(page) -> None:
    try:
        clicked = page.evaluate(
            """() => {
              const words = /^(view|show|see post|yes,? view|عرض|عرض المنشور|نعم، عرض|عرض الوسائط|متابعة المشاهدة)$/i;
              const nodes = [...document.querySelectorAll('button, [role="button"], a')];
              const hit = nodes.find((node) => words.test((node.innerText || "").replace(/\\s+/g, " ").trim()) && node.getClientRects().length);
              if (!hit) return false;
              hit.click();
              return true;
            }"""
        )
        if clicked:
            page.wait_for_timeout(900)
    except Exception:
        pass


def read_status_gate(page) -> str:
    try:
        state = page.evaluate(
            """() => {
              const articles = [...document.querySelectorAll('article[data-testid="tweet"]')];
              const live = articles.find((article) => !/was deleted|deleted by the post author|تم حذف|غير متاح/i.test(article.innerText || ""));
              if (live) return "tweet";
              const chunks = [];
              for (const node of document.querySelectorAll('[data-testid="primaryColumn"], [data-testid="empty_state_header_text"], [data-testid="error-detail"], [role="status"]')) {
                chunks.push(node.innerText || "");
              }
              if (!chunks.length && document.body) chunks.push((document.body.innerText || "").slice(0, 1800));
              const text = chunks.join(" ").replace(/\\s+/g, " ");
              if (/was deleted|deleted by the post author|this post is unavailable|this post was deleted|doesn.?t exist|account is suspended|unable to view this post|هذه الصفحة غير موجودة|هذا المنشور غير متاح|تم حذف|حذف صاحب|الحساب موقوف/i.test(text)) return "gone";
              if (document.querySelector('[data-testid="empty_state_header_text"], [data-testid="error-detail"]')) return "gone";
              return "wait";
            }"""
        )
    except Exception:
        return "wait"
    return state if state in {"tweet", "gone", "wait"} else "wait"


QUICK_ACTIONS_ON_JS = r"""
({statusId, names}) => {
  if (!statusId) return false;
  const card = [...document.querySelectorAll('article[data-testid="tweet"], [data-testid="tweet"]')].find((article) =>
    [...article.querySelectorAll('a[href*="/status/"]')].some((node) => (node.getAttribute("href") || "").includes("/status/" + statusId)));
  if (!card) return false;
  const root = card.closest('[data-testid="cellInnerDiv"]') || card;
  const on = {repost: "unretweet", like: "unlike", bookmark: "removeBookmark"};
  const labels = {unretweet: /undo repost|unretweet|تم إعادة|إلغاء إعادة/i, unlike: /unlike|liked|أعجبني|معجب/i, removeBookmark: /remove bookmark|إزالة الإشارة/i};
  const has = (testid) => {
    if (root.querySelector('[data-testid="' + testid + '"]')) return true;
    const re = labels[testid];
    if (!re) return false;
    return [...root.querySelectorAll("button, [role='button']")].some((node) => re.test(node.getAttribute("aria-label") || ""));
  };
  return names.length > 0 && names.every((name) => on[name] && has(on[name]));
}
"""


BUTTONS_READY_JS = r"""
({statusId, names}) => {
  const want = {
    like: ["like", "unlike"],
    repost: ["retweet", "unretweet"],
    bookmark: ["bookmark", "removeBookmark"]
  };
  const roots = [...document.querySelectorAll('article, [data-testid="tweet"], [data-testid="cellInnerDiv"]')];
  const card = roots.find((node) => [...node.querySelectorAll('a[href*="/status/"]')].some((link) => (link.getAttribute("href") || "").includes("/status/" + statusId)));
  if (!card) return false;
  return names.length > 0 && names.every((name) => (want[name] || []).some((id) => card.querySelector('[data-testid="' + id + '"]')));
}
"""


def tweet_flags_from_api(data, status_id: str) -> dict | None:
    """Find the tweet in X's own API reply and read its like / repost / bookmark state."""
    stack = [data]
    seen = 0
    while stack and seen < 20000:
        node = stack.pop()
        seen += 1
        if isinstance(node, dict):
            legacy = node.get("legacy")
            if str(node.get("rest_id") or "") == status_id and isinstance(legacy, dict):
                return {
                    "like": bool(legacy.get("favorited")),
                    "repost": bool(legacy.get("retweeted")),
                    "bookmark": bool(legacy.get("bookmarked")),
                }
            stack.extend(node.values())
        elif isinstance(node, list):
            stack.extend(node)
    return None


def open_status_page(page, url: str, skip_if_on: list[str] | None = None) -> tuple[str | None, str]:
    """Open a tweet. With skip_if_on, return (path, "already_on") the moment the
    tweet's buttons show every listed action already on, without waiting for the
    rest of the page to load."""
    match = re.search(r"status/(\d{6,25})", url or "")
    status_id = match.group(1) if match else ""
    canonical = normalize_status_path(url) or ""
    if status_id:
        target = f"https://x.com/i/web/status/{status_id}"
    elif canonical:
        target = "https://x.com" + canonical
    else:
        return None, "fail"
    quick = [name for name in (skip_if_on or []) if name in ACTION_CONTROLS]
    if skip_if_on and len(quick) != len(skip_if_on):
        quick = []
    # X's page asks its API for the tweet before drawing it. Listening to that reply
    # gives the button states before they appear on screen. Only replies that have
    # finished downloading are read: reading one that is still arriving waits with no
    # time limit, so a reply that stalls halfway would freeze the task on this tweet.
    replies: list = []
    api_flags: dict | None = None

    def on_finished(request):
        address = request.url
        if "/graphql/" in address and ("TweetDetail" in address or "TweetResultByRestId" in address):
            replies.append(request)

    if quick and status_id:
        page.on("requestfinished", on_finished)
    try:
        try:
            page.goto(target, wait_until="commit" if quick else "domcontentloaded", timeout=20_000)
        except Exception:
            return None, "fail"
        revealed = False
        deadline = time.monotonic() + (12 if quick else 8)
        while time.monotonic() < deadline:
            if quick and status_id:
                while replies and api_flags is None:
                    request = replies.pop(0)
                    try:
                        response = request.response()
                        api_flags = tweet_flags_from_api(response.json(), status_id) if response else None
                    except Exception:
                        api_flags = None
                    if api_flags is not None and os.environ.get("COLLECT_DEBUG"):
                        print(f"tweet {status_id} api state: {api_flags}", flush=True)
                if api_flags is not None and all(api_flags.get(name) for name in quick):
                    return canonical or f"/i/web/status/{status_id}", "already_on"
                try:
                    if page.evaluate(QUICK_ACTIONS_ON_JS, {"statusId": status_id, "names": quick}):
                        return canonical or f"/i/web/status/{status_id}", "already_on"
                    if page.evaluate(BUTTONS_READY_JS, {"statusId": status_id, "names": quick}):
                        return canonical or f"/i/web/status/{status_id}", ""
                except Exception:
                    pass
            state = read_status_gate(page)
            if state == "gone":
                return None, "gone"
            if state == "tweet":
                href = ""
                if status_id:
                    try:
                        href = page.evaluate(
                            """(id) => {
                              const link = [...document.querySelectorAll('a[href*="/status/"]')]
                                .find((node) => (node.getAttribute("href") || "").includes("/status/" + id));
                              return link ? (link.getAttribute("href") || "") : "";
                            }""",
                            status_id,
                        ) or ""
                    except Exception:
                        href = ""
                return normalize_status_path(str(href)) or canonical or f"/i/web/status/{status_id}", ""
            if not revealed and time.monotonic() + 5 < deadline:
                pass
            elif not revealed:
                reveal_status(page)
                revealed = True
                if read_status_gate(page) == "gone":
                    return None, "gone"
            page.wait_for_timeout(120)
        if read_status_gate(page) == "gone":
            return None, "gone"
        return None, "fail"
    finally:
        if quick and status_id:
            try:
                page.remove_listener("requestfinished", on_finished)
            except Exception:
                pass


def all_actions_already_on(page, path: str, actions: list[str], timeout_s: float = 1.5) -> bool:
    """Read the tweet's buttons as soon as they appear. True only when every
    requested action is already on, so the tweet can be skipped without waiting
    for the rest of the page to load."""
    if not actions or any(action not in ACTION_CONTROLS for action in actions):
        return False
    match = re.search(r"status/(\d{6,25})", path or "")
    status_id = match.group(1) if match else ""
    deadline = time.monotonic() + timeout_s
    while True:
        state = read_action_state(page, status_id, actions) or {}
        rows = [state.get(action) if isinstance(state.get(action), dict) else {} for action in actions]
        if rows and all(row.get("on") for row in rows):
            return True
        if rows and all(row.get("on") or row.get("box") for row in rows):
            return False
        if time.monotonic() >= deadline:
            return False
        page.wait_for_timeout(150)


DONE_HISTORY_PATH = DATA_DIR / "done_history.json"
DONE_HISTORY_HOURS = 8
done_history_lock = threading.Lock()
done_history: dict[str, dict[str, dict[str, float]]] = {}


def prune_done_history_unlocked() -> None:
    cutoff = time.time() - DONE_HISTORY_HOURS * 3600
    for account in list(done_history):
        tweets = done_history[account]
        for status_id in list(tweets):
            kept = {action: stamp for action, stamp in tweets[status_id].items() if stamp >= cutoff}
            if kept:
                tweets[status_id] = kept
            else:
                del tweets[status_id]
        if not tweets:
            del done_history[account]


def load_done_history() -> None:
    loaded = read_private_json(DONE_HISTORY_PATH) or {}
    rows = loaded.get("accounts")
    if not isinstance(rows, dict):
        return
    with done_history_lock:
        for account, tweets in rows.items():
            if not isinstance(tweets, dict):
                continue
            clean: dict[str, dict[str, float]] = {}
            for status_id, done in tweets.items():
                if isinstance(done, dict):
                    clean[str(status_id)] = {str(a): float(t) for a, t in done.items() if isinstance(t, (int, float))}
            done_history[str(account)] = clean
        prune_done_history_unlocked()


def tweet_status_id(url: str) -> str:
    match = re.search(r"status/(\d{6,25})", url or "")
    return match.group(1) if match else ""


def same_x_account(account: str) -> set[str]:
    """The added accounts that are this one X account (the same @name signed in more than once, in two or three
    of the app's accounts), by their profile keys, this one among them. Their 8-hour memory is one: a tweet one
    of them acted on, the others skip, so the X account never acts twice on it."""
    twins = {account}
    if not account:
        return twins
    with sessions_lock:
        rows = [(profile_key(row["token"]), str(row.get("username") or "").lower()) for row in saved_sessions]
    name = next((found for key, found in rows if key == account and found), "") or str(account_names.get(account) or "").lower()
    if name:
        twins.update(key for key, found in rows if found == name)
    return twins


def already_done_recently(account: str, status_id: str, actions: list[str]) -> bool:
    """True when every requested action was done on this tweet in the last 8 hours by this account, or by
    another of the app's accounts that is the same X account (see same_x_account)."""
    if not account or not status_id or not actions:
        return False
    cutoff = time.time() - DONE_HISTORY_HOURS * 3600
    twins = same_x_account(account)
    with done_history_lock:
        done: dict[str, float] = {}
        for twin in twins:
            for action, stamp in ((done_history.get(twin) or {}).get(status_id) or {}).items():
                done[action] = max(done.get(action, 0.0), float(stamp))
        return all(done.get(action, 0) >= cutoff for action in actions)


ACTION_COUNTS_PATH = DATA_DIR / "action_counts.json"
action_counts_lock = threading.Lock()
ACTION_NAMES = ("repost", "like", "bookmark", "comment")
# The totals shown at the top of the page, kept for each account on its own (keyed by profile_key).
action_counts: dict[str, dict[str, int]] = {}


def zero_counts() -> dict[str, int]:
    return {action: 0 for action in ACTION_NAMES}


def account_counts(account: str) -> dict[str, int]:
    """A copy of one account's totals (zeros when it has none yet)."""
    with action_counts_lock:
        row = action_counts.get(account) or {}
    return {action: int(row.get(action) or 0) for action in ACTION_NAMES}


def load_action_counts() -> None:
    loaded = read_private_json(ACTION_COUNTS_PATH) or {}
    by_account = loaded.get("by_account") if isinstance(loaded, dict) else None
    with action_counts_lock:
        action_counts.clear()
        if isinstance(by_account, dict):
            for key, row in by_account.items():
                if not isinstance(row, dict):
                    continue
                action_counts[str(key)] = {action: max(0, int(row.get(action) or 0)) for action in ACTION_NAMES}


def count_successes(outcome: dict[str, str], account: str = "") -> None:
    """Add this tweet's successful actions to this account's totals shown at the top of the page."""
    done = [action for action, note in (outcome or {}).items() if note == "تم التنفيذ" and action in ACTION_NAMES]
    if not done or not account:
        return
    with action_counts_lock:
        row = action_counts.get(account)
        if row is None:
            row = action_counts[account] = zero_counts()
        for action in done:
            row[action] += 1
        try:
            write_private_json(ACTION_COUNTS_PATH, {"by_account": action_counts})
        except Exception:
            pass
    stats_changed()


def remember_done(account: str, status_id: str, outcome: dict[str, str]) -> None:
    """Save the actions that are now on for this tweet (done now or already on)."""
    if not account or not status_id:
        return
    now = time.time()
    finished = [
        action for action, note in (outcome or {}).items()
        if (action in ACTION_CONTROLS and (note == "تم التنفيذ" or "مفعّل مسبقًا" in str(note)))
        or (action == "comment" and (note == "تم التنفيذ" or str(note).startswith("أُرسل الطلب")))
    ]
    if not finished:
        return
    with done_history_lock:
        tweets = done_history.setdefault(account, {})
        record = tweets.setdefault(status_id, {})
        for action in finished:
            record[action] = now
        prune_done_history_unlocked()
        try:
            write_private_json(DONE_HISTORY_PATH, {"version": 1, "accounts": done_history})
        except Exception:
            pass


# Two tweets in a row that would not open: the browser is closed for a while, then the task goes back
# to the first of them. The first time for 3.5 minutes, the second time for 1 minute; the third time
# the task stops (X is likely not letting this account open tweets now).
TWEET_FAIL_PAUSES = (210, 60)


def open_task_tweet(page, url: str, skip_if_on):
    """Open a task's tweet with two tries. Returns (opened path or None, reason)."""
    opened, reason = open_status_page(page, url, skip_if_on)
    if not opened and reason != "gone":
        opened, reason = open_status_page(page, url, skip_if_on)
    return opened, reason


class TweetsKeptFailing(Exception):
    """Two tweets in a row would not open a third time in one task, so it stops. results: what it did
    before (with the two that would not open); at: the number of the tweet it stopped at (from 1)."""

    def __init__(self, results: list[dict], at: int):
        super().__init__("تعذّر فتح التغريدات ثلاث مرات")
        self.results = results
        self.at = at


class FailedTweets:
    """The tweets of a task that would not open (a deleted one does not count). Two in a row that would
    not open close the browser for a pause, then the task goes back to the first of them: the first
    pause is TWEET_FAIL_PAUSES[0] seconds, the second TWEET_FAIL_PAUSES[1]; the third time, the task
    stops."""

    def __init__(self):
        self.last: int | None = None   # the tweet tried before, when it would not open
        self.pauses = 0                # the pauses this task has had

    def opened(self) -> None:
        self.last = None

    def failed(self, index: int) -> int | None:
        """This tweet would not open. Returns the first of the two in a row that would not (to go back to
        after a pause), or None to go on."""
        before, self.last = self.last, index
        if before is None:
            return None
        self.last = None
        return before

    def next_pause(self) -> int | None:
        """How many seconds the next pause lasts; None when the task has had them all and stops."""
        if self.pauses >= len(TWEET_FAIL_PAUSES):
            return None
        self.pauses += 1
        return TWEET_FAIL_PAUSES[self.pauses - 1]


def pause_after_failures(should_stop=None, on_progress=None, total: int = 0, after_reopen=None,
                         seconds: int = TWEET_FAIL_PAUSES[0], phase: str = "pause"):
    """Close the browser for seconds, then reopen it. Returns the new page, or None when the task was
    stopped during the wait (the browser then stays closed) or the browser cannot be reopened here.
    phase: "pause" for the first pause, "pause_again" for the next one (said on the page)."""

    def wait_closed() -> bool:
        end = time.monotonic() + seconds
        shown = None
        while (left := math.ceil(end - time.monotonic())) > 0:
            if should_stop and should_stop():
                return False
            if on_progress and (shown is None or shown - left >= 5):
                on_progress(left, total, phase)
                shown = left
            time.sleep(min(1.0, max(0.0, end - time.monotonic())))
        if on_progress:
            on_progress(0, total, phase)
        return True

    new_page = restart_browser(wait_closed)
    if new_page is not None and after_reopen:
        after_reopen(new_page)
    return new_page


FAST_ACTION_JS = r"""
async ({tweetId, actions}) => {
  if (!document.querySelector(".r-4ny6nl")) {
    document.body.insertAdjacentHTML("beforeend", '<svg viewBox="0 0 24 24" class="r-4ny6nl" aria-hidden="true" style="position:absolute;width:0;height:0;overflow:hidden"><g><path d="M18.244 2.25h3.308l-7.227 8.26 8.502 11.24H16.17l-5.214-6.817L4.99 21.75H1.68l7.73-8.835L1.254 2.25H8.08l4.713 6.231zm-1.161 17.52h1.833L7.084 4.126H5.117z"></path><path d="M 10,30 C 122,187 104,187 103,126 h 138 s 227,202 174,135 C 152,101 34,196 34,87 h 6 s 226,188 106,153 C 231,147 29,174 201,196 h 204 s 228,148 25,98 C 50,176 119,37 179,166 h 238 s 165,79 149,248 C 174,109 209,150 145,241 h 147 s 232,158 29,130 C 93,223 109,131 25,248 h 32 s 0,188 126,131 C 60,243 17,86 23,33 h 192 s 126,253 172,188 C 126,73 139,14 3,216 h 30 s 90,215 111,153 C 155,162 193,46 245,226 h 92 s 191,137 89,230 C 248,58 105,73 70,150 h 125 s 16,137 172,157 C 95,36 92,165 130,133 h 40 s 77,193 26,205 C 178,240 72,243 224,186 h 119 s 90,85 129,109 C 105,22 118,126 102,5 h 150 s 31,50 184,95 C 25,0 253,76 191,143 h 46 s 237,163 152,173 C 188,70 200,28 131,107 h 173 s 154,236 38,62 C 108,128 158,54 218,65 h 200 s 231,231 210,236" fill="#1d9bf008"></path></g></svg>');
  }
  const bearer = "AAAAAAAAAAAAAAAAAAAAANRILgAAAAAAnNwIzUejRCOuH5E6I8xnZz4puTs%3D1Zv7ttfk8LF81IUq16cHjhLTvJu4FA33AGWWjCpTnA";
  const ops = {
    like: ["FavoriteTweet", "lI07N6Otwv1PhnEgXILM7A"],
    repost: ["CreateRetweet", "mbRO74GrOvSfRcJnlMapnQ"],
    bookmark: ["CreateBookmark", "aoDbu3RHznuiSkQ9aNM67Q"]
  };
  const OPEN_TEMPLATES = {"TweetDetail":{"id":"dQDdKtt882nl-Km98FJGSQ","variables":"{\"focalTweetId\":\"2120842815139623164\",\"with_rux_injections\":false,\"rankingMode\":\"Relevance\",\"includePromotedContent\":true,\"withCommunity\":true,\"withQuickPromoteEligibilityTweetFields\":true,\"withBirdwatchNotes\":true,\"withVoice\":true}","features":"{\"rweb_video_screen_enabled\":false,\"rweb_cashtags_enabled\":true,\"profile_label_improvements_pcf_label_in_post_enabled\":true,\"responsive_web_profile_redirect_enabled\":true,\"rweb_tipjar_consumption_enabled\":false,\"verified_phone_label_enabled\":false,\"creator_subscriptions_tweet_preview_api_enabled\":true,\"responsive_web_graphql_timeline_navigation_enabled\":true,\"premium_content_api_read_enabled\":false,\"communities_web_enable_tweet_community_results_fetch\":true,\"c9s_tweet_anatomy_moderator_badge_enabled\":true,\"responsive_web_grok_analyze_button_fetch_trends_enabled\":false,\"responsive_web_grok_analyze_post_followups_enabled\":true,\"rweb_cashtags_composer_attachment_enabled\":true,\"responsive_web_jetfuel_frame\":true,\"rweb_sports_post_context_enabled\":true,\"x_elections_post_context_enabled\":true,\"responsive_web_grok_share_attachment_enabled\":true,\"responsive_web_grok_annotations_enabled\":true,\"articles_preview_enabled\":true,\"responsive_web_edit_tweet_api_enabled\":true,\"rweb_conversational_replies_downvote_enabled\":false,\"graphql_is_translatable_rweb_tweet_is_translatable_enabled\":true,\"view_counts_everywhere_api_enabled\":true,\"longform_notetweets_consumption_enabled\":true,\"responsive_web_twitter_article_tweet_consumption_enabled\":true,\"content_disclosure_indicator_enabled\":true,\"content_disclosure_ai_generated_indicator_enabled\":true,\"responsive_web_grok_show_grok_translated_post\":true,\"responsive_web_grok_analysis_button_from_backend\":true,\"post_ctas_fetch_enabled\":false,\"freedom_of_speech_not_reach_fetch_enabled\":true,\"standardized_nudges_misinfo\":true,\"tweet_with_visibility_results_prefer_gql_limited_actions_policy_enabled\":true,\"longform_notetweets_rich_text_read_enabled\":true,\"longform_notetweets_inline_media_enabled\":false,\"responsive_web_nested_quote_preview_enabled\":true,\"responsive_web_grok_image_annotation_enabled\":true,\"responsive_web_grok_imagine_annotation_enabled\":true,\"responsive_web_made_on_x_label_enabled\":false,\"responsive_web_grok_community_note_auto_translation_is_enabled\":true,\"responsive_web_enhance_cards_enabled\":false}","fieldToggles":"{\"withPayments\":false,\"withDmBlocks\":false,\"withArticleRichContentState\":true,\"withArticlePlainText\":false,\"withArticleSummaryText\":true,\"withArticleVoiceOver\":true,\"withGrokAnalyze\":false,\"withDisallowedReplyControls\":false}"},"TweetResultByRestId":{"id":"U8lc5aomF5krJzZ9vJ9wxg","variables":"{\"tweetId\":\"2120842815139623164\",\"includePromotedContent\":true,\"withBirdwatchNotes\":true,\"withVoice\":true,\"withCommunity\":true}","features":"{\"creator_subscriptions_tweet_preview_api_enabled\":true,\"premium_content_api_read_enabled\":false,\"communities_web_enable_tweet_community_results_fetch\":true,\"c9s_tweet_anatomy_moderator_badge_enabled\":true,\"responsive_web_grok_analyze_button_fetch_trends_enabled\":false,\"responsive_web_grok_analyze_post_followups_enabled\":true,\"rweb_cashtags_composer_attachment_enabled\":true,\"responsive_web_jetfuel_frame\":true,\"rweb_sports_post_context_enabled\":true,\"x_elections_post_context_enabled\":true,\"responsive_web_grok_share_attachment_enabled\":true,\"responsive_web_grok_annotations_enabled\":true,\"articles_preview_enabled\":true,\"responsive_web_edit_tweet_api_enabled\":true,\"rweb_conversational_replies_downvote_enabled\":false,\"graphql_is_translatable_rweb_tweet_is_translatable_enabled\":true,\"view_counts_everywhere_api_enabled\":true,\"longform_notetweets_consumption_enabled\":true,\"responsive_web_twitter_article_tweet_consumption_enabled\":true,\"content_disclosure_indicator_enabled\":true,\"content_disclosure_ai_generated_indicator_enabled\":true,\"responsive_web_grok_show_grok_translated_post\":true,\"responsive_web_grok_analysis_button_from_backend\":true,\"post_ctas_fetch_enabled\":false,\"rweb_cashtags_enabled\":true,\"freedom_of_speech_not_reach_fetch_enabled\":true,\"standardized_nudges_misinfo\":true,\"tweet_with_visibility_results_prefer_gql_limited_actions_policy_enabled\":true,\"longform_notetweets_rich_text_read_enabled\":true,\"longform_notetweets_inline_media_enabled\":false,\"profile_label_improvements_pcf_label_in_post_enabled\":true,\"responsive_web_profile_redirect_enabled\":true,\"rweb_tipjar_consumption_enabled\":false,\"verified_phone_label_enabled\":false,\"responsive_web_nested_quote_preview_enabled\":true,\"responsive_web_grok_image_annotation_enabled\":true,\"responsive_web_grok_imagine_annotation_enabled\":true,\"responsive_web_made_on_x_label_enabled\":false,\"responsive_web_grok_community_note_auto_translation_is_enabled\":true,\"responsive_web_graphql_timeline_navigation_enabled\":true}","fieldToggles":"{\"withArticleRichContentState\":true,\"withArticlePlainText\":false,\"withArticleSummaryText\":true,\"withArticleVoiceOver\":true,\"withPayments\":false}"}};
  const started = Date.now();
  while (!self.webpackChunk_twitter_responsive_web && Date.now() - started < 8000) {
    await new Promise((done) => setTimeout(done, 40));
  }
  const chunks = self.webpackChunk_twitter_responsive_web;
  if (!chunks) return {};
  const req = await new Promise((resolve) => {
    chunks.push([["ggfast"], {}, (got) => resolve(got)]);
  });
  let sign = null;
  try {
    let chunkId = 59924;
    let modId = 564498;
    for (const chunk of chunks) {
      const mods = chunk && chunk[1];
      if (!mods) continue;
      for (const fn of Object.values(mods)) {
        let source = "";
        try { source = Function.prototype.toString.call(fn); } catch (error) { continue; }
        if (source.indexOf("x-client-transaction-id") < 0) continue;
        const match = source.match(/\.e\((\d+)\)\.then\(\(\)=>[A-Za-z]\((\d+)\)\)\.then\([A-Za-z]=>[A-Za-z]\([A-Za-z]\.default\(\)\)\)/);
        if (match) { chunkId = Number(match[1]); modId = Number(match[2]); }
      }
    }
    const factory = await req.e(chunkId).then(() => req(modId));
    sign = await factory.default();
  } catch (error) {}
  const ct0 = decodeURIComponent((document.cookie.match(/(?:^|; )ct0=([^;]+)/) || [])[1] || "");
  if (!ct0) return {};
  const lang = ((document.documentElement && document.documentElement.lang) || navigator.language || "en").slice(0, 2);
  const signedHeaders = async (path, method) => {
    let tx = "";
    if (sign) {
      for (let attempt = 0; attempt < 12 && !tx; attempt++) {
        try { tx = await sign(path, method); }
        catch (error) { await new Promise((done) => setTimeout(done, 60)); }
      }
    }
    const headers = {
      authorization: "Bearer " + bearer,
      "x-csrf-token": ct0,
      "x-twitter-auth-type": "OAuth2Session",
      "x-twitter-active-user": "yes",
      "x-twitter-client-language": lang
    };
    if (tx) headers["x-client-transaction-id"] = tx;
    return headers;
  };
  const startOpen = async (name) => {
    const spec = OPEN_TEMPLATES[name];
    if (!spec) return null;
    const variables = JSON.parse(spec.variables);
    if (variables.focalTweetId) variables.focalTweetId = String(tweetId);
    if (variables.tweetId) variables.tweetId = String(tweetId);
    const path = "/i/api/graphql/" + spec.id + "/" + name;
    const url = new URL("https://x.com" + path);
    url.searchParams.set("variables", JSON.stringify(variables));
    url.searchParams.set("features", spec.features);
    if (spec.fieldToggles) url.searchParams.set("fieldToggles", spec.fieldToggles);
    const headers = await signedHeaders(path, "GET");
    fetch(url, {method: "GET", credentials: "include", headers}).catch(() => null);
  };
  await Promise.all(["TweetDetail", "TweetResultByRestId"].map((name) => startOpen(name).catch(() => null)));
  const out = {};
  let sent = false;
  for (const action of actions) {
    const pair = ops[action];
    if (!pair) continue;
    if (sent) await new Promise((done) => setTimeout(done, 300 + Math.floor(Math.random() * 501)));
    sent = true;
    const name = pair[0];
    const queryId = pair[1];
    const path = "/i/api/graphql/" + queryId + "/" + name;
    const variables = action === "repost" ? {tweet_id: String(tweetId), dark_request: false} : {tweet_id: String(tweetId)};
    const headers = await signedHeaders(path, "POST");
    headers["content-type"] = "application/json";
    try {
      const response = await fetch("https://x.com" + path, {
        method: "POST",
        credentials: "include",
        headers,
        body: JSON.stringify({variables, queryId})
      });
      const raw = await response.text();
      const already = /already|duplicate|327|139/i.test(raw);
      let errors = [];
      try { errors = (JSON.parse(raw).errors) || []; } catch (error) {}
      const ok = (response.status === 200 && errors.length === 0) || already;
      out[action] = {ok, already, error: (errors[0] && errors[0].message) || ("HTTP " + response.status)};
    } catch (error) {
      out[action] = {ok: false, error: String(error).slice(0, 120)};
    }
  }
  return out;
}
"""


def pause_span(low: float, high: float, should_stop=None) -> None:
    """Wait a random gap. Returns early when the task is stopped."""
    end = time.monotonic() + random.uniform(low, high)
    while time.monotonic() < end:
        if should_stop and should_stop():
            return
        time.sleep(min(0.1, max(0.0, end - time.monotonic())))


def apply_actions_immediately(page, url: str, actions: list[str]) -> dict[str, str]:
    """Go to the tweet address only, then send the open requests and the buttons.
    The tweet card is not waited for."""
    match = re.search(r"status/(\d{6,25})", url or "")
    if not match:
        return {}
    status_id = match.group(1)
    wanted = [action for action in actions if action in {"repost", "like", "bookmark"}]
    if not wanted:
        return {}
    trace_click("تنفيذ مباشر: طلب الفتح ثم الزر دون انتظار ظهور التغريدة")
    try:
        page.goto(f"https://x.com/i/web/status/{status_id}", wait_until="commit", timeout=20_000)
    except Exception as exc:
        if browser_closed_error(exc):
            raise
        trace_click("تنفيذ مباشر: تعذّر فتح العنوان " + type(exc).__name__)
        return {}
    try:
        payload = page.evaluate(FAST_ACTION_JS, {"tweetId": status_id, "actions": wanted}) or {}
    except Exception as exc:
        if browser_closed_error(exc):
            raise
        trace_click("تنفيذ مباشر فشل: " + type(exc).__name__)
        return {}
    outcome: dict[str, str] = {}
    for action in wanted:
        row = payload.get(action) if isinstance(payload, dict) else None
        if not isinstance(row, dict) or not row.get("ok"):
            trace_click(f"تنفيذ مباشر {action} لم يقبل: {(row or {}).get('error') or 'بلا رد'}")
            continue
        outcome[action] = "مفعّل مسبقًا — تم التجاوز" if row.get("already") else "تم التنفيذ"
    if outcome:
        trace_click("تنفيذ مباشر: " + "، ".join(f"{key}={value}" for key, value in outcome.items()))
    return outcome


# ---------------------------------------------------------------------------- إعادة المحاولة للفاشلة
# مهمة اكتملت وفيها إجراءات فشلت على بعض التغريدات: «إعادة المحاولة للفاشلة» تبدأ مهمة جديدة على نفس الحساب
# بتلك التغريدات وحدها، ولكل تغريدة الإجراءات التي فشلت عليها فقط (item["only"]).
# الرتويت والإعجاب والمرجعية آمنة الإعادة دائمًا: تُقرأ حالة الزر قبل النقر فلا يُلغى ما نجح. أما التعليق فلا
# يُعاد إلا إن فشل قبل إرساله، حتى لا يُنشر ردّان على التغريدة نفسها.
COMMENT_RETRY_SAFE = (
    "تعذر فتح التغريدة", "تعذر العثور على المنشور", "لم يُرجع النموذج تعليقًا صالحًا", "لم يظهر مربع كتابة الرد",
    "زر النشر بقي معطّلًا", "لم تُفتح التغريدة في الوقت المناسب", "الحساب وصل حد الردود مؤقتًا",
)


def item_actions(item: dict, actions: list[str]) -> list[str]:
    """The actions to take on this tweet: all of the task's, or in a retry of the failed only those that failed."""
    only = item.get("only") if isinstance(item, dict) else None
    if isinstance(only, list):
        return [action for action in actions if action in only]
    return list(actions)


def action_failed(note: str) -> bool:
    """As the page counts it: not done, and not skipped (on already, done before, deleted, not available)."""
    note = str(note or "")
    return note != "تم التنفيذ" and not any(word in note for word in ("مفعّل", "تخطي", "تجاوز"))


def action_retryable(action: str, note: str) -> bool:
    if not action_failed(note):
        return False
    if action != "comment":
        return True
    note = str(note or "")
    if note.startswith("تعذر نشر التعليق: "):
        note = note[len("تعذر نشر التعليق: "):]
    return note in COMMENT_RETRY_SAFE or note.startswith("تعذر توليد التعليق") or note.startswith("تعذر الاتصال")


def failed_retry_items(job: dict) -> list[dict]:
    """The finished task's tweets with an action to retry, each with only those actions."""
    out: list[dict] = []
    seen: set[str] = set()
    for row in job.get("results") or []:
        if not isinstance(row, dict):
            continue
        url = str(row.get("url") or "")
        only = [action for action, note in (row.get("actions") or {}).items()
                if action in ALLOWED_ACTIONS and action_retryable(action, note)]
        if not only or not url or url in seen or tweet_is_ignored(url):
            continue
        seen.add(url)
        out.append({"url": url, "text": str(row.get("text") or ""), "only": only})
    return out


def failed_retry_count(job: dict) -> int:
    if job.get("status") != "done" or job.get("retried_by") or (job.get("kind") or "") != "execute":
        return 0
    return len(failed_retry_items(job))


def visit_and_apply(page, items: list[dict], task_actions: list[str], on_progress=None, on_snapshot=None, should_stop=None, account: str = "") -> list[dict]:
    results: list[dict] = []
    total = len(items)
    failures = FailedTweets()
    # Where each tweet's result starts in results: going back after a pause drops them from there on.
    starts: dict[int, int] = {}
    if on_progress:
        on_progress(0, total, "act")
    index = -1
    acted = False
    while index + 1 < total:
        index += 1
        item = items[index]
        actions = item_actions(item, task_actions)      # (all the task's, or only those that failed on it before)
        if should_stop and should_stop():
            break
        starts[index] = len(results)
        result = {"url": item.get("url", ""), "text": item.get("text", ""), "actions": {}}
        status_id = tweet_status_id(str(item.get("url") or ""))
        if already_done_recently(account, status_id, actions):
            # Done by this account in the last 8 hours: skip without opening the tweet.
            result["actions"] = {key: "سبق التفاعل خلال ٨ ساعات — تم التخطي" for key in actions}
            results.append(result)
            if on_snapshot:
                on_snapshot(list(results))
            if on_progress:
                on_progress(index + 1, total, "act")
            continue
        if acted:
            pause_span(0.15, 0.4, should_stop)
            if should_stop and should_stop():
                break
        acted = True
        try:
            opened, reason = open_task_tweet(page, str(item.get("url") or ""), actions)
        except Exception as exc:
            if browser_closed_error(exc):
                if on_snapshot and results:
                    on_snapshot(list(results))
                raise BrowserClosed() from exc
            raise
        if opened or reason == "gone":
            failures.opened()
        else:
            back = failures.failed(index)
            new_page = None
            if back is not None:
                seconds = failures.next_pause()
                if seconds is None:
                    # A third time: the task stops here, with what it did (these two would not open).
                    result["actions"] = {key: "تعذر فتح التغريدة" for key in actions}
                    results.append(result)
                    if on_snapshot:
                        on_snapshot(list(results))
                    raise TweetsKeptFailing(results, index + 1)
                new_page = pause_after_failures(should_stop, on_progress, total, None, seconds,
                                                "pause" if failures.pauses == 1 else "pause_again")
            if new_page is not None:
                # Back to the first of the two that would not open; what was recorded from it on goes.
                page = new_page
                del results[starts[back]:]
                if on_snapshot:
                    on_snapshot(list(results))
                if on_progress:
                    on_progress(back, total, "act")
                index = back - 1
                continue
        if not opened:
            note = "محذوفة — تم التخطي" if reason == "gone" else "تعذر فتح التغريدة"
            result["actions"] = {key: note for key in actions}
            results.append(result)
            if on_snapshot:
                on_snapshot(list(results))
            if on_progress:
                on_progress(index + 1, total, "act")
            continue
        if tweet_is_ignored("https://x.com" + opened):
            # The opened tweet's author is an ignored account: take no action and leave no trace.
            forget_collected("https://x.com" + opened)
            if on_progress:
                on_progress(index + 1, total, "act")
            continue
        result["url"] = "https://x.com" + opened
        try:
            already_on = reason == "already_on" or all_actions_already_on(page, opened, actions)
        except Exception as exc:
            if browser_closed_error(exc):
                raise BrowserClosed() from exc
            already_on = False
        if already_on:
            result["actions"] = {key: "مفعّل مسبقًا — تم التجاوز" for key in actions}
            remember_done(account, status_id or tweet_status_id(opened), result["actions"])
            results.append(result)
            if on_snapshot:
                on_snapshot(list(results))
            if on_progress:
                on_progress(index + 1, total, "act")
            continue
        close_popups(page)
        try:
            result["actions"] = apply_actions_on_path(page, opened, actions)
        except Exception as exc:
            if browser_closed_error(exc):
                raise BrowserClosed() from exc
            result["actions"] = {key: "تعذر تنفيذ الإجراء بعد فتح التغريدة" for key in actions}
        remember_done(account, status_id or tweet_status_id(opened), result["actions"])
        count_successes(result["actions"], account)
        results.append(result)
        if on_snapshot:
            on_snapshot(list(results))
        if on_progress:
            on_progress(index + 1, total, "act")
    return results


def fetch_group_names(auth_token: str, pin: str, settle: bool = False, settle_seconds: int = 10) -> tuple[list[str], str | None]:
    def work(page):
        if not ensure_logged_in(page):
            return [], "الجلسة غير مسجّلة الدخول."
        handle = read_session_username(page)
        if handle:
            remember_session(auth_token, handle, pin)
        error = open_chat(page, pin)
        if error:
            return [], error
        show_groups_only(page)
        if settle:
            page.wait_for_timeout(max(1, min(120, int(settle_seconds))) * 1000)
        names = collect_groups(page)
        if not names:
            return [], "فُتحت الدردشة لكن لم تظهر قروبات."
        return names, None
    try:
        return run_on_browser(auth_token, work)
    except Exception:
        return [], "تعذّر فتح المتصفح."


class JobStopped(Exception):
    pass


# Arguments of each group task, kept in memory so the retry button can continue it.
job_run_args: dict[str, tuple] = {}


class BrowserClosed(Exception):
    """Chromium died or the tab was closed. The job can reopen and continue."""


def browser_closed_error(exc: BaseException) -> bool:
    text = str(exc).lower()
    return (
        "has been closed" in text
        or "target closed" in text
        or "connection closed" in text
        or "browser closed" in text
    )


def job_cancelled(job_id: str) -> bool:
    with jobs_lock:
        job = jobs.get(job_id) or {}
        return bool(job.get("cancel"))


# Each account's line of tasks. A task added while its account is working waits («في الانتظار») and starts
# by itself when the ones before it end, first come first served. Accounts do not wait for one another.
MAX_TASKS_PER_ACCOUNT = 10          # in one account's line: the working one and those waiting
account_turns = threading.Condition()
account_lines: dict[str, deque] = {}


def account_line_join(auth_digest: str, job_id: str) -> int:
    """Put a task at the end of its account's line. Returns how many tasks are before it (0: its turn now)."""
    with account_turns:
        line = account_lines.setdefault(auth_digest, deque())
        if job_id not in line:
            line.append(job_id)
        return list(line).index(job_id)


def account_line_size(auth_digest: str) -> int:
    with account_turns:
        return len(account_lines.get(auth_digest) or ())


def account_line_leave(auth_digest: str, job_id: str) -> None:
    with account_turns:
        line = account_lines.get(auth_digest)
        if line is not None:
            try:
                line.remove(job_id)
            except ValueError:
                pass
        account_turns.notify_all()


def waiting_message(ahead: int) -> str:
    if ahead <= 1:
        return "في الانتظار: تبدأ تلقائيًا بعد انتهاء المهمة السابقة على هذا الحساب."
    if ahead == 2:
        return "في الانتظار: تبدأ تلقائيًا بعد انتهاء مهمتين قبلها على هذا الحساب."
    return f"في الانتظار: تبدأ تلقائيًا بعد انتهاء {ahead} مهام قبلها على هذا الحساب."


def wait_account_turn(auth_digest: str, job_id: str) -> bool:
    """Wait until the task is first in its account's line. False when it was stopped while it waited."""
    shown = None
    while True:
        with account_turns:
            line = account_lines.setdefault(auth_digest, deque())
            if job_id not in line:
                line.append(job_id)
            ahead = list(line).index(job_id)
        if ahead == 0:
            return True
        if job_cancelled(job_id):
            account_line_leave(auth_digest, job_id)
            return False
        if ahead != shown:
            publish_job(job_id, phase="queue", message=waiting_message(ahead))
            shown = ahead
        with account_turns:
            account_turns.wait(1.0)


def run_group_job_in_turn(job_id: str, auth_digest: str, start_phase: str, start_message: str, args: tuple) -> None:
    """A group task in its account's line: it waits for its turn, runs, then lets the next one start."""
    with as_account(profile_key(str(args[0]) if args else "")):      # (all it prints is its account's)
        _run_group_job_in_turn(job_id, auth_digest, start_phase, start_message, args)


def _run_group_job_in_turn(job_id: str, auth_digest: str, start_phase: str, start_message: str, args: tuple) -> None:
    # (a waiting task counts as work for the app too, so it stays working in the background between two tasks)
    app_task_running(True)
    try:
        if not wait_account_turn(auth_digest, job_id):
            publish_job(job_id, status="done", success=False, message="أُلغيت المهمة قبل أن يأتي دورها.")
            return
        with jobs_lock:
            waited = (jobs.get(job_id) or {}).get("phase") == "queue"
        if waited:
            publish_job(job_id, phase=start_phase, message=start_message)
        run_group_job(job_id, *args)
    finally:
        account_line_leave(auth_digest, job_id)
        app_task_running(False)


def account_busy(auth_digest: str) -> bool:
    """Whether the account has a task working or waiting now."""
    with jobs_lock:
        return any(job.get("status") == "running" and job.get("kind") == "execute" and job.get("auth_digest") == auth_digest
                   for job in jobs.values())


DEFAULT_GROUP_WAIT_SECONDS = 8
# «روابط التغريدات»: a task on tweets pasted on the page, instead of opening a group and collecting.
# The page sends each tweet as "handle/id", or "id" when its link has no author's name.
MAX_TWEET_LINKS = MAX_REPOSTS_REQUEST
LINKS_TASK_NAME = "روابط التغريدات"


def tweet_links_from(entries) -> list[dict]:
    """The pasted tweets as the same {"url", "text"} rows a group's collecting gives: each tweet
    once, in the order pasted."""
    items: list[dict] = []
    seen: set[str] = set()
    for entry in entries if isinstance(entries, list) else []:
        match = re.fullmatch(r"(?:([A-Za-z0-9_]{1,15})/)?(\d{6,25})", str(entry or "").strip())
        if not match or match.group(2) in seen:
            continue
        handle, status_id = match.group(1) or "", match.group(2)
        seen.add(status_id)
        if handle.lower() in _HANDLE_NOT_A_USER:
            handle = ""
        url = f"https://x.com/{handle}/status/{status_id}" if handle else f"https://x.com/i/web/status/{status_id}"
        items.append({"url": url, "text": ""})
    return items


def run_group_job(job_id: str, auth_token: str, pin: str, group_name: str, requested_count: int, actions: list[str], gemini_api_key: str = "", gemini_model: str = "", stop_id: str = "", group_wait_s: int = DEFAULT_GROUP_WAIT_SECONDS, reply_voice: str = DEFAULT_REPLY_VOICE, tweet_links: list[dict] | None = None) -> None:
    def on_progress(done: int, requested: int, phase: str) -> None:
        if job_cancelled(job_id):
            raise JobStopped
        if phase == "collect":
            if stop_id:
                publish_job(job_id, phase="collect", collected=done, requested=0, message=f"جُمعت {done}. التمرير مستمر حتى التغريدة المحددة.")
            else:
                publish_job(job_id, phase="collect", collected=done, requested=requested, message=f"جُمعت {done} من {requested}.")
        elif phase == "seek":
            publish_job(job_id, phase="collect", collected=0, requested=0, message=f"يبحث عن التغريدة المحددة. الخطوة {done}، وما زال يحمّل الأقدم.")
        elif phase == "act":
            publish_job(job_id, phase="act", done=done, collected=done, requested=requested, message=f"تنفيذ {done} من {requested}.")
        elif phase in ("pause", "pause_again"):
            # Two tweets in a row would not open: the browser is closed, done = seconds left. The second
            # time ("pause_again") is the last: a third time stops the task.
            again = phase == "pause_again"
            if done > 0:
                publish_job(job_id, phase="act", message=(
                    f"تعذّر فتح تغريدتين متتاليتين{' مرة أخرى' if again else ''}، فأُغلق المتصفح. المتابعة منهما بعد {done // 60}:{done % 60:02d}."
                    + (" إن تعذّر مرة ثالثة تتوقف المهمة." if again else "")))
            else:
                publish_job(job_id, phase="act", message="انتهى الانتظار. إعادة فتح المتصفح والمتابعة من التغريدتين…")
        else:
            publish_job(job_id, phase=phase, message="فتح الدردشة والقروب…")

    job_run_args[job_id] = (auth_token, pin, group_name, requested_count, actions, gemini_api_key, gemini_model, stop_id, group_wait_s, reply_voice, tweet_links)

    def work(page):
        try:
            # Pick up any change to the ignored-accounts list (the owner sets it in «توزيع البرنامج»,
            # which shares this folder; a user's copy keeps it current from its check-in).
            load_skip_users()
            with jobs_lock:
                saved = jobs.get(job_id) or {}
                items = list(saved["items"]) if isinstance(saved.get("items"), list) else []
                prefix = list(saved["results"]) if isinstance(saved.get("results"), list) else []
            if items and len(prefix) > len(items):
                prefix = prefix[: len(items)]
            if not items and tweet_links:
                # «روابط التغريدات»: the tweets were pasted on the page, so no chat, no group and no
                # collecting: check the session, then straight to the actions.
                publish_job(job_id, phase="prepare", message="التحقق من الجلسة…")
                if not ensure_logged_in(page):
                    publish_job(job_id, status="done", success=False, message="فشل التحقق: الجلسة غير مسجّلة الدخول.")
                    return
                accept_cookies(page)
                handle = read_session_username(page)
                if handle:
                    remember_session(auth_token, handle, pin)
                # A tweet by an ignored account leaves no trace here either (one whose link has no
                # author's name is caught once it is open, as for a group).
                items = [dict(item) for item in tweet_links if not tweet_is_ignored(str(item.get("url") or ""))]
                if not items:
                    publish_job(job_id, status="done", success=False, message="لا توجد تغريدات للتنفيذ.")
                    return
                prefix = []
                publish_job(job_id, phase="act", collected=len(items), requested=len(items), items=items,
                            message=f"بدأ تنفيذ الإجراءات على {len(items)} تغريدة من الروابط.")
            elif not items:
                publish_job(job_id, phase="login", message="التحقق من الجلسة ثم فتح القروب مباشرة…")
                if not ensure_logged_in(page):
                    publish_job(job_id, status="done", success=False, message="فشل التحقق: الجلسة غير مسجّلة الدخول.")
                    return
                accept_cookies(page)
                handle = read_session_username(page)
                if handle:
                    remember_session(auth_token, handle, pin)
                publish_job(job_id, status="done", success=False, message="التجميع غير موجود في هذه النسخة.")
                return
            elif not ensure_logged_in(page):
                publish_job(job_id, status="done", success=False, message="فشل التحقق: الجلسة غير مسجّلة الدخول.")
                return
            else:
                publish_job(job_id, phase="act", requested=len(items), collected=len(items), done=len(prefix), message=f"استئناف التنفيذ من {len(prefix)} من {len(items)}.")
            stopped_at = 0   # the tweet the task stopped at when two kept failing to open
            if len(prefix) >= len(items):
                results = prefix
            else:
                pending = items[len(prefix) :]

                def snapshot(rows: list[dict]) -> None:
                    merged = prefix + list(rows)
                    publish_job(
                        job_id, phase="act", done=len(merged), requested=len(items), collected=len(items),
                        results=merged, items=items, message=f"تنفيذ {len(merged)} من {len(items)}.",
                    )

                def on_act(done: int, requested: int, phase: str) -> None:
                    if phase in ("pause", "pause_again"):
                        on_progress(done, requested, phase)
                    else:
                        on_progress(len(prefix) + done, len(items), "act")

                try:
                    if "comment" in actions:
                        fresh = execute_comment_actions(
                            page, pending, actions, gemini_api_key, gemini_model, on_act,
                            lambda: job_cancelled(job_id), snapshot, profile_key(auth_token), reply_voice,
                        )
                    else:
                        fresh = visit_and_apply(page, pending, actions, on_act, snapshot, lambda: job_cancelled(job_id), profile_key(auth_token))
                except TweetsKeptFailing as stop:
                    fresh, stopped_at = stop.results, len(prefix) + stop.at
                results = prefix + fresh
                refine_collected_links(fresh)
            if stopped_at:
                publish_job(
                    job_id, status="done", success=False, phase="act", done=len(results), requested=len(items),
                    collected=len(items), results=results, items=items, actions=actions, username=group_name,
                    message=(f"توقفت المهمة عند التغريدة {stopped_at} من {len(items)}: تعذّر فتح تغريدتين متتاليتين ثلاث مرات "
                             f"(بعد انتظار ثلاث دقائق ونصف ثم دقيقة)، والأرجح أن X يمنع هذا الحساب من فتح التغريدات الآن."),
                )
                return
            if job_cancelled(job_id):
                publish_job(
                    job_id, status="done", success=False, phase="act", done=len(results), requested=len(items),
                    collected=len(items), message="تم إيقاف التنفيذ.",
                    results=results, items=items, actions=actions, username=group_name,
                )
                return
            publish_job(
                job_id, status="done", success=True, phase="act", done=len(results), requested=len(items),
                collected=len(items), message=f"اكتمل التنفيذ على {len(results)} تغريدة من {group_name}.",
                results=results, items=items, actions=actions, username=group_name,
            )
        except JobStopped:
            publish_job(job_id, status="done", success=False, message="تم إيقاف التنفيذ.")
            return
        except BrowserClosed:
            raise
        except Exception as exc:
            if browser_closed_error(exc):
                raise BrowserClosed() from exc
            app.logger.warning("group run failed")
            publish_job(job_id, status="done", success=False, message=str(exc) or "تعذّر تنفيذ إجراءات القروب.")
            raise
    # One attempt only. If anything fails, the task stops with a message and is not retried.
    live_task.job_id = job_id
    app_task_running(True)
    try:
        run_on_fresh_browser(auth_token, work)
    except BrowserClosed:
        with jobs_lock:
            job = jobs.get(job_id) or {}
            already_done = job.get("status") == "done"
        if not already_done:
            publish_job(
                job_id, status="done", success=False,
                message="توقف التنفيذ لأن المتصفح أُغلق. ما اكتمل قبل الإغلاق ما زال ظاهرًا.",
            )
    except Exception as exc:
        with jobs_lock:
            job = jobs.get(job_id) or {}
            already_done = job.get("status") == "done"
        if not already_done:
            app.logger.warning("group run failed")
            message = "أُغلق المتصفح أثناء العمل." if browser_closed_error(exc) else (str(exc) or "تعذّر تنفيذ إجراءات القروب.")
            publish_job(job_id, status="done", success=False, message=message)
    finally:
        live_task.job_id = ""
        app_task_running(False)
        with live_views_lock:
            live_views.pop(job_id, None)


def allow_attempt(client: str) -> bool:
    now = time.monotonic()
    with attempts_lock:
        q = attempts[client]
        while q and now - q[0] > ATTEMPT_WINDOW_SECONDS:
            q.popleft()
        if len(q) >= MAX_ATTEMPTS_PER_CLIENT:
            return False
        q.append(now)
        return True


def csrf_matches(submitted: str) -> bool:
    expected = session.get("csrf_token", "")
    return bool(expected) and hmac.compare_digest(str(submitted), expected)


def csrf_ok(data: dict) -> bool:
    return csrf_matches(str(data.get("csrf_token", "")))


def valid_auth_token(value: str) -> bool:
    return 20 <= len(value) <= 512


@app.before_request
def limit_request_size():
    if (request.content_length or 0) > SMALL_REQUEST_BYTES and request.endpoint not in ("group_run_endpoint", "support_upload_endpoint"):
        abort(413)


@app.after_request
def secure_response(response):
    response.headers["Cache-Control"] = "no-store, max-age=0"
    response.headers["Pragma"] = "no-cache"
    response.headers["X-Content-Type-Options"] = "nosniff"
    response.headers["Referrer-Policy"] = "no-referrer"
    response.headers["Content-Security-Policy"] = "default-src 'self'; img-src 'self' blob: https://pbs.twimg.com; style-src 'self' 'unsafe-inline'; script-src 'self' 'unsafe-inline'; font-src 'self'; connect-src 'self'; form-action 'self'; base-uri 'none'"
    return response


@app.after_request
def compress_response(response):
    """Big answers (a finished task's list, the page itself) go gzipped: a phone loads them in a
    fraction of the time."""
    if (
        response.status_code != 200
        or response.direct_passthrough
        or "Content-Encoding" in response.headers
        or "gzip" not in (request.headers.get("Accept-Encoding") or "").lower()
        or response.mimetype not in ("application/json", "text/html")
    ):
        return response
    body = response.get_data()
    if len(body) < 2048:
        return response
    response.set_data(gzip.compress(body, compresslevel=5))
    response.headers["Content-Encoding"] = "gzip"
    response.vary.add("Accept-Encoding")
    return response


@app.get("/healthz")
def health():
    return "ok", 200, {"Content-Type": "text/plain; charset=utf-8"}


@app.get("/")
def root():
    return redirect("/" + ACCESS_PATH, code=302)


@app.get("/<access_path>")
def login_page(access_path: str):
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    csrf_token = session.get("csrf_token")
    if not csrf_token:
        csrf_token = secrets.token_urlsafe(32)
        session["csrf_token"] = csrf_token
    response = make_response(render_template_string(
        PAGE, csrf_token=csrf_token, api_root="/" + ACCESS_PATH, app_version=shown_version(), owner_copy=is_owner_copy(), max_links=MAX_TWEET_LINKS,
        claude_here=key_typed_here(), claude_default=CLAUDE_DEFAULT_MODEL, control_on=control_configured(),
        content_ready=content_ready.is_set() or (CONTENT_FILE.is_file() if is_owner_copy() else bool(CONTENT_EMBEDDED)),
        tweets_in_content=content_shows_tweets, in_app=IN_APP, max_accounts=MAX_ACCOUNTS,
    ))
    return response


@app.post("/<access_path>/browser-login")
def browser_login_endpoint(access_path: str):
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    data = request.get_json(silent=True) or {}
    if not csrf_ok(data):
        return jsonify(success=False, message="انتهت صلاحية الصفحة. أعد تحميلها ثم حاول مجددًا."), 400
    if not IN_APP:
        return jsonify(success=False, message="تسجيل الدخول من المتصفح متاح داخل التطبيق."), 400
    try:
        message = start_manual_login()
    except Exception:
        app.logger.warning("manual login browser failed", exc_info=True)
        return jsonify(success=False, message="تعذّر فتح المتصفح. أعد المحاولة."), 502
    return jsonify(success=True, message=message or "سجّل الدخول في تبويب المتصفح، ثم ارجع إلى اللوحة واضغط تحقق.")


@app.post("/<access_path>/browser-session")
def browser_session_endpoint(access_path: str):
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    data = request.get_json(silent=True) or {}
    if not csrf_ok(data):
        return jsonify(success=False, message="انتهت صلاحية الصفحة. أعد تحميلها ثم حاول مجددًا."), 400
    token = manual_login_token()
    if not valid_auth_token(token):
        return jsonify(success=False, message="لم تكتمل جلسة المتصفح بعد.")
    return jsonify(success=True, auth_token=token)


@app.post("/<access_path>/verify-login")
def verify_login_endpoint(access_path: str):
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    data = request.get_json(silent=True) or {}
    if not csrf_ok(data):
        return jsonify(success=False, message="انتهت صلاحية الصفحة. أعد تحميلها ثم حاول مجددًا."), 400
    if not allow_attempt(request.remote_addr or "unknown"):
        return jsonify(success=False, message="تجاوزت عدد المحاولات المسموح به مؤقتًا. انتظر قليلًا ثم أعد المحاولة."), 429
    auth_token = str(data.get("auth_token", "")).strip()
    if not valid_auth_token(auth_token):
        return jsonify(success=False, message="أدخل auth_token صالحًا."), 400
    try:
        success, handle = verify_x_login(auth_token)
        if success:
            remember_session(auth_token, handle)
        if success and handle:
            message = f"تم التحقق بنجاح: هذه الجلسة تخص @{handle}."
        elif success:
            message = "تم التحقق من تسجيل الدخول، لكن تعذّر قراءة اسم الحساب. حُفظ الرمز ويمكن اختياره لاحقًا."
        else:
            message = "فشل التحقق: لم يظهر الحساب مسجّل الدخول. قد يكون الرمز غير صالح أو منتهيًا."
        return jsonify(success=success, message=message, username=handle)
    except Exception:
        app.logger.warning("X login verification failed (details suppressed)")
        return jsonify(success=False, message="تعذّر إكمال التحقق بسبب مشكلة في الاتصال أو تشغيل المتصفح."), 502
    finally:
        auth_token = ""


def write_private_json(path: Path, payload: dict, compact: bool = False) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    text = json.dumps(payload, ensure_ascii=False, separators=(",", ":")) if compact else json.dumps(payload, ensure_ascii=False, indent=2)
    temporary.write_text(text, encoding="utf-8")
    try:
        os.chmod(temporary, 0o600)
    except OSError:
        pass
    temporary.replace(path)
    try:
        os.chmod(path, 0o600)
    except OSError:
        pass


def read_private_json(path: Path) -> dict | None:
    try:
        loaded = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return None
    except (OSError, json.JSONDecodeError):
        if path.exists():
            broken = path.with_suffix(path.suffix + ".corrupt")
            path.replace(broken)
        return None
    return loaded if isinstance(loaded, dict) else None


# Ignored accounts. The owner sets a list of handles in «توزيع البرنامج» (stored beside g.py in
# data/skip_users.json); every user's copy takes the list on its check-in and caches it in the same
# file on its own server. A collected tweet whose author is on the list is dropped right after it is
# gathered — before it is opened — so it is never acted on and never appears anywhere in the result.
SKIP_USERS_PATH = DATA_DIR / "skip_users.json"
skip_users_lock = threading.Lock()
skip_users_cache: set[str] = set()
_HANDLE_NOT_A_USER = {"i", "web", "intent", "share", "home", "search", "messages", "notifications", "explore"}


def normalize_handle(value: str) -> str:
    """An X handle, lowercased, no leading @; "" when it is not a valid handle."""
    handle = (value or "").strip().lstrip("@").lower()
    return handle if re.fullmatch(r"[a-z0-9_]{1,15}", handle) else ""


def _clean_handles(handles) -> list[str]:
    seen = {h for h in (normalize_handle(x) for x in (handles or [])) if h}
    return sorted(seen)


def load_skip_users() -> None:
    data = read_private_json(SKIP_USERS_PATH) or {}
    users = data.get("users") if isinstance(data, dict) else []
    cleaned = _clean_handles(users if isinstance(users, list) else [])
    with skip_users_lock:
        skip_users_cache.clear()
        skip_users_cache.update(cleaned)


def store_skip_users(handles) -> list[str]:
    """Replace the ignored-accounts list, persist it only when it changed, and return it cleaned."""
    cleaned = _clean_handles(handles)
    with skip_users_lock:
        changed = set(cleaned) != skip_users_cache
        if changed:
            skip_users_cache.clear()
            skip_users_cache.update(cleaned)
    if changed:
        try:
            write_private_json(SKIP_USERS_PATH, {"users": cleaned})
        except OSError:
            pass
    return cleaned


def skip_users_list() -> list[str]:
    with skip_users_lock:
        return sorted(skip_users_cache)


def tweet_author_handle(url: str) -> str:
    """The author handle inside an x.com/<handle>/status/<id> link, or "" for a handle-less link."""
    match = re.search(r"(?:^|[^A-Za-z0-9_])([A-Za-z0-9_]{1,15})/status/\d", url or "")
    if match:
        handle = match.group(1).lower()
        if handle not in _HANDLE_NOT_A_USER:
            return handle
    return ""


def tweet_is_ignored(url: str) -> bool:
    """True when this tweet's author is an ignored account, so it must be skipped silently."""
    handle = tweet_author_handle(url)
    if not handle:
        return False
    with skip_users_lock:
        return handle in skip_users_cache


# «عرض التغريدات»: the tweets the tasks collected in the last 7 days. Each tweet is saved once, when it
# is first collected (its time and group); collecting it again does not add it again. It is kept 7
# days from then. The page sorts the tweets into days in the viewer's own time zone.
COLLECTED_PATH = DATA_DIR / "collected_tweets.json"
COLLECTED_KEEP_SECONDS = 7 * 24 * 3600
collected_lock = threading.Lock()
collected_tweets: dict[str, dict] = {}


def prune_collected_unlocked(now: float) -> bool:
    """Drop the tweets saved more than 7 days ago. True when any was dropped."""
    oldest = now - COLLECTED_KEEP_SECONDS
    gone = [status_id for status_id, row in collected_tweets.items() if row["at"] < oldest]
    for status_id in gone:
        del collected_tweets[status_id]
    return bool(gone)


def persist_collected_unlocked() -> None:
    try:
        write_private_json(COLLECTED_PATH, {"version": 2, "tweets": collected_tweets}, compact=True)
    except OSError:
        pass


def load_collected() -> None:
    data = read_private_json(COLLECTED_PATH) or {}
    rows = data.get("tweets") if isinstance(data.get("tweets"), dict) else {}
    loaded: dict[str, dict] = {}
    for status_id, row in rows.items():
        if not isinstance(row, dict) or not re.fullmatch(r"\d{6,25}", str(status_id)):
            continue
        try:
            if row.get("at") is not None:
                at = int(row["at"])
            else:
                # Saved by the first version, which kept every collection: the first one is the time.
                at = min(int(entry[0]) for entry in row.get("seen") or [])
        except (TypeError, ValueError, IndexError):
            continue
        group = row.get("group")
        if not group and isinstance(row.get("groups"), list) and row["groups"]:
            group = row["groups"][0]
        record = {
            "url": str(row.get("url") or "")[:300],
            "text": str(row.get("text") or "")[:300],
            "group": str(group or "")[:80],
            "at": at,
        }
        # «عرض الأكثر مشاهدة»: the view count from the last check, and when (views None: no count then).
        try:
            if row.get("views_at") is not None:
                record["views_at"] = int(row["views_at"])
                record["views"] = None if row.get("views") is None else max(0, int(row["views"]))
        except (TypeError, ValueError):
            record.pop("views_at", None)
        record.update(tweet_content(row))
        loaded[str(status_id)] = record
    with collected_lock:
        collected_tweets.clear()
        collected_tweets.update(loaded)
        if prune_collected_unlocked(time.time()) or any(isinstance(r, dict) and "seen" in r for r in rows.values()):
            persist_collected_unlocked()


def remember_collected(items: list[dict], group_name: str) -> None:
    """Save the tweets a task has just collected from a group, each only the first time (for
    «عرض التغريدات»). A tweet already saved is not saved again; only a missing text, or a link
    without the author's name, is filled in."""
    now = int(time.time())
    group = re.sub(r"\s+", " ", group_name or "").strip()[:80]
    changed = False
    with collected_lock:
        if prune_collected_unlocked(now):
            changed = True
        for item in items or []:
            url = str(item.get("url") or "")
            status_id = tweet_status_id(url)
            if not status_id:
                continue
            text = re.sub(r"\s+", " ", str(item.get("text") or "")).strip()
            text = "" if text == "تغريدة" else text[:300]
            row = collected_tweets.get(status_id)
            if row is None:
                collected_tweets[status_id] = {"url": url[:300], "text": text, "group": group, "at": now}
                changed = True
                continue
            if text and not row["text"]:
                row["text"] = text
                changed = True
            if tweet_author_handle(url) and not tweet_author_handle(row["url"]):
                row["url"] = url[:300]
                changed = True
        if changed:
            persist_collected_unlocked()


def forget_collected(url: str) -> None:
    """Remove a saved tweet: it turned out to be by an ignored account, which leaves no trace."""
    status_id = tweet_status_id(url)
    if not status_id:
        return
    with collected_lock:
        if collected_tweets.pop(status_id, None) is not None:
            persist_collected_unlocked()


def refine_collected_links(results: list[dict]) -> None:
    """After a task, give each saved tweet the link it really opened at (it has the author's name)."""
    changed = False
    with collected_lock:
        for result in results or []:
            url = str(result.get("url") or "")
            status_id = tweet_status_id(url)
            row = collected_tweets.get(status_id) if status_id else None
            if row and tweet_author_handle(url) and not tweet_author_handle(row["url"]):
                row["url"] = url[:300]
                changed = True
        if changed:
            persist_collected_unlocked()


# Once per copy, when it starts: the tweets it worked on lately put in «التغريدات المجموعة» as if they had
# been collected then, so a copy that has not collected any yet (it was updated since) has them on its page.
# From its tasks of the last day: each tweet a group task collected, with its text and group, at the
# task's time; then from the tweets its accounts acted on in the last 8 hours (kept to skip them), the
# ones not found there, at their first action. Their views and content are then asked for.
COLLECTED_FILLED_PATH = DATA_DIR / "collected_filled.json"


def fill_collected_from_history() -> int:
    """Add those tweets (the ones not saved yet) and ask for their views; how many were added."""
    if COLLECTED_FILLED_PATH.exists():
        return 0
    found: dict[str, dict] = {}
    with jobs_lock:
        tasks = [dict(job) for job in jobs.values()]
    for job in tasks:
        group = re.sub(r"\s+", " ", str(job.get("username") or "")).strip()[:80]
        if job.get("kind") != "execute" or group == LINKS_TASK_NAME or not isinstance(job.get("items"), list):
            continue
        try:
            at = int(float(job.get("created_at") or 0))
        except (TypeError, ValueError):
            continue
        for item in job["items"]:
            url = str(item.get("url") or "") if isinstance(item, dict) else ""
            status_id = tweet_status_id(url)
            if not status_id or not at:
                continue
            text = re.sub(r"\s+", " ", str(item.get("text") or "")).strip()
            text = "" if text == "تغريدة" else text[:300]
            row = found.get(status_id)
            if row is None or at < row["at"]:
                found[status_id] = {"url": url[:300], "text": text or (row or {}).get("text", ""), "group": group, "at": at}
            elif text and not row["text"]:
                row["text"] = text
    with done_history_lock:
        acted: dict[str, float] = {}
        for tweets in done_history.values():
            for status_id, done in tweets.items():
                if done and re.fullmatch(r"\d{6,25}", status_id):
                    acted[status_id] = min(min(done.values()), acted.get(status_id, float("inf")))
    for status_id, at in acted.items():
        if status_id not in found:
            found[status_id] = {"url": f"https://x.com/i/web/status/{status_id}", "text": "", "group": "", "at": int(at)}
    now = time.time()
    added = []
    with collected_lock:
        for status_id, row in found.items():
            if status_id not in collected_tweets and now - row["at"] < COLLECTED_KEEP_SECONDS and not tweet_is_ignored(row["url"]):
                collected_tweets[status_id] = row
                added.append(status_id)
        if added:
            persist_collected_unlocked()
    try:
        write_private_json(COLLECTED_FILLED_PATH, {"at": now, "added": len(added)})
    except OSError:
        pass
    if added:
        queue_views(sorted(added, key=lambda status_id: -found[status_id]["at"]))
    return len(added)


def collected_payload() -> list[dict]:
    """The saved tweets for the page, newest first; ignored accounts left out."""
    with collected_lock:
        if prune_collected_unlocked(time.time()):
            persist_collected_unlocked()
        rows = [{"id": status_id, **row} for status_id, row in collected_tweets.items()]
    rows = [row for row in rows if not tweet_is_ignored(row["url"])]
    rows.sort(key=lambda row: row["at"], reverse=True)
    return rows


# «عرض الأكثر مشاهدة» in «عرض التغريدات»: the current view count of a day's tweets, from FxTwitter's free
# API (api.fxtwitter.com/status/<id>). It is asked FX_AT_ONCE tweets at a time, with no wait between
# them (a test asked 140 at once, then 140 one after another, and none was refused). If the service
# refuses (too many requests), or several tweets get no answer while none is answered, the fetching
# waits a few minutes (longer each time), then goes on where it stopped, one tweet at a time, slowly.
# The counts are kept with the saved tweets. Every day of the last 7 can be checked (today's too); once a
# day is asked for, its button waits VIEWS_AGAIN_SECONDS, then it can be asked for again (all its tweets).
FX_STATUS_URL = "https://api.fxtwitter.com/status/{}"
FX_AT_ONCE = 10                      # tweets asked at the same time
FX_SLOW_GAP_SECONDS = (5.0, 8.0)     # once the service has refused: one tweet at a time, this far apart
FX_PAUSE_SECONDS = 180               # the first wait; the next ones wait 6, 9, 12 then 15 minutes
FX_PAUSE_MAX_SECONDS = 900
FX_MAX_PAUSES = 6                    # waits in a row with no answer between them: then it stops
VIEWS_DAYS = (0, 6)                  # the days that can be checked: today to 6 days ago
VIEWS_AGAIN_SECONDS = 600            # a day asked for can be asked for again after 10 minutes
# With its views, a tweet's content is kept: its text, its pictures (a photo, or the still of a video or
# a GIF; from X's picture server only, at most 4) and the tweet it quotes, if any.
TWEET_PICTURE = re.compile(r"https://pbs\.twimg\.com/[A-Za-z0-9_./-]{1,200}(?:\?[A-Za-z0-9_=&.-]{1,80})?")
TWEET_HANDLE = re.compile(r"[A-Za-z0-9_]{1,30}")
TWEET_BODY_MAX = 2000
QUOTE_BODY_MAX = 1000
views_lock = threading.Lock()
views_queue: deque = deque()
views_state: dict = {"running": False, "paused_until": 0.0, "error": "", "removed": [], "slow": False}
# The days asked for in the last VIEWS_AGAIN_SECONDS: the start of the day (in the asker's time zone) → when.
views_asked: dict[int, float] = {}


def recent_views_asks(now: float) -> dict[int, float]:
    """The days still waiting after being asked for (the older ones are dropped). Call with views_lock held."""
    for start in [start for start, at in views_asked.items() if now - at >= VIEWS_AGAIN_SECONDS]:
        del views_asked[start]
    return dict(views_asked)


def minutes_text(seconds: float) -> str:
    """«دقيقة»، «دقيقتين»، «3 دقائق»، «11 دقيقة»: the minutes, rounded up."""
    minutes = max(1, math.ceil(seconds / 60))
    if minutes <= 2:
        return ("دقيقة", "دقيقتين")[minutes - 1]
    return f"{minutes} {'دقائق' if 3 <= minutes % 100 <= 10 else 'دقيقة'}"


def tweet_pictures(value) -> list[list[str]]:
    """Pictures as kept, [kind, address] with kind "photo" or "video" (its still): only X's picture
    server, at most 4."""
    found = []
    for pair in value if isinstance(value, list) else []:
        if (isinstance(pair, list) and len(pair) == 2 and pair[0] in ("photo", "video")
                and isinstance(pair[1], str) and TWEET_PICTURE.fullmatch(pair[1])):
            found.append([pair[0], pair[1]])
    return found[:4]


def tweet_content(row: dict) -> dict:
    """A saved tweet's content ("body", "pictures", and "quote": "by", "body", "pictures"), checked
    again; {} when it has none (its views were not fetched since this was added)."""
    if not isinstance(row.get("body"), str):
        return {}
    content = {"body": row["body"][:TWEET_BODY_MAX], "pictures": tweet_pictures(row.get("pictures"))}
    quoted = row.get("quote")
    if isinstance(quoted, dict):
        by = str(quoted.get("by") or "")
        content["quote"] = {"by": by if TWEET_HANDLE.fullmatch(by) else "", "body": str(quoted.get("body") or "")[:QUOTE_BODY_MAX],
                            "pictures": tweet_pictures(quoted.get("pictures"))}
    return content


def fx_content(tweet: dict) -> dict:
    """The content kept from FxTwitter's answer about a tweet (see tweet_content)."""
    def pictures(of: dict) -> list[list[str]]:
        media = of.get("media")
        found = []
        for item in (media.get("all") or []) if isinstance(media, dict) else []:
            if isinstance(item, dict) and item.get("type") in ("photo", "video", "gif"):
                found.append(["photo", item.get("url")] if item["type"] == "photo" else ["video", item.get("thumbnail_url")])
        return tweet_pictures(found)
    content = {"body": str(tweet.get("text") or "")[:TWEET_BODY_MAX], "pictures": pictures(tweet)}
    quoted = tweet.get("quote")
    if isinstance(quoted, dict):
        author = quoted.get("author") if isinstance(quoted.get("author"), dict) else {}
        by = str(author.get("screen_name") or "")
        content["quote"] = {"by": by if TWEET_HANDLE.fullmatch(by) else "", "body": str(quoted.get("text") or "")[:QUOTE_BODY_MAX],
                            "pictures": pictures(quoted)}
    return content


def fx_tweet_views(status_id: str) -> tuple[str, int | None, str, dict | None]:
    """Ask FxTwitter about one tweet. Returns (outcome, views, detail, content): ("ok", views or None,
    the tweet's link, its content) · ("gone", None, "", None) deleted, private or not found ·
    ("blocked", None, seconds to wait or "", None) too many requests · ("error", None, why, None) no
    usable answer."""
    asking = urllib.request.Request(FX_STATUS_URL.format(status_id), headers={
        "User-Agent": "x-group-tool/1.0", "Accept": "application/json"})
    try:
        with urllib.request.urlopen(asking, timeout=20) as response:
            data = json.loads(response.read(4 * 1024 * 1024).decode("utf-8"))
    except urllib.error.HTTPError as exc:
        try:
            body = json.loads(exc.read(4096).decode("utf-8"))
        except Exception:
            body = None
        if exc.code == 429:
            return "blocked", None, str(exc.headers.get("Retry-After") or ""), None
        if isinstance(body, dict) and body.get("code") in (401, 403, 404, 410):
            return "gone", None, "", None    # FxTwitter's own answer about this tweet
        if exc.code in (403, 503):
            return "blocked", None, str(exc.headers.get("Retry-After") or ""), None
        if exc.code in (404, 410):
            return "gone", None, "", None
        return "error", None, f"HTTP {exc.code}", None
    except Exception as exc:                 # no answer, a cut connection, or not JSON
        return "error", None, type(exc).__name__, None
    tweet = data.get("tweet") if isinstance(data, dict) else None
    if not isinstance(tweet, dict):
        return "gone", None, "", None
    views = tweet.get("views")
    if isinstance(views, bool) or not isinstance(views, (int, float)) or views < 0:
        views = None
    return "ok", None if views is None else int(views), str(tweet.get("url") or ""), fx_content(tweet)


def views_to_end_of_line(status_ids: list[str]) -> None:
    """These tweets are asked again after the others."""
    with views_lock:
        for status_id in status_ids:
            try:
                views_queue.remove(status_id)
            except ValueError:
                continue
            views_queue.append(status_id)


def views_worker() -> None:
    """The fetching thread. It marks itself finished under the lock when the line is empty, so a new
    request starts a new thread; if something unexpected breaks it, it stops cleanly the same way."""
    try:
        fetch_queued_views()
    except Exception:
        app.logger.warning("views fetching failed")
        with views_lock:
            views_queue.clear()
            views_state.update(running=False, paused_until=0.0, slow=False,
                               error="توقف جلب المشاهدات بسبب خطأ. اضغط «عرض الأكثر مشاهدة» ليكمل.")


def keep_views(answers: list[tuple[str, str, int | None, str, dict | None]]) -> None:
    """Keep what FxTwitter said of these tweets ((id, outcome, views, link, content)): the count, or
    «لا يوجد رقم» (deleted, private, no count, or no answer three times), and the tweet's content,
    then take them out of the line. A tweet whose author turns out to be an ignored account is
    removed, and the page is told."""
    ignored = {status_id for status_id, outcome, _, link, _ in answers if outcome == "ok" and link and tweet_is_ignored(link)}
    with collected_lock:
        for status_id, outcome, views, link, content in answers:
            row = collected_tweets.get(status_id)
            if row is None:
                continue
            if status_id in ignored:
                del collected_tweets[status_id]
                continue
            row["views"] = views if outcome == "ok" else None
            row["views_at"] = int(time.time())
            if outcome == "ok" and link and tweet_author_handle(link) and not tweet_author_handle(row["url"]):
                row["url"] = link[:300]
            if outcome == "ok" and content:
                for key in ("body", "pictures", "quote"):
                    row.pop(key, None)
                row.update(content)
            elif outcome == "gone":
                for key in ("body", "pictures", "quote"):
                    row.pop(key, None)       # deleted or private: nothing of it to show
        persist_collected_unlocked()
    with views_lock:
        for status_id, *_ in answers:
            try:
                views_queue.remove(status_id)
            except ValueError:
                pass
        if ignored:
            views_state["removed"] = (views_state["removed"] + [status_id for status_id, *_ in answers if status_id in ignored])[-500:]


def fetch_queued_views() -> None:
    """Fetch the queued tweets' view counts, FX_AT_ONCE at a time with no wait between them. A refusal
    (or no answer at all) makes it wait out the block, then go on one tweet at a time, slowly."""
    pauses = 0                       # waits in a row, with no answer between them
    failed: dict[str, int] = {}      # failed asks of each tweet
    failing: set[str] = set()        # the tweets that failed since the last answer
    slow = False
    with concurrent.futures.ThreadPoolExecutor(max_workers=FX_AT_ONCE, thread_name_prefix="tweet-views") as pool:
        while True:
            with views_lock:
                if not views_queue:
                    views_state.update(running=False, paused_until=0.0, slow=False)
                    return
                asking = list(itertools.islice(views_queue, 1 if slow else FX_AT_ONCE))
            done, again, refused = [], [], []
            for status_id, (outcome, views, detail, content) in zip(asking, pool.map(fx_tweet_views, asking)):
                if outcome == "blocked":
                    refused.append(detail)           # stays where it is: asked again after the wait
                    continue
                if outcome == "error":
                    failed[status_id] = failed.get(status_id, 0) + 1
                    failing.add(status_id)
                    if failed[status_id] < 3:
                        again.append(status_id)      # asked again after the others
                        continue
                    # It keeps failing while others are answered: no count for it.
                done.append((status_id, outcome, views, detail if outcome == "ok" else "", content if outcome == "ok" else None))
            answered = any(outcome in ("ok", "gone") for _, outcome, *_ in done)
            if answered:
                pauses = 0
                failing.clear()
            if done:
                keep_views(done)
            views_to_end_of_line(again)
            if not refused and not answered and len(failing) >= 3:
                refused.append("")                   # three tweets and no answer: the service or the connection is down
            if refused:
                pauses += 1
                if pauses > FX_MAX_PAUSES:
                    with views_lock:
                        views_queue.clear()
                        views_state.update(running=False, paused_until=0.0, slow=False,
                                           error="توقف جلب المشاهدات لأن الخدمة لم تعد تجيب. اضغط «عرض الأكثر مشاهدة» لاحقًا ليكمل.")
                    return
                asked = 0
                for detail in refused:
                    try:
                        asked = max(asked, int(float(detail)))
                    except (ValueError, OverflowError):
                        pass                         # no number of seconds (empty, a date, "inf")
                wait = min(max(asked, FX_PAUSE_SECONDS * pauses), FX_PAUSE_MAX_SECONDS)
                slow = True
                with views_lock:
                    views_state.update(paused_until=time.time() + wait, slow=True)
                time.sleep(wait)
                with views_lock:
                    views_state["paused_until"] = 0.0
                continue
            if again and not answered:
                time.sleep(10)                       # a moment's trouble: try them again shortly
            elif slow:
                time.sleep(random.uniform(*FX_SLOW_GAP_SECONDS))


def queue_views(ids: list[str]) -> int:
    """Add tweets to the ones waiting for their view count; start fetching if it is not running."""
    with views_lock:
        waiting = set(views_queue)
        added = [status_id for status_id in dict.fromkeys(ids) if status_id not in waiting]
        views_queue.extend(added)
        views_state["error"] = ""
        if views_queue and not views_state["running"]:
            views_state.update(running=True, slow=False)
            threading.Thread(target=views_worker, name="tweet-views", daemon=True).start()
        return len(added)


def views_status_payload(since: float) -> dict:
    """How the fetching is going, and the counts fetched since `since` (a time this server gave)."""
    now = time.time()
    with views_lock:
        state = {"running": views_state["running"], "waiting": list(views_queue), "error": views_state["error"],
                 "paused": max(0, int(views_state["paused_until"] - now)), "removed": list(views_state["removed"]),
                 "slow": views_state["slow"]}
    with collected_lock:
        state["views"] = {status_id: [row.get("views"), row["views_at"], tweet_content(row) or None] for status_id, row in collected_tweets.items()
                          if row.get("views_at") and row["views_at"] >= since - 2}
    state["now"] = now
    return state


def local_day_number(seconds: float, offset_minutes: int) -> int:
    """The calendar day (days since 1970) a moment falls on, at the viewer's UTC offset."""
    return math.floor((seconds + offset_minutes * 60) / 86400)


def day_spans(data: dict) -> list[tuple[int, int]]:
    """The days the page asks about, as [start, end) in seconds (in the viewer's own time zone)."""
    spans = []
    for pair in (data.get("ranges") or [])[:10]:
        try:
            start, end = int(pair[0]), int(pair[1])
        except (TypeError, ValueError, IndexError):
            continue
        if 0 < end - start <= 26 * 3600:
            spans.append((start, end))
    return spans


# Updates. Users and their keys live in g.py beside the owner's script ("توزيع البرنامج"),
# which this script starts on its own port; a user's copy takes updates from it with its key.
CONTROL_FILE = Path(__file__).resolve().with_name("g.py")
CONTROL_PORT = int(os.getenv("CONTROL_PORT", "5050"))
# Where «توزيع البرنامج» opens, when not this host on CONTROL_PORT (e.g. behind a domain).
CONTROL_URL = os.getenv("CONTROL_URL", "")
BACKUPS_DIR = DATA_DIR / "backups"
MAX_PROGRAM_BYTES = 8 * 1024 * 1024
# Set once g.py's page is up.
distribution_started = threading.Event()
# g.py's page, once this program serves it.
distribution_page = None
# Set while a user's copy installs an update: no new task starts.
updating = threading.Event()
update_check_cache: dict = {"at": 0.0, "answer": None}


def is_owner_copy() -> bool:
    """The owner's own copy has «توزيع البرنامج»; a copy given to a user takes updates."""
    return not UPDATE_SOURCE


def on_its_own() -> bool:
    """A copy on its own: the owner's kind of copy with no «توزيع البرنامج» (no g.py beside it, nor what that
    page saved), such as the script downloaded alone into a folder of its own."""
    return (is_owner_copy() and distribution_page is None and not CONTROL_FILE.is_file()
            and not (CONTROL_FILE.with_name("data") / "distribution.json").is_file())


def shown_version() -> str:
    """The version on the page: in the owner's copy, the one last published from «توزيع البرنامج»."""
    if is_owner_copy():
        published = (read_private_json(DATA_DIR / "distribution.json") or {}).get("published_version")
        if published:
            return str(published)
    return APP_VERSION


def start_distribution(bind_host: str) -> None:
    """Serve g.py's page («توزيع البرنامج») from this same program, on CONTROL_PORT, when g.py
    sits beside the owner's script. It hands out this script."""
    if not is_owner_copy() or not CONTROL_FILE.is_file():
        return
    try:
        spec = importlib.util.spec_from_file_location("distribution_page", CONTROL_FILE)
        control = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(control)
        control.PROGRAM_PATH = Path(__file__).resolve()
        server = make_server(bind_host, CONTROL_PORT, control.app, threaded=True)
    except (Exception, SystemExit) as exc:
        # Werkzeug exits the program when the port is taken; the script keeps running without the page.
        reason = "المنفذ مستخدم من برنامج آخر" if isinstance(exc, SystemExit) else str(exc)
        print(f"لم تبدأ صفحة التوزيع ({CONTROL_FILE.name}) على المنفذ {CONTROL_PORT}: {reason}", flush=True)
        return
    threading.Thread(target=server.serve_forever, name="distribution", daemon=True).start()
    global distribution_page
    distribution_page = control             # (its choice of who writes the comments is this copy's too)
    distribution_started.set()
    print(f"صفحة التوزيع ({CONTROL_FILE.name}) على المنفذ {CONTROL_PORT}", flush=True)


def version_of(text: str) -> str:
    match = re.search(r'^APP_VERSION = "([0-9][0-9.]*)"', text, re.M)
    return match.group(1) if match else ""


def version_tuple(version: str) -> tuple[int, ...]:
    return tuple(int(part) for part in re.findall(r"\d+", version or "")) or (0,)


def ask_update_source(path: str, timeout: float, report: dict | None = None) -> tuple[int, bytes]:
    """A user's copy asks the owner's g.py (posting report when given). Returns (HTTP status, body);
    status 0 when unreachable."""
    headers = {"X-Update-Key": UPDATE_KEY, "User-Agent": "x-group-update"}
    body = None
    if report is not None:
        body = json.dumps(report).encode("utf-8")
        headers["Content-Type"] = "application/json"
    asking = urllib.request.Request(UPDATE_SOURCE.rstrip("/") + path, data=body, headers=headers)
    try:
        with urllib.request.urlopen(asking, timeout=timeout) as answer:
            return answer.status, answer.read(MAX_PROGRAM_BYTES + 1)
    except urllib.error.HTTPError as exc:
        return exc.code, exc.read(4096)
    except (urllib.error.URLError, OSError, ValueError):
        return 0, b""


# A user's copy checks in with the owner this often, and when its page opens.
OWNER_SYNC_EVERY = 120
owner_sync_lock = threading.Lock()
owner_sync_state = {"at": 0.0, "ok": False}


def apply_owner_gemini(key: str, model: str = "") -> None:
    """Use the Gemini key and model the owner set for this copy; when the owner deleted the key, drop
    it here too. With no model from the owner, the copy keeps its own."""
    model = normalize_gemini_model(model) or ""
    with gemini_lock:
        current, managed = saved_gemini.get("api_key") or "", bool(saved_gemini.get("managed"))
        changed = False
        if key and valid_gemini_key(key):
            if key != current or not managed:
                saved_gemini.update(api_key=key, managed=True)
                changed = True
        elif managed and current:
            saved_gemini.update(api_key="", managed=False)
            changed = True
        if model and model != saved_gemini.get("model"):
            saved_gemini["model"] = model
            changed = True
        if changed:
            persist_gemini_unlocked()


def sync_with_owner() -> None:
    """A user's copy checks in with the owner's g.py: it reports its Gemini comments and cost, takes
    the Gemini key the owner set for it (or drops the one deleted), and resets its cost when asked."""
    if is_owner_copy() or not owner_sync_lock.acquire(blocking=False):
        return
    try:
        for _ in range(2):  # after a reset, report the new cost straight away
            with gemini_usage_lock:
                done = str(gemini_usage.get("reset_id") or "")
                report = {
                    # Since the cost was last reset, like the cost beside it in «إدارة».
                    "comments": int(gemini_usage.get("cost_comments") or 0),
                    "cost": round(int(gemini_usage.get("cost_comments") or 0) * GEMINI_PRICE_PER_COMMENT, 6),
                    "reset_id": done,
                    # Since this copy began (never reset): its total cost from the beginning.
                    "total_comments": int(gemini_usage.get("comments") or 0),
                    "total_cost": round(int(gemini_usage.get("comments") or 0) * GEMINI_PRICE_PER_COMMENT, 6),
                }
            status, body = ask_update_source("/user/sync", 15, report)
            try:
                answer = json.loads(body.decode("utf-8")) if status == 200 else {}
            except (UnicodeDecodeError, json.JSONDecodeError):
                answer = {}
            ok = isinstance(answer, dict) and bool(answer.get("success"))
            if ok:
                # The keys, into memory only (see apply_owner_gemini, apply_owner_comments).
                apply_owner_gemini(str(answer.get("gemini_key") or ""), str(answer.get("gemini_model") or ""))
                engine = str(answer.get("comments_engine") or "")
                kind = "claude" if engine == "claude" else "grok"
                apply_owner_comments(engine, str(answer.get(kind + "_key") or ""), str(answer.get(kind + "_model") or ""))
            # (Set once the answer is applied: whoever waits for the keys sees them with it.)
            owner_sync_state.update(at=time.monotonic(), ok=ok)
            if not ok:
                return
            if isinstance(answer.get("skip_users"), list):
                store_skip_users(answer["skip_users"])
            wanted = str(answer.get("reset_id") or "")
            if not wanted or wanted == done:
                return
            reset_gemini_cost(wanted)
    finally:
        owner_sync_lock.release()


def owner_keys_ready(gemini_only: bool = False) -> bool:
    """A user's copy has what writes its comments: Grok (the owner's choice) or its Gemini key; with
    gemini_only, its Gemini key (for «إنشاء محتوى»)."""
    with gemini_lock:
        gemini = valid_gemini_key(str(saved_gemini.get("api_key") or ""))
    return gemini or (not gemini_only and not gemini_writes_comments())


def wait_for_owner_keys(seconds: float = 10.0, gemini_only: bool = False) -> bool:
    """A user's copy keeps its keys in memory only, from its check-ins: when it has none (it has just
    started, or the owner could not be reached), it checks in now and waits a little for them. It stops
    waiting as soon as the owner answers without them. True when it has them."""
    if is_owner_copy() or owner_keys_ready(gemini_only):
        return True
    began = time.monotonic()
    while True:
        sync_with_owner()                      # (returns at once while another check-in is under way)
        answered = owner_sync_state["ok"] and owner_sync_state["at"] >= began
        if owner_keys_ready(gemini_only) or answered or time.monotonic() - began >= seconds:
            return owner_keys_ready(gemini_only)
        time.sleep(1)


def no_keys_message() -> str:
    """Why a user's copy has no key for its comments."""
    if not owner_sync_state.get("ok"):
        return "تعذّر الاتصال بصاحب البرنامج لجلب مفتاح التعليقات. حاول بعد قليل."
    return "لا يوجد مفتاح للتعليقات في هذه النسخة. اطلبه من صاحب البرنامج."


def owner_sync_loop() -> None:
    while True:
        try:
            sync_with_owner()
        except Exception:
            pass
        time.sleep(OWNER_SYNC_EVERY)


def latest_update() -> dict:
    """The version the owner offers this copy {"version", "sha256"}, or {"message"} saying why not."""
    status, body = ask_update_source("/update/latest", 15)
    try:
        answer = json.loads(body.decode("utf-8")) if body else {}
    except (UnicodeDecodeError, json.JSONDecodeError):
        answer = {}
    if status == 200 and isinstance(answer, dict) and answer.get("version"):
        return {"version": str(answer["version"]), "sha256": str(answer.get("sha256") or "")}
    message = answer.get("message") if isinstance(answer, dict) else ""
    return {"message": str(message or "تعذّر الاتصال بمصدر التحديث.")}


def new_program_problem(body: bytes, latest: dict) -> str:
    """Why a downloaded program must not be installed; "" when it is fine."""
    if not body or len(body) > MAX_PROGRAM_BYTES:
        return "لم يصل ملف التحديث كاملًا. أعد المحاولة."
    if not hmac.compare_digest(hashlib.sha256(body).hexdigest(), latest.get("sha256") or ""):
        return "لم يصل ملف التحديث كاملًا. أعد المحاولة."
    try:
        text = body.decode("utf-8")
        compile(text, "update.py", "exec")
    except (UnicodeDecodeError, SyntaxError, ValueError):
        return "ملف التحديث غير صالح. لم يتغير شيء."
    if version_of(text) != latest.get("version"):
        return "رقم إصدار ملف التحديث لا يطابق. لم يتغير شيء."
    if not re.search(r'^UPDATE_SOURCE = "https?://[^"\s]+"$', text, re.M) or not re.search(r'^UPDATE_KEY = "[^"\s]+"$', text, re.M):
        return "ملف التحديث بلا عنوان أو مفتاح. لم يتغير شيء."
    return ""


def program_starts(body: bytes) -> bool:
    """Load the new program once in a separate Python, in a scratch folder, to see that it starts."""
    trial = BACKUPS_DIR / "trial"
    shutil.rmtree(trial, ignore_errors=True)
    try:
        trial.mkdir(parents=True)
        program = trial / "program.py"
        program.write_bytes(body)
        load = ("import importlib.util, sys; spec = importlib.util.spec_from_file_location('trial', sys.argv[1]); "
                "spec.loader.exec_module(importlib.util.module_from_spec(spec))")
        result = subprocess.run([sys.executable, "-c", load, str(program)], cwd=trial, capture_output=True, timeout=90)
        return result.returncode == 0
    except (OSError, subprocess.SubprocessError):
        return False
    finally:
        shutil.rmtree(trial, ignore_errors=True)


def install_program(body: bytes) -> None:
    """Keep the running file in data/backups, then put the new one in its place."""
    script = Path(__file__).resolve()
    BACKUPS_DIR.mkdir(parents=True, exist_ok=True)
    shutil.copy2(script, BACKUPS_DIR / f"{script.stem}-{APP_VERSION}.py")
    temporary = script.with_name(script.name + ".new")
    temporary.write_bytes(body)
    try:
        shutil.copymode(script, temporary)
    except OSError:
        pass
    temporary.replace(script)


def restart_program() -> None:
    """Run the program again in this same process, so the new file takes over."""
    time.sleep(1.5)
    try:
        shutdown_jobs()
    except Exception:
        pass
    # Flask's server leaves its listening socket open across exec; close it there so the new
    # program can listen on the same port.
    server_fd = os.environ.pop("WERKZEUG_SERVER_FD", "")
    if server_fd.isdigit():
        try:
            os.set_inheritable(int(server_fd), False)
        except OSError:
            pass
    sys.stdout.flush()
    sys.stderr.flush()
    command = list(getattr(sys, "orig_argv", None) or [sys.executable, *sys.argv])
    os.execv(sys.executable, [sys.executable, *command[1:]])


def remember_gemini(api_key: str, model: str) -> None:
    key = (api_key or "").strip()
    normalized = normalize_gemini_model(model or "") or saved_gemini.get("model") or "gemini-3.5-flash"
    if key and not valid_gemini_key(key):
        return
    with gemini_lock:
        if key and key != saved_gemini.get("api_key"):
            # A key typed on this page is this copy's own, not the owner's.
            saved_gemini["api_key"] = key
            saved_gemini["managed"] = False
        saved_gemini["model"] = normalized
        persist_gemini_unlocked()


# A user's copy never keeps an API key on its disk: the owner's Gemini and Grok keys come with each
# check-in and stay in the running program's memory only (a copy just started asks for them at once). The
# owner's own copy keeps the Gemini key typed in its panel in data/gemini.json, sealed, so the file shows
# nothing readable: it is encrypted with a key made from a secret in this program and this copy's update key
# (a stream from SHA-256 with a random nonce each time it is saved, and a tag that tells a damaged file).
# A file from before, with a key in the clear (or a user's copy's sealed one), is rewritten without it.
KEY_SEAL_SECRET = bytes.fromhex("d8867d215ab7fb097f3a535a380696b36506ee694e0ef27fdba0c4f8fd77b658")


def key_seal_material() -> bytes:
    return hashlib.sha256(KEY_SEAL_SECRET + UPDATE_KEY.encode("utf-8")).digest()


def key_stream(material: bytes, nonce: bytes, length: int) -> bytes:
    stream = bytearray()
    counter = 0
    while len(stream) < length:
        stream += hashlib.sha256(material + nonce + counter.to_bytes(4, "big")).digest()
        counter += 1
    return bytes(stream[:length])


def seal_key(text: str) -> str:
    """A key as it is kept on disk ("" for none)."""
    if not text:
        return ""
    material, nonce, raw = key_seal_material(), os.urandom(16), text.encode("utf-8")
    body = bytes(a ^ b for a, b in zip(raw, key_stream(material, nonce, len(raw))))
    tag = hmac.new(material, nonce + body, hashlib.sha256).digest()[:16]
    return "s1:" + base64.b64encode(nonce + tag + body).decode("ascii")


def open_key(sealed) -> str:
    """The key a sealed one holds; "" when there is none, or it is damaged or another copy's."""
    if not isinstance(sealed, str) or not sealed.startswith("s1:"):
        return ""
    try:
        data = base64.b64decode(sealed[3:], validate=True)
    except ValueError:
        return ""
    if len(data) <= 32:
        return ""
    nonce, tag, body = data[:16], data[16:32], data[32:]
    material = key_seal_material()
    if not hmac.compare_digest(tag, hmac.new(material, nonce + body, hashlib.sha256).digest()[:16]):
        return ""
    try:
        return bytes(a ^ b for a, b in zip(body, key_stream(material, nonce, len(body)))).decode("utf-8")
    except UnicodeDecodeError:
        return ""


def persist_gemini_unlocked() -> None:
    # The owner's copy keeps its own key, sealed; a user's copy keeps the owner's key in memory only, from its
    # check-ins, never on its disk.
    sealed = seal_key(saved_gemini["api_key"]) if is_owner_copy() else ""
    write_private_json(GEMINI_PATH, {"version": 2, "api_key_sealed": sealed, "model": saved_gemini["model"],
                                     "managed": bool(saved_gemini.get("managed"))})


def load_gemini() -> None:
    global saved_gemini
    loaded = read_private_json(GEMINI_PATH) or {}
    owner = is_owner_copy()
    plain = str(loaded.get("api_key") or "").strip()
    sealed = loaded.get("api_key_sealed")
    # A user's copy reads no key from its disk: the owner's comes with its first check-in.
    key = ((open_key(sealed).strip() if sealed else plain) if owner else "")
    model = normalize_gemini_model(str(loaded.get("model") or "")) or "gemini-3.5-flash"
    if key and not valid_gemini_key(key):
        key = ""
    # managed: the owner set this key from «توزيع البرنامج», and may delete it from there.
    saved_gemini = {"api_key": key, "model": model, "managed": bool(key and loaded.get("managed"))}
    if plain or (sealed and not owner):
        with gemini_lock:
            persist_gemini_unlocked()      # the owner's key now sealed; a user's copy: the key taken off its disk


def persist_sessions_unlocked() -> None:
    write_private_json(SESSIONS_PATH, {"version": 1, "sessions": saved_sessions})


def load_sessions() -> None:
    global saved_sessions
    loaded = read_private_json(SESSIONS_PATH)
    rows = loaded.get("sessions") if loaded else None
    if not isinstance(rows, list):
        saved_sessions = []
        return
    cleaned = []
    for row in rows:
        if not isinstance(row, dict):
            continue
        token = str(row.get("token") or "")
        username = str(row.get("username") or "").lstrip("@")
        if not valid_auth_token(token):
            continue
        if username and not re.fullmatch(r"[A-Za-z0-9_]{1,15}", username):
            username = ""
        cleaned.append({
            "id": str(row.get("id") or secrets.token_urlsafe(12)),
            "digest": hashlib.sha256(token.encode("utf-8")).hexdigest(),
            "token": token,
            "username": username,
            "chat_pin": str(row.get("chat_pin") or "") if valid_chat_pin(str(row.get("chat_pin") or "")) else "",
            "verified_at": float(row.get("verified_at") or 0),
        })
    cleaned.sort(key=lambda item: item["verified_at"], reverse=True)
    saved_sessions = cleaned[:MAX_ACCOUNTS]             # up to three accounts, newest kept
    for row in saved_sessions:
        if row["username"]:
            account_names[profile_key(row["token"])] = row["username"]


def remember_session(auth_token: str, username: str, chat_pin: str = "") -> None:
    token = (auth_token or "").strip()
    if not valid_auth_token(token):
        return
    username = (username or "").strip().lstrip("@")
    if username and not re.fullmatch(r"[A-Za-z0-9_]{1,15}", username):
        username = ""
    if username:
        account_names[profile_key(token)] = username
    pin = (chat_pin or "").strip()
    if pin and not valid_chat_pin(pin):
        pin = ""
    digest = hashlib.sha256(token.encode("utf-8")).hexdigest()
    now = time.time()
    with sessions_lock:
        found = next((row for row in saved_sessions if hmac.compare_digest(row["digest"], digest)), None)
        if found:
            if username:
                found["username"] = username
            if pin:
                found["chat_pin"] = pin
            found["token"] = token
            found["verified_at"] = now
        else:
            saved_sessions.append({
                "id": secrets.token_urlsafe(12),
                "digest": digest,
                "token": token,
                "username": username,
                "chat_pin": pin,
                "verified_at": now,
            })
        saved_sessions.sort(key=lambda item: item["verified_at"], reverse=True)
        del saved_sessions[MAX_ACCOUNTS:]            # up to three accounts: the oldest drops when a fourth is added
        persist_sessions_unlocked()


def public_session(row: dict) -> dict:
    token = row["token"]
    hint = token[:4] + "…" + token[-4:] if len(token) >= 12 else "••••"
    return {
        "id": row["id"],
        "username": row.get("username") or "",
        "hint": hint,
        "token": token,
        "chat_pin": row.get("chat_pin") or "",
        "verified_at": row.get("verified_at") or 0,
    }


def request_client_id() -> str:
    raw = (request.headers.get("X-Client-Id") or "").strip()
    if re.fullmatch(r"[A-Za-z0-9_-]{16,80}", raw):
        return raw
    return ""


def job_record(job: dict) -> dict:
    return {field: job.get(field) for field in JOB_FIELDS}


# Task progress is saved to jobs.json at most this often; a change of status is saved at once.
JOBS_SAVE_EVERY = 2.0
jobs_saved_at = 0.0
jobs_unsaved = False


def persist_jobs_unlocked() -> None:
    global jobs_saved_at, jobs_unsaved
    write_private_json(JOBS_PATH, {"version": 1, "jobs": {key: job_record(job) for key, job in jobs.items()}}, compact=True)
    jobs_saved_at = time.monotonic()
    jobs_unsaved = False


def save_jobs_in_background() -> None:
    """Write progress that was held back by the 2-second limit."""
    while True:
        time.sleep(JOBS_SAVE_EVERY)
        try:
            with jobs_lock:
                if jobs_unsaved:
                    persist_jobs_unlocked()
        except Exception:
            pass


def mark_job_interrupted(job: dict) -> None:
    if job.get("status") != "running":
        return
    previous = (job.get("message") or "").strip()
    job["status"] = "interrupted"
    job["success"] = False
    job["updated_at"] = time.time()
    job["message"] = "توقفت العملية مع إيقاف السكربت ولم تُستكمل." + (f" آخر حالة: {previous}" if previous else "")


def load_jobs() -> None:
    loaded = read_private_json(JOBS_PATH)
    rows = loaded.get("jobs") if loaded else None
    if not isinstance(rows, dict):
        return
    now = time.time()
    with jobs_lock:
        for job_id, row in rows.items():
            if not isinstance(job_id, str) or not isinstance(row, dict):
                continue
            job = job_record(row)
            job["items"] = job["items"] if isinstance(job["items"], list) else []
            job["results"] = job["results"] if isinstance(job["results"], list) else []
            job["actions"] = job["actions"] if isinstance(job["actions"], list) else []
            if job.get("status") not in {"running", "done", "interrupted"}:
                job["status"] = "interrupted"
            mark_job_interrupted(job)
            if job.get("status") != "running" and now - float(job.get("updated_at") or 0) > JOB_TTL_SECONDS:
                continue
            jobs[job_id] = job
        persist_jobs_unlocked()


def shutdown_jobs() -> None:
    with jobs_lock:
        for job in jobs.values():
            mark_job_interrupted(job)
        if jobs:
            persist_jobs_unlocked()


def prune_jobs() -> None:
    now = time.time()
    stale = [
        key for key, job in jobs.items()
        if job.get("status") != "running" and now - float(job.get("updated_at") or job.get("created_at") or now) > JOB_TTL_SECONDS
    ]
    for key in stale:
        jobs.pop(key, None)
    if len(jobs) > 40:
        finished = sorted(
            (key for key, job in jobs.items() if job.get("status") != "running"),
            key=lambda key: float(jobs[key].get("updated_at") or 0),
        )
        for key in finished[: max(0, len(jobs) - 40)]:
            jobs.pop(key, None)


def notify_task_done(success: bool, message: str) -> None:
    """In the app, a phone notification: اكتملت المهمة or فشلت المهمة."""
    if os.environ.get("GG_IN_APP") != "1":
        return
    try:
        from java import jclass
        jclass("app.tg.groups.Alerts").result(bool(success), (message or "")[:180])
    except Exception:
        pass


def publish_job(job_id: str, **fields) -> None:
    global jobs_unsaved
    finished = None
    with jobs_lock:
        job = jobs.get(job_id)
        if not job:
            return
        job.update(fields)
        job["updated_at"] = time.time()
        if fields.get("status") == "done":
            finished = (bool(job.get("success")), str(job.get("message") or ""))
        if "status" in fields or time.monotonic() - jobs_saved_at >= JOBS_SAVE_EVERY:
            persist_jobs_unlocked()
        else:
            jobs_unsaved = True
    if finished:
        notify_task_done(finished[0], finished[1])


def begin_job(owner: str, client_id: str, requested: int, phase: str, message: str, kind: str, username: str) -> tuple[str, str]:
    job_id = secrets.token_urlsafe(18)
    job_key = secrets.token_urlsafe(24)
    now = time.time()
    with jobs_lock:
        prune_jobs()
        jobs[job_id] = {
            "owner": owner,
            "client_id": client_id,
            "created_at": now,
            "updated_at": now,
            "status": "running",
            "phase": phase,
            "kind": kind,
            "collected": 0,
            "done": 0,
            "requested": requested,
            "message": message,
            "success": None,
            "username": username,
            "actions": [],
            "items": [],
            "results": [],
            "key_hash": hashlib.sha256(job_key.encode("utf-8")).hexdigest(),
        }
        persist_jobs_unlocked()
    return job_id, job_key


def job_key_matches(job: dict, presented: str) -> bool:
    if not presented or len(presented) > 200:
        return False
    digest = hashlib.sha256(presented.encode("utf-8")).hexdigest()
    expected = str(job.get("key_hash") or "")
    return bool(expected) and hmac.compare_digest(digest, expected)


def public_job(job: dict, light: bool = False, links: bool = False) -> dict:
    """light: while the task runs, leave out its tweet and result lists (the page only
    needs the counts and message then; the full lists are sent once it finishes).
    links: add the extracted tweets' links (the task card's copy button asks once)."""
    payload = {
        "status": job["status"],
        "phase": job.get("phase") or "collect",
        "kind": job.get("kind") or "preview",
        "collected": job.get("collected") or 0,
        "done": job.get("done") or 0,
        "requested": job.get("requested") or 0,
        "requested_count": job.get("requested") or 0,
        "message": job.get("message") or "",
        "success": job.get("success"),
        "username": job.get("username") or "",
        "actions": job.get("actions") or [],
        "items": job.get("items") or [],
        "results": job.get("results") or [],
        "resumable": bool(job.get("resumable")) and job.get("status") == "done",
        "retry_failed": failed_retry_count(job),
    }
    if light and job["status"] == "running":
        payload["items"] = []
        payload["results"] = []
    if links:
        payload["links"] = [item["url"] for item in job.get("items") or [] if isinstance(item, dict) and item.get("url")]
    return payload


SCREEN_PATH = DATA_DIR / "screen.json"              # (the panel saved before accounts were kept apart)
ACTIVE_ACCOUNT_PATH = DATA_DIR / "active_account.json"
screen_lock = threading.RLock()
# What each account's panel showed (its groups, its group, its tweet, its actions, its last task), in its own
# folder: data/accounts/<key>/screen.json. The panel shows one account at a time: active_token.
screens: dict[str, dict] = {}
active_token = ""


def blank_screen() -> dict:
    return {"auth_token": "", "chat_pin": "", "groups": [], "group": "", "stop_tweet": "",
            "actions": ["repost", "like", "bookmark"], "job_id": "", "job_key": "", "started_at": 0}


def clean_screen(loaded: dict) -> dict:
    row = blank_screen()
    groups = loaded.get("groups")
    if isinstance(groups, list):
        row["groups"] = [re.sub(r"\s+", " ", str(name)).strip() for name in groups if str(name).strip()][:200]
    for key in ("auth_token", "chat_pin", "group", "job_id", "job_key"):
        value = str(loaded.get(key) or "").strip()
        if value:
            row[key] = value
    actions = loaded.get("actions")
    if isinstance(actions, list):
        picked = [action for action in actions if isinstance(action, str) and action in ALLOWED_ACTIONS]
        if picked:
            row["actions"] = list(dict.fromkeys(picked))
    row["stop_tweet"] = str(loaded.get("stop_tweet") or "")
    try:
        row["started_at"] = float(loaded.get("started_at") or 0)
    except (TypeError, ValueError):
        row["started_at"] = 0
    return row


def account_screen_unlocked(token: str) -> dict:
    """The account's own panel (read from its folder the first time). Call with screen_lock held."""
    key = profile_key(token)
    row = screens.get(key)
    if row is None:
        row = clean_screen(read_private_json(account_dir(key) / "screen.json") or {})
        screens[key] = row
    row["auth_token"] = token
    return row


def persist_account_screen_unlocked(token: str) -> None:
    write_private_json(account_dir(profile_key(token)) / "screen.json", {"version": 1, **account_screen_unlocked(token)})


def set_active_account(token: str) -> None:
    """The panel now shows this account ("" for none): its own panel, its own log in the app."""
    global active_token
    token = token if valid_auth_token(token) else ""
    with screen_lock:
        changed = token != active_token
        active_token = token
        if changed:
            try:
                write_private_json(ACTIVE_ACCOUNT_PATH, {"auth_token": token})
            except Exception:
                pass
    if IN_APP:
        try:
            import ggapp
            key = profile_key(token) if token else ""
            ggapp.set_active_account(key, account_names.get(key, "") if token else "")
        except Exception:
            pass
        show_active_browser()


def load_screen() -> None:
    """The account the panel showed last. A panel saved before accounts were kept apart becomes its account's."""
    token = str((read_private_json(ACTIVE_ACCOUNT_PATH) or {}).get("auth_token") or "")
    legacy = read_private_json(SCREEN_PATH)
    if legacy:
        old = clean_screen(legacy)
        if valid_auth_token(old["auth_token"]):
            key = profile_key(old["auth_token"])
            if not (account_dir(key) / "screen.json").exists():
                with screen_lock:
                    screens[key] = old
                    try:
                        persist_account_screen_unlocked(old["auth_token"])
                    except Exception:
                        pass
            if not valid_auth_token(token):
                token = old["auth_token"]
        try:
            SCREEN_PATH.replace(SCREEN_PATH.with_name("screen.before-accounts.json"))
        except OSError:
            pass
    set_active_account(token)


def save_screen(**fields) -> None:
    """Save into an account's own panel: the account named by auth_token (the panel then shows it), else the
    one the panel shows now. auth_token "" means the panel shows no account (nothing is saved then)."""
    with screen_lock:
        if "auth_token" in fields:
            token = str(fields.pop("auth_token") or "")
            set_active_account(token)
        else:
            token = active_token
        if not valid_auth_token(token):
            return
        row = account_screen_unlocked(token)
        for key, value in fields.items():
            if key in row:
                row[key] = value
        try:
            persist_account_screen_unlocked(token)
        except Exception:
            pass


def account_screen(token: str) -> dict:
    """A copy of the account's own panel (a blank one for no account)."""
    with screen_lock:
        return dict(account_screen_unlocked(token)) if valid_auth_token(token) else blank_screen()


def running_job_rows(account: str, limit: int = 5) -> list[dict]:
    """The account's own tasks that are working (or waiting) now."""
    with jobs_lock:
        running = [(job_id, job) for job_id, job in jobs.items()
                   if job.get("status") == "running" and account and job.get("account") == account]
    running.sort(key=lambda pair: float(pair[1].get("created_at") or 0), reverse=True)
    rows = []
    for job_id, job in running[:limit]:
        row = public_job(job, light=True)
        row["id"] = job_id
        rows.append(row)
    return rows


def screen_payload(token: str | None = None) -> dict:
    """An account's panel (the one shown now when token is None), with its last task and its working ones."""
    with screen_lock:
        if token is None:
            token = active_token
    row = account_screen(token)
    key = profile_key(token) if valid_auth_token(token) else ""
    payload = {
        "auth_token": row.get("auth_token") or "",
        "chat_pin": row.get("chat_pin") or "",
        "groups": list(row.get("groups") or []),
        "group": row.get("group") or "",
        "stop_tweet": row.get("stop_tweet") or "",
        "actions": list(row.get("actions") or []),
        "job_id": row.get("job_id") or "",
        "job_key": row.get("job_key") or "",
        "started_at": row.get("started_at") or 0,
    }
    with jobs_lock:
        job = jobs.get(payload["job_id"])
        payload["job"] = public_job(job, light=True) if job and key and job.get("account") == key else None
    payload["running_jobs"] = running_job_rows(key)
    payload["success"] = True
    return payload


@app.get("/<access_path>/state")
def state_endpoint(access_path: str):
    """The panel of the account the page asks for (X-Account-Token), else of the account shown last."""
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    token = (request.headers.get("X-Account-Token") or "").strip()
    return jsonify(screen_payload(token if valid_auth_token(token) else None))


@app.post("/<access_path>/screen")
def save_screen_endpoint(access_path: str):
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    data = request.get_json(silent=True) or {}
    fields: dict = {}
    token = str(data.get("auth_token") or "").strip()
    if token == "" or valid_auth_token(token):
        fields["auth_token"] = token
    pin = str(data.get("chat_pin") or "").strip()
    if valid_chat_pin(pin):
        fields["chat_pin"] = pin
    group_name = re.sub(r"\s+", " ", str(data.get("group") or "")).strip()
    if group_name and len(group_name) <= 80:
        fields["group"] = group_name
    if "stop_tweet" in data:
        fields["stop_tweet"] = str(data.get("stop_tweet") or "").strip()[:300]
    actions = data.get("actions")
    if isinstance(actions, list):
        picked = [action for action in actions if isinstance(action, str) and action in ALLOWED_ACTIONS]
        if picked:
            fields["actions"] = list(dict.fromkeys(picked))
    groups = data.get("groups")
    if isinstance(groups, list) and groups:
        fields["groups"] = [re.sub(r"\s+", " ", str(name)).strip() for name in groups if str(name).strip()][:200]
    if fields:
        save_screen(**fields)
    return jsonify(success=True)


@app.post("/<access_path>/reset-browser")
def reset_browser_endpoint(access_path: str):
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    data = request.get_json(silent=True) or {}
    if not csrf_ok(data):
        return jsonify(success=False, message="انتهت صلاحية الصفحة. أعد تحميلها ثم حاول مجددًا."), 400
    # Only the shown account's browser is closed; its profile stays (its cookies and session are kept).
    token = str(data.get("auth_token") or "").strip()
    if not valid_auth_token(token):
        with screen_lock:
            token = active_token
    if valid_auth_token(token):
        folder = manual_profile_folder(token)
        try:
            _drop_task_browser(folder)
        except Exception:
            pass
        if _login_state.get("page") is not None and str(_login_state.get("folder") or MANUAL_BROWSER) == folder:
            release_manual_browser()
        return jsonify(success=True, message="تمت إعادة تعيين متصفح هذا الحساب. جلسته محفوظة.")
    release_manual_browser()
    return jsonify(success=True, message="تمت إعادة تعيين المتصفح.")


@app.get("/<access_path>/phone-check")
def phone_check_endpoint(access_path: str):
    """«اختبار قدرة الهاتف»: what the app reads of the phone (memory, processor, its WebView, heat, battery,
    background permissions). The page adds a speed test and says how many accounts can work at once."""
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    report: dict = {"in_app": False}
    if IN_APP:
        try:
            from java import jclass
            loaded = json.loads(str(jclass("app.tg.groups.BrowserHost").deviceReport()) or "{}")
            if isinstance(loaded, dict):
                report = loaded
        except Exception:
            report = {"in_app": False}
    with jobs_lock:
        report["tasks_running"] = sum(1 for job in jobs.values() if job.get("status") == "running" and job.get("kind") == "execute")
    report["max_accounts"] = MAX_ACCOUNTS
    return jsonify(success=True, report=report)


@app.post("/<access_path>/groups")
def groups_endpoint(access_path: str):
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    data = request.get_json(silent=True) or {}
    if not csrf_ok(data):
        return jsonify(success=False, message="انتهت صلاحية الصفحة. أعد تحميلها ثم حاول مجددًا."), 400
    auth_token = str(data.get("auth_token", "")).strip()
    pin = str(data.get("chat_pin", "")).strip()
    if not valid_auth_token(auth_token):
        return jsonify(success=False, message="أدخل auth_token صالحًا."), 400
    if not valid_chat_pin(pin):
        return jsonify(success=False, message="رمز الدردشة يجب أن يكون من ٤ إلى ٨ أرقام."), 400
    settle = bool(data.get("wait"))
    settle_seconds = parse_requested_count(data.get("wait_seconds")) or 10
    settle_seconds = max(1, min(120, settle_seconds))
    if account_busy(hashlib.sha256(auth_token.encode("utf-8")).hexdigest()):
        # Its browser is taken by a task (or will be): the groups list would wait until all of them end.
        return jsonify(success=False, message="هذا الحساب يعمل على مهمة الآن. اختر من القروبات المعروضة سابقًا، "
                                              "أو اعرض القروبات بعد انتهاء مهامه.", groups=[])
    try:
        names, error = fetch_group_names(auth_token, pin, settle, settle_seconds)
    except Exception:
        app.logger.warning("group list failed")
        return jsonify(success=False, message="تعذّر فتح الدردشة."), 502
    if error:
        return jsonify(success=False, message=error, groups=[])
    current_group = str(account_screen(auth_token).get("group") or "")     # (this account's own)
    if current_group not in names:
        current_group = ""
    save_screen(auth_token=auth_token, chat_pin=pin, groups=names, group=current_group)
    return jsonify(success=True, groups=names, message=f"ظهر {len(names)} قروب.")


@app.post("/<access_path>/group-run")
def group_run_endpoint(access_path: str):
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    data = request.get_json(silent=True) or {}
    if not csrf_ok(data):
        return jsonify(success=False, message="انتهت صلاحية الصفحة. أعد تحميلها ثم حاول مجددًا."), 400
    auth_token = str(data.get("auth_token", "")).strip()
    pin = str(data.get("chat_pin", "")).strip()
    # «روابط التغريدات»: the page sends the pasted tweets instead of a group (no chat PIN needed then).
    by_links = data.get("links") is not None
    tweet_links: list[dict] = []
    if by_links:
        group_name, stop_raw, stop_id = LINKS_TASK_NAME, "", ""
        if not valid_chat_pin(pin):
            pin = ""
    else:
        group_name = re.sub(r"\s+", " ", str(data.get("group", ""))).strip()
        stop_raw = str(data.get("stop_tweet") or "").strip()
        stop_id = extract_status_id(stop_raw) if stop_raw else ""
    requested_actions = data.get("actions")
    if not valid_auth_token(auth_token):
        return jsonify(success=False, message="أدخل auth_token صالحًا."), 400
    if by_links:
        if not isinstance(data.get("links"), list) or len(data["links"]) > MAX_TWEET_LINKS:
            return jsonify(success=False, message=f"الحد الأقصى {MAX_TWEET_LINKS} رابط في المهمة الواحدة."), 400
        tweet_links = tweet_links_from(data["links"])
        if not tweet_links:
            return jsonify(success=False, message="الصق رابط تغريدة واحدًا على الأقل."), 400
        tweet_links = [item for item in tweet_links if not tweet_is_ignored(item["url"])]
        if not tweet_links:
            return jsonify(success=False, message="لا توجد تغريدات للتنفيذ."), 400
    else:
        if not valid_chat_pin(pin):
            return jsonify(success=False, message="رمز الدردشة يجب أن يكون من ٤ إلى ٨ أرقام."), 400
        if not group_name or len(group_name) > 80:
            return jsonify(success=False, message="اختر قروبًا من القائمة."), 400
        if stop_raw and not stop_id:
            return jsonify(success=False, message="رابط التغريدة غير صالح. الصق رابطها أو رقمها."), 400
        if not stop_id:
            return jsonify(success=False, message="الصق رابط التغريدة المحددة أو رقمها."), 400
    requested_count = len(tweet_links)
    if not isinstance(requested_actions, list) or not requested_actions or any(not isinstance(action, str) or action not in ALLOWED_ACTIONS for action in requested_actions):
        return jsonify(success=False, message="اختر إجراء واحدًا على الأقل."), 400
    group_wait_raw = data.get("group_wait")
    group_wait_s = DEFAULT_GROUP_WAIT_SECONDS
    if group_wait_raw is not None:
        parsed_wait = parse_requested_count(group_wait_raw)
        if parsed_wait is not None:
            group_wait_s = max(0, min(300, parsed_wait))
    reply_voice = str(data.get("reply_voice") or DEFAULT_REPLY_VOICE)
    if reply_voice not in REPLY_VOICES:
        reply_voice = DEFAULT_REPLY_VOICE
    requested_actions = list(dict.fromkeys(requested_actions))
    gemini_api_key = str(data.get("gemini_api_key") or "").strip()
    gemini_model = normalize_gemini_model(str(data.get("gemini_model") or ""))
    if not is_owner_copy():
        # A user's copy uses the Gemini key and model the owner set; what the page sends is ignored.
        gemini_api_key, gemini_model = "", ""
    if "comment" in requested_actions and not is_owner_copy():
        wait_for_owner_keys()                  # (a copy just started gets them now)
    if "comment" in requested_actions and gemini_writes_comments() and not control_configured():
        if not gemini_api_key:
            gemini_api_key = saved_gemini.get("api_key") or ""
        if not gemini_model:
            gemini_model = normalize_gemini_model(saved_gemini.get("model") or "")
        if not valid_gemini_key(gemini_api_key) or not gemini_model:
            if not is_owner_copy():
                return jsonify(success=False, message=no_keys_message()), 400
            return jsonify(success=False, message="أدخل مفتاح Gemini واسم النموذج قبل التعليق."), 400
        if is_owner_copy():
            remember_gemini(gemini_api_key, gemini_model or "")
    elif "comment" in requested_actions and is_owner_copy() and valid_gemini_key(gemini_api_key) and gemini_model:
        remember_gemini(gemini_api_key, gemini_model)      # (Grok writes the comments; the key typed is kept all the same)
    if updating.is_set():
        return jsonify(success=False, message="يجري تحديث البرنامج. انتظر قليلًا ثم أعد المحاولة."), 503
    auth_digest = hashlib.sha256(auth_token.encode("utf-8")).hexdigest()
    # A task added while the account is working is not refused: it waits in the account's line.
    if account_line_size(auth_digest) >= MAX_TASKS_PER_ACCOUNT:
        return jsonify(success=False, message=f"لهذا الحساب {MAX_TASKS_PER_ACCOUNT} مهام بين عاملة ومنتظرة (الحد الأقصى). "
                                              "انتظر انتهاء بعضها ثم أضف مهمة جديدة."), 429
    owner = session.get("csrf_token", "")
    client_id = request_client_id()
    start_phase, start_message = ("prepare", "التحقق من الجلسة…") if by_links else ("login", "فتح القروب…")
    if by_links:
        job_id, job_key = begin_job(owner, client_id, requested_count, "prepare", "التحقق من الجلسة…", "execute", group_name)
        # The group chosen on the page, and its tweet, stay as they were for the next group task.
        save_screen(auth_token=auth_token, actions=requested_actions, job_id=job_id, job_key=job_key, started_at=time.time())
    else:
        job_id, job_key = begin_job(owner, client_id, requested_count, "login", "فتح القروب…", "execute", group_name)
        save_screen(
            auth_token=auth_token,
            chat_pin=pin,
            group=group_name,
            stop_tweet=stop_raw,
            actions=requested_actions,
            job_id=job_id,
            job_key=job_key,
            started_at=time.time(),
        )
    with jobs_lock:
        if job_id in jobs:
            jobs[job_id]["auth_digest"] = auth_digest     # the account's line this task waits in
            jobs[job_id]["account"] = profile_key(auth_token)   # (its own: shown only on its account's panel)
    ahead = account_line_join(auth_digest, job_id)
    if ahead:
        publish_job(job_id, phase="queue", message=waiting_message(ahead))
    run_args = (auth_token, pin, group_name, requested_count, requested_actions, gemini_api_key, gemini_model or "",
                stop_id, group_wait_s, reply_voice, tweet_links)
    threading.Thread(
        target=run_group_job_in_turn,
        args=(job_id, auth_digest, start_phase, start_message, run_args),
        daemon=True,
    ).start()
    if ahead:
        return jsonify(success=True, job_id=job_id, job_key=job_key, queued=True, ahead=ahead, message=waiting_message(ahead))
    return jsonify(success=True, job_id=job_id, job_key=job_key, queued=False, message="بدأ التنفيذ.")


@app.post("/<access_path>/retry")
def retry_job_endpoint(access_path: str):
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    data = request.get_json(silent=True) or {}
    if not csrf_ok(data):
        return jsonify(success=False, message="انتهت صلاحية الصفحة. أعد تحميلها ثم حاول مجددًا."), 400
    job_id = str(data.get("job_id") or "").strip()
    job_key = str(data.get("job_key") or "").strip()
    with jobs_lock:
        job = jobs.get(job_id)
        if not job:
            return jsonify(success=False, message="لم يعد سجل هذه المهمة متاحًا."), 404
        key_ok = job_key_matches(job, job_key)
        owner_ok = bool(job.get("owner")) and job.get("owner") == session.get("csrf_token", "")
        if not key_ok and not owner_ok:
            return jsonify(success=False, message="لم يعد سجل هذه المهمة متاحًا."), 404
        if job.get("status") == "running":
            return jsonify(success=True, message="المهمة تعمل الآن.")
        args = job_run_args.get(job_id)
        if not job.get("resumable") or not args:
            return jsonify(success=False, message="لا يمكن إعادة هذه المهمة. ابدأ مهمة جديدة."), 400
        if updating.is_set():
            return jsonify(success=False, message="يجري تحديث البرنامج. انتظر قليلًا ثم أعد المحاولة."), 503
        auth_digest = str(job.get("auth_digest") or "") or hashlib.sha256(str(args[0]).encode("utf-8")).hexdigest()
        job["auth_digest"] = auth_digest
        start_phase = str(job.get("phase") or "act")
        start_message = f"إعادة المحاولة من التغريدة {len(job.get('results') or []) + 1}…"
        job["status"] = "running"
        job["success"] = None
        job["resumable"] = False
        job["cancel"] = False
        job["message"] = start_message
        job["updated_at"] = time.time()
        persist_jobs_unlocked()
    # (in its account's line, like a new task: it waits while the account is working)
    ahead = account_line_join(auth_digest, job_id)
    if ahead:
        publish_job(job_id, phase="queue", message=waiting_message(ahead))
    threading.Thread(target=run_group_job_in_turn, args=(job_id, auth_digest, start_phase, start_message, args), daemon=True).start()
    return jsonify(success=True, message=waiting_message(ahead) if ahead else "بدأت إعادة المحاولة.")


@app.post("/<access_path>/retry-failed")
def retry_failed_endpoint(access_path: str):
    """«إعادة المحاولة للفاشلة»: a new task on the same account with the finished task's failed tweets only, and on
    each only the actions that failed on it."""
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    data = request.get_json(silent=True) or {}
    if not csrf_ok(data):
        return jsonify(success=False, message="انتهت صلاحية الصفحة. أعد تحميلها ثم حاول مجددًا."), 400
    job_id = str(data.get("job_id") or "").strip()
    job_key = str(data.get("job_key") or "").strip()
    with jobs_lock:
        job = jobs.get(job_id)
        if not job or (not job_key_matches(job, job_key)
                       and not (job.get("owner") and job.get("owner") == session.get("csrf_token", ""))):
            return jsonify(success=False, message="لم يعد سجل هذه المهمة متاحًا."), 404
        if job.get("status") == "running":
            return jsonify(success=False, message="المهمة تعمل الآن. انتظر انتهاءها."), 409
        if job.get("retried_by"):
            return jsonify(success=False, message="أُعيدت المحاولة لفاشلة هذه المهمة من قبل."), 409
        items = failed_retry_items(job)
        actions = [action for action in (job.get("actions") or []) if action in ALLOWED_ACTIONS]
        args = job_run_args.get(job_id)
        account = str(job.get("account") or "")
        title = str(job.get("username") or LINKS_TASK_NAME)
    if not items:
        return jsonify(success=False, message="لا توجد إجراءات فاشلة يمكن إعادتها في هذه المهمة."), 400
    actions = [action for action in actions if any(action in item["only"] for item in items)] or \
        list(dict.fromkeys(action for item in items for action in item["only"]))
    # The account's token: as the task had it, or (after the app restarted) from the saved accounts.
    auth_token = str(args[0]) if args else ""
    if not auth_token and account:
        auth_token = next((row["token"] for row in saved_sessions if profile_key(row["token"]) == account), "")
    if not valid_auth_token(auth_token):
        return jsonify(success=False, message="لم يعد حساب هذه المهمة محفوظًا. اختره وأعد المهمة."), 400
    gemini_api_key = str(args[5]) if args else ""
    gemini_model = str(args[6]) if args else ""
    reply_voice = str(args[9]) if args and args[9] in REPLY_VOICES else DEFAULT_REPLY_VOICE
    if "comment" in actions and not is_owner_copy():
        wait_for_owner_keys()
    if "comment" in actions and gemini_writes_comments() and not control_configured():
        gemini_api_key = gemini_api_key or saved_gemini.get("api_key") or ""
        gemini_model = gemini_model or normalize_gemini_model(saved_gemini.get("model") or "") or ""
        if not valid_gemini_key(gemini_api_key) or not gemini_model:
            return jsonify(success=False, message=no_keys_message() if not is_owner_copy()
                           else "أدخل مفتاح Gemini واسم النموذج قبل التعليق."), 400
    if updating.is_set():
        return jsonify(success=False, message="يجري تحديث البرنامج. انتظر قليلًا ثم أعد المحاولة."), 503
    auth_digest = hashlib.sha256(auth_token.encode("utf-8")).hexdigest()
    if account_line_size(auth_digest) >= MAX_TASKS_PER_ACCOUNT:
        return jsonify(success=False, message=f"لهذا الحساب {MAX_TASKS_PER_ACCOUNT} مهام بين عاملة ومنتظرة (الحد الأقصى). "
                                              "انتظر انتهاء بعضها ثم أعد المحاولة."), 429
    name = (title if title.startswith("إعادة الفاشلة") else "إعادة الفاشلة · " + title)[:80]
    new_id, new_key = begin_job(session.get("csrf_token", ""), request_client_id(), len(items), "prepare",
                                "التحقق من الجلسة…", "execute", name)
    with jobs_lock:
        if new_id in jobs:
            jobs[new_id]["auth_digest"] = auth_digest
            jobs[new_id]["account"] = profile_key(auth_token)
        old = jobs.get(job_id)
        if old is not None:
            old["retried_by"] = new_id              # (its button goes: the retry is the new task)
        persist_jobs_unlocked()
    ahead = account_line_join(auth_digest, new_id)
    if ahead:
        publish_job(new_id, phase="queue", message=waiting_message(ahead))
    run_args = (auth_token, "", name, len(items), actions, gemini_api_key, gemini_model, "", DEFAULT_GROUP_WAIT_SECONDS,
                reply_voice, items)
    threading.Thread(target=run_group_job_in_turn, args=(new_id, auth_digest, "prepare", "التحقق من الجلسة…", run_args),
                     daemon=True).start()
    count = sum(len(item["only"]) for item in items)
    return jsonify(success=True, job_id=new_id, job_key=new_key, queued=bool(ahead), tweets=len(items), actions=count,
                   message=(waiting_message(ahead) if ahead
                            else f"بدأت إعادة {count} إجراء فاشل على {len(items)} تغريدة."))


@app.post("/<access_path>/stop")
def stop_job_endpoint(access_path: str):
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    data = request.get_json(silent=True) or {}
    if not csrf_ok(data):
        return jsonify(success=False, message="انتهت صلاحية الصفحة. أعد تحميلها ثم حاول مجددًا."), 400
    job_id = str(data.get("job_id") or "").strip()
    job_key = str(data.get("job_key") or "").strip()
    with jobs_lock:
        job = jobs.get(job_id)
        if not job:
            return jsonify(success=False, message="لا توجد عملية تعمل الآن."), 404
        key_ok = job_key_matches(job, job_key)
        owner_ok = bool(job.get("owner")) and job.get("owner") == session.get("csrf_token", "")
        if not key_ok and not owner_ok:
            return jsonify(success=False, message="لا توجد عملية تعمل الآن."), 404
        if job.get("status") != "running":
            return jsonify(success=True, message="التنفيذ متوقف أصلًا.")
        job["cancel"] = True
        job["message"] = "جارٍ إيقاف التنفيذ…"
        job["updated_at"] = time.time()
        persist_jobs_unlocked()
    return jsonify(success=True, message="جارٍ إيقاف التنفيذ.")


@app.get("/<access_path>/jobs/<job_id>/view")
def job_view(access_path: str, job_id: str):
    """The latest picture of a running task's browser, if newer than ?after=; asking keeps pictures coming for 3 s."""
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    with jobs_lock:
        job = jobs.get(job_id)
        allowed = bool(job) and (
            job_key_matches(job, request.headers.get("X-Job-Key", ""))
            or (csrf_matches(request.headers.get("X-CSRF-Token", ""))
                and bool(job.get("owner")) and job.get("owner") == session.get("csrf_token", ""))
        )
        running = allowed and job.get("status") == "running"
    if not allowed:
        return jsonify(success=False, message="لا توجد عملية بهذا المعرّف."), 404
    if not running:
        return "", 204
    try:
        after = int(request.args.get("after") or 0)
    except ValueError:
        after = 0
    with live_views_lock:
        view = live_views.setdefault(job_id, {"wanted_until": 0.0, "taken_at": 0.0, "image": None, "seq": 0})
        view["wanted_until"] = time.monotonic() + 3
        image, seq = view["image"], view["seq"]
    if not image or seq <= after:
        return "", 204
    return image, 200, {"Content-Type": "image/jpeg", "X-Frame": str(seq)}


@app.get("/<access_path>/jobs/<job_id>")
def job_status(access_path: str, job_id: str):
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    light = request.args.get("light") == "1"
    links = request.args.get("links") == "1"
    with jobs_lock:
        job = jobs.get(job_id)
        if not job:
            return jsonify(success=False, message="لا توجد عملية بهذا المعرّف."), 404
        if job_key_matches(job, request.headers.get("X-Job-Key", "")):
            return jsonify(public_job(job, light=light, links=links))
        if not csrf_matches(request.headers.get("X-CSRF-Token", "")):
            return jsonify(success=False, message="انتهت صلاحية الصفحة. أعد تحميلها ثم حاول مجددًا."), 400
        owner_ok = bool(job.get("owner")) and job.get("owner") == session.get("csrf_token", "")
        if not owner_ok:
            return jsonify(success=False, message="لا توجد عملية بهذا المعرّف."), 404
        return jsonify(public_job(job, light=light, links=links))


@app.get("/<access_path>/sessions")
def list_sessions_endpoint(access_path: str):
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    if not csrf_matches(request.headers.get("X-CSRF-Token", "")):
        return jsonify(success=False, message="انتهت صلاحية الصفحة. أعد تحميلها ثم حاول مجددًا."), 400
    with sessions_lock:
        rows = [public_session(row) for row in saved_sessions]
    with gemini_lock:
        gemini_key = saved_gemini.get("api_key") or ""
        gemini_model = saved_gemini.get("model") or ""
    if gemini_key and not is_owner_copy():
        # A user's page only shows that a key is there; the copy itself uses it.
        gemini_key = f"{gemini_key[:4]}…{gemini_key[-4:]}"
    # Whether someone (Grok, or Gemini with its key) can write this copy's comments; the owner's page is also
    # told when Grok writes them (chosen in «توزيع البرنامج»), and then asks for no Gemini key.
    writer = comments_writer()[0]
    comments_ready = writer != "gemini" or valid_gemini_key(saved_gemini.get("api_key") or "")
    engine = writer if is_owner_copy() else ""
    if not comments_ready and not is_owner_copy() and not owner_sync_state["ok"] and time.monotonic() - owner_sync_state["at"] > 5:
        threading.Thread(target=sync_with_owner, name="owner-sync", daemon=True).start()   # (no keys yet: ask now)
    own = own_claude_shown() if key_typed_here() else {"claude_key": "", "claude_model": ""}
    return jsonify(success=True, sessions=rows, gemini_api_key=gemini_key, gemini_model=gemini_model, comments_ready=comments_ready,
                   comments_engine=engine, **own)


@app.get("/<access_path>/gemini-usage")
def gemini_usage_endpoint(access_path: str):
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    if not csrf_matches(request.headers.get("X-CSRF-Token", "")):
        return jsonify(success=False, message="انتهت صلاحية الصفحة. أعد تحميلها ثم حاول مجددًا."), 400
    with gemini_usage_lock:
        comments = int(gemini_usage.get("comments") or 0)
        cost_comments = int(gemini_usage.get("cost_comments") or 0)
        since = gemini_usage.get("since") or 0
    return jsonify(
        success=True,
        since=since,
        comments=comments,
        # The comments the cost counts: since it was last reset.
        cost_comments=cost_comments,
        price_per_comment=GEMINI_PRICE_PER_COMMENT,
        total=round(cost_comments * GEMINI_PRICE_PER_COMMENT, 6),
    )


# The comments written for this copy and their cost, as the page shows them at its top. With a control server
# they are its numbers (kept there by code and by X account, so they stay when the app is installed again),
# asked for at most every COMMENTS_USAGE_CACHE_SECONDS; without one, this copy's own count.
COMMENTS_USAGE_CACHE_SECONDS = 30
_comments_usage_lock = threading.Lock()
_comments_usage_cache: dict = {"at": 0.0, "data": None}


def comments_usage(fresh: bool = False) -> dict:
    if not control_configured():
        with gemini_usage_lock:
            comments = int(gemini_usage.get("comments") or 0)
            cost_comments = int(gemini_usage.get("cost_comments") or 0)
        return {"success": True, "source": "local", "total": comments, "price": GEMINI_PRICE_PER_COMMENT,
                "cost": round(cost_comments * GEMINI_PRICE_PER_COMMENT, 2), "accounts": [], "stale": False}
    with _comments_usage_lock:
        cached = _comments_usage_cache["data"]
        if cached is not None and not fresh and time.monotonic() - _comments_usage_cache["at"] < COMMENTS_USAGE_CACHE_SECONDS:
            return cached
    token = _current_token()
    if not token:
        return {"success": False, "message": "التطبيق غير مُفعّل."}
    try:
        answer = _control_request("usage", {"token": token}, seconds=10)
    except RuntimeError as exc:                  # (unreachable too: the last numbers read are shown, marked old)
        with _comments_usage_lock:
            cached = _comments_usage_cache["data"]
        if cached is not None:
            return {**cached, "stale": True}
        return {"success": False, "message": str(exc)}
    accounts = []
    for row in answer.get("accounts") or []:
        if isinstance(row, dict):
            accounts.append({"name": str(row.get("name") or "")[:40], "n": int(row.get("n") or 0), "cost": round(float(row.get("cost") or 0), 2)})
    data = {"success": True, "source": "control", "total": int(answer.get("total") or 0), "cost": round(float(answer.get("cost") or 0), 2),
            "price": float(answer.get("price") or GEMINI_PRICE_PER_COMMENT), "accounts": accounts, "stale": False}
    with _comments_usage_lock:
        _comments_usage_cache.update(at=time.monotonic(), data=data)
    return data


def forget_comments_usage() -> None:
    """A comment was just written: the next look at the numbers asks the control server again."""
    with _comments_usage_lock:
        _comments_usage_cache["at"] = 0.0


@app.get("/<access_path>/comments-usage")
def comments_usage_endpoint(access_path: str):
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    if not csrf_matches(request.headers.get("X-CSRF-Token", "")):
        return jsonify(success=False, message="انتهت صلاحية الصفحة. أعد تحميلها ثم حاول مجددًا."), 400
    return jsonify(**comments_usage(fresh=request.args.get("fresh") == "1"))


@app.get("/<access_path>/stats")
def stats_endpoint(access_path: str):
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    if not csrf_matches(request.headers.get("X-CSRF-Token", "")):
        return jsonify(success=False, message="انتهت صلاحية الصفحة. أعد تحميلها ثم حاول مجددًا."), 400
    # The counts of the account the page is showing now (its token comes in a header; zeros when none).
    token = (request.headers.get("X-Account-Token") or "").strip()
    counts = account_counts(profile_key(token)) if valid_auth_token(token) else zero_counts()
    return jsonify(success=True, counts=counts)


@app.post("/<access_path>/gemini-usage/reset")
def gemini_usage_reset_endpoint(access_path: str):
    if not hmac.compare_digest(access_path, ACCESS_PATH) or not is_owner_copy():
        abort(404)
    data = request.get_json(silent=True) or {}
    if not csrf_ok(data):
        return jsonify(success=False, message="انتهت صلاحية الصفحة. أعد تحميلها ثم حاول مجددًا."), 400
    if not allow_attempt("cost-reset:" + (request.remote_addr or "unknown")):
        return jsonify(success=False, message="محاولات كثيرة. انتظر بضع دقائق ثم أعد المحاولة."), 429
    password = str(data.get("password") or "")
    if not hmac.compare_digest(password.encode("utf-8"), COST_RESET_PASSWORD.encode("utf-8")):
        return jsonify(success=False, message="كلمة السر غير صحيحة."), 403
    reset_gemini_cost()
    return jsonify(success=True, message="أُعيد تعيين التكلفة وعدد تعليقاتها إلى 0. العدد في أعلى الصفحة كما هو.")


@app.post("/<access_path>/gemini")
def save_gemini_endpoint(access_path: str):
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    data = request.get_json(silent=True) or {}
    if not csrf_ok(data):
        return jsonify(success=False, message="انتهت صلاحية الصفحة."), 400
    if not is_owner_copy():
        return jsonify(success=False, message="يضبط مفتاح Gemini والنموذج صاحب البرنامج."), 403
    api_key = str(data.get("gemini_api_key") or "").strip()
    model = normalize_gemini_model(str(data.get("gemini_model") or ""))
    if api_key and not valid_gemini_key(api_key):
        return jsonify(success=False, message="صيغة مفتاح Gemini غير صالحة."), 400
    if str(data.get("gemini_model") or "").strip() and not model:
        return jsonify(success=False, message="اسم النموذج غير صالح."), 400
    if not api_key and not model:
        return jsonify(success=True, message="لا يوجد ما يُحفظ.")
    remember_gemini(api_key, model or "")
    return jsonify(success=True, message="حُفظ مفتاح Gemini.")


@app.post("/<access_path>/claude")
def save_claude_endpoint(access_path: str):
    """«مفتاح Claude» in the panel of a copy with no «توزيع البرنامج»: saved, its comments are Claude's."""
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    data = request.get_json(silent=True) or {}
    if not csrf_ok(data):
        return jsonify(success=False, message="انتهت صلاحية الصفحة."), 400
    if not key_typed_here():
        return jsonify(success=False, message="مفتاح Claude هنا لنسخة تعمل بلا «توزيع البرنامج»."), 403
    api_key = str(data.get("api_key") or "").strip()
    model = str(data.get("model") or "").strip().lower() or CLAUDE_DEFAULT_MODEL
    with grok_lock:
        current = saved_grok["api_key"] if saved_grok["engine"] == "claude" else ""
    if not api_key and not current:
        return jsonify(success=False, message="الصق مفتاح Claude."), 400
    if api_key and not valid_claude_key(api_key):
        return jsonify(success=False, message="صيغة مفتاح Claude غير صالحة."), 400
    if not valid_claude_model(model):
        return jsonify(success=False, message="اسم نموذج Claude غير صالح."), 400
    remember_own_claude(api_key or current, model)
    return jsonify(success=True, message="حُفظ مفتاح Claude: التعليقات الآن بواسطة Claude.", comments_engine="claude", **own_claude_shown())


@app.post("/<access_path>/claude/delete")
def delete_claude_endpoint(access_path: str):
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    data = request.get_json(silent=True) or {}
    if not csrf_ok(data):
        return jsonify(success=False, message="انتهت صلاحية الصفحة."), 400
    if not key_typed_here():
        return jsonify(success=False, message="مفتاح Claude هنا لنسخة تعمل بلا «توزيع البرنامج»."), 403
    remember_own_claude("", "")
    return jsonify(success=True, message="حُذف مفتاح Claude: التعليقات بواسطة Gemini.", comments_engine="gemini", **own_claude_shown())


@app.post("/<access_path>/sessions/pin")
def save_session_pin_endpoint(access_path: str):
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    data = request.get_json(silent=True) or {}
    if not csrf_ok(data):
        return jsonify(success=False, message="انتهت صلاحية الصفحة."), 400
    auth_token = str(data.get("auth_token") or "").strip()
    pin = str(data.get("chat_pin") or "").strip()
    if not valid_auth_token(auth_token):
        return jsonify(success=False, message="أدخل رمز الجلسة أولًا."), 400
    if not valid_chat_pin(pin):
        return jsonify(success=False, message="رمز الدردشة ٤ إلى ٨ أرقام."), 400
    digest = hashlib.sha256(auth_token.encode("utf-8")).hexdigest()
    with sessions_lock:
        found = next((row for row in saved_sessions if hmac.compare_digest(row["digest"], digest)), None)
        if not found:
            return jsonify(success=False, message="احفظ الجلسة أولًا بالتحقق من الحساب."), 404
        found["chat_pin"] = pin
        persist_sessions_unlocked()
    return jsonify(success=True, message="حُفظ رمز الدردشة لهذا الحساب.")


@app.post("/<access_path>/sessions/delete")
def delete_session_endpoint(access_path: str):
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    data = request.get_json(silent=True) or {}
    if not csrf_ok(data):
        return jsonify(success=False, message="انتهت صلاحية الصفحة."), 400
    session_id = str(data.get("id", ""))
    removed = None
    with sessions_lock:
        removed = next((row for row in saved_sessions if row["id"] == session_id), None)
        if removed:
            saved_sessions[:] = [row for row in saved_sessions if row["id"] != session_id]
            persist_sessions_unlocked()
    if removed:
        with screen_lock:
            current = active_token
        if current and hmac.compare_digest(current, removed["token"]):
            save_screen(auth_token="")
        delete_profile(removed["token"])
        forget_account_data(removed["token"])
    return jsonify(success=True, message="حُذفت الجلسة.")


def forget_account_data(auth_token: str) -> None:
    """The account is removed: everything of its own goes with it, as when a copy of the program is deleted:
    its folder (its panel, its groups, its log), its counters, its memory of what it did, its tasks' records."""
    key = profile_key(auth_token)
    with screen_lock:
        screens.pop(key, None)
    with group_ids_lock:
        _group_stores.pop(key, None)
    shutil.rmtree(account_dir(key), ignore_errors=True)
    with action_counts_lock:
        if action_counts.pop(key, None) is not None:
            try:
                write_private_json(ACTION_COUNTS_PATH, {"by_account": action_counts})
            except Exception:
                pass
    stats_changed()
    with done_history_lock:
        if done_history.pop(key, None) is not None:
            try:
                write_private_json(DONE_HISTORY_PATH, {"version": 1, "accounts": done_history})
            except Exception:
                pass
    with jobs_lock:
        for job_id in [job_id for job_id, job in jobs.items() if job.get("account") == key and job.get("status") != "running"]:
            jobs.pop(job_id, None)
        for job in jobs.values():
            if job.get("account") == key and job.get("status") == "running":
                job["cancel"] = True                # (its tasks stop too: the account is gone)
        persist_jobs_unlocked()


@app.get("/<access_path>/update/check")
def update_check(access_path: str):
    """This copy's version and, in a user's copy, whether the owner offers a newer one."""
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    if is_owner_copy():
        return jsonify(success=True, owner=True, version=APP_VERSION, control_url=CONTROL_URL,
                       control_port=CONTROL_PORT if distribution_started.is_set() else 0)
    if request.args.get("light") or updating.is_set():
        return jsonify(success=True, owner=False, version=APP_VERSION, updating=updating.is_set())
    if time.monotonic() - owner_sync_state["at"] > 10:
        threading.Thread(target=sync_with_owner, name="owner-sync", daemon=True).start()
    now = time.monotonic()
    answer = update_check_cache["answer"]
    if answer is None or now - update_check_cache["at"] > 60:
        answer = latest_update()
        update_check_cache.update(at=now, answer=answer)
    if not answer.get("version"):
        return jsonify(success=True, owner=False, version=APP_VERSION, message=answer.get("message") or "")
    newer = version_tuple(answer["version"]) > version_tuple(APP_VERSION)
    return jsonify(success=True, owner=False, version=APP_VERSION, latest=answer["version"], available=newer)


@app.post("/<access_path>/update/apply")
def update_apply(access_path: str):
    """«تحديث» in a user's copy: download the owner's newest version, check it, keep the old file,
    put the new one in place and start again. Nothing changes when any step fails."""
    if not hmac.compare_digest(access_path, ACCESS_PATH) or is_owner_copy():
        abort(404)
    data = request.get_json(silent=True) or {}
    if not csrf_ok(data):
        return jsonify(success=False, message="انتهت صلاحية الصفحة. أعد تحميلها ثم حاول مجددًا."), 400

    def busy() -> bool:
        with jobs_lock:
            return any(job.get("status") == "running" for job in jobs.values())

    with jobs_lock:
        if updating.is_set():
            return jsonify(success=False, message="التحديث جارٍ."), 409
        updating.set()
    installed = False
    try:
        if busy():
            return jsonify(success=False, message="انتظر حتى تنتهي المهام الجارية ثم اضغط «تحديث»."), 409
        latest = latest_update()
        if not latest.get("version"):
            return jsonify(success=False, message=latest.get("message") or "تعذّر الاتصال بمصدر التحديث."), 502
        if version_tuple(latest["version"]) <= version_tuple(APP_VERSION):
            return jsonify(success=False, message="هذه النسخة على آخر إصدار."), 409
        status, body = ask_update_source("/update/file", 60)
        if status != 200:
            return jsonify(success=False, message=latest_update().get("message") or "تعذّر تنزيل التحديث."), 502
        problem = new_program_problem(body, latest)
        if problem:
            return jsonify(success=False, message=problem), 502
        if not program_starts(body):
            return jsonify(success=False, message="الإصدار الجديد لا يعمل على هذه الاستضافة. لم يتغير شيء."), 502
        if busy():
            return jsonify(success=False, message="بدأت مهمة أثناء التنزيل. انتظر حتى تنتهي ثم اضغط «تحديث»."), 409
        install_program(body)
        installed = True
    except OSError:
        return jsonify(success=False, message="تعذّر حفظ ملف التحديث. لم يتغير شيء."), 500
    finally:
        if not installed:
            updating.clear()
    threading.Thread(target=restart_program, name="restart", daemon=True).start()
    return jsonify(success=True, version=latest["version"], message=f"نُزّل الإصدار {latest['version']}. يُعاد تشغيل البرنامج…")


load_sessions()
load_group_ids()
load_done_history()
load_gemini()
load_panel_key()
load_gemini_usage()
load_action_counts()
load_jobs()
threading.Thread(target=save_jobs_in_background, name="jobs-saver", daemon=True).start()
if IN_APP:
    threading.Thread(target=close_idle_browsers_in_background, name="idle-browsers", daemon=True).start()
load_screen()
load_skip_users()
load_collected()
atexit.register(shutdown_jobs)


# «التغريدات المجموعة»: the tweets collected in the last 7 days, day by day, with «عرض الأكثر مشاهدة» on the
# days from yesterday to 6 days ago. One part in two places: content.py's page («إنشاء محتوى») shows it under its
# link box (see tweets_part), and without content.py it is a page of its own (TWEETS_PAGE). Its look is
# kept inside #tweets, so it changes nothing else on the page it is in; that page may set --tweets-day
# and --tweets-tweet, the backgrounds of a day and of a tweet.
TWEETS_PART_STYLE = r'''<style>
    #tweets { line-height: 1.55; }
    #tweets .tweets-summary { margin: 2px 0 0; color: var(--muted); font-size: 13px; }
    #tweets details { margin-top: 10px; border-radius: 14px; background: var(--tweets-day, var(--sheet)); box-shadow: inset 0 0 0 1px var(--line); }
    #tweets summary { display: flex; flex-wrap: wrap; align-items: center; gap: 6px; padding: 10px; cursor: pointer; list-style: none; font-weight: 700; }
    #tweets summary::-webkit-details-marker { display: none; }
    #tweets summary .day { font-size: 15px; white-space: nowrap; }
    #tweets summary .tail { margin-inline-start: auto; display: flex; align-items: center; gap: 6px; }
    #tweets summary .count { color: var(--muted); font-size: 13px; font-weight: 600; white-space: nowrap; }
    #tweets summary .tail::after { content: "‹"; color: var(--muted); font-size: 18px; line-height: 1; transition: transform 0.15s; }
    #tweets details[open] summary .tail::after { transform: rotate(-90deg); }
    #tweets ol { list-style: none; margin: 0; padding: 0 10px 10px; display: flex; flex-direction: column; gap: 6px; }
    #tweets li { position: relative; padding: 8px 10px; border-radius: 10px; background: var(--tweets-tweet, var(--paper)); box-shadow: inset 0 0 0 1px var(--line); }
    #tweets .text { margin: 0; font-size: 14px; white-space: pre-line; overflow-wrap: anywhere; display: -webkit-box; -webkit-line-clamp: 3; -webkit-box-orient: vertical; overflow: hidden; }
    #tweets li.has-content .text { padding-inline-end: 30px; }
    #tweets li.is-open .text { display: block; overflow: visible; }
    #tweets .tw-open { position: absolute; top: 6px; inset-inline-end: 6px; display: grid; place-items: center; width: 26px; height: 26px; min-height: 0;
      padding: 0; border: 0; border-radius: 50%; background: var(--tweets-day, var(--sheet)); color: var(--muted); box-shadow: inset 0 0 0 1px var(--line);
      font: inherit; font-size: 16px; font-weight: 700; line-height: 1; cursor: pointer; }
    #tweets .tw-open::before { content: "‹"; transition: transform 0.15s; }
    #tweets li.is-open .tw-open::before { transform: rotate(-90deg); }
    #tweets .more { display: flex; flex-direction: column; gap: 6px; margin-top: 6px; }
    #tweets .pics { display: grid; grid-template-columns: repeat(2, minmax(0, 1fr)); gap: 4px; }
    #tweets .pic { position: relative; display: block; aspect-ratio: 1; overflow: hidden; border-radius: 8px; background: var(--line); }
    #tweets .pic img { display: block; width: 100%; height: 100%; object-fit: cover; }
    #tweets .pics.one { grid-template-columns: minmax(0, 1fr); }
    #tweets .pics.one .pic { aspect-ratio: auto; min-height: 60px; }
    #tweets .pics.one .pic img { height: auto; max-height: 300px; object-fit: contain; }
    #tweets .quote .pics.one .pic img { max-height: 200px; }
    #tweets .pic.is-video::after { content: "▶"; position: absolute; inset: 0; display: grid; place-items: center; color: #fff; font-size: 24px;
      text-shadow: 0 1px 6px rgba(0, 0, 0, 0.6); }
    #tweets .pic.is-broken img { visibility: hidden; }
    #tweets .pic.is-broken::before { content: "تعذّر عرض الصورة"; position: absolute; inset: 0; display: grid; place-items: center; padding: 6px;
      color: var(--muted); font-size: 12px; text-align: center; }
    #tweets .quote { padding: 8px 10px; border-radius: 10px; background: var(--tweets-day, var(--sheet)); box-shadow: inset 0 0 0 1px var(--line); }
    #tweets .quote .by { color: var(--muted); font-size: 12px; font-weight: 600; }
    #tweets .quote p { margin: 2px 0 0; font-size: 13px; white-space: pre-line; overflow-wrap: anywhere; }
    #tweets .quote .pics { margin-top: 6px; }
    #tweets .meta { display: flex; flex-wrap: wrap; align-items: center; gap: 2px 10px; margin-top: 4px; color: var(--muted); font-size: 12px; }
    #tweets .meta .open { margin-inline-start: auto; color: var(--pine); font-weight: 700; text-decoration: none; }
    #tweets .tweets-empty { margin: 18px 0 6px; text-align: center; color: var(--muted); }
    #tweets .vbtn { flex: 0 0 auto; min-height: 30px; padding: 0 8px; border: 0; border-radius: 8px; background: var(--pine); color: #f4fbf7; box-shadow: none;
      font: inherit; font-size: 12px; font-weight: 700; cursor: pointer; }
    #tweets .vbtn:disabled { opacity: 0.45; cursor: default; }
    #tweets .vstatus { margin: 0 12px 8px; color: var(--muted); font-size: 12px; }
    #tweets .vstatus.is-bad { color: var(--clay); }
    #tweets .views { color: var(--pine); font-weight: 800; }
    #tweets .views.is-none { color: var(--muted); font-weight: 600; }
  </style>'''
TWEETS_PART_BODY = '''<p id="tweets-summary" class="tweets-summary"></p>
      <div id="tweets-days"></div>
      <p id="tweets-empty" class="tweets-empty" hidden>لم تُجمع تغريدات خلال آخر ٧ أيام.</p>'''
TWEETS_PART_SCRIPT = r'''<script>
  (() => {
    const tweets = {{ tweets|tojson }};
    const apiRoot = {{ api_root|tojson }};
    const csrf = {{ csrf_token|tojson }};
    let since = {{ server_now|tojson }};
    const pad = (n) => String(n).padStart(2, "0");
    const dayKey = (when) => when.getFullYear() + "-" + pad(when.getMonth() + 1) + "-" + pad(when.getDate());
    const dayName = new Intl.DateTimeFormat("ar-u-nu-latn", {weekday: "long", day: "numeric", month: "long"});
    const clock = new Intl.DateTimeFormat("ar-u-nu-latn", {hour: "numeric", minute: "2-digit"});
    const number = new Intl.NumberFormat("ar-u-nu-latn");
    const now = new Date();
    const todayStart = new Date(now.getFullYear(), now.getMonth(), now.getDate());
    const yesterday = new Date(now.getFullYear(), now.getMonth(), now.getDate() - 1);
    const label = (key, when) => key === dayKey(now) ? "اليوم" : key === dayKey(yesterday) ? "أمس" : dayName.format(when);
    // «عرض الأكثر مشاهدة» is for the days the script allows (today to 6 days ago). A day asked for waits
    // VIEWS_AGAIN seconds (10 minutes) before it can be asked for again; VIEWS_ASKED: the days still waiting
    // (the start of the day, in seconds → when it was asked for), in the server's time.
    const VIEWS_DAYS = {{ views_days|tojson }};
    const VIEWS_AGAIN = {{ views_again|tojson }};
    const VIEWS_ASKED = {{ views_asked|tojson }};
    const skew = since - Date.now() / 1000;
    const serverNow = () => Date.now() / 1000 + skew;
    let lastState = null;            // how the fetching was going when the server last said
    const minutesText = (seconds) => {
      const minutes = Math.max(1, Math.ceil(seconds / 60));
      return minutes === 1 ? "دقيقة" : minutes === 2 ? "دقيقتين" : minutes + (minutes % 100 >= 3 && minutes % 100 <= 10 ? " دقائق" : " دقيقة");
    };
    const daysAgo = (key) => {
      const [year, month, date] = key.split("-").map(Number);
      return Math.round((todayStart - new Date(year, month - 1, date)) / 86400000);
    };
    const canCheck = (key) => daysAgo(key) >= VIEWS_DAYS[0] && daysAgo(key) <= VIEWS_DAYS[1];
    const safeLink = (url) => /^https:\/\/(?:www\.)?(?:x|twitter)\.com\/[^\s"'<>]+$/.test(url || "") ? url : "";
    const viewsText = (tweet) => !tweet.views_at ? "" : tweet.views == null ? "لا يوجد رقم" : number.format(tweet.views) + " مشاهدة";
    const showViews = (span, tweet) => {
      span.textContent = viewsText(tweet);
      span.className = tweet.views == null ? "views is-none" : "views";
      span.hidden = !span.textContent;
    };
    const checkedAt = (seconds) => {
      const when = new Date(seconds * 1000);
      const today = new Date();
      const before = new Date(today.getFullYear(), today.getMonth(), today.getDate() - 1);
      const key = dayKey(when);
      return (key === dayKey(today) ? "" : key === dayKey(before) ? "أمس " : dayName.format(when) + " ") + clock.format(when);
    };

    // Each tweet once, under the day (in this device's time zone) it was first collected on.
    const days = new Map();
    for (const tweet of tweets) {
      const key = dayKey(new Date(tweet.at * 1000));
      if (!days.has(key)) days.set(key, {key, items: []});
      days.get(key).items.push({tweet, first: tweet.at});
    }
    const list = [...days.values()].sort((a, b) => b.key.localeCompare(a.key));
    const byId = new Map();          // tweet id → {tweet, day, li, views}
    let total = tweets.length;
    const showTotal = () => { document.getElementById("tweets-summary").textContent = "آخر ٧ أيام · " + total + " تغريدة"; };
    showTotal();
    document.getElementById("tweets-empty").hidden = list.length > 0;
    const box = document.getElementById("tweets-days");

    // A tweet's content (its text, pictures and the tweet it quotes) comes with its views. A small arrow
    // over the tweet opens it: the text in full, then the pictures. Closed, the text shows 3 lines.
    const smaller = (address) => /[?&]name=/.test(address) ? address.replace(/([?&]name=)[^&]*/, "$1small")
      : address + (address.includes("?") ? "&" : "?") + "name=small";
    function pictures(list, tweetLink) {
      const box = document.createElement("div");
      box.className = list.length === 1 ? "pics one" : "pics";
      for (const [kind, address] of list) {
        const link = document.createElement("a");
        link.className = kind === "video" ? "pic is-video" : "pic";
        link.href = kind === "photo" ? address : tweetLink || address;     // a photo opens in full; a video plays on X
        link.target = "_blank";
        link.rel = "noopener noreferrer";
        const image = document.createElement("img");
        image.src = smaller(address);
        image.alt = kind === "video" ? "فيديو" : "صورة";
        image.loading = "lazy";
        image.referrerPolicy = "no-referrer";
        image.addEventListener("error", () => link.classList.add("is-broken"));
        link.append(image);
        box.append(link);
      }
      return box;
    }
    function contentBox(tweet) {
      const box = document.createElement("div");
      box.className = "more";
      const link = safeLink(tweet.url);
      if ((tweet.pictures || []).length) box.append(pictures(tweet.pictures, link));
      const quoted = tweet.quote;
      if (quoted && (quoted.body || (quoted.pictures || []).length)) {
        const quote = document.createElement("div");
        quote.className = "quote";
        if (quoted.by) {
          const by = document.createElement("bdi");
          by.className = "by";
          by.dir = "ltr";
          by.textContent = "@" + quoted.by;
          quote.append(by);
        }
        if (quoted.body) {
          const text = document.createElement("p");
          text.dir = "auto";
          text.textContent = quoted.body;
          quote.append(text);
        }
        if ((quoted.pictures || []).length) quote.append(pictures(quoted.pictures, link));
        box.append(quote);
      }
      return box;
    }
    function setOpen(entry, open) {
      entry.open = open;
      entry.li.classList.toggle("is-open", open);
      entry.toggle.setAttribute("aria-expanded", open ? "true" : "false");
      if (open && !entry.more) {
        entry.more = contentBox(entry.tweet);    // made when first opened: a closed tweet loads no pictures
        entry.text.after(entry.more);
      }
      if (entry.more) entry.more.hidden = !open;
    }
    function showContent(entry) {
      const tweet = entry.tweet;
      entry.text.textContent = tweet.body || tweet.text || "تغريدة";
      const quoted = tweet.quote || {};
      // Not fetched yet (or nothing in it): no arrow.
      if (typeof tweet.body !== "string" || !(tweet.body || (tweet.pictures || []).length || quoted.body || (quoted.pictures || []).length)) return;
      if (!entry.toggle) {
        const toggle = document.createElement("button");
        toggle.type = "button";
        toggle.className = "tw-open";
        toggle.setAttribute("aria-label", "محتوى التغريدة");
        toggle.addEventListener("click", () => setOpen(entry, !entry.open));
        entry.li.classList.add("has-content");
        entry.li.prepend(toggle);
        entry.toggle = toggle;
      }
      if (entry.more) {
        entry.more.remove();                       // new content: made again when shown
        entry.more = null;
      }
      setOpen(entry, entry.open);
    }

    // The day's tweets: most viewed first once it has counts (tweets without one after), else newest first.
    function order(day) {
      const counted = day.items.some((item) => item.tweet.views_at);
      const sorted = [...day.items].sort((a, b) => {
        if (counted) {
          const va = a.tweet.views == null ? -1 : a.tweet.views;
          const vb = b.tweet.views == null ? -1 : b.tweet.views;
          if (va !== vb) return vb - va;
        }
        return b.first - a.first;
      });
      day.ol.replaceChildren(...sorted.map((item) => byId.get(item.tweet.id).li));
      // The first tweet with content shows it, the others are closed: so it is clear each one can be opened.
      let first = true;
      for (const item of sorted) {
        const entry = byId.get(item.tweet.id);
        if (!entry.toggle) continue;
        setOpen(entry, first);
        first = false;
      }
    }

    function showDay(day, state) {
      const status = day.status;
      const waiting = day.items.filter((item) => state && state.waiting.has(item.tweet.id)).length;
      status.className = "vstatus";
      if (waiting) {
        if (day.button) day.button.disabled = true;
        let text = (state.slow ? "يجلب المشاهدات ببطء لأن الخدمة طلبت التمهّل… بقي " : "يجلب المشاهدات… بقي ") + waiting + " من " + day.items.length;
        if (state.paused) text = "متوقف مؤقتًا لتجنّب الحظر · يتابع بعد " + Math.floor(state.paused / 60) + ":" + pad(state.paused % 60) + " · بقي " + waiting + " من " + day.items.length;
        status.textContent = text;
        status.hidden = false;
        day.busy = true;
        return;
      }
      if (day.busy) order(day);      // just finished: sort it now (not while numbers arrive)
      day.busy = false;
      // Asked for less than 10 minutes ago: its button waits (and comes back by itself).
      const wait = day.askedAt ? day.askedAt + VIEWS_AGAIN - serverNow() : 0;
      if (day.button) day.button.disabled = wait > 0;
      const counted = day.items.filter((item) => item.tweet.views_at).length;
      const last = Math.max(0, ...day.items.map((item) => item.tweet.views_at || 0));
      if (state && state.error && day.asked) {
        status.textContent = state.error;
        status.className = "vstatus is-bad";
      } else if (wait > 0) {
        status.textContent = (last ? "مرتّبة من الأكثر مشاهدة · فُحصت " + clock.format(new Date(last * 1000)) + " · " : "")
          + "يُتاح الفحص مجددًا بعد " + minutesText(wait);
      } else if (counted && counted < day.items.length && day.button) {
        status.textContent = "فُحصت " + counted + " من " + day.items.length + " · اضغط «عرض الأكثر مشاهدة» ليكمل";
      } else {
        status.textContent = last ? "مرتّبة من الأكثر مشاهدة · آخر فحص " + checkedAt(last) : "";
      }
      status.hidden = !status.textContent;
    }

    // Every day starts folded (today's too); a day opens when tapped, or when its views are asked for.
    list.forEach((day) => {
      day.items.sort((a, b) => b.first - a.first);
      const details = document.createElement("details");
      const summary = document.createElement("summary");
      const title = document.createElement("span");
      title.className = "day";
      title.textContent = label(day.key, new Date(day.items[0].first * 1000));
      // The count, the button and the fold arrow together: on a narrow screen they go under the day's name as one.
      const tail = document.createElement("span");
      tail.className = "tail";
      const count = document.createElement("span");
      count.className = "count";
      count.textContent = day.items.length + " تغريدة";
      tail.append(count);
      summary.append(title, tail);
      let button = null;
      if (canCheck(day.key)) {
        button = document.createElement("button");
        button.type = "button";
        button.className = "vbtn";
        button.textContent = "عرض الأكثر مشاهدة";
        tail.append(button);
      }
      const status = document.createElement("p");
      status.className = "vstatus";
      status.hidden = true;
      const ol = document.createElement("ol");
      const [year, month, date] = day.key.split("-").map(Number);
      // The day as the script knows it: its start, in seconds (and when it was last asked for, if lately).
      const start = new Date(year, month - 1, date).getTime() / 1000;
      Object.assign(day, {details, ol, status, button, count, start, askedAt: VIEWS_ASKED[String(start)] || 0});
      for (const item of day.items) {
        const li = document.createElement("li");
        const text = document.createElement("p");
        text.className = "text";
        text.dir = "auto";
        const meta = document.createElement("div");
        meta.className = "meta";
        const views = document.createElement("span");
        showViews(views, item.tweet);
        const time = document.createElement("span");
        time.textContent = clock.format(new Date(item.first * 1000));
        meta.append(views, time);
        if (item.tweet.group) {
          const group = document.createElement("span");
          group.textContent = item.tweet.group;
          meta.append(group);
        }
        const link = safeLink(item.tweet.url);
        if (link) {
          const open = document.createElement("a");
          open.className = "open";
          open.href = link;
          open.target = "_blank";
          open.rel = "noopener noreferrer";
          open.textContent = "فتح";
          meta.append(open);
        }
        li.append(text, meta);
        const entry = {tweet: item.tweet, day, li, views, text, toggle: null, more: null, open: false};
        byId.set(item.tweet.id, entry);
        showContent(entry);
      }
      order(day);
      showDay(day, null);
      if (button) button.addEventListener("click", async (event) => {
        event.preventDefault();
        event.stopPropagation();
        details.open = true;
        day.asked = true;
        button.disabled = true;
        status.className = "vstatus";
        status.textContent = "يبدأ جلب المشاهدات…";
        status.hidden = false;
        const range = [day.start, new Date(year, month - 1, date + 1).getTime() / 1000];
        let data;
        try {
          const response = await fetch(apiRoot + "/tweets/views", {
            method: "POST",
            headers: {"Content-Type": "application/json"},
            body: JSON.stringify({ranges: [range], offset: -new Date().getTimezoneOffset(), csrf_token: csrf})
          });
          data = await response.json();
        } catch (_) {
          data = {success: false, message: "تعذّر الاتصال بالسكربت."};
        }
        if (!data.success) {
          if (data.asked_at) day.askedAt = data.asked_at;     // asked for lately (from another page): it waits
          status.textContent = data.message || "تعذّر البدء.";
          status.className = data.done ? "vstatus" : "vstatus is-bad";
          button.disabled = !!data.done;
          return;
        }
        day.askedAt = (data.asked || {})[String(day.start)] || serverNow();
        apply(data);
        follow();
      });
      details.append(summary, status, ol);
      box.append(details);
    });

    // New counts from the server go into their tweets; then each day's line is brought up to date.
    function apply(data) {
      if (typeof data.now === "number") since = data.now;
      for (const [id, pair] of Object.entries(data.views || {})) {
        const entry = byId.get(id);
        if (!entry) continue;
        entry.tweet.views = pair[0];
        entry.tweet.views_at = pair[1];
        showViews(entry.views, entry.tweet);
        if (pair[2]) {
          for (const key of ["body", "pictures", "quote"]) delete entry.tweet[key];
          Object.assign(entry.tweet, pair[2]);
          showContent(entry);
        }
      }
      for (const id of data.removed || []) {
        const entry = byId.get(id);
        if (!entry) continue;
        entry.li.remove();
        entry.day.items = entry.day.items.filter((item) => item.tweet.id !== id);
        entry.day.count.textContent = entry.day.items.length + " تغريدة";
        byId.delete(id);
        total -= 1;
        showTotal();
      }
      const state = {waiting: new Set(data.waiting || []), paused: data.paused || 0, error: data.error || "", slow: !!data.slow};
      lastState = state;
      for (const day of list) showDay(day, state);
      return data.running || state.waiting.size > 0;
    }

    // The days waiting after a check: their line counts down, and their button comes back after 10 minutes.
    setInterval(() => {
      for (const day of list) if (day.askedAt && !day.busy) showDay(day, lastState);
    }, 15000);

    let following = false;
    async function follow() {
      if (following) return;
      following = true;
      for (;;) {
        await new Promise((done) => setTimeout(done, 2000));
        let data;
        try {
          data = await (await fetch(apiRoot + "/tweets/views?since=" + since, {cache: "no-store"})).json();
        } catch (_) {
          continue;
        }
        if (!data.success || !apply(data)) break;
      }
      following = false;
    }

    // A fetch may already be running (started earlier, or from another tab): follow it.
    fetch(apiRoot + "/tweets/views?since=" + since, {cache: "no-store"})
      .then((response) => response.json())
      .then((data) => { if (data.success && apply(data)) follow(); })
      .catch(() => {});
  })();
  </script>'''
TWEETS_PAGE = r'''<!doctype html>
<html lang="ar" dir="rtl">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>التغريدات المجموعة</title>
  <style>
    :root { --paper: #f3f5fa; --sheet: #ffffff; --ink: #101828; --muted: #667085; --line: #e4e7ec; --pine: #2f5bea; --clay: #b42318; color-scheme: light; }
    * { box-sizing: border-box; }
    [hidden] { display: none !important; }
    body { margin: 0; background: var(--paper); color: var(--ink); font-family: "IBM Plex Sans Arabic", "Segoe UI", Tahoma, sans-serif; line-height: 1.55; }
    main { width: min(560px, 100%); margin: 0 auto; padding: 14px 12px 32px; }
    header { display: flex; align-items: center; gap: 10px; }
    h1 { margin: 0; font-size: 18px; }
    .back { margin-inline-start: auto; display: inline-flex; align-items: center; min-height: 36px; padding: 0 12px; border-radius: 8px; background: var(--sheet);
      box-shadow: inset 0 0 0 1px var(--line); color: var(--ink); font-size: 13px; font-weight: 600; text-decoration: none; white-space: nowrap; }
  </style>
  ''' + TWEETS_PART_STYLE + r'''
</head>
<body>
  <main>
    <header>
      <h1>التغريدات المجموعة</h1>
      <a class="back" href="{{ back }}">رجوع</a>
    </header>
    <section id="tweets">
      ''' + TWEETS_PART_BODY + r'''
    </section>
  </main>
  ''' + TWEETS_PART_SCRIPT + r'''
</body>
</html>
'''


def tweets_part_values() -> dict:
    """What the tweets part is drawn with: the tweets, the panel's address, this browser's CSRF token
    (made here when it has none yet) and the server's time (the counts fetched after it are asked for)."""
    csrf_token = session.get("csrf_token")
    if not csrf_token:
        csrf_token = secrets.token_urlsafe(32)
        session["csrf_token"] = csrf_token
    now = time.time()
    with views_lock:
        asked = {str(start): at for start, at in recent_views_asks(now).items()}
    return {"tweets": collected_payload(), "api_root": "/" + ACCESS_PATH, "csrf_token": csrf_token, "server_now": now,
            "views_days": list(VIEWS_DAYS), "views_asked": asked, "views_again": VIEWS_AGAIN_SECONDS}


def tweets_part() -> dict[str, str]:
    """The tweets part for content.py's page, drawn now: its style, its markup and its script, each
    ready to put in the page as it is (the page gives the part's element the id "tweets")."""
    return {"style": TWEETS_PART_STYLE, "body": TWEETS_PART_BODY,
            "script": render_template_string(TWEETS_PART_SCRIPT, **tweets_part_values())}


@app.get("/<access_path>/tweets")
def tweets_page(access_path: str):
    """«عرض التغريدات»: the tweets collected in the last 7 days, day by day. When content.py shows them
    on its page, under its link box, they are there (an old link to this page goes to them)."""
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    if content_shows_tweets:
        return redirect("/" + ACCESS_PATH + "/content#tweets")
    return render_template_string(TWEETS_PAGE, back="/" + ACCESS_PATH, **tweets_part_values())


@app.post("/<access_path>/tweets/views")
def tweets_views_start(access_path: str):
    """«عرض الأكثر مشاهدة»: queue a day's tweets for their current view count. Any of the last 7 days (in
    the viewer's time zone); a day asked for waits VIEWS_AGAIN_SECONDS before it can be asked for again."""
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    data = request.get_json(silent=True) or {}
    if not csrf_ok(data):
        return jsonify(success=False, message="انتهت صلاحية الصفحة. أعد تحميلها."), 400
    spans = day_spans(data)
    try:
        offset = int(data.get("offset"))
    except (TypeError, ValueError):
        offset = None
    if not spans or offset is None or abs(offset) > 14 * 60:
        return jsonify(success=False, message="أعد تحميل الصفحة ثم حاول مرة أخرى."), 400
    now = time.time()
    today = local_day_number(now, offset)
    if any(not VIEWS_DAYS[0] <= today - local_day_number((start + end) / 2, offset) <= VIEWS_DAYS[1] for start, end in spans):
        return jsonify(success=False, message="فحص المشاهدات متاح لتغريدات آخر ٧ أيام فقط."), 400
    with views_lock:
        asked = recent_views_asks(now)
    last = max((asked.get(int(start), 0) for start, end in spans), default=0)
    if last:
        return jsonify(success=False, done=True, asked_at=last,
                       message=f"فُحص هذا اليوم قبل قليل. يُتاح الفحص مجددًا بعد {minutes_text(last + VIEWS_AGAIN_SECONDS - now)}."), 409
    with collected_lock:
        rows = [(row.get("views_at") or 0, -row["at"], status_id, row["url"]) for status_id, row in collected_tweets.items()
                if any(start <= row["at"] < end for start, end in spans)]
    rows = [entry for entry in rows if not tweet_is_ignored(entry[3])]
    if not rows:
        return jsonify(success=False, message="لا توجد تغريدات في هذا اليوم."), 400
    # All the day's tweets: the never counted first (newest first), then the oldest counts. So pressing
    # again after a stop starts with the ones it had not reached.
    rows.sort()
    queued = queue_views([status_id for checked, _, status_id, _ in rows])
    with views_lock:
        for start, end in spans:
            views_asked[int(start)] = now
    return jsonify(success=True, queued=queued, asked={str(int(start)): now for start, end in spans}, **views_status_payload(now))


@app.get("/<access_path>/tweets/views")
def tweets_views_status(access_path: str):
    """How «عرض الأكثر مشاهدة» is going, and the counts fetched since the page last asked."""
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    try:
        since = float(request.args.get("since") or 0)
    except ValueError:
        since = 0.0
    return jsonify(success=True, **views_status_payload(since))


# «إنشاء محتوى»: content.py beside the script adds its page to this panel.
CONTENT_FILE = Path(__file__).resolve().with_name("content.py")
content_ready = threading.Event()
# Why content.py could not be added when the script started ("" if it was, or was not there).
content_problem = ""
# content.py's page shows the collected tweets (under its link box), so they have no page of their own.
content_shows_tweets = False


def content_accounts() -> list[dict]:
    with sessions_lock:
        return [{"id": row["id"], "username": row.get("username") or "", "token": row["token"]} for row in saved_sessions]


def content_gemini_key() -> str:
    """The Gemini key saved on the panel (the owner's, on users' copies: in memory, from the check-ins)."""
    wait_for_owner_keys(gemini_only=True)
    with gemini_lock:
        return str(saved_gemini.get("api_key") or "")


def content_error(exc: BaseException) -> str:
    """The error, with the line of content.py it came from."""
    if isinstance(exc, SyntaxError):
        message, line = exc.msg, exc.lineno
    else:
        message, line = str(exc), None
        for frame in traceback.extract_tb(exc.__traceback__):
            if Path(frame.filename).name == CONTENT_FILE.name:
                line = frame.lineno
    return f"{type(exc).__name__}: {message}" + (f" (line {line})" if line else "")


def attach_content() -> None:
    """Add «إنشاء محتوى»: from content.py beside the owner's script, or, on a user's copy, from the one the
    owner packed into it (a content.py put beside a user's copy is not used: the page is the owner's)."""
    global content_problem, content_shows_tweets
    owner = is_owner_copy()
    if not (CONTENT_FILE.is_file() if owner else CONTENT_EMBEDDED):
        return
    try:
        if owner:
            spec = importlib.util.spec_from_file_location("content_page", CONTENT_FILE)
            content = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(content)
        else:
            source = gzip.decompress(base64.b64decode(CONTENT_EMBEDDED)).decode("utf-8")
            content = importlib.util.module_from_spec(importlib.util.spec_from_loader("content_page", loader=None, origin=str(CONTENT_FILE)))
            content.__file__ = str(CONTENT_FILE)
            exec(compile(source, str(CONTENT_FILE), "exec"), content.__dict__)
        added = content.attach(app, ACCESS_PATH, SimpleNamespace(
            data_dir=DATA_DIR,
            accounts=content_accounts,
            current_token=lambda: screen_payload()["auth_token"],
            # Any free browser profile of the account, so a running task does not hold it up.
            run_browser=lambda token, work: run_on_fresh_browser(token, work),
            goto_x=goto_x,
            gemini_key=content_gemini_key,
            tweets_part=tweets_part,
            posts_per_day=None if owner else USER_POSTS_PER_DAY,
        ))
    except Exception as exc:
        content_problem = content_error(exc)
        print(f"لم تُضف صفحة إنشاء المحتوى ({CONTENT_FILE.name}): {content_problem}", flush=True)
        return
    # What its page took on (an older content.py says nothing: the tweets keep their own page).
    content_shows_tweets = isinstance(added, dict) and bool(added.get("tweets"))
    content_ready.set()


CONTENT_UNAVAILABLE_PAGE = """<!doctype html>
<html lang="ar" dir="rtl">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>إنشاء محتوى</title>
  <style>
    * { box-sizing: border-box; }
    body { margin: 0; background: #f3efe6; color: #1c1915; font-family: "IBM Plex Sans Arabic", "Segoe UI", Tahoma, sans-serif; }
    main { width: min(560px, 100%); margin: 0 auto; padding: 16px; }
    h1 { margin: 0; font-size: 18px; }
    .why { margin-top: 12px; padding: 12px 14px; border-radius: 14px; background: #fbf1ee; color: #8d3a32; line-height: 1.7; }
    .why p { margin: 0; }
    .why pre { margin: 8px 0; padding: 8px 10px; border-radius: 8px; background: #fff; direction: ltr; text-align: left;
      white-space: pre-wrap; overflow-wrap: anywhere; font-size: 13px; }
    .hint { color: #6e675e; font-size: 13px; line-height: 1.6; overflow-wrap: anywhere; }
    a { color: #0f6b50; font-weight: 600; }
  </style>
</head>
<body>
  <main>
    <h1>إنشاء محتوى</h1>
    <div class="why">
      <p>{{ reason }}</p>
      {% if problem %}<pre>{{ problem }}</pre>{% endif %}
      {% if fix %}<p>{{ fix }}</p>{% endif %}
    </div>
    <p class="hint">مجلد gg.py الذي يعمل الآن: <bdi dir="ltr">{{ here }}</bdi><br>Python <bdi dir="ltr">{{ python }}</bdi></p>
    <a href="{{ panel }}">العودة للوحة</a>
  </main>
</body>
</html>"""


def content_unavailable(access: str):
    """«إنشاء محتوى» when its page could not be added: why, and what to do."""
    if not hmac.compare_digest(access, ACCESS_PATH):
        abort(404)
    problem = fix = ""
    if not is_owner_copy():
        if content_problem:
            reason, problem, fix = "تعذّر تحميل صفحة إنشاء المحتوى في هذه النسخة:", content_problem, "أرسل هذه الرسالة لصاحب البرنامج."
        else:
            reason = "صفحة إنشاء المحتوى لم تصل إلى هذه النسخة بعد: تصل مع تحديث ينشره صاحب البرنامج."
    elif not CONTENT_FILE.is_file():
        reason = "لا يوجد ملف content.py بجانب gg.py في هذا المجلد."
    elif content_problem:
        reason, problem, fix = "تعذّر تحميل content.py عند تشغيل gg.py:", content_problem, "أعد تنزيل content.py ثم أعد تشغيل gg.py."
    else:
        reason = "وُضع content.py بعد تشغيل gg.py. أعد تشغيل gg.py لتظهر صفحة إنشاء المحتوى."
    return render_template_string(CONTENT_UNAVAILABLE_PAGE, reason=reason, problem=problem, fix=fix, here=str(CONTENT_FILE.parent),
                                  python=sys.version.split()[0], panel="/" + ACCESS_PATH), 503


attach_content()
if not content_ready.is_set():
    # The button shows whenever content.py is beside the script; without its page it says why.
    app.add_url_rule("/<access>/content", "content_unavailable", content_unavailable, methods=["GET"])






# ============================================================================
# قفل التطبيق + ربطه بخادم التحكّم (control_server.py على استضافة المالك).
# التطبيق لا يفتح إلا برمز يعرفه الخادم ولم يوقفه المالك، والتعليقات تُكتب على
# الخادم بمفاتيح المالك (لا تُرسل المفاتيح للجهاز). رابط الخادم مثبّت هنا، وبصمة
# شهادته داخل الرابط فلا يقبل التطبيق خادمًا آخر.
# ============================================================================
import http.client as _http_client
import ssl as _ssl

# رابط خادم التحكّم (المالك يضعه قبل البناء). متغيّر البيئة GG_CONTROL_LINK يغلبه (للاختبار).
CONTROL_LINK = "https://217.216.77.23:8443/yPyHqJkUQvv52HD7xxuomYeST1xigjf0mLPoFJHq#b8a830644e5ed5eb80bf2ee7005ec4c29d7a60ad7f47ab3eee899bb04ac47a46"
_CONTROL_RE = re.compile(r"https://(\[[0-9A-Fa-f:]{2,39}\]|[A-Za-z0-9](?:[A-Za-z0-9.\-]{0,251}[A-Za-z0-9])?)(?::(\d{1,5}))?/([A-Za-z0-9_\-]{16,64})/?#([0-9a-fA-F]{64})")
UNLOCK_PATH = DATA_DIR / "unlock.json"
_unlock_lock = threading.Lock()
_unlock_cache = {"token": "", "code": "", "ok": False, "at": 0.0}
_CONTROL_GRACE = 120          # ثوانٍ: بين كل تحقّق وآخر مع الخادم (حتى لا يُثقل كل طلب)


class _ControlUnreachable(RuntimeError):
    pass


def control_link() -> str:
    return (os.environ.get("GG_CONTROL_LINK") or CONTROL_LINK or "").strip()


DEVICE_PATH = DATA_DIR / "device.json"
_device_lock = threading.Lock()
_device_id_cache = ""


def device_id() -> str:
    """A stable id for this install, made once and kept — so a code binds to one phone (a copy of the code on
    another phone is refused). Letters and digits only."""
    global _device_id_cache
    with _device_lock:
        if _device_id_cache:
            return _device_id_cache
        got = str((read_private_json(DEVICE_PATH) or {}).get("id") or "")
        if not re.fullmatch(r"[A-Za-z0-9]{16,64}", got):
            got = secrets.token_hex(16)
            write_private_json(DEVICE_PATH, {"id": got})
        _device_id_cache = got
        return got


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


def _control_request(action: str, body: dict | None = None, seconds: float = 30) -> dict:
    """طلب واحد لخادم التحكّم، مع تثبيت شهادته ببصمة الرابط. يعيد ما يردّه، أو يرفع خطأ بعبارة للمستخدم."""
    parsed = _control_parse(control_link())
    if not parsed:
        raise RuntimeError("خادم التحكّم غير مضبوط في هذه النسخة. راجع صاحب البرنامج.")
    host, port, secret, pin = parsed
    context = _ssl.SSLContext(_ssl.PROTOCOL_TLS_CLIENT)
    context.check_hostname = False
    context.verify_mode = _ssl.CERT_NONE               # الشهادة تُعرف ببصمتها لا باسمها
    connection = _http_client.HTTPSConnection(host, port, timeout=8, context=context)
    try:
        try:
            connection.connect()
        except _ssl.SSLError:
            raise RuntimeError("على عنوان خادم التحكّم برنامج آخر. راجع الرابط.") from None
        except OSError:
            raise _ControlUnreachable("تعذّر الوصول إلى خادم التحكّم. تأكد من الإنترنت ومن أن الخادم يعمل.") from None
        seen = hashlib.sha256(connection.sock.getpeercert(binary_form=True) or b"").hexdigest()
        if not hmac.compare_digest(seen, pin):
            raise RuntimeError("شهادة خادم التحكّم لا تطابق الرابط المثبّت في التطبيق.")
        connection.sock.settimeout(seconds)
        sent = json.dumps(body or {}, ensure_ascii=False).encode("utf-8")
        connection.request("POST", f"/{secret}/{action}", body=sent,
                           headers={"Content-Type": "application/json; charset=utf-8", "Accept": "application/json", "Connection": "close"})
        answer = connection.getresponse()
        status, raw = answer.status, answer.read(1 << 20)
    except (socket.timeout, TimeoutError):
        raise _ControlUnreachable("طال انتظار خادم التحكّم. أعد المحاولة.") from None
    except (OSError, _http_client.HTTPException):
        raise _ControlUnreachable("انقطع الاتصال بخادم التحكّم. أعد المحاولة.") from None
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


def _load_unlock() -> tuple[str, str]:
    data = read_private_json(UNLOCK_PATH) or {}
    return str(data.get("token") or ""), str(data.get("code") or "")


def _current_token() -> str:
    with _unlock_lock:
        if _unlock_cache["token"]:
            return _unlock_cache["token"]
    token, code = _load_unlock()
    with _unlock_lock:
        _unlock_cache["token"], _unlock_cache["code"] = token, code
    return token


def _forget_unlock() -> None:
    try:
        UNLOCK_PATH.unlink()
    except OSError:
        pass
    with _unlock_lock:
        _unlock_cache.update(token="", code="", ok=False, at=0.0)


def control_activate(code: str) -> str:
    """يُفعّل بالرمز عبر الخادم (مربوطًا بجهاز هذا التطبيق)، ويحفظ رمز الجلسة. يعيد اسم المحرّك، أو يرفع خطأ."""
    data = _control_request("activate", {"code": code, "device": device_id()})
    token = str(data.get("token") or "")
    if not token:
        raise RuntimeError("لم يصل رمز الجلسة من الخادم. أعد المحاولة.")
    write_private_json(UNLOCK_PATH, {"token": token, "code": code})
    with _unlock_lock:
        _unlock_cache.update(token=token, code=code, ok=True, at=time.monotonic())
    stats_changed()
    return str(data.get("engine") or "")


def is_unlocked() -> bool:
    """هل التطبيق مفتوح: يوجد رمز جلسة محفوظ والخادم لم يوقف الرمز (يُتحقّق كل فترة). عند تعذّر الوصول
    للخادم يبقى على آخر حالة معروفة، فلا يُقفل المستخدم بانقطاع مؤقت للإنترنت."""
    token = _current_token()
    if not token:
        return False
    now = time.monotonic()
    with _unlock_lock:
        if _unlock_cache["ok"] and now - _unlock_cache["at"] < _CONTROL_GRACE:
            return True
    try:
        active = bool(_control_request("check", {"token": token}, seconds=8).get("active"))
    except _ControlUnreachable:
        with _unlock_lock:
            _unlock_cache.update(ok=True, at=now)       # إمهال: يبقى مفتوحًا برمز محفوظ ما دام الخادم بعيدًا
        return True
    except RuntimeError:
        active = False
    with _unlock_lock:
        _unlock_cache.update(ok=active, at=now)
    if not active:
        _forget_unlock()
    return active


def control_comment(tweet_text: str, image: bytes | None, voice: str, account: str, tweet_id: str) -> str:
    """تعليق واحد يُكتب على خادم التحكّم بمفتاح المالك المُفعّل (لا يُرسل المفتاح للجهاز)."""
    token = _current_token()
    if not token:
        raise RuntimeError("التطبيق غير مُفعّل. أدخل رمز الدخول.")
    if account:
        manner = int(hashlib.sha256(("reply-manner:" + account).encode("utf-8")).hexdigest()[:8], 16) % len(REPLY_MANNERS)
    else:
        manner = random.randrange(len(REPLY_MANNERS))
    with replies_memory_lock:
        own = list(replies_by_account.get(account) or []) if account else []
        others = [text for text in (replies_by_tweet.get(tweet_id) or []) if text not in own] if tweet_id else []
    before = (own[-6:] + others[-4:])[-10:]
    body = {"token": token, "text": tweet_text or "", "voice": voice, "manner": manner, "before": before,
            "account": account or "", "name": account_names.get(account, "")}
    if image:
        body["image"] = base64.b64encode(image).decode("ascii")
    text = str(_control_request("comment", body, seconds=90).get("comment") or "")
    if not text:
        raise RuntimeError("لم يصل تعليق من خادم التحكّم. أعد المحاولة.")
    record_comment_generated()
    forget_comments_usage()
    remember_reply(account, tweet_id, text)
    return text


# تنبيهات المالك وتعليماته من لوحة خادم التحكّم: تُطلب كل فترة، ويُحفظ آخر رقم وصل فلا يصل التنبيه مرتين.
NOTICES_SEEN_PATH = DATA_DIR / "notices_seen.json"
_notices_lock = threading.Lock()


def control_notices() -> list:
    """التنبيهات الجديدة من خادم التحكّم (الأقدم أولًا)، أو قائمة فارغة إن لم يكن مضبوطًا أو تعذّر الوصول."""
    if not control_configured():
        return []
    token = _current_token()
    if not token:
        return []
    with _notices_lock:
        try:
            after = int((read_private_json(NOTICES_SEEN_PATH) or {}).get("last") or 0)
        except (TypeError, ValueError):
            after = 0
        try:
            answer = _control_request("notices", {"token": token, "after": after}, seconds=10)
        except RuntimeError:                       # (_ControlUnreachable منها): يُعاد الطلب في المرة القادمة
            return []
        items = []
        for item in answer.get("notices") or []:
            if not isinstance(item, dict):
                continue
            text = str(item.get("text") or "").strip()[:1000]
            if not text:
                continue
            kind = str(item.get("kind") or "info")
            items.append({"id": int(item.get("id") or 0), "text": text,
                          "kind": kind if kind in ("info", "warn", "urgent") else "info", "at": int(item.get("at") or 0)})
        try:
            last = int(answer.get("last") or 0)
        except (TypeError, ValueError):
            last = after
        if last != after:
            write_private_json(NOTICES_SEEN_PATH, {"last": last})
    for item in items:
        print(f"تنبيه من الإدارة: {item['text']}", flush=True)
    return items


@app.get("/<access_path>/notices")
def notices_endpoint(access_path: str):
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    if not csrf_matches(request.headers.get("X-CSRF-Token", "")):
        return jsonify(success=False, message="انتهت صلاحية الصفحة. أعد تحميلها ثم حاول مجددًا."), 400
    return jsonify(success=True, notices=control_notices())


# «مساعدة»: رسالة من المستخدم إلى صاحب البرنامج (تصل إلى «الرسائل» في لوحة التحكّم) فيها وصف المشكلة وصور أو فيديو
# قصير. الصفحة تسلّم الملفات هنا واحدًا واحدًا (support/upload)، ثم ترسل الرسالة (support/send) فتُرفع الملفات إلى
# الخادم واحدًا واحدًا ثم الرسالة، في الخلفية، وتسأل الصفحة عن الحال (support/status).
SUPPORT_OUTBOX = DATA_DIR / "support-outbox"
SUPPORT_IMAGE_MAX = 8 * 1024 * 1024
SUPPORT_VIDEO_MAX = 25 * 1024 * 1024
SUPPORT_FILES_MAX = 5
_support_lock = threading.Lock()
_support_state = {"id": "", "state": "idle", "message": ""}


def _media_kind(head: bytes) -> str:
    """"image" or "video" by the file's own first bytes, or "" (the control server checks again)."""
    if head.startswith(b"\xff\xd8\xff") or head.startswith(b"\x89PNG") or head[:6] in (b"GIF87a", b"GIF89a") \
            or (head[:4] == b"RIFF" and head[8:12] == b"WEBP"):
        return "image"
    if head[4:8] == b"ftyp" and head[8:12] not in (b"heic", b"heix", b"mif1", b"msf1"):
        return "video"
    if head.startswith(b"\x1a\x45\xdf\xa3"):
        return "video"
    return ""


def _support_set(**fields) -> None:
    with _support_lock:
        _support_state.update(fields)


def support_meta() -> dict:
    """What is added to the message by itself, to help find the problem: the version, the phone, the accounts and
    the last lines of the log."""
    meta = {"version": shown_version(), "device": "", "log": "",
            "accounts": ", ".join("@" + name for name in sorted(set(account_names.values())) if name)}
    if IN_APP:
        try:
            import ggapp
            meta["device"] = str(ggapp.device_line())
            meta["log"] = (str(ggapp.log_text(60)) + "\n\n" + str(ggapp.general_log_text(40)))[-12000:]
        except Exception:
            pass
    return meta


def _support_send(send_id: str, text: str, ids: list[str]) -> None:
    token = _current_token()
    try:
        if not token:
            raise RuntimeError("التطبيق غير مُفعّل. أدخل رمز الدخول.")
        sent = []
        for number, file_id in enumerate(ids, 1):
            _support_set(state="sending", message=f"يرفع الملف {number} من {len(ids)}… (قد يأخذ وقتًا مع الفيديو)")
            path = SUPPORT_OUTBOX / file_id
            name = (read_private_json(SUPPORT_OUTBOX / (file_id + ".json")) or {}).get("name") or ""
            body = {"token": token, "name": name, "data": base64.b64encode(path.read_bytes()).decode("ascii")}
            sent.append(str(_control_request("support-file", body, seconds=300).get("file") or ""))
        _support_set(state="sending", message="يرسل الرسالة…")
        _control_request("support", {"token": token, "text": text, "files": [f for f in sent if f], "meta": support_meta()},
                         seconds=60)
        _support_set(state="done", message="وصلت رسالتك إلى صاحب البرنامج. يصلك ردّه في قائمة التنبيهات.")
        print("أُرسلت رسالة «مساعدة» إلى صاحب البرنامج.", flush=True)
    except (RuntimeError, OSError) as exc:
        _support_set(state="failed", message="لم تُرسل الرسالة: " + (str(exc) or "خطأ غير متوقع."))
    finally:
        for file_id in ids:
            for path in (SUPPORT_OUTBOX / file_id, SUPPORT_OUTBOX / (file_id + ".json")):
                try:
                    path.unlink()
                except OSError:
                    pass


@app.post("/<access_path>/support/upload")
def support_upload_endpoint(access_path: str):
    """One picture or video for «مساعدة», as the request's whole body (it is larger than the other requests)."""
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    if not csrf_matches(request.headers.get("X-CSRF-Token", "")):
        return jsonify(success=False, message="انتهت صلاحية الصفحة. أعد تحميلها ثم حاول مجددًا."), 400
    if not control_configured():
        return jsonify(success=False, message="المساعدة غير متاحة في هذه النسخة."), 400
    video = (request.headers.get("X-File-Type") or "").startswith("video/")
    limit = SUPPORT_VIDEO_MAX if video else SUPPORT_IMAGE_MAX
    size = request.content_length or 0
    if size <= 0:
        return jsonify(success=False, message="لم يصل الملف."), 400
    if size > limit:
        return jsonify(success=False, message=f"الملف أكبر من {limit // 1048576} ميجابايت."), 413
    SUPPORT_OUTBOX.mkdir(parents=True, exist_ok=True)
    cutoff = time.time() - 3 * 3600                     # (files left by a send that never came)
    for old in SUPPORT_OUTBOX.glob("*"):
        try:
            if old.stat().st_mtime < cutoff:
                old.unlink()
        except OSError:
            pass
    file_id = secrets.token_hex(12)
    path = SUPPORT_OUTBOX / file_id
    stream = request.environ.get("wsgi.input")
    left = size
    with open(path, "wb") as out:
        while left > 0:
            chunk = stream.read(min(65536, left)) if stream is not None else b""
            if not chunk:
                break
            out.write(chunk)
            left -= len(chunk)
    with open(path, "rb") as handle:
        head = handle.read(16)
    if left > 0 or not _media_kind(head):
        path.unlink(missing_ok=True)
        return jsonify(success=False, message="وصل الملف ناقصًا أو بنوع غير مدعوم. أرفق صورة أو فيديو MP4."), 400
    from urllib.parse import unquote
    name = unquote(request.headers.get("X-File-Name") or "")[:80]
    write_private_json(SUPPORT_OUTBOX / (file_id + ".json"), {"name": name})
    return jsonify(success=True, id=file_id)


@app.post("/<access_path>/support/send")
def support_send_endpoint(access_path: str):
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    data = request.get_json(silent=True) or {}
    if not csrf_ok(data):
        return jsonify(success=False, message="انتهت صلاحية الصفحة. أعد تحميلها ثم حاول مجددًا."), 400
    if not control_configured():
        return jsonify(success=False, message="المساعدة غير متاحة في هذه النسخة."), 400
    text = str(data.get("text") or "").strip()[:2000]
    ids = [str(item) for item in (data.get("files") or []) if re.fullmatch(r"[0-9a-f]{24}", str(item))][:SUPPORT_FILES_MAX]
    ids = [item for item in ids if (SUPPORT_OUTBOX / item).is_file()]
    if not text and not ids:
        return jsonify(success=False, message="اكتب وصف المشكلة."), 400
    with _support_lock:
        if _support_state["state"] == "sending":
            return jsonify(success=False, message="رسالة سابقة تُرسل الآن. انتظر انتهاءها."), 409
        send_id = secrets.token_hex(8)
        _support_state.update(id=send_id, state="sending", message="يبدأ الإرسال…")
    threading.Thread(target=_support_send, args=(send_id, text, ids), name="support-send", daemon=True).start()
    return jsonify(success=True, id=send_id)


@app.get("/<access_path>/support/status")
def support_status_endpoint(access_path: str):
    if not hmac.compare_digest(access_path, ACCESS_PATH):
        abort(404)
    if not csrf_matches(request.headers.get("X-CSRF-Token", "")):
        return jsonify(success=False, message="انتهت صلاحية الصفحة."), 400
    with _support_lock:
        return jsonify(success=True, **_support_state)


# أرقام التنفيذ (كما في رأس الصفحة) لكل حساب X تُرسل إلى خادم التحكّم ليراها المالك عند كل مستخدم. تُرسل قيمها
# كاملة لا زيادات، بعد كل تنفيذ (تُجمع ثوانيَ قليلة في إرسال واحد)، وكل ساعة حتى لو لم تتغيّر.
_stats_wake = threading.Event()
_stats_sent = {"body": "", "at": 0.0}
_STATS_GATHER = 20            # ثوانٍ: تُجمع فيها عدة تنفيذات في إرسال واحد
_STATS_EVERY = 3600           # ثوانٍ: يُرسل كل ساعة ولو لم يتغيّر شيء (إن فُقد إرسال أو أُعيد ضبط الخادم)


def stats_changed() -> None:
    _stats_wake.set()


def stats_snapshot() -> list:
    with action_counts_lock:
        rows = {key: dict(row) for key, row in action_counts.items()}
    return [dict({action: int(row.get(action) or 0) for action in ACTION_NAMES}, id=key, name=account_names.get(key, ""))
            for key, row in rows.items()]


def report_stats() -> bool:
    """يرسل الأرقام إن تغيّرت منذ آخر إرسال ناجح (أو مضت ساعة). يعيد True إن لم يبقَ شيء يُرسل."""
    if not control_configured():
        return True
    token = _current_token()
    if not token:
        return True
    accounts = stats_snapshot()
    body = json.dumps(accounts, sort_keys=True, ensure_ascii=False)
    if body == _stats_sent["body"] and time.monotonic() - _stats_sent["at"] < _STATS_EVERY:
        return True
    try:
        _control_request("stats", {"token": token, "accounts": accounts}, seconds=15)
    except RuntimeError:
        return False
    _stats_sent.update(body=body, at=time.monotonic())
    return True


def report_stats_in_background() -> None:
    _stats_wake.set()                         # أول إرسال بعد التشغيل
    while True:
        _stats_wake.wait(_STATS_EVERY)
        _stats_wake.clear()
        time.sleep(_STATS_GATHER)
        try:
            done = report_stats()
        except Exception:
            done = False
        if not done:                          # تعذّر الوصول: يُعاد بعد دقيقتين
            time.sleep(120)
            _stats_wake.set()


threading.Thread(target=report_stats_in_background, name="stats-to-control", daemon=True).start()


UNLOCK_PAGE = """<!doctype html><html lang="ar" dir="rtl"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1"><title>الدخول</title>
<style>body{font:16px/1.7 "IBM Plex Sans Arabic",system-ui,-apple-system,sans-serif;background:#f3f5fa;color:#101828;margin:0;display:grid;place-items:center;min-height:100vh;padding:16px;box-sizing:border-box}
.box{background:#fff;padding:28px 24px;border-radius:20px;width:min(92vw,350px);box-shadow:0 0 0 1px rgba(16,24,40,.06),0 18px 44px rgba(16,24,40,.10);text-align:center}
.box::before{content:"";display:block;width:46px;height:46px;margin:0 auto 12px;border-radius:14px;background:linear-gradient(135deg,#2f5bea,#7c5cff);box-shadow:0 8px 18px rgba(47,91,234,.3)}
h1{font-size:20px;margin:0 0 4px}p{color:#667085;font-size:14px;margin:0 0 18px}
input{width:100%;box-sizing:border-box;padding:13px;border-radius:12px;border:1px solid #e4e7ec;background:#f9fafb;color:#101828;text-align:center;font-size:18px;letter-spacing:2px}
input:focus{outline:none;border-color:#2f5bea;box-shadow:0 0 0 4px rgba(47,91,234,.14);background:#fff}
button{width:100%;padding:13px;border:0;border-radius:12px;background:linear-gradient(135deg,#2f5bea,#5b6ef5);color:#fff;font-weight:700;font-size:16px;cursor:pointer;margin-top:12px;box-shadow:0 8px 18px rgba(47,91,234,.28)}
button:disabled{opacity:.6}.msg{min-height:20px;color:#b42318;font-size:14px;margin-top:12px}</style></head>
<body><form class="box" onsubmit="go(event)"><h1>قروبات</h1><p>أدخل رمز الدخول الذي أعطاك إياه صاحب البرنامج.</p>
<input id="code" placeholder="XXXX-XXXX-XXXX" autocomplete="off" autocapitalize="characters" autofocus>
<button id="btn" type="submit">دخول</button><div class="msg" id="msg"></div></form>
<script>
async function go(e){e.preventDefault();var b=document.getElementById("btn"),m=document.getElementById("msg");
var code=document.getElementById("code").value.trim();if(!code)return;b.disabled=true;m.textContent="جارٍ التحقّق…";m.style.color="#667085";
try{var r=await fetch("/unlock",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({code:code})});
var d=await r.json();if(d.ok){location.href="/";}else{m.style.color="#b42318";m.textContent=d.error||"الرمز غير صحيح.";b.disabled=false;}}
catch(x){m.style.color="#b42318";m.textContent="تعذّر الاتصال. أعد المحاولة.";b.disabled=false;}}
</script></body></html>"""


@app.get("/unlock")
def unlock_screen():
    if not control_configured() or is_unlocked():
        return redirect("/" + ACCESS_PATH, code=302)
    return make_response(render_template_string(UNLOCK_PAGE))


@app.post("/unlock")
def unlock_submit():
    body = request.get_json(silent=True) or {}
    code = str(body.get("code") or "").strip()
    if not code:
        return jsonify(ok=False, error="أدخل الرمز."), 200
    try:
        control_activate(code)
    except RuntimeError as exc:
        return jsonify(ok=False, error=str(exc)), 200
    return jsonify(ok=True)


@app.before_request
def _unlock_gate():
    # لا قفل إن لم يُضبط خادم تحكّم (نسخة بلا رابط). وإلا: لا يمرّ شيء قبل إدخال رمز صالح.
    if not control_configured():
        return None
    path = request.path
    if path == "/healthz" or path == "/unlock":
        return None
    if is_unlocked():
        return None
    if request.method == "GET" and "text/html" in (request.headers.get("Accept") or ""):
        return redirect("/unlock", code=302)
    return jsonify(ok=False, error="التطبيق مقفل. أدخل رمز الدخول."), 423



if __name__ == "__main__":
    port = int(os.getenv("PORT", "5000"))
    bind_host = os.getenv("BIND_HOST", "0.0.0.0")
    public_base_url = os.getenv("PUBLIC_BASE_URL", "").rstrip("/")
    if public_base_url:
        print(f"X profile/repost checker: {public_base_url}/", flush=True)
    else:
        print(f"Flask listening on {bind_host}:{port}", flush=True)
        print(f"Local URL: http://127.0.0.1:{port}/", flush=True)
        try:
            for address in sorted(set(socket.gethostbyname_ex(socket.gethostname())[2])):
                if not address.startswith("127."):
                    print(f"Host URL: http://{address}:{port}/", flush=True)
        except OSError:
            pass
        print("For public use, configure HTTPS and set PUBLIC_BASE_URL.", flush=True)
    start_distribution(bind_host)
    try:
        fill_collected_from_history()
    except Exception as exc:          # (never in the way of starting)
        print(f"لم تُضف التغريدات الأخيرة إلى التغريدات المجموعة: {type(exc).__name__}: {exc}", flush=True)
    if not is_owner_copy():
        threading.Thread(target=owner_sync_loop, name="owner-sync", daemon=True).start()
    app.run(host=bind_host, port=port, debug=False, threaded=True)
