
import array
import ctypes
import datetime
import glob
import hashlib
import hmac
import ipaddress
import ssl
import uuid
import unicodedata
import io
import math
import wave
import concurrent.futures
import difflib
import json
import os
import queue
import random
import re
import secrets
import socket
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

try:
    import psutil
    HAVE_PSUTIL = True
except ImportError:
    HAVE_PSUTIL = False

ENABLE_PY_WAKE = "--now" not in sys.argv and os.environ.get("JARVIS_PY_WAKE", "1") == "1"
HAVE_AUDIO = False
HAVE_WAKEWORD = False
if ENABLE_PY_WAKE:
    try:
        import numpy as np
        import sounddevice as sd
        HAVE_AUDIO = True
    except ImportError:
        pass
    try:
        import openwakeword
        from openwakeword.model import Model as WakeWordModel
        HAVE_WAKEWORD = HAVE_AUDIO
    except ImportError:
        pass

try:
    import sherpa_onnx
    HAVE_SPK = True
except ImportError:
    HAVE_SPK = False

try:
    import asyncio as _asyncio
    import edge_tts
    HAVE_EDGE_TTS = True
except ImportError:
    HAVE_EDGE_TTS = False

try:
    import anthropic
    HAVE_ANTHROPIC = True
except ImportError:
    HAVE_ANTHROPIC = False

EDGE_VOICE_EN = os.environ.get("JARVIS_EDGE_VOICE_EN", "en-US-EricNeural")
EDGE_VOICE_KO = os.environ.get("JARVIS_EDGE_VOICE_KO", "ko-KR-InJoonNeural")
EDGE_VOICE_OTHER = {"ja": "ja-JP-KeitaNeural", "zh-CN": "zh-CN-YunxiNeural", "es": "es-ES-AlvaroNeural",
                    "fr": "fr-FR-HenriNeural", "de": "de-DE-ConradNeural"}
EDGE_RATE = os.environ.get("JARVIS_EDGE_RATE", "+35%")
EDGE_RATE_DEFAULT = EDGE_RATE
EDGE_PITCH = os.environ.get("JARVIS_EDGE_PITCH", "-7Hz")

HAVE_WINDLL = hasattr(ctypes, "windll")

PORT = 5005
JARVIS_VERSION = os.environ.get("JARVIS_VERSION", "14.3")
ALLOW_COMPUTER_POWER = os.environ.get("JARVIS_ALLOW_SHUTDOWN", "0") == "1"
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
HTML_PATH = os.path.join(BASE_DIR, "jarvis.html")
START_TIME = time.time()
LOG_PATH = os.path.join(BASE_DIR, "jarvis_log.txt")
LOG_LOCK = threading.Lock()

WAKE_MODEL_NAME = "hey_jarvis"
WAKE_THRESHOLD = 0.4
WAKE_DEBUG = False
WAKE_SAMPLE_RATE = 16000
WAKE_CHUNK_SAMPLES = 1280
WAKE_COOLDOWN_SEC = 5

CLAP_ENABLED = True
CLAP_PEAK_THRESHOLD = 0.18
CLAP_QUIET_THRESHOLD = 0.07
CLAP_MIN_GAP_SEC = 0.12
CLAP_MAX_GAP_SEC = 1.0
CLAP_COOLDOWN_SEC = 5
CLAP_DEBUG = False
CLAP_DEBUG_MIN = 0.08

ACTIVITY_LOCK = threading.Lock()
LAST_SEEN_AT = 0.0
WAKE_PENDING = False


DASHBOARD_CLOSED = False


def mark_seen():
    global LAST_SEEN_AT, DASHBOARD_CLOSED
    with ACTIVITY_LOCK:
        LAST_SEEN_AT = time.time()
        DASHBOARD_CLOSED = False


def mark_closed():
    global DASHBOARD_CLOSED
    with ACTIVITY_LOCK:
        DASHBOARD_CLOSED = True


def tab_likely_open():
    with ACTIVITY_LOCK:
        return (not DASHBOARD_CLOSED) and (time.time() - LAST_SEEN_AT) < 90


def set_wake_pending():
    global WAKE_PENDING
    with ACTIVITY_LOCK:
        WAKE_PENDING = True


def consume_wake_pending():
    global WAKE_PENDING
    with ACTIVITY_LOCK:
        pending = WAKE_PENDING
        WAKE_PENDING = False
        return pending

ALLOWED_ORIGINS = {f"http://localhost:{PORT}", f"http://127.0.0.1:{PORT}"}
ALLOWED_HOSTS = {f"localhost:{PORT}", f"127.0.0.1:{PORT}"}
MAX_JSON_BYTES = 64 * 1024
MAX_AUDIO_BYTES = 15 * 1024 * 1024

SERVER_TOKEN = secrets.token_hex(16)
TOKEN_HEADER = "X-Jarvis-Token"

PHONE_ENABLED = os.environ.get("JARVIS_PHONE", "1") != "0"
PHONE_PORT = int(os.environ.get("JARVIS_PHONE_PORT", "5006"))
PHONE_COOKIE = "jarvis_phone"
PHONE_SESSION_DAYS = 30

CRASH_LOG = os.path.join(os.path.dirname(os.path.abspath(__file__)), "jarvis_crash.txt")
RUN_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "jarvis_run.json")
_RUN = {"crashed": False, "fh": None, "ctrl": None, "owner": False}


def _crash_note(text):
    try:
        with open(CRASH_LOG, "a", encoding="utf-8") as f:
            f.write(time.strftime("%Y-%m-%d %H:%M:%S") + "  " + text.rstrip() + "\n")
    except Exception:
        pass


def _run_state(**kw):
    try:
        st = {}
        if os.path.exists(RUN_FILE):
            with open(RUN_FILE, encoding="utf-8") as f:
                st = json.load(f)
        st.update(kw)
        with open(RUN_FILE, "w", encoding="utf-8") as f:
            json.dump(st, f, ensure_ascii=False)
    except Exception:
        pass


def mark_server_running():
    _RUN["owner"] = True
    now = time.strftime("%Y-%m-%d %H:%M:%S")
    _run_state(state="running", pid=os.getpid(), started=now, alive=now)

    def _alive():
        while True:
            time.sleep(30)
            _run_state(alive=time.strftime("%Y-%m-%d %H:%M:%S"))
    threading.Thread(target=_alive, daemon=True, name="alive").start()


def install_crash_logging(version):
    import atexit
    import faulthandler
    import traceback
    try:
        with open(RUN_FILE, encoding="utf-8") as f:
            prev = json.load(f)
        alive = HAVE_PSUTIL and prev.get("pid") and psutil.pid_exists(int(prev["pid"]))
        if prev.get("state") == "running" and not alive:
            _crash_note(f"[지난 실행이 갑자기 꺼짐] 시작 {prev.get('started')} · 마지막으로 살아 있던 시각 {prev.get('alive')} "
                        f"(창이 닫혔거나, 강제로 꺼졌거나, 컴퓨터가 꺼짐)")
    except Exception:
        pass
    _crash_note(f"[시작] v{version} pid {os.getpid()}")
    try:
        _RUN["fh"] = open(CRASH_LOG, "a", encoding="utf-8")
        faulthandler.enable(file=_RUN["fh"], all_threads=True)
    except Exception:
        pass

    def _hook(et, ev, tb):
        _RUN["crashed"] = True
        _crash_note("[오류로 꺼짐]\n" + "".join(traceback.format_exception(et, ev, tb)))
        sys.__excepthook__(et, ev, tb)
    sys.excepthook = _hook

    def _thread_hook(a):
        if a.exc_type is SystemExit:
            return
        _crash_note(f"[작업 스레드 오류: {a.thread.name if a.thread else '?'}] (서버는 계속 동작)\n"
                    + "".join(traceback.format_exception(a.exc_type, a.exc_value, a.exc_traceback)))
    threading.excepthook = _thread_hook

    def _bye():
        if not _RUN["crashed"]:
            _crash_note("[종료] 정상 종료")
        if _RUN["owner"]:
            _run_state(state="crashed" if _RUN["crashed"] else "stopped", stopped=time.strftime("%Y-%m-%d %H:%M:%S"))
    atexit.register(_bye)

    if os.name == "nt":
        try:
            k32 = ctypes.windll.kernel32
            names = {0: "Ctrl+C", 1: "Ctrl+Break", 2: "콘솔 창을 닫음(X)", 5: "로그오프", 6: "컴퓨터 종료"}

            @ctypes.WINFUNCTYPE(ctypes.c_int, ctypes.c_uint)
            def _on_ctrl(ev):
                _crash_note(f"[종료 신호] {names.get(ev, ev)}")
                if ev in (2, 5, 6) and _RUN["owner"]:
                    _run_state(state="stopped", stopped=time.strftime("%Y-%m-%d %H:%M:%S"))
                return 0
            _RUN["ctrl"] = _on_ctrl
            k32.SetConsoleCtrlHandler(_on_ctrl, True)
            h = k32.GetStdHandle(-10)
            mode = ctypes.c_uint()
            if k32.GetConsoleMode(h, ctypes.byref(mode)):
                k32.SetConsoleMode(h, (mode.value & ~0x0040) | 0x0080)
        except Exception:
            pass

WEBSITES = {
    "유튜브 뮤직": "https://music.youtube.com",
    "유튜브뮤직": "https://music.youtube.com",
    "유튜브": "https://youtube.com",
    "구글": "https://google.com",
    "네이버": "https://naver.com",
    "지메일": "https://mail.google.com",
    "메일": "https://mail.google.com",
    "깃허브": "https://github.com",
    "노션": "https://notion.so",
    "넷플릭스": "https://netflix.com",
    "인스타그램": "https://instagram.com",
    "페이스북": "https://facebook.com",
    "트위터": "https://twitter.com",
    "위키피디아": "https://ko.wikipedia.org",
    "지도": "https://map.naver.com",
    "날씨": "https://weather.naver.com",
}

HOME = os.path.expanduser("~")
_KNOWN_FOLDER_IDS = {
    "Desktop": "B4BFCC3A-DB2C-424C-B029-7FE99A87C641", "Documents": "FDD39AD0-238F-46AF-ADB4-6C85480369C7",
    "Downloads": "374DE290-123F-4565-9164-39C4925E467B", "Pictures": "33E28130-4E1E-4676-835A-98395C3BC3BB",
    "Music": "4BD8D571-6D19-48D3-BE97-422220080E43", "Videos": "18989B1D-99B5-455B-841C-AB7C74E4DDFC",
}


def known_folder(name):
    try:
        import ctypes as _ct
        import uuid as _uuid
        guid = (_ct.c_ubyte * 16).from_buffer_copy(_uuid.UUID(_KNOWN_FOLDER_IDS[name]).bytes_le)
        out = _ct.c_wchar_p()
        if _ct.windll.shell32.SHGetKnownFolderPath(_ct.byref(guid), 0, None, _ct.byref(out)) == 0:
            path = out.value
            _ct.windll.ole32.CoTaskMemFree(out)
            if path and os.path.isdir(path):
                return path
    except Exception:
        pass
    return os.path.join(HOME, name)


KNOWN = {k: known_folder(k) for k in _KNOWN_FOLDER_IDS}
FOLDER_KEYWORDS = {
    "바탕화면": KNOWN["Desktop"],
    "데스크탑": KNOWN["Desktop"],
    "다운로드": KNOWN["Downloads"],
    "문서": KNOWN["Documents"],
    "사진": KNOWN["Pictures"],
    "그림": KNOWN["Pictures"],
    "음악": KNOWN["Music"],
    "동영상": KNOWN["Videos"],
    "비디오": KNOWN["Videos"],
}

SEARCH_DIRS = list(dict.fromkeys(list(KNOWN.values()) + [os.path.join(HOME, d) for d in
                                   ("Desktop", "Downloads", "Documents", "Pictures", "Music", "Videos")]))
SKIP_DIR_NAMES = {"node_modules", ".git", "__pycache__", ".venv", "venv", "appdata", "$recycle.bin",
                  ".cache", "site-packages", ".idea", ".vscode", "dist", "build",
                  "windows", "program files", "program files (x86)", "programdata", "system volume information"}
FOLDER_INDEX_MAX_DEPTH = 6

VERB_STOPWORDS = [
    "열어줘", "열어봐", "열어", "실행해줘", "실행시켜줘", "실행해", "켜줘", "켜봐", "켜",
    "찾아줘", "찾아", "검색해줘", "검색해줘요", "검색", "보여줘", "틀어줘", "틀어봐",
    "폴더", "파일", "좀", "해줘", "부탁해",
]


def has_batchim(word):
    if not word:
        return False
    ch = word[-1]
    code = ord(ch)
    if 0xAC00 <= code <= 0xD7A3:
        return (code - 0xAC00) % 28 != 0
    if ch.isdigit():
        return ch in "013678"
    return False


def particle(word, with_batchim, without_batchim):
    return with_batchim if has_batchim(word) else without_batchim


UWP_PREFIX = "uwp:"


def _guest_open_denied(path):
    if guest_on() and not guest_program_ok(None, path):
        print(f"[JARVIS] 체험 모드라서 열지 않았어요: {os.path.basename(str(path))}")
        return True
    return False


def open_path(path):
    if _guest_open_denied(path):
        return False
    if isinstance(path, str) and path.startswith(UWP_PREFIX):
        app_id = path[len(UWP_PREFIX):]
        try:
            os.startfile(f"shell:AppsFolder\\{app_id}")
            return True
        except Exception:
            return run_hidden(["explorer.exe", f"shell:AppsFolder\\{app_id}"])
    try:
        os.startfile(path)
        return True
    except AttributeError:
        try:
            subprocess.Popen(["xdg-open", path])
            return True
        except Exception:
            return False
    except Exception:
        return False


SW_MAXIMIZE = 3


def _visible_windows_of_class(class_name):
    user32 = ctypes.windll.user32
    found = set()

    @ctypes.WINFUNCTYPE(ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p)
    def enum_handler(hwnd, _lparam):
        buf = ctypes.create_unicode_buffer(256)
        user32.GetClassNameW(hwnd, buf, 256)
        if buf.value == class_name and user32.IsWindowVisible(hwnd):
            found.add(hwnd)
        return 1

    try:
        user32.EnumWindows(enum_handler, 0)
    except Exception:
        pass
    return found


def open_path_maximized(path, class_name="CabinetWClass", timeout=2.0):
    if _guest_open_denied(path):
        return False
    if not HAVE_WINDLL:
        return open_path(path)

    before = _visible_windows_of_class(class_name)
    ok = open_path(path)

    new_hwnd = None
    deadline = time.time() + timeout
    while time.time() < deadline:
        time.sleep(0.15)
        newly = _visible_windows_of_class(class_name) - before
        if newly:
            new_hwnd = next(iter(newly))
            break

    if new_hwnd:
        try:
            ctypes.windll.user32.ShowWindow(new_hwnd, SW_MAXIMIZE)
        except Exception:
            pass

    return ok


def run_hidden(args):
    try:
        kwargs = {}
        if hasattr(subprocess, "CREATE_NO_WINDOW"):
            kwargs["creationflags"] = subprocess.CREATE_NO_WINDOW
        subprocess.Popen(args, **kwargs)
        return True
    except Exception:
        return False


def build_program_index():
    index = {}
    start_menu_dirs = []

    program_data = os.environ.get("PROGRAMDATA")
    if program_data:
        start_menu_dirs.append(os.path.join(program_data, "Microsoft", "Windows", "Start Menu", "Programs"))

    appdata = os.environ.get("APPDATA")
    if appdata:
        start_menu_dirs.append(os.path.join(appdata, "Microsoft", "Windows", "Start Menu", "Programs"))

    desktop = os.path.join(HOME, "Desktop")
    start_menu_dirs.append(desktop)

    for base in start_menu_dirs:
        if not base or not os.path.isdir(base):
            continue
        for root, _dirs, files in os.walk(base):
            for f in files:
                if f.lower().endswith((".lnk", ".url")):
                    name = os.path.splitext(f)[0].strip()
                    key = name.lower()
                    if key and key not in index:
                        index[key] = os.path.join(root, f)
    return index


def run_powershell_json(script, timeout=20):
    try:
        result = subprocess.run(
            ["powershell", "-NoProfile", "-Command", script],
            capture_output=True, text=True, timeout=timeout,
            creationflags=subprocess.CREATE_NO_WINDOW if hasattr(subprocess, "CREATE_NO_WINDOW") else 0,
        )
        text = (result.stdout or "").strip()
        return json.loads(text) if text else None
    except Exception:
        return None


def build_uwp_index():
    index = {}
    data = run_powershell_json("Get-StartApps | ConvertTo-Json -Compress")
    if not data:
        return index
    if isinstance(data, dict):
        data = [data]
    for item in data:
        name = (item.get("Name") or "").strip()
        app_id = (item.get("AppID") or "").strip()
        key = name.lower()
        if key and app_id and key not in index:
            index[key] = UWP_PREFIX + app_id
    return index


PROGRAM_INDEX = build_program_index()
for _key, _val in build_uwp_index().items():
    if any(_key in vs for vs in VERB_STOPWORDS):
        continue
    PROGRAM_INDEX.setdefault(_key, _val)
PROGRAM_KEYS_SORTED = sorted(PROGRAM_INDEX.keys(), key=len, reverse=True)

PROGRAM_ALIASES = {
    "크롬": "chrome",
    "구글크롬": "chrome",
    "엣지": "edge",
    "에지": "edge",
    "워드": "word",
    "엑셀": "excel",
    "파워포인트": "powerpoint",
    "피피티": "powerpoint",
    "메모장": "notepad",
    "탐색기": "explorer",
    "계산기": "calculator",
    "줌": "zoom",
    "브레이브": "brave",
    "카카오톡": "kakaotalk",
    "카톡": "kakaotalk",
    "디스코드": "discord",
    "슬랙": "slack",
    "스포티파이": "spotify",
    "워썬더": "war thunder",
    "ppt": "powerpoint",
    "작업 관리자": "task manager",
    "작업관리자": "task manager",
    "제어판": "control panel",
    "그림판": "paint",
    "캡처 도구": "snipping tool",
    "캡쳐 도구": "snipping tool",
    "명령 프롬프트": "command prompt",
    "cmd": "command prompt",
    "파워 포인트": "powerpoint",
    "vs코드": "visual studio code",
    "vs 코드": "visual studio code",
    "브이에스 코드": "visual studio code",
    "브이에스코드": "visual studio code",
    "비주얼 스튜디오 코드": "visual studio code",
    "vscode": "visual studio code",
    "우분투": "wsl",
    "우분트": "wsl",
    "파워쉘": "windows powershell",
}

_WINDIR = os.environ.get("WINDIR", r"C:\Windows")
SYSTEM_PROGRAMS = {}
for _name, _rel in (
    ("notepad", os.path.join("System32", "notepad.exe")),
    ("calculator", os.path.join("System32", "calc.exe")),
    ("explorer", "explorer.exe"),
    ("task manager", os.path.join("System32", "Taskmgr.exe")),
    ("control panel", os.path.join("System32", "control.exe")),
    ("paint", os.path.join("System32", "mspaint.exe")),
    ("snipping tool", os.path.join("System32", "SnippingTool.exe")),
    ("command prompt", os.path.join("System32", "cmd.exe")),
):
    _p = os.path.join(_WINDIR, _rel)
    if os.path.isfile(_p):
        SYSTEM_PROGRAMS[_name] = _p


def find_program(cmd_lower):
    for key in PROGRAM_KEYS_SORTED:
        if len(key) < 2:
            continue
        if key in cmd_lower or cmd_lower in key:
            return key, PROGRAM_INDEX[key]

    for alias, target in PROGRAM_ALIASES.items():
        if alias in cmd_lower:
            if target in SYSTEM_PROGRAMS:
                return target, SYSTEM_PROGRAMS[target]
            matches = [key for key in PROGRAM_INDEX if target in key]
            if matches:
                exact = [key for key in matches if key == target]
                chosen = exact[0] if exact else min(matches, key=len)
                return chosen, PROGRAM_INDEX[chosen]

    keyword = strip_verbs(cmd_lower)
    if keyword and len(keyword) >= 2 and PROGRAM_INDEX:
        close = difflib.get_close_matches(keyword, PROGRAM_INDEX.keys(), n=1, cutoff=0.60)
        if close:
            key = close[0]
            return key, PROGRAM_INDEX[key]

    return None, None


def strip_verbs(text):
    cleaned = text
    for v in VERB_STOPWORDS:
        cleaned = cleaned.replace(v, " ")
    return " ".join(cleaned.split()).strip()


FILE_INDEX = {}
FILE_INDEX_LOCK = threading.Lock()
FILE_INDEX_REFRESH_SEC = 30
MAX_INDEX_FILES = 20000


FOLDER_INDEX = []
MAX_INDEX_FOLDERS = 20000


def build_file_index():
    idx = {}
    folders = []
    count = 0
    try:
        for d in os.listdir(HOME):
            p = os.path.join(HOME, d)
            if os.path.isdir(p) and not d.startswith(".") and d.lower() not in SKIP_DIR_NAMES:
                folders.append((d.lower(), p, 1))
    except Exception:
        pass
    for base in SEARCH_DIRS:
        if not os.path.isdir(base):
            continue
        base_depth = base.rstrip("\\/").count(os.sep)
        for root, dirs, files in os.walk(base):
            depth = root.rstrip("\\/").count(os.sep) - base_depth
            dirs[:] = [d for d in dirs if d.lower() not in SKIP_DIR_NAMES and not d.startswith(".")]
            if depth >= FOLDER_INDEX_MAX_DEPTH:
                dirs[:] = []
            for d in dirs:
                if len(folders) < MAX_INDEX_FOLDERS:
                    folders.append((d.lower(), os.path.join(root, d), depth + 1))
            for f in files:
                if count < MAX_INDEX_FILES:
                    idx[f.lower()] = os.path.join(root, f)
                    count += 1
    return idx, folders


def refresh_file_index():
    global FILE_INDEX, FOLDER_INDEX
    idx, folders = build_file_index()
    with FILE_INDEX_LOCK:
        FILE_INDEX = idx
        FOLDER_INDEX = folders


def file_index_worker():
    while True:
        try:
            refresh_file_index()
        except Exception:
            pass
        time.sleep(FILE_INDEX_REFRESH_SEC)


RE_FOLDER_OPEN = re.compile(r"^(.*?)\s*폴더\s*(?:를|을)?\s*(?:좀\s*)?(?:열어|열기|열|보여|띄워|켜|찾아|들어가)")
_LOCATION_HINTS = [
    (r"다운로드|다운로드\s*폴더", KNOWN["Downloads"]),
    (r"[바가파]탕\s*화면|데스크\s*탑", KNOWN["Desktop"]),
    (r"문서", KNOWN["Documents"]),
    (r"사진|그림", KNOWN["Pictures"]),
    (r"음악", KNOWN["Music"]),
    (r"동영상|비디오", KNOWN["Videos"]),
]
_LOCATION_PREFIX_RE = re.compile(
    r"^(?:(?:파일\s*)?(?:폴더\s*)?탐색기|내\s*(?:컴퓨터|pc|피시)|컴퓨터|윈도우)?\s*(?:에서|에|로|으로)?\s*"
    r"(?:(다운로드|[바가파]탕\s*화면|데스크\s*탑|문서|사진|그림|음악|동영상|비디오|[c-zC-Z]\s*드라이브)\s*(?:폴더)?\s*"
    r"(?:에서|에\s*있는|안에\s*있는|안에|안의|의|속|에)\s*)?", re.I)


def _canon_loc(loc):
    if re.search(r"[바가파]탕\s*화면|데스크\s*탑", loc or ""):
        return "바탕화면"
    return (loc or "").replace(" ", "")


def _norm_name(t):
    t = unicodedata.normalize("NFC", t or "")
    return re.sub(r"[\s_\-.()\[\]]", "", t.lower())


def _mtime(p):
    try:
        return os.path.getmtime(p)
    except Exception:
        return 0


def _hangul_to_english_guess(name):
    if not re.search(r"[가-힣]", name):
        return []
    out = _groq_request([
        {"role": "system", "content": "The user said a computer folder name in Korean pronunciation. "
                                      "Give up to 3 likely English spellings, lowercase, comma separated, nothing else. "
                                      "Example: 자비스 -> jarvis / 씨티에프 -> ctf / 마인크래프트 -> minecraft"},
        {"role": "user", "content": name}], max_tokens=30, temperature=0)
    return [w.strip().lower() for w in (out or "").split(",") if w.strip()][:3]


def find_folder(name, base=None):
    with FILE_INDEX_LOCK:
        folders = list(FOLDER_INDEX)
    if base and os.path.isdir(base) and not any(p.startswith(base) for _, p, _ in folders):
        for root, dirs, _files in os.walk(base):
            dirs[:] = [d for d in dirs if d.lower() not in SKIP_DIR_NAMES and not d.startswith(("$", "."))]
            depth = root[len(base):].count(os.sep)
            if depth >= 3:
                dirs[:] = []
            for d in dirs:
                folders.append((d.lower(), os.path.join(root, d), depth + 1))
            if len(folders) > 60000:
                break
    if base:
        folders = [f for f in folders if f[1].lower().startswith(base.lower())]
    if not folders or not _norm_name(name):
        return None, 0
    normed = [(_norm_name(n), p, d) for n, p, d in folders]
    found = _match_folder([_norm_name(name)], normed)
    if found[0]:
        return found
    guesses = [_norm_name(g) for g in _hangul_to_english_guess(name)]
    return _match_folder([g for g in guesses if g], normed)


def _match_folder(targets, normed):
    if not targets:
        return None, 0
    for rule in ("exact", "contains", "fuzzy"):
        hits = []
        for t in targets:
            if rule == "exact":
                hits += [(0, d, p) for n, p, d in normed if n == t]
            elif rule == "contains":
                hits += [(abs(len(n) - len(t)), d, p) for n, p, d in normed
                         if len(t) >= 2 and (t in n or (len(n) >= 3 and n in t))]
            else:
                names = list({n for n, _, _ in normed})
                for close in difflib.get_close_matches(t, names, n=3, cutoff=0.75):
                    hits += [(abs(len(close) - len(t)), d, p) for n, p, d in normed if n == close]
        if hits:
            hits.sort(key=lambda h: (h[0], h[1], -_mtime(h[2])))
            return hits[0][2], len({h[2] for h in hits})
    return None, 0


_NESTED_RE = re.compile(r"(?P<parent>[^\s]+)\s*폴더\s*(?:를|을)?\s*(?:열고\s*(?:거기|그\s*안|그\s*폴더)\S*|안에\s*있는|안에서|안의|안에|에서|에\s*있는|의)"
                        r"\s+(?P<rest>.+)$")


def _nested_folder(cmd):
    nm = _NESTED_RE.search(cmd)
    if not nm:
        return None, cmd
    parent = re.sub(r"^.*탐색기\S*\s*", "", nm.group("parent"))
    ppath, _ = find_folder(parent) if parent and parent not in ("파일", "폴더") else (None, 0)
    return (ppath, nm.group("rest")) if ppath else (None, cmd)


def handle_folder_open(cmd, inside=None):
    if inside is None:
        ppath, rest = _nested_folder(cmd)
        if ppath and RE_FOLDER_OPEN.search(rest):
            r = handle_folder_open(rest, ppath)
            if r:
                r["nested"] = True
                return r
    m = RE_FOLDER_OPEN.search(cmd)
    if not m:
        return None
    phrase = m.group(1).strip()
    base = None
    lm = _LOCATION_PREFIX_RE.match(phrase)
    loc = lm.group(1) if lm else None
    name = phrase[lm.end():].strip() if lm else phrase
    if loc:
        dm = re.match(r"([c-zC-Z])\s*드라이브", loc)
        if dm:
            base = dm.group(1).upper() + ":\\"
        else:
            for pat, path in _LOCATION_HINTS:
                if re.fullmatch(pat, loc.replace(" ", "")) or re.search(pat, loc):
                    base = path
                    break
    if inside:
        base = inside
    name = re.sub(r"^(?:에서|에|안에|의|있는|그|그거|이|저)\s+", "", name)
    name = re.sub(r"\s*(?:이라는|라는|이란|란)$", "", name).strip(" ,.'\"")
    if not name or any(re.fullmatch(p, name.replace(" ", "")) for p, _ in _LOCATION_HINTS) \
            or name in FOLDER_KEYWORDS or re.fullmatch(r"(?:파일\s*)?탐색기", name):
        return None
    path, n = find_folder(name, base)
    where = (_canon_loc(loc) + "에서 ") if loc else (os.path.basename(inside) + " 폴더에서 " if inside else "")
    if not path:
        scope = loc if loc else (os.path.basename(inside) + " 폴더" if inside else "바탕화면, 다운로드, 문서, 사진 등")
        return {"reply": f"'{name}' 폴더를 {scope}에서 찾지 못했어요. 폴더 이름을 조금 다르게 말씀해 주시겠어요?",
                "action": "error", "matched": None}
    open_path_maximized(path)
    extra = f" 비슷한 폴더가 {n}개 있어서 가장 가까운 걸 열었어요." if n > 1 else ""
    return {"reply": f"네, {where}{os.path.basename(path)} 폴더를 열었어요.{extra}", "action": "folder", "matched": path}


_FILE_KINDS = [
    (r"ppt|pptx|피피티|파워\s*포인트|발표\s*자료", (".pptx", ".ppt"), "PPT"),
    (r"pdf|피디에프", (".pdf",), "PDF"),
    (r"한글\s*파일|hwp|한글\s*문서", (".hwp", ".hwpx"), "한글 파일"),
    (r"워드|word|docx", (".docx", ".doc"), "워드 파일"),
    (r"엑셀|excel|xlsx", (".xlsx", ".xls", ".csv"), "엑셀 파일"),
    (r"사진|이미지|그림\s*파일", (".jpg", ".jpeg", ".png", ".gif", ".bmp", ".webp"), "사진"),
    (r"동영상|영상|mp4", (".mp4", ".mkv", ".avi", ".mov", ".wmv"), "영상"),
    (r"노래\s*파일|음악\s*파일|mp3", (".mp3", ".wav", ".m4a", ".flac"), "음악 파일"),
    (r"텍스트\s*파일|메모장\s*파일|txt", (".txt", ".md"), "텍스트 파일"),
    (r"파일", None, "파일"),
]
RE_FILE_OPEN = re.compile(r"^(.*?)\s*(?:이라는|라는|이란|란)?\s*(" + "|".join(k for k, _, _ in _FILE_KINDS) +
                          r")\s*(?:을|를)?\s*(?:좀\s*)?(?:열어|틀어|실행|보여|띄워|켜|재생)", re.I)


def find_file_named(name, exts=None, base=None):
    with FILE_INDEX_LOCK:
        files = list(FILE_INDEX.values())
    if base:
        files = [p for p in files if p.lower().startswith(base.lower())]
    if exts:
        files = [p for p in files if os.path.splitext(p)[1].lower() in exts]
    if not files:
        return None, 0
    normed = [(_norm_name(os.path.splitext(os.path.basename(p))[0]), p, 0) for p in files]
    found = _match_folder([_norm_name(name)], normed)
    if found[0] or not re.search(r"[가-힣]", name):
        return found
    return _match_folder([_norm_name(g) for g in _hangul_to_english_guess(name)], normed)


def handle_file_open(cmd, inside=None):
    if inside is None:
        ppath, rest = _nested_folder(cmd)
        if ppath and RE_FILE_OPEN.search(rest):
            r = handle_file_open(rest, ppath)
            if r:
                r["nested"] = True
                return r
    m = RE_FILE_OPEN.search(cmd)
    if not m:
        return None
    phrase, kind_word = m.group(1).strip(), m.group(2)
    exts, kind_name = None, "파일"
    for pat, e, nm in _FILE_KINDS:
        if re.fullmatch(pat, kind_word.replace(" ", ""), re.I) or re.fullmatch(pat, kind_word, re.I):
            exts, kind_name = e, nm
            break
    lm = _LOCATION_PREFIX_RE.match(phrase)
    loc = lm.group(1) if lm else None
    name = (phrase[lm.end():] if lm else phrase).strip()
    name = re.sub(r"\s*(?:이라는|라는|이란|란)$", "", name).strip(" ,.'\"")
    if not name:
        return None
    base = None
    if loc:
        for pat, path in _LOCATION_HINTS:
            if re.search(pat, loc):
                base = path
                break
    if inside:
        base = inside
    path, n = find_file_named(name, exts, base)
    where = (_canon_loc(loc) + "에서 ") if loc else (os.path.basename(inside) + " 폴더에서 " if inside else "")
    if not path:
        if not loc and kind_name in ("영상", "사진", "음악 파일", "파일"):
            return None
        scope = loc or (os.path.basename(inside) + " 폴더" if inside else "바탕화면, 다운로드, 문서")
        return {"reply": f"'{name}' {kind_name}{particle(kind_name, '을', '를')} "
                         f"{scope}에서 찾지 못했어요.", "action": "error", "matched": None}
    open_path(path)
    return {"reply": f"네, {where}{os.path.basename(path)} 열었어요.", "action": "file", "matched": path}


def search_file(query):
    if not query:
        return None
    query_lower = query.lower()
    with FILE_INDEX_LOCK:
        snapshot = list(FILE_INDEX.items())
    for name, path in snapshot:
        if query_lower in name:
            return path
    return None


VK_VOLUME_MUTE = 0xAD
VK_VOLUME_DOWN = 0xAE
VK_VOLUME_UP = 0xAF
KEYEVENTF_KEYUP = 0x0002


_AUDIO_EP = {"iface": None}


def _endpoint_volume():
    from comtypes import GUID, IUnknown, COMMETHOD, HRESULT, CoCreateInstance, CLSCTX_ALL, CoInitialize
    from ctypes import POINTER, c_int, c_uint, c_float, c_void_p, cast
    try:
        CoInitialize()
    except Exception:
        pass

    class IAudioEndpointVolume(IUnknown):
        _iid_ = GUID("{5CDF2C82-841E-4546-9722-0CF74078229A}")
        _methods_ = [
            COMMETHOD([], HRESULT, "RegisterControlChangeNotify", (["in"], c_void_p)),
            COMMETHOD([], HRESULT, "UnregisterControlChangeNotify", (["in"], c_void_p)),
            COMMETHOD([], HRESULT, "GetChannelCount", (["out"], POINTER(c_uint))),
            COMMETHOD([], HRESULT, "SetMasterVolumeLevel", (["in"], c_float), (["in"], POINTER(GUID))),
            COMMETHOD([], HRESULT, "SetMasterVolumeLevelScalar", (["in"], c_float), (["in"], POINTER(GUID))),
            COMMETHOD([], HRESULT, "GetMasterVolumeLevel", (["out"], POINTER(c_float))),
            COMMETHOD([], HRESULT, "GetMasterVolumeLevelScalar", (["out"], POINTER(c_float))),
            COMMETHOD([], HRESULT, "SetChannelVolumeLevel", (["in"], c_uint), (["in"], c_float), (["in"], POINTER(GUID))),
            COMMETHOD([], HRESULT, "SetChannelVolumeLevelScalar", (["in"], c_uint), (["in"], c_float), (["in"], POINTER(GUID))),
            COMMETHOD([], HRESULT, "GetChannelVolumeLevel", (["in"], c_uint), (["out"], POINTER(c_float))),
            COMMETHOD([], HRESULT, "GetChannelVolumeLevelScalar", (["in"], c_uint), (["out"], POINTER(c_float))),
            COMMETHOD([], HRESULT, "SetMute", (["in"], c_int), (["in"], POINTER(GUID))),
            COMMETHOD([], HRESULT, "GetMute", (["out"], POINTER(c_int))),
        ]

    class IMMDevice(IUnknown):
        _iid_ = GUID("{D666063F-1587-4E43-81F1-B948E807363F}")
        _methods_ = [COMMETHOD([], HRESULT, "Activate", (["in"], POINTER(GUID)), (["in"], c_uint),
                               (["in"], c_void_p), (["out"], POINTER(c_void_p)))]

    class IMMDeviceEnumerator(IUnknown):
        _iid_ = GUID("{A95664D2-9614-4F35-A746-DE8DB63617E6}")
        _methods_ = [COMMETHOD([], HRESULT, "EnumAudioEndpoints", (["in"], c_int), (["in"], c_uint), (["out"], POINTER(c_void_p))),
                     COMMETHOD([], HRESULT, "GetDefaultAudioEndpoint", (["in"], c_int), (["in"], c_int),
                               (["out"], POINTER(POINTER(IMMDevice))))]

    en = CoCreateInstance(GUID("{BCDE0395-E52F-467C-8E3D-C4579291692E}"), IMMDeviceEnumerator, CLSCTX_ALL)
    dev = en.GetDefaultAudioEndpoint(0, 1)
    ptr = dev.Activate(IAudioEndpointVolume._iid_, CLSCTX_ALL, None)
    return cast(ptr, POINTER(IAudioEndpointVolume))


def system_muted():
    if not HAVE_WINDLL:
        return None
    try:
        return bool(_endpoint_volume().GetMute())
    except Exception:
        return None


def set_system_mute(on):
    st = system_muted()
    if st is None:
        return press_key(VK_VOLUME_MUTE)
    if st != bool(on):
        try:
            _endpoint_volume().SetMute(1 if on else 0, None)
        except Exception:
            return press_key(VK_VOLUME_MUTE)
    return True


def press_key(vk, times=1):
    if not HAVE_WINDLL:
        return False
    try:
        user32 = ctypes.windll.user32
        for _ in range(times):
            user32.keybd_event(vk, 0, 0, 0)
            user32.keybd_event(vk, 0, KEYEVENTF_KEYUP, 0)
            time.sleep(0.03)
        return True
    except Exception:
        return False


def system_lock():
    if not HAVE_WINDLL:
        return False
    try:
        ctypes.windll.user32.LockWorkStation()
        return True
    except Exception:
        return False


def system_sleep():
    return run_hidden(["rundll32.exe", "powrprof.dll,SetSuspendState", "0,1,0"])


def system_shutdown(delay_sec=30):
    return run_hidden(["shutdown", "/s", "/t", str(delay_sec)])


def system_restart(delay_sec=30):
    return run_hidden(["shutdown", "/r", "/t", str(delay_sec)])


def system_cancel_shutdown():
    return run_hidden(["shutdown", "/a"])


PROTECTED_PROCESSES = {
    "system", "system idle process", "registry", "smss.exe", "csrss.exe", "wininit.exe", "winlogon.exe",
    "services.exe", "lsass.exe", "svchost.exe", "dwm.exe", "explorer.exe", "fontdrvhost.exe", "sihost.exe",
    "ctfmon.exe", "audiodg.exe", "runtimebroker.exe", "searchhost.exe", "startmenuexperiencehost.exe",
    "shellexperiencehost.exe", "conhost.exe", "msmpeng.exe", "securityhealthservice.exe",
    "python.exe", "pythonw.exe", "py.exe", "powershell.exe", "pwsh.exe", "windowsterminal.exe", "cmd.exe",
    "openconsole.exe",
}


def find_running_process(cmd_lower):
    if not HAVE_PSUTIL:
        return None
    try:
        procs = list(psutil.process_iter(["name"]))
    except Exception:
        return None

    me = os.getpid()
    procs = [p for p in procs
             if p.pid != me and (p.info.get("name") or "").lower() not in PROTECTED_PROCESSES]

    for proc in procs:
        name = proc.info.get("name") or ""
        base = name[:-4] if name.lower().endswith(".exe") else name
        if len(base) >= 3 and base.lower() in cmd_lower:
            return proc, base

    for alias, target in PROGRAM_ALIASES.items():
        if alias in cmd_lower:
            for proc in procs:
                name = proc.info.get("name") or ""
                if target in name.lower():
                    base = name[:-4] if name.lower().endswith(".exe") else name
                    return proc, base

    return None


WM_CLOSE = 0x0010


def post_close_to_windows(pid):
    if not HAVE_WINDLL:
        return False
    user32 = ctypes.windll.user32
    found = []

    @ctypes.WINFUNCTYPE(ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p)
    def enum_handler(hwnd, _lparam):
        window_pid = ctypes.c_ulong()
        user32.GetWindowThreadProcessId(hwnd, ctypes.byref(window_pid))
        if window_pid.value == pid and user32.IsWindowVisible(hwnd):
            user32.PostMessageW(hwnd, WM_CLOSE, 0, 0)
            found.append(hwnd)
        return 1

    try:
        user32.EnumWindows(enum_handler, 0)
    except Exception:
        return False
    return len(found) > 0


def close_app(cmd_lower):
    found = find_running_process(cmd_lower)
    if not found:
        return None, False
    proc, display_name = found
    if post_close_to_windows(proc.pid):
        return display_name, True
    try:
        proc.terminate()
        return display_name, False
    except Exception:
        return None, False


def log_command(command, result):
    line = "{}\t{}\t{}\t{}\t{}\n".format(
        time.strftime("%Y-%m-%d %H:%M:%S"),
        command.replace("\t", " ").replace("\n", " "),
        result.get("action"),
        str(result.get("reply")).replace("\t", " ").replace("\n", " "),
        f"{result.get('_sec', '')}초",
    )
    try:
        with LOG_LOCK:
            with open(LOG_PATH, "a", encoding="utf-8") as f:
                f.write(line)
    except Exception:
        pass


URL_RE = re.compile(r"(https?://\S+|\b[\w-]+\.(com|net|org|co\.kr|kr|io)\b)")

RE_CANCEL = re.compile(r"취소")
RE_COMPUTER = re.compile(r"(컴퓨터|pc|피시|노트북)", re.IGNORECASE)
RE_RESTART = re.compile(r"(재부팅|재시작)")
RE_SLEEP = re.compile(r"(절전|재워줘|잠재워줘|슬립\s*모드)")
RE_LOCK = re.compile(r"(화면\s*잠|잠금|잠가줘|잠궈줘|락\s*걸)")
RE_SHUTDOWN = re.compile(r"(종료|꺼줘|꺼라)")
RE_POWER_OFF = re.compile(r"전원\s*(을|좀)?\s*(꺼|끄|내려|오프|off|종료)")
RE_VOLUME = re.compile(r"(볼륨|소리)")
RE_UNMUTE = re.compile(r"((음소거|뮤트|묵음)\s*(를|을)?\s*(풀|해제|끄|꺼|취소|없애)|(소리|볼륨)\s*(를|을)?\s*(다시\s*)?(켜|살려|돌려))")
RE_MUTE = re.compile(r"(음소거|뮤트|묵음|(소리|볼륨)\s*(을|를)?\s*(완전히?\s*|다\s*|좀\s*)?(꺼|끄|없애|죽여))")
RE_VOL_UP = re.compile(r"(올려|키워|높여|크게)")
RE_VOL_DOWN = re.compile(r"(내려|줄여|낮춰|작게)")
RE_CLOSE_APP = re.compile(r"(종료해줘|꺼줘|닫아줘|닫아)")
RE_SECURITY_CHECK = re.compile(r"보안\s*(상태)?\s*(확인|점검)")
RE_VERSION = re.compile(r"(버전|version|몇\s*버전|버전\s*(뭐|알려|몇))")
RE_WEATHER = re.compile(r"(날씨|기온|온도|더워|추워|더운지|추운지|비\s*(와|오|온)|눈\s*(와|오|온))")
RE_TIME = re.compile(r"(몇\s*시|시간\s*(알려|말|어)|지금\s*시간|현재\s*시(각|간))")
RE_TIME_ASK = re.compile(r"((지금|현재)\s*(몇\s*시|시간|시각)|몇\s*시\s*(몇\s*분|야|예요|에요|이야|이에요|지|니|냐|인지|인가|일까|임|쯤\s*(됐|이)|됐)|"
                         r"몇\s*시\s*[?？]|몇\s*시\s*$|시간\s*(좀\s*)?(알려|말해)|시각\s*(좀\s*)?(알려|말해))")
RE_DATE = re.compile(r"(며칠|몇\s*일|날짜|무슨\s*요일|무슨\s*날|오늘\s*요일|요일\s*(알려|뭐|어))")
RE_NEWS = re.compile(r"(뉴스|헤드라인|주요\s*소식|오늘\s*소식)")
RE_HELP = re.compile(r"(어떤\s*(일|거|것|기능)\S*\s*할\s*(수|줄)|뭐\s*할\s*줄|할\s*줄\s*아는|할\s*수\s*있는\s*(게|거|것|일|기능)|무슨\s*기능|뭐\s*(를)?\s*할\s*수|무엇을\s*할\s*수|뭘\s*할\s*수|도움말|기능\s*(이|을)?\s*(알려|뭐|목록)|명령어?\s*(알려|목록|뭐|뭐야))")

_KO_WEEKDAYS = ["월", "화", "수", "목", "금", "토", "일"]


NEWS_SENSITIVE_RE = re.compile(
    r"(대통령|대통령실|국회|여당|야당|여야|민주당|국민의힘|정당|의원|장관|총리|선거|대선|총선|지선|탄핵|특검|검찰|기소|"
    r"구속|재판|판결|정치|국정|국감|내란|계엄|북한|전쟁|미사일|공습|사망|숨져|숨진|살해|살인|폭행|성폭|성범죄|마약|"
    r"자살|극단적|참사|추락|화재로|흉기|시신|사고로|사상자|부상자|테러|혐오|윤석열|이재명|한동훈|조국|김건희|트럼프)")


def get_news(n=3):
    if guest_on():
        for topic in ("TECHNOLOGY", "SCIENCE"):
            r = _get_news_from(f"https://news.google.com/rss/headlines/section/topic/{topic}?hl=ko&gl=KR&ceid=KR:ko",
                               n, safe=True)
            if r:
                return r.replace("오늘의 주요 뉴스입니다.", "오늘의 IT·과학 소식이에요." if topic == "TECHNOLOGY"
                                 else "오늘의 과학 소식이에요.")
        return _get_news_from("https://news.google.com/rss?hl=ko&gl=KR&ceid=KR:ko", n, safe=True)
    return _get_news_from("https://news.google.com/rss?hl=ko&gl=KR&ceid=KR:ko", n)


def _get_news_from(url, n, safe=False):
    try:
        req = urllib.request.Request(url, headers={"User-Agent": "jarvis-local/1.0"})
        with urllib.request.urlopen(req, timeout=8) as resp:
            xml_text = resp.read().decode("utf-8")
        import xml.etree.ElementTree as ET
        root = ET.fromstring(xml_text)
        titles = []
        for item in root.findall(".//item"):
            t = (item.findtext("title") or "").strip()
            t = t.split(" - ")[0].strip()
            if safe and NEWS_SENSITIVE_RE.search(t):
                continue
            if t:
                titles.append(t)
            if len(titles) >= n:
                break
        if not titles:
            return None
        body = " . ".join(f"{i + 1}번, {t}" for i, t in enumerate(titles))
        return "오늘의 주요 뉴스입니다. " + body + "."
    except Exception:
        return None


_WEATHER_KO = [
    ("thunder", "천둥번개"), ("torrential", "폭우"), ("heavy rain", "폭우"),
    ("light rain", "약한 비"), ("patchy rain", "비 조금"), ("drizzle", "이슬비"), ("rain", "비"),
    ("heavy snow", "폭설"), ("light snow", "약한 눈"), ("blizzard", "눈보라"), ("snow", "눈"),
    ("sleet", "진눈깨비"), ("mist", "안개"), ("fog", "안개"), ("haze", "실안개"),
    ("partly cloudy", "구름 조금"), ("overcast", "흐림"), ("cloud", "흐림"),
    ("clear", "맑음"), ("sunny", "맑음"),
]


def _weather_desc_ko(desc_en):
    d = (desc_en or "").lower()
    for k, v in _WEATHER_KO:
        if k in d:
            return v
    return desc_en


INTRO_SHORT = "저는 자비스입니다. {boss}님이 직접 만든 인공지능 비서예요. 말 한마디면 컴퓨터를 움직이고, 궁금한 건 바로 찾아 드리죠. 여러 나라 말도 할 줄 알아요."
INTRO_FULL = (
    "안녕하세요, 저는 자비스입니다. {boss}님이 직접 만든 인공지능 비서예요. "
    "말 한마디로 프로그램을 열고, 날씨와 길 안내, 번역까지 해 드리고, 여러 나라 말로 대화할 수 있어요. "
    "잘 부탁드려요!"
)
INTRO_LONG = (
    "안녕하세요, 저는 자비스입니다. 아이언맨의 인공지능 비서에서 이름을 따 왔고, {boss}님이 직접 만들었어요. "
    "저는 말 한마디로 프로그램을 열고, 날씨와 길을 알려 드리고, 검색과 번역, 음악까지 챙깁니다. "
    "한국어는 물론 영어, 일본어, 중국어로도 대화하고, 번역한 말은 그 나라 목소리로 들려 드려요. "
    "주변이 시끄러워도 마이크 가까이에서 하는 말을 골라 들어요. "
    "지금은 버전 {ver}이고, 업데이트할 때마다 조금씩 더 똑똑해지고 있어요. 잘 부탁드립니다."
)
RE_HOW_MADE = re.compile(r"(어떻게\s*(만들|만든|만들어|만드)|어떤\s*(종류의\s*)?(코딩|프로그래밍|언어)|무슨\s*(언어|프로그램)\S*\s*(로|으로)?\s*만들|"
                         r"뭘로\s*만들|뭐로\s*만들|무엇으로\s*만들|어떤\s*기술)")
HOW_MADE = ("보스가 파이썬으로 직접 만들었어요. 들은 말은 음성 인식으로 글자로 바꾸고, "
            "명령이면 컴퓨터를 움직이고, 대화면 인공지능이 대답을 만들어요. "
            "제 목소리는 음성 합성으로 나오고, 화면은 HTML과 자바스크립트로 만들었어요.")
BOSS_INFO_FILE = os.path.join(BASE_DIR, "boss_info.json")


def _load_boss_info():
    try:
        with open(BOSS_INFO_FILE, "r", encoding="utf-8") as f:
            return json.load(f) or {}
    except Exception:
        return {}


_BOSS_INFO = _load_boss_info()
BOSS_INTRO = _BOSS_INFO.get("intro") or (
    "제 보스를 소개합니다! 코딩과 개발을 정말 좋아해서, 노트북 한 대로 저 자비스를 처음부터 직접 설계하고 만드셨죠. "
    "제가 가장 믿고 따르는 분이에요!"
)
BOSS_INTRO_GUEST = (
    "제 보스를 소개합니다! 코딩과 개발을 정말 좋아해서, 노트북 한 대로 저 자비스를 처음부터 직접 설계하고 만드셨죠. "
    "지금도 저를 계속 고치고 키워 주고 계세요. 제가 가장 믿고 따르는 분이에요!"
)
BOSS_PROFILE_GUEST = ("나를 만든 사람(보스) 정보: 코딩과 개발을 좋아하고, 자비스를 직접 만듦. "
                      "이름·닉네임·나이·소속·꿈·연락처·사는 곳 같은 개인 정보는 하나도 말하지 않고, 물으면 개인 정보라 말할 수 없다고 함. "
                      "그냥 '보스'라고 부름.")
BOSS_PROFILE = _BOSS_INFO.get("profile") or "보스 정보: 코딩과 개발을 좋아함. 자비스를 직접 만든 사람."
BOSS_SECRET_NAMES = tuple(n for n in _BOSS_INFO.get("secret_names", []) if n)
BOSS_AFFILIATION_PATTERNS = [re.compile(x) for x in _BOSS_INFO.get("affiliation_patterns", []) if x]
BOSS_AFFILIATION_WORDS = re.compile(_BOSS_INFO["affiliation_words"]) if _BOSS_INFO.get("affiliation_words") else None
BOSS_AFFILIATION_REPLACE = _BOSS_INFO.get("affiliation_replace", "")
RE_BOSS_INTRO = re.compile(r"((보스|주인|나|날|저|제|내|만든\s*사람)\s*(를|을|에\s*대해|에\s*대해서)?\s*(좀\s*)?소개|"
                           r"(너의?|네|자비스의?)\s*(보스|주인)\S*\s*(는|가|이)?\s*(누구|소개)|"
                           r"(누가|누구가)\s*(너를|널|자비스를)\s*만들|(넌|너는|자비스는)\s*누가\s*만들|"
                           r"(너를|널)?\s*만[든난]\s*사람\S*\s*(이름\S*\s*)?누구)")
INTRO_GREET = "여러분, 안녕하세요! 저는 {boss}님의 인공지능 비서, 자비스입니다. 오늘 발표를 함께하게 되어 기쁩니다. 잘 부탁드려요!"
RE_INTRO_FULL = re.compile(r"(자기\s*소개|(너|네|자비스)(에\s*대해|를|에\s*대해서)?\s*(소개|설명)|"
                           r"소개\s*(좀\s*|한\s*번\s*|한번\s*)?해\s*(줘|봐|줄래|볼래|주세요))")
RE_INTRO_SHORT = re.compile(r"^(넌|너는|너|당신은|자비스(는|가|란|이란)?)\s*(누구|뭐|무엇)(야|니|예요|이야|인가요|지|에요)?\??$")
RE_GREET_ALL = re.compile(r"((여러분|사람들|친구들|선생님들|청중)\S*\s*)?인사\s*(좀\s*)?(해|드려|하자)|^\s*(여러분|사람들|친구들|선생님들|청중)\S*\s*인사\S*\s*$")


MULTI_INTRO_BASE = "안녕하세요, 저는 {boss}님이 만든 인공지능 비서 자비스입니다."
MULTI_INTRO_LANGS = ["en", "ja", "zh-CN", "es", "ru"]


def multilang_intro(langs=None):
    base = intro_text(MULTI_INTRO_BASE)
    results = {}
    lang_list = langs or MULTI_INTRO_LANGS

    def work(code):
        results[code] = translate_text(base, code)

    threads = [threading.Thread(target=work, args=(c,)) for c in lang_list]
    for t in threads:
        t.start()
    for t in threads:
        t.join(10)
    parts = ([] if langs else [{"text": base, "lang": "ko"}]) + [{"text": results[c], "lang": c}
                                                              for c in lang_list if results.get(c)]
    return {"reply": " / ".join(p["text"] for p in parts), "action": "info", "matched": "intro_multi",
            "speak_parts": parts}


def intro_text_guest(template):
    t = template.replace("{boss}님이", "보스가").replace("{boss}님의", "보스의").replace("{boss}님", "보스")
    return t.format(boss="보스", ver=JARVIS_VERSION)


def intro_text(template):
    if guest_on():
        return intro_text_guest(template)
    return template.format(boss=boss_name() or "보스", ver=JARVIS_VERSION)


PROFILE_FILE = os.path.join(BASE_DIR, "profile.json")


def boss_name():
    try:
        with open(PROFILE_FILE, "r", encoding="utf-8") as f:
            return (json.load(f) or {}).get("name", "")
    except Exception:
        return ""


def set_boss_name(name):
    try:
        with open(PROFILE_FILE, "w", encoding="utf-8") as f:
            json.dump({"name": name.strip()}, f, ensure_ascii=False)
    except Exception:
        pass


def _http_get_text(url, timeout=8, must_contain=None):
    headers = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)", "Accept-Language": "ko-KR,ko;q=0.9"}
    try:
        with urllib.request.urlopen(urllib.request.Request(url, headers=headers), timeout=timeout) as r:
            text = r.read().decode("utf-8", errors="ignore")
        if not must_contain or must_contain in text:
            return text
    except Exception:
        pass
    curl = os.path.join(os.environ.get("SystemRoot", r"C:\Windows"), "System32", "curl.exe")
    if os.path.exists(curl):
        try:
            out = subprocess.run([curl, "-s", "-m", str(timeout), "-A", headers["User-Agent"],
                                  "-H", "Accept-Language: ko-KR,ko;q=0.9", url],
                                 capture_output=True, timeout=timeout + 2)
            return out.stdout.decode("utf-8", errors="ignore")
        except Exception:
            pass
    return ""


def youtube_first(query):
    html = _http_get_text("https://www.youtube.com/results?search_query=" + urllib.parse.quote(query),
                          must_contain='"videoRenderer"')
    m = re.search(r'"videoRenderer":\{"videoId":"([\w-]{11})".*?"title":\{"runs":\[\{"text":"(.*?)"', html)
    if not m:
        return None, None
    try:
        title = json.loads('"' + m.group(2) + '"')
    except Exception:
        title = m.group(2)
    return m.group(1), title


def handle_music(cmd):
    if "스포티" in cmd:
        song = re.sub(r"(스포티파이에서|스포티파이|스포티|노래|음악|틀어줘|틀어|열어줘|열어|켜줘|켜|좀|해줘)", " ", cmd)
        song = re.sub(r"\s+", " ", song).strip()
        webbrowser.open("https://open.spotify.com/search/" + urllib.parse.quote(song) if song else "https://open.spotify.com")
        return {"reply": f"스포티파이에서 {song} 찾아볼게요." if song else "스포티파이를 열게요.", "action": "music", "matched": song or "spotify"}
    vm = re.search(r"(틀어|들려|재생|플레이|play\b)", cmd, re.I)
    if vm:
        tail = re.match(r"\S*", cmd[vm.end():]).group(0)
        cmd = cmd[:vm.end()] + tail
    cmd = re.sub(r"^\s*(야|자비스|저기|헤이|얘)\s*[^,]{0,8},\s*", "", cmd)
    song = re.sub(r"(유튜브\s*뮤직에서|유튜브\s*뮤직으로|유튜브\s*뮤직|유튜브에서|노래\s*좀|노래|음악|플레이리스트|"
                  r"틀어\s*(줘|봐|줄래|주세요)?|들려\s*(줘|봐|줄래)?|재생해\s*줘|재생|플레이|열어\s*줘|열어|켜\s*줘|켜|듣고\s*싶어|좀|해줘|줘)", " ", cmd)
    song = re.sub(r"\s+", " ", song).strip(" ,.")
    if re.fullmatch(r"(도|하나|하나만|한\s*곡|아무\s*(거|노래|곡)?\s*(나|이나)?|신나는\s*거|요즘\s*거|뭐든|뭐라도)?", song):
        song = ""
    if not song:
        vid, title = youtube_first("요즘 인기 노래 플레이리스트")
        if vid:
            webbrowser.open(f"https://music.youtube.com/watch?v={vid}")
            return {"reply": "네, 요즘 인기 있는 노래를 틀어 드릴게요.", "action": "music", "matched": title}
        webbrowser.open("https://music.youtube.com")
        return {"reply": "유튜브 뮤직을 열게요.", "action": "music", "matched": "youtube music"}
    query = song if re.search(r"(노래|음악|playlist|플레이리스트|ost|mv|커버|cover|lofi)", song, re.I) else song + " 노래"
    vid, title = youtube_first(query)
    if vid:
        webbrowser.open(f"https://music.youtube.com/watch?v={vid}")
        said = re.sub(r"(유튜브\s*뮤직에서|유튜브\s*뮤직으로|유튜브\s*뮤직|유튜브에서|틀어\s*줘|틀어|들려\s*줘|재생해\s*줘|재생|"
                      r"플레이|열어\s*줘|열어|켜\s*줘|켜|듣고\s*싶어|좀|해줘)", " ", cmd)
        said = re.sub(r"\s+", " ", said).strip(" ,.") or song
        return {"reply": f"네, 유튜브 뮤직에서 {said} 틀어 드릴게요.", "action": "music", "matched": title}
    webbrowser.open("https://music.youtube.com/search?q=" + urllib.parse.quote(song))
    return {"reply": f"유튜브 뮤직에서 {song} 찾아볼게요.", "action": "music", "matched": song}


SETTINGS_PAGES = [
    (r"(와이파이|wifi|wi-fi|인터넷|네트워크)", "ms-settings:network-wifi", "와이파이 설정"),
    (r"(블루투스|bluetooth)", "ms-settings:bluetooth", "블루투스 설정"),
    (r"(소리|사운드|스피커|마이크)", "ms-settings:sound", "소리 설정"),
    (r"(디스플레이|화면|모니터|밝기)", "ms-settings:display", "디스플레이 설정"),
    (r"(배터리|전원)", "ms-settings:batterysaver", "배터리 설정"),
    (r"(업데이트)", "ms-settings:windowsupdate", "윈도우 업데이트"),
    (r"(위치)", "ms-settings:privacy-location", "위치 설정"),
    (r"(앱)", "ms-settings:appsfeatures", "앱 설정"),
]
RE_SETTINGS = re.compile(r"(윈도우\s*)?설정\s*(창|화면|앱)?\s*(좀\s*)?(열어|켜|띄워|보여|들어가)")


def open_settings(cmd):
    for pat, uri, name in SETTINGS_PAGES:
        if re.search(pat, cmd):
            break
    else:
        uri, name = "ms-settings:", "윈도우 설정"
    if guest_on():
        return {"reply": "죄송해요, 보스. 그건 체험 모드에서는 할 수 없어요. 날씨나 음악, 번역, 자기소개 같은 걸 해 보세요!",
                "action": "info", "matched": "guest_blocked"}
    try:
        os.startfile(uri)
    except Exception:
        return {"reply": "설정 화면을 열지 못했어요.", "action": "error", "matched": None}
    return {"reply": f"네, {name}{particle(name, '을', '를')} 열었어요.", "action": "program", "matched": uri}


LOCATION_FILE = os.path.join(BASE_DIR, "location_cache.json")
_LOCATION = {"lat": None, "lon": None, "name": "", "query": "", "at": 0}
_LOCATION_LOCK = threading.Lock()


def _load_location():
    try:
        with open(LOCATION_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict) and data.get("lat") is not None:
            with _LOCATION_LOCK:
                _LOCATION.update(data)
    except Exception:
        pass


def _save_location():
    try:
        with open(LOCATION_FILE, "w", encoding="utf-8") as f:
            json.dump(_LOCATION, f, ensure_ascii=False)
    except Exception:
        pass


def _reverse_geocode(lat, lon):
    url = (f"https://nominatim.openstreetmap.org/reverse?lat={lat:.3f}&lon={lon:.3f}"
           f"&format=json&accept-language=ko&zoom=16")
    req = urllib.request.Request(url, headers={"User-Agent": "jarvis-local/1.0 (personal voice assistant)"})
    with urllib.request.urlopen(req, timeout=8) as resp:
        a = (json.loads(resp.read().decode("utf-8")) or {}).get("address", {})
    big = a.get("city") or a.get("town") or a.get("county") or a.get("province") or ""
    gu = a.get("borough") or a.get("city_district") or ""
    dong = a.get("quarter") or a.get("suburb") or a.get("neighbourhood") or a.get("village") or ""
    parts = []
    for x in (big, gu, dong):
        if x and x not in parts:
            parts.append(x)
    return " ".join(parts[:2]), " ".join(parts)


def set_location(lat, lon):
    with _LOCATION_LOCK:
        old_lat, old_lon, has_name = _LOCATION["lat"], _LOCATION["lon"], bool(_LOCATION["name"])
    if (old_lat is not None and has_name and abs(old_lat - lat) < 0.005 and abs(old_lon - lon) < 0.005):
        with _LOCATION_LOCK:
            _LOCATION["at"] = time.time()
            _save_location()
        return
    try:
        name, query = _reverse_geocode(lat, lon)
    except Exception:
        name, query = "", ""
    with _LOCATION_LOCK:
        _LOCATION.update({"lat": lat, "lon": lon, "name": name, "query": query, "at": time.time()})
        _save_location()
    if name:
        print(f"[JARVIS] 현재 위치를 확인했어요: {query or name}")


def current_location():
    with _LOCATION_LOCK:
        return dict(_LOCATION)


RE_ROUTE = re.compile(r"(어떻게\s*(가|갈|알까)|갈\s*(건데|껀데|거거든|거\s*같은데|려고|려는데|려면|예정)|어떻게\s*가|가는\s*(길|법|방법)|가려면|갈\s*수\s*있|길\s*(좀\s*)?(찾|안내|알려)|길찾기|경로)")
RE_ROUTE_SPLIT = re.compile(r"\s*(까지|으로|에)?\s*(갈|가는|가려|가고|가야|어떻게|길\s*찾|길\s*안내|길찾기|길\s*(좀\s*)?알려|경로)")
RE_NEARBY = re.compile(r"(근처|주변|가까운|가까이)")


def _strip_ro(word):
    if len(word) > 1 and word.endswith("로"):
        prev = word[-2]
        if "가" <= prev <= "힣":
            batchim = (ord(prev) - 0xAC00) % 28
            if batchim in (0, 8):
                return word[:-1]
    return word


def route_destination(cmd):
    m = RE_ROUTE_SPLIT.search(cmd)
    dest = cmd[:m.start()] if m and m.start() > 0 else ""
    if not dest:
        m2 = re.search(r"(길\s*찾기|길\s*안내|경로)\s*(해\s*줘)?\s*(.+)", cmd)
        dest = m2.group(3) if m2 else ""
    dest = re.sub(r"^\S+\s*에서\s+(?=\S)", "", dest.strip())
    dest = re.sub(r"^(여기서|지금|내일|오늘|이따|나중에|우리|저|나)\s+", "", dest.strip())
    dest = re.sub(r"\s*(차로|자동차로|운전해서|걸어서|도보로|자전거로|버스로|지하철로|대중교통으로)\s*", " ", dest)
    dest = re.sub(r"(까지|으로|에)$", "", dest.strip()).strip()
    return _strip_ro(dest)


def route_mode(cmd):
    if re.search(r"(차로|자동차|운전|드라이브)", cmd):
        return "driving", "자동차"
    if re.search(r"(걸어|도보|걷)", cmd):
        return "walking", "걸어서 가는"
    if "자전거" in cmd:
        return "bicycling", "자전거"
    return "transit", "대중교통"


def _geocode(place):
    def search(extra):
        params = {"q": place, "format": "json", "accept-language": "ko", "countrycodes": "kr", "limit": "1"}
        params.update(extra)
        url = "https://nominatim.openstreetmap.org/search?" + urllib.parse.urlencode(params)
        req = urllib.request.Request(url, headers={"User-Agent": "jarvis-local/1.0 (personal voice assistant)"})
        with urllib.request.urlopen(req, timeout=6) as resp:
            data = json.loads(resp.read().decode("utf-8")) or []
        return data[0] if data else None

    best = search({})
    loc = current_location()
    if loc.get("lat") is not None:
        lat, lon = loc["lat"], loc["lon"]
        near = search({"viewbox": f"{lon-0.3},{lat+0.3},{lon+0.3},{lat-0.3}", "bounded": "1"})
        if near and (not best or float(near.get("importance", 0)) >= float(best.get("importance", 0)) - 0.05):
            best = near
    if not best:
        return None
    return float(best["lat"]), float(best["lon"]), best.get("display_name", place)


def _distance_km(lat1, lon1, lat2, lon2):
    import math
    r = 6371.0
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dp, dl = p2 - p1, math.radians(lon2 - lon1)
    a = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * r * math.asin(math.sqrt(a))


def open_route(dest, cmd):
    mode, mode_ko = route_mode(cmd)
    loc = current_location()
    params = {"api": "1", "destination": dest, "travelmode": mode}
    if loc.get("lat") is not None:
        params["origin"] = f"{loc['lat']:.5f},{loc['lon']:.5f}"
    webbrowser.open("https://www.google.com/maps/dir/?" + urllib.parse.urlencode(params))
    where = f"{loc['name']}에서 " if loc.get("name") else "지금 위치에서 "
    extra = ""
    try:
        g = _geocode(dest)
        if g and loc.get("lat") is not None:
            km = _distance_km(loc["lat"], loc["lon"], g[0], g[1])
            extra = (f" 직선거리로 약 {km:.0f}킬로미터예요." if km >= 1
                     else f" 직선거리로 약 {int(km * 1000)}미터, 아주 가까워요.")
    except Exception:
        pass
    if not extra:
        return (f"'{dest}'{particle(dest, '을', '를')} 지도에서 찾아 띄웠어요. "
                "원하는 곳이 아니면 장소 이름을 다시 또박또박 말씀해 주세요.")
    return f"{where}{dest}까지 {mode_ko} 길을 지도에 띄웠어요.{extra} 자세한 경로는 화면에서 확인해 주세요, 보스."


def nearby_query(cmd):
    vm = re.search(r"(찾아|알려|보여|어디|추천)", cmd)
    if vm:
        cmd = cmd[:vm.start()] + vm.group(0) + (re.match(r"\S*", cmd[vm.end():]).group(0) if vm.group(0) != "어디" else cmd[vm.end():])
    q = re.sub(r"(이\s*)?(근처|주변|가까운|가까이)(에|에서|의)?", " ", cmd)
    q = re.sub(r"(여기서|여기|제일|가장|젤|좀)\s", " ", q + " ")
    q = re.sub(r"(찾아\s*줘|찾아\S*|알려\s*줘|보여\s*줘|어디\s*(있어|있지|야|에\s*있어)?|있어|있나|있을까|좀|추천해\s*줘|추천|뭐가)", " ", q)
    return re.sub(r"\s+", " ", q).strip(" ?")


def open_nearby(q):
    loc = current_location()
    url = "https://www.google.com/maps/search/" + urllib.parse.quote(q)
    if loc.get("lat") is not None:
        url += f"/@{loc['lat']:.5f},{loc['lon']:.5f},15z"
    webbrowser.open(url)
    where = loc.get("name") or "지금 위치"
    return f"{where} 근처 {q}, 지도에 찾아 띄웠어요."


WEATHER_SHOW_PAGE = True


def _wx_desc(entry):
    desc = ""
    if entry.get("lang_ko"):
        desc = (entry["lang_ko"][0].get("value") or "").strip()
    if not desc:
        desc = (entry.get("weatherDesc", [{}])[0].get("value") or "").strip()
    return _weather_desc_ko(desc)


def _wx_advice(rain, tmax, tmin):
    tips = []
    if rain >= 50:
        tips.append("우산 꼭 챙기세요.")
    elif rain >= 30:
        tips.append("혹시 모르니 작은 우산 하나 챙기시면 좋겠어요.")
    if tmax >= 30:
        tips.append("꽤 더우니 물 자주 드세요.")
    elif tmin <= 0:
        tips.append("많이 추우니 따뜻하게 입으세요.")
    elif tmax - tmin >= 10:
        tips.append("일교차가 크니 겉옷 하나 챙기세요.")
    return " ".join(tips[:2])


def get_weather_naver(place, day=0, label=""):
    url = "https://m.search.naver.com/search.naver?query=" + urllib.parse.quote(f"{place} 날씨".strip())
    req = urllib.request.Request(url, headers={
        "User-Agent": "Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) AppleWebKit/605.1.15 "
                      "(KHTML, like Gecko) Version/17.0 Mobile/15E148 Safari/604.1",
        "Accept-Language": "ko-KR,ko;q=0.9"})
    with urllib.request.urlopen(req, timeout=6) as resp:
        html = resp.read().decode("utf-8", errors="ignore")
    t = re.sub(r"\s+", " ", re.sub(r"<[^>]+>", " ", html)).replace("&nbsp;", " ")
    tag = "오늘" if day == 0 else "내일"
    wk = re.search(tag + r" \d+\.\d+\. (?:오전 )?(\d+)% (.+?) (?:오후 )?(\d+)% (.+?) 최저기온 (-?\d+)° 최고기온 (-?\d+)°", t)
    if not wk:
        return None
    rain = max(int(wk.group(1)), int(wk.group(3)))
    am_sky, pm_sky = wk.group(2).strip(), wk.group(4).strip()
    tmin, tmax = int(wk.group(5)), int(wk.group(6))
    advice = _wx_advice(rain, tmax, tmin)
    if day == 0:
        cur = re.search(r"오늘의 날씨 (\S+(?: \S+)?) 현재 온도 (-?[\d.]+) ?°", t)
        if not cur:
            return None
        sky, temp = cur.group(1), float(cur.group(2))
        dust = re.search(r"(?<!초)미세먼지 (좋음|보통|나쁨|매우나쁨)", t)
        head = f"{label} 날씨 알려드릴게요." if label else "오늘 날씨 알려드릴게요."
        body = (f" 지금은 {sky}, 기온 {round(temp)}도예요. 오늘 최고 {tmax}도, 최저 {tmin}도이고, "
                f"비 올 확률은 {rain}퍼센트예요." + (f" 미세먼지는 {dust.group(1)}이에요." if dust else ""))
    else:
        sky = pm_sky if pm_sky == am_sky else f"오전 {am_sky}, 오후 {pm_sky}"
        head = f"{label} 내일 날씨예요." if label else "내일 날씨예요."
        body = f" 내일은 {sky}, 최고 {tmax}도, 최저 {tmin}도이고, 비 올 확률은 {rain}퍼센트예요."
    return (head + body + (" " + advice if advice else "")).strip()


def get_weather(city_ko="", day=0):
    try:
        loc = current_location()
        place = city_ko.strip() or loc.get("query") or loc.get("name") or ""
        label = city_ko.strip() or loc.get("name") or ""
        if place:
            nv = get_weather_naver(place, day, label)
            if nv:
                return nv
    except Exception as e:
        print(f"[JARVIS] 네이버 날씨를 못 읽어서 다른 곳에서 가져올게요. ({str(e)[:60]})")
    try:
        city = city_ko.strip()
        target, label = city, city
        if not city:
            loc = current_location()
            if loc.get("lat") is not None:
                target = f"{loc['lat']:.2f},{loc['lon']:.2f}"
                label = loc.get("name") or ""
        url = f"https://wttr.in/{urllib.parse.quote(target)}?format=j1&lang=ko"
        req = urllib.request.Request(url, headers={"User-Agent": "jarvis-local/1.0"})
        with urllib.request.urlopen(req, timeout=8) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        days = data.get("weather") or []
        d = days[min(day, len(days) - 1)] if days else {}
        tmax = int(d.get("maxtempC", 0) or 0)
        tmin = int(d.get("mintempC", 0) or 0)
        hourly = d.get("hourly") or []
        if day == 0:
            now_h = datetime.datetime.now().hour
            later = [h for h in hourly if int(h.get("time", "0")) // 100 >= now_h - 2] or hourly
        else:
            later = hourly
        rain = max((int(h.get("chanceofrain", 0) or 0) for h in later), default=0)
        advice = _wx_advice(rain, tmax, tmin)

        if day == 0:
            cur = data["current_condition"][0]
            head = f"{label} 날씨 알려드릴게요." if label else "오늘 날씨 알려드릴게요."
            body = (f" 지금은 {_wx_desc(cur)}, 기온 {cur.get('temp_C', '?')}도예요."
                    f" 오늘 최고 {tmax}도, 최저 {tmin}도이고, 비 올 확률은 {rain}퍼센트예요.")
        else:
            noon = next((h for h in hourly if h.get("time") == "1200"), hourly[len(hourly) // 2] if hourly else {})
            head = f"{label} 내일 날씨예요." if label else "내일 날씨예요."
            body = (f" 내일은 {_wx_desc(noon)}, 최고 {tmax}도, 최저 {tmin}도이고,"
                    f" 비 올 확률은 {rain}퍼센트예요.")
        return (head + body + (" " + advice if advice else "")).strip()
    except Exception:
        return None


LANGS = [
    (r"인도네시아(?:어|말)?", "id", "인도네시아어", "Indonesian", "id-ID-ArdiNeural"),
    (r"영어|영국말|미국말", "en", "영어", "English", None),
    (r"일본(?:어|말)|(?<![독덕])일어(?!나)", "ja", "일본어", "Japanese", "ja-JP-KeitaNeural"),
    (r"중국(?:어|말)", "zh-CN", "중국어", "Simplified Chinese", "zh-CN-YunxiNeural"),
    (r"스페인(?:어|말)", "es", "스페인어", "Spanish", "es-ES-AlvaroNeural"),
    (r"프랑스(?:어|말)|불어", "fr", "프랑스어", "French", "fr-FR-HenriNeural"),
    (r"독[일열얼](?:어|허|말)", "de", "독일어", "German", "de-DE-ConradNeural"),
    (r"러시아(?:어|말)|노어", "ru", "러시아어", "Russian", "ru-RU-DmitryNeural"),
    (r"힌디(?:어)?|인도(?:어|말)", "hi", "힌디어", "Hindi", "hi-IN-MadhurNeural"),
    (r"베트남(?:어|말)", "vi", "베트남어", "Vietnamese", "vi-VN-NamMinhNeural"),
    (r"태국(?:어|말)", "th", "태국어", "Thai", "th-TH-NiwatNeural"),
    (r"이탈리아(?:어|말)", "it", "이탈리아어", "Italian", "it-IT-DiegoNeural"),
    (r"포르투갈(?:어|말)", "pt", "포르투갈어", "Portuguese", "pt-BR-AntonioNeural"),
    (r"아랍(?:어|말)", "ar", "아랍어", "Arabic", "ar-SA-HamedNeural"),
    (r"한국(?:어|말)|한글|우리말", "ko", "한국어", "Korean", None),
]
_LANG_ALT = "|".join(p for p, *_ in LANGS)
EDGE_VOICE_OTHER.update({code: v for _, code, _, _, v in LANGS if v})


def find_langs(text):
    found = []
    for pat, code, _, _, _ in LANGS:
        m = re.search(pat, text)
        if m:
            found.append((m.start(), code))
    return [c for _, c in sorted(found)]


def find_lang(text):
    for pat, code, kname, _, _ in LANGS:
        if re.search(pat, text):
            return code, kname
    return None, None


RE_TRANSLATE = re.compile(r"(번역|(?:" + _LANG_ALT + r")\s*(?:로|으로))")
RE_TRANSLATE_LANG = re.compile(r"(?:" + _LANG_ALT + r")")


_LANG_NAMES_EN = {code: en for _, code, _, en, _ in LANGS}


_RR_INIT = ["g", "kk", "n", "d", "tt", "r", "m", "b", "pp", "s", "ss", "", "j", "jj", "ch", "k", "t", "p", "h"]
_RR_MED = ["a", "ae", "ya", "yae", "eo", "e", "yeo", "ye", "o", "wa", "wae", "oe", "yo", "u", "wo", "we", "wi",
           "yu", "eu", "ui", "i"]
_RR_FIN = ["", "k", "k", "k", "n", "n", "n", "t", "l", "k", "m", "l", "l", "l", "p", "l", "m", "p", "p", "t", "t",
           "ng", "t", "t", "k", "t", "p", "t"]


def romanize_ko(word):
    out = []
    for ch in word:
        code = ord(ch) - 0xAC00
        if 0 <= code < 11172:
            out.append(_RR_INIT[code // 588] + _RR_MED[(code % 588) // 28] + _RR_FIN[code % 28])
        else:
            out.append(ch)
    return "".join(out).capitalize()


_NAME_FORMS = {}


def name_in(name, target):
    roman = romanize_ko(name)
    if target not in ("ja", "zh-CN"):
        return roman
    key = (name, target)
    if key not in _NAME_FORMS:
        script = "Japanese katakana" if target == "ja" else "Chinese characters"
        out = _groq_request([
            {"role": "system", "content": f"Write the given Korean personal name in {script} by its pronunciation "
                                          "(a transliteration of the sound, not a translation of meaning). "
                                          "Answer with only the name."},
            {"role": "user", "content": f"{name} ({roman})"}], max_tokens=20, temperature=0)
        out = (out or "").strip().strip("'\"「」")
        if not out or len(out) > 12:
            return roman
        _NAME_FORMS[key] = out
    return _NAME_FORMS[key]


def _translate_groq(text, target):
    lang = _LANG_NAMES_EN.get(target, "English")
    out = _groq_request([
        {"role": "system", "content": f"You are a translator. Translate the user's text into natural {lang}. "
                                      "Output only the translation, with no quotes, notes or romanization. "
                                      + (f"'{boss_name()}' is a person's name: write it exactly as "
                                         f"'{name_in(boss_name(), target)}', never translate it as a word. "
                                         if boss_name() and boss_name() in text else "")
                                      + "'자비스' is the name Jarvis."},
        {"role": "user", "content": text}], max_tokens=200, temperature=0.2)
    return (out or "").strip().strip('"').strip() or None


def _translate_google(text, target):
    url = ("https://translate.googleapis.com/translate_a/single?client=gtx&sl=auto&tl="
           + target + "&dt=t&q=" + urllib.parse.quote(text))
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(req, timeout=6) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    return "".join(seg[0] for seg in data[0] if seg and seg[0]).strip() or None


def _translate_mymemory(text, target):
    src = "en" if _detect_lang(text) == "en" else "ko"
    if src == target:
        src = "en" if target == "ko" else "ko"
    url = ("https://api.mymemory.translated.net/get?q=" + urllib.parse.quote(text)
           + "&langpair=" + src + "|" + target)
    with urllib.request.urlopen(urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"}), timeout=6) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    return (data.get("responseData") or {}).get("translatedText") or None


def translate_text(text, target="en"):
    for fn in (_translate_groq, _translate_google, _translate_mymemory):
        try:
            out = fn(text, target)
            if out:
                return out
        except Exception:
            continue
    return None


REPLY_LANG_FILE = os.path.join(BASE_DIR, "reply_lang.json")
_REPLY_LANG = {"code": "ko", "name": "한국어"}
_LANG_WORDS = "(" + _LANG_ALT + ")"
RE_LANG_MODE = re.compile(r"^(.*?)" + _LANG_WORDS + r"\s*(로|으로)\s*(만)?\s*(?:다시|계속|좀|그냥|이제)?\s*"
                          r"(말|대답|얘기|이야기|대화|바꿔|돌아|하자|할래|할게|한다|하기|부탁|실시|진행|모드|"
                          r"해(?=$|\s|줘|요|라|봐|[.!])|[.!?]*$)\S*")
RE_LANG_MODE_EN = re.compile(r"\b(speak|talk|answer|reply)\b.*\b(korean|english|japanese|chinese|german|french|spanish|russian)\b|"
                             r"\b(korean|english|japanese|chinese|german|french|spanish|russian)\s+only\b", re.I)


def _load_reply_lang():
    try:
        with open(REPLY_LANG_FILE, "r", encoding="utf-8") as f:
            d = json.load(f) or {}
        if d.get("code"):
            _REPLY_LANG.update(code=d["code"], name=d.get("name", d["code"]))
    except Exception:
        pass


_LANG_SET_AT = {"t": 0.0}


def reply_lang():
    return _REPLY_LANG["code"]


TTS_RATE_FILE = os.path.join(BASE_DIR, "tts_rate.json")
RE_SPEED = re.compile(r"(\d(?:\.\d+)?)\s*배\s*속|(말|말하는|목소리|대답)\s*(의\s*)?(속도|빠르기)|"
                      r"(빨리|빠르게|천천히|느리게|느릿느릿)\s*(좀\s*)?(말해|말하|얘기해|얘기하|대답해|읽어)")


def _rate_pct():
    return int(EDGE_RATE.replace("%", "") or 0)


def set_tts_rate(pct):
    global EDGE_RATE
    pct = max(-30, min(100, int(pct)))
    EDGE_RATE = f"{pct:+d}%"
    try:
        with open(TTS_RATE_FILE, "w", encoding="utf-8") as f:
            json.dump({"rate": EDGE_RATE}, f)
    except Exception:
        pass
    return pct


def _load_tts_rate():
    global EDGE_RATE
    try:
        with open(TTS_RATE_FILE, encoding="utf-8") as f:
            r = (json.load(f) or {}).get("rate", "")
        if re.fullmatch(r"[+-]\d{1,3}%", r):
            EDGE_RATE = r
    except Exception:
        pass


def handle_speed(cmd):
    if not RE_SPEED.search(cmd):
        return None
    if guest_on():
        return {"reply": "말 속도는 보스만 바꿀 수 있어요. 대신 다른 걸 해 볼까요?", "action": "info", "matched": "speed"}
    m = re.search(r"(\d(?:\.\d+)?)\s*배\s*속", cmd)
    cur = _rate_pct()
    if m:
        pct = round((float(m.group(1)) - 1) * 100)
    elif re.search(r"(원래|기본|보통|처음)", cmd):
        pct = int(EDGE_RATE_DEFAULT.replace("%", ""))
    elif re.search(r"(빨리|빠르게|빠른)", cmd):
        pct = cur + 15
    elif re.search(r"(천천히|느리게|느린|느릿)", cmd):
        pct = cur - 15
    else:
        return {"reply": f"지금은 {1 + cur / 100:.2f}배속으로 말하고 있어요. '1.5배속으로 말해'처럼 바꿀 수 있어요.".replace("0배속", "배속"),
                "action": "info", "matched": "speed"}
    pct = set_tts_rate(pct)
    x = f"{1 + pct / 100:.2f}".rstrip("0").rstrip(".")
    return {"reply": f"네, 이제 {x}배속으로 말할게요.", "action": "info", "matched": "speed"}


def set_reply_lang(code, name):
    _REPLY_LANG.update(code=code, name=name)
    _LANG_SET_AT["t"] = time.time()
    try:
        with open(REPLY_LANG_FILE, "w", encoding="utf-8") as f:
            json.dump(_REPLY_LANG, f, ensure_ascii=False)
    except Exception:
        pass


_LAST_REPLY = {"text": ""}


def try_lang_mode(cmd):
    code = name = None
    if reply_lang() != "ko" and len(cmd) <= 25 and re.search(r"(한국어|한국말|korean)", cmd, re.I) \
            and not re.search(r"(번역|뭐야|뭐라고|어떻게\s*말|무슨\s*뜻|뜻이)", cmd):
        set_reply_lang("ko", "한국어")
        again = ""
        if re.search(r"다시\s*(말|해|얘기)", cmd) and _LAST_REPLY.get("text"):
            again = translate_text(_LAST_REPLY["text"], "ko") or ""
        return {"reply": "네, 보스. 다시 한국어로 말씀드릴게요." + (" " + again if again else ""),
                "action": "info", "matched": "lang_mode"}
    m0 = re.search(r"(지금부터|이제부터|앞으로는?|다시)\s*" + _LANG_WORDS + r"(?:로|으로)?\s*(?:만|모드)?\s*(?:해|해줘|하자|말해|말해줘|대답해|대답해줘)?[.!?\s]*$", cmd)
    if m0 and "번역" not in cmd:
        code, name = find_lang(m0.group(2))
        if code:
            m = None
        else:
            m0 = None
    m = None if m0 else RE_LANG_MODE.search(cmd)
    trial = re.search(r"(말해\s*볼래|말해\s*봐|말할\s*수\s*있|할\s*수\s*있어|가능해|해\s*볼래)", cmd) and \
        not re.search(r"(이제부터|지금부터|앞으로|계속|만\s*(말|대답)|모드|바꿔)", cmd)
    if m and trial:
        code, name = find_lang(m.group(2))
        if code and code != "ko":
            kname = find_lang(m.group(2))[1]
            sample = translate_text(f"네, 보스. {kname}로도 말할 수 있어요. 계속 {kname}로 말하길 원하시면 말씀해 주세요.", code)
            if sample:
                return {"reply": sample, "action": "info", "matched": "translate",
                        "speak_parts": [{"text": sample, "lang": code}]}
        m = None
    if m:
        prefix = re.sub(r"(이제부터|지금부터|앞으로는?|이제는?|계속|다시|그냥|자비스|헤이|네|응|아니|아니야|너|넌|좀|"
                        r"[가-힣]?[비미]스|jarvis|[,.!?\s])", "", m.group(1), flags=re.I)
        if prefix and not m.group(4) and (re.search(r"(을|를)$", prefix) or len(prefix) > 4) \
                and find_lang(m.group(2))[0] != "ko":
            return None
        code, name = find_lang(m.group(2))
    elif not m0:
        m2 = RE_LANG_MODE_EN.search(cmd)
        if not m2:
            return None
        w = (m2.group(2) or m2.group(3) or "").lower()
        code, name = {"korean": ("ko", "한국어"), "english": ("en", "영어"), "japanese": ("ja", "일본어"),
                      "chinese": ("zh-CN", "중국어"), "german": ("de", "독일어"), "french": ("fr", "프랑스어"),
                      "spanish": ("es", "스페인어"), "russian": ("ru", "러시아어")}[w]
    if not code:
        return None
    set_reply_lang(code, name)
    again = ""
    if re.search(r"다시\s*(말|해|얘기)", cmd) and _LAST_REPLY.get("text"):
        again = translate_text(_LAST_REPLY["text"], code) or ""
    if code == "ko":
        msg = "네, 보스. 다시 한국어로 말씀드릴게요." + (" " + again if again else "")
        return {"reply": msg, "action": "info", "matched": "lang_mode"}
    msg = translate_text(f"알겠습니다, 보스. 이제부터 {name}로만 말씀드릴게요.", code) or f"OK. {name}"
    if again:
        msg += " " + again
    return {"reply": msg, "action": "info", "matched": "lang_mode",
            "speak_parts": [{"text": msg, "lang": code}]}


def handle_translate(cmd):
    target, tname = find_lang(cmd)
    if not target:
        target, tname = "en", "영어"
    lang_words = "(" + _LANG_ALT + ")"
    text = re.sub(r"\s*(을|를)?\s*" + lang_words + r"\s*(로|으로)?\s*(는|번역\S*|뭐\S*|어떻게\s*\S*|말해\S*|알려\S*|해\s*줘|좀)*.*$", "", cmd)
    text = re.sub(r"\s*(을|를)?\s*번역\S*.*$", "", text)
    text = re.sub(r"^(이거|이걸|이 말|다음 말|번역해\s*줘)\s*", "", text).strip(" ,.'\"")
    if not text:
        text = re.sub(r"^\s*" + lang_words + r"\s*(로|으로)\s*(는)?\s*", "", cmd)
        text = re.sub(r"\s*(을|를)?\s*(번역\S*|말해\S*|해\s*줘|알려\S*|뭐\S*|어떻게\s*\S*)(\s*\S*)?$", "", text).strip(" ,.'\"")
    text = re.sub(r"(?<=[요다해워와야지까니])(가|는|라|은|이)$", "", text).strip()
    if not text:
        return {"reply": "번역할 말을 함께 말씀해 주세요. 예를 들면, 사랑해를 영어로 번역해줘.", "action": "info", "matched": "translate"}
    tr = translate_text(text, target)
    if not tr:
        return {"reply": "지금은 번역 서비스에 연결이 안 돼요. 잠시 뒤에 다시 말씀해 주세요.", "action": "error", "matched": None}
    return {"reply": f"'{text}' {tname}로는, {tr}", "action": "info", "matched": "translate",
            "speak_parts": [{"text": f"{text}, {tname}로는", "lang": "ko"}, {"text": tr, "lang": target}]}


NOTES_FILE = os.path.join(BASE_DIR, "jarvis_notes.txt")
RE_NOTE_CLEAR = re.compile(r"메모\s*(전부|다|모두)?\s*(지워|삭제|비워)")
RE_NOTE_READ = re.compile(r"(메모|할\s*일)\s*(뭐|읽|보여|알려|목록|있)")
RE_NOTE_ADD = re.compile(r"(메모\s*(해|추가|남겨|하자)|적어\s*(둬|놔|줘)|할\s*일\s*(추가|등록))")


def add_note(text):
    try:
        with open(NOTES_FILE, "a", encoding="utf-8") as f:
            f.write(text.strip() + "\n")
        return True
    except Exception:
        return False


def read_notes():
    try:
        with open(NOTES_FILE, encoding="utf-8") as f:
            return [ln.strip() for ln in f if ln.strip()]
    except Exception:
        return []


def clear_notes():
    try:
        open(NOTES_FILE, "w", encoding="utf-8").close()
        return True
    except Exception:
        return False


FINANCE_ENABLED = False

RE_FX = re.compile(r"환율")
_FX_MAP = {"달러": ("USD", "달러"), "미국": ("USD", "달러"), "엔화": ("JPY", "엔"), "엔": ("JPY", "엔"),
           "유로": ("EUR", "유로"), "위안": ("CNY", "위안"), "파운드": ("GBP", "파운드")}


def _naver_json(url):
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X)"})
    with urllib.request.urlopen(req, timeout=6) as resp:
        return json.loads(resp.read().decode("utf-8"))


def get_fx(code, name):
    try:
        r = _naver_json(f"https://m.stock.naver.com/front-api/marketIndex/productDetail?category=exchange&reutersCode=FX_{code}KRW")
        price = float(str(r["result"]["closePrice"]).replace(",", ""))
        if code == "JPY":
            return f"현재 100엔은 약 {round(price):,}원이에요."
        return f"현재 1{name}는 약 {round(price):,}원이에요."
    except Exception:
        pass
    try:
        url = f"https://open.er-api.com/v6/latest/{code}"
        req = urllib.request.Request(url, headers={"User-Agent": "jarvis-local/1.0"})
        with urllib.request.urlopen(req, timeout=8) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        krw = data.get("rates", {}).get("KRW")
        if not krw:
            return None
        if code == "JPY":
            return f"현재 100엔은 약 {round(krw * 100):,}원이에요."
        return f"현재 1{name}는 약 {round(krw):,}원이에요."
    except Exception:
        return None


RE_STOCK = re.compile(r"(주가|주식|시세)")
_TICKERS = {"애플": "AAPL", "테슬라": "TSLA", "엔비디아": "NVDA", "마이크로소프트": "MSFT",
            "구글": "GOOGL", "아마존": "AMZN", "메타": "META", "넷플릭스": "NFLX",
            "삼성전자": "005930.KS", "삼성": "005930.KS", "sk하이닉스": "000660.KS",
            "하이닉스": "000660.KS", "카카오": "035720.KS", "네이버": "035420.KS",
            "현대차": "005380.KS", "lg에너지솔루션": "373220.KS"}


def get_stock(name, ticker):
    name = re.sub(r"^sk", "SK", name)
    if ticker.endswith((".KS", ".KQ")):
        try:
            d = _naver_json(f"https://m.stock.naver.com/api/stock/{ticker.split('.')[0]}/basic")
            price = d["closePrice"]
            pct = float(str(d.get("fluctuationsRatio", "0")).replace(",", ""))
            closed = d.get("marketStatus") == "CLOSE"
            s = f"{name} {'오늘 종가는' if closed else '현재 주가는'} {price}원이에요."
            if pct:
                s += f" 전날보다 {abs(pct)}퍼센트 {'올랐어요' if pct > 0 else '내렸어요'}."
            return s
        except Exception:
            pass
    try:
        url = f"https://query1.finance.yahoo.com/v8/finance/chart/{ticker}?interval=1d&range=1d"
        req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
        with urllib.request.urlopen(req, timeout=8) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        meta = data["chart"]["result"][0]["meta"]
        price = meta.get("regularMarketPrice")
        prev = meta.get("chartPreviousClose") or meta.get("previousClose")
        cur = meta.get("currency", "")
        unit = "원" if cur == "KRW" else ("달러" if cur == "USD" else cur)
        val = round(price) if unit == "원" else round(price, 2)
        s = f"{name} 현재 주가는 {val:,}{unit}입니다"
        if prev:
            pct = (price - prev) / prev * 100
            s += f". 전일 대비 {abs(round(pct, 2))}퍼센트 {'상승' if pct >= 0 else '하락'}했습니다"
        return s + "."
    except Exception:
        return None


RE_MUSIC = re.compile(r"(틀어|재생|노래|음악|스포티|플레이|플레이리스트)")

RE_WIKI = re.compile(r"(위키|위키백과|에\s*대해\s*(설명|알려)|에\s*대해서|뜻이?\s*뭐|무슨\s*뜻|누구야|누구니)")


def get_wikipedia(query):
    try:
        title = urllib.parse.quote(query.strip().replace(" ", "_"))
        url = f"https://ko.wikipedia.org/api/rest_v1/page/summary/{title}"
        req = urllib.request.Request(url, headers={"User-Agent": "jarvis-local/1.0"})
        with urllib.request.urlopen(req, timeout=8) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        if data.get("type", "").endswith("not_found"):
            return None
        extract = (data.get("extract") or "").strip()
        if not extract or data.get("type") == "disambiguation" or re.search(r"(다음을\s*가리킨다|다음과\s*같은\s*뜻)", extract):
            return None
        extract = re.sub(r"\s*[(（][^()（）]*[)）]", "", extract)
        sents = re.split(r"(?<=[.!?。])\s+", extract)
        return " ".join(sents[:2])
    except Exception:
        return None


RE_CALC = re.compile(r"(-?\d[\d,\.]*)\s*(더하기|플러스|빼기|마이너스|곱하기|곱하면|나누기|\+|\-|\*|x|X|÷|/)\s*(\d[\d,\.]*)")


_KO_DIGIT = {"일": 1, "이": 2, "삼": 3, "사": 4, "오": 5, "육": 6, "륙": 6, "칠": 7, "팔": 8, "구": 9}
_KO_NUM_RE = re.compile(r"(?:([이삼사오육칠팔구])?(천))?(?:([이삼사오육칠팔구])?(백))?(?:([이삼사오육칠팔구])?(십))?([일이삼사오육륙칠팔구])?")
_CALC_OP = r"(더하기|플러스|빼기|마이너스|곱하기|곱하면|나누기)"


def _ko_num(word):
    m = _KO_NUM_RE.match(word or "")
    if not m or not m.group(0):
        return None
    v = 0
    for d, unit, mul in ((1, 2, 1000), (3, 4, 100), (5, 6, 10)):
        if m.group(unit):
            v += (_KO_DIGIT[m.group(d)] if m.group(d) else 1) * mul
    if m.group(7):
        v += _KO_DIGIT[m.group(7)]
    return v, len(m.group(0))


def _ko_calc_numbers(cmd):
    def left(mt):
        w = mt.group(1)
        r = _ko_num(w)
        return (str(r[0]) + " " + mt.group(2)) if r and r[1] == len(w) else mt.group(0)
    def right(mt):
        w = mt.group(2)
        r = _ko_num(w)
        return (mt.group(1) + " " + str(r[0]) + w[r[1]:]) if r else mt.group(0)
    cmd = re.sub(r"(?<![가-힣])상(?=\s*" + _CALC_OP + ")", "삼", cmd)
    cmd = re.sub(r"(?<![가-힣])([일이삼사오육륙칠팔구십백천]+)\s*" + _CALC_OP, left, cmd)
    cmd = re.sub(_CALC_OP + r"\s*([일이삼사오육륙칠팔구십백천]+)", right, cmd)
    return cmd


def do_calc(cmd):
    cmd = _ko_calc_numbers(cmd)
    m = RE_CALC.search(cmd.replace(",", ""))
    if not m:
        return None
    a, op, b = float(m.group(1)), m.group(2), float(m.group(3))
    if op in ("더하기", "플러스", "+"):
        r = a + b
    elif op in ("빼기", "마이너스", "-"):
        r = a - b
    elif op in ("곱하기", "곱하면", "*", "x", "X"):
        r = a * b
    elif op in ("나누기", "÷", "/"):
        if b == 0:
            return "0으로는 나눌 수 없습니다."
        r = a / b
    else:
        return None
    r = int(r) if r == int(r) else round(r, 4)
    b_txt = m.group(3)
    res = f"{r:,}" if isinstance(r, int) else f"{r}"
    op_word = {"+": "더하기", "-": "빼기", "*": "곱하기", "x": "곱하기", "X": "곱하기", "/": "나누기", "÷": "나누기",
               "곱하면": "곱하기"}.get(op, op)
    return f"{m.group(1)} {op_word} {b_txt}{particle(b_txt, '은', '는')} {res}입니다."


RE_COIN = re.compile(r"(동전\s*(던져|던지기|던질|튕겨|굴려)|앞\s*뒤)")
RE_DICE = re.compile(r"(주사위)")
_KO_COUNT = {"한": 1, "하나": 1, "두": 2, "둘": 2, "세": 3, "셋": 3, "1": 1, "2": 2, "3": 3}


_LAST_FUN = {"kind": None, "cmd": "", "at": 0.0}
RE_FUN_AGAIN = re.compile(r"^\s*((한|하나|두|둘|세|셋|[123])\s*개\s*(로|를|만)?\s*(굴려|던져|돌려)|(다시|한\s*번\s*더|또|한\s*번만\s*더)\s*(굴려|던져|돌려|해)|"
                          r"(굴려|던져|돌려)\s*(줘|봐)?\s*(다시|한\s*번\s*더)?)\s*(줘|봐|주세요|줄래)?\s*[.!?~]*\s*$")


def fun_again(cmd):
    k = _LAST_FUN["kind"]
    if not k or time.time() - _LAST_FUN["at"] > 60 or not RE_FUN_AGAIN.search(cmd):
        return None
    if k == "dice":
        return roll_dice(cmd if re.search(r"(한|하나|두|둘|세|셋|[123])\s*개", cmd) else _LAST_FUN["cmd"])
    if k == "coin":
        return flip_coin()
    return spin_roulette(_LAST_FUN["cmd"])


def _remember_fun(kind, cmd):
    _LAST_FUN.update(kind=kind, cmd=cmd, at=time.time())


def roll_dice(cmd):
    m = re.search(r"(한|하나|두|둘|세|셋|[123])\s*(개|번)?\s*(의\s*)?주사위|(주사위\s*(를\s*)?|^\s*)(한|하나|두|둘|세|셋|[123])\s*개", cmd)
    n = _KO_COUNT.get((m.group(1) or m.group(6)) if m else "1", 1)
    _remember_fun("dice", f"주사위 {n}개")
    vals = [random.randint(1, 6) for _ in range(n)]
    if n == 1:
        res = f"{vals[0]}{particle(str(vals[0]), '이', '가')} 나왔습니다."
        sub = "1부터 6 중에서"
    else:
        tot = sum(vals)
        res = f"{', '.join(map(str, vals))}, 합해서 {tot}{particle(str(tot), '이', '가')} 나왔습니다."
        sub = f"합계 {tot}"
    before = "주사위를 굴립니다." if n == 1 else f"주사위 {n}개를 굴립니다."
    return {"reply": f"{before} {res}", "action": "info", "matched": "dice",
            "card": {"icon": "", "title": "주사위", "big": " + ".join(map(str, vals)) if n > 1 else str(vals[0]),
                     "sub": sub, "anim": "dice", "values": vals, "say_before": before, "say_after": res}}


def flip_coin():
    _remember_fun("coin", "")
    side = random.choice(["앞면", "뒷면"])
    return {"reply": f"동전을 던집니다. 결과는 {side}입니다.", "action": "info", "matched": "coin",
            "card": {"icon": "", "title": "동전 던지기", "big": side, "sub": "", "anim": "coin", "side": side,
                     "say_before": "동전을 던집니다.", "say_after": f"동전의 {side}이 나왔습니다."}}


RE_JOKE = re.compile(r"(((아재\s*)?개그|농담|웃긴\s*(얘기|이야기|거|말|썰)|(웃기는|재밌는)\s*(얘기|이야기|말))\s*((을|를|좀|하나|한\s*(개|번|마디)|더)\s*)*"
                     r"(해|들려|말해|알려|쳐|읊어|부탁|ㄱ)|웃겨\s*(줘|봐|주세요|볼래)|tell\s+(me\s+)?a\s+joke)", re.I)
_LAUGHS = {"ko": ["하하하하!", "푸하하하!", "으하하하!", "크크크, 하하하!"], "ja": ["あはははは！", "ははは！"],
           "en": ["Ha ha ha!", "Hahaha!"], "zh": ["哈哈哈！"]}


JOKES = [
    ("세상에서 가장 가난한 왕은?", "최저임금", "임금이 왕이니까요."),
    ("왕이 넘어지면?", "킹콩", "킹이 콩 넘어졌으니까요."),
    ("세상에서 가장 뜨거운 과일은?", "천도복숭아", "천 도니까요."),
    ("바나나가 웃으면?", "바나나킥", "킥킥 웃으니까요."),
    ("오리가 얼면?", "언덕", "언 덕, 덕은 영어로 오리."),
    ("딸기가 직장을 잃으면?", "딸기시럽", "딸기 실업이니까요."),
    ("세상에서 가장 쉬운 숫자는?", "십구만", "쉽구만!"),
    ("미국에서 비가 오면?", "유에스비", "유에스에 비가 오니까요."),
    ("자동차를 톡 치면?", "카톡", "카를 톡!"),
    ("개가 사람을 가르치면?", "개인지도", ""),
    ("아몬드가 죽으면?", "다이아몬드", "다이, 아몬드."),
    ("토끼가 쓰는 빗은?", "래빗", "래빗은 영어로 토끼."),
    ("반성문을 영어로 하면?", "글로벌", "글로 벌 받으니까요."),
    ("비가 한 시간 동안 내리면?", "추적 육십 분", "추적추적 육십 분."),
    ("물고기의 반대말은?", "불고기", "물 반대는 불."),
    ("가장 지루한 중학교는?", "로딩중", ""),
    ("칼이 정색하면?", "검정색", "검이 정색."),
    ("사과가 웃으면?", "풋사과", "풋! 하고 웃으니까요."),
    ("세상에서 가장 착한 사자는?", "자원봉사자", ""),
    ("깨가 죽으면?", "주근깨", "죽은 깨."),
    ("엄마가 길을 잃으면?", "맘마미아", "맘이 마이 아파요."),
    ("가장 비싼 새는?", "백조", "백 조 원이니까요."),
]
_JOKE_DECK = []


def tell_joke():
    if not _JOKE_DECK:
        _JOKE_DECK.extend(random.sample(JOKES, len(JOKES)))
    q, a, why = _JOKE_DECK.pop()
    after = f"정답은 {a}! {why}".strip()
    return {"reply": f"{q} {after}", "action": "info", "matched": "joke", "laugh": laugh_line(),
            "card": {"icon": "😆", "title": "아재개그", "big": a, "sub": why, "anim": "joke", "question": q,
                     "say_before": q, "say_after": after}}


def laugh_line():
    code = reply_lang()
    return {"text": random.choice(_LAUGHS.get(code) or _LAUGHS["en"]), "lang": "ko-KR" if code == "ko" else code}


RE_ROULETTE = re.compile(r"(룰렛|롤렛|룰레트|돌림판|돌림\s*판|제비\s*뽑기|랜덤\s*(으로\s*)?(골라|뽑아|정해))")
ROULETTE_PRESETS = [
    (re.compile(r"(점심|저녁|아침|야식|메뉴|뭐\s*먹|먹을\s*거|음식)"),
     ["짜장면", "김치찌개", "돈가스", "햄버거", "떡볶이", "치킨", "라면", "초밥"]),
    (re.compile(r"(벌칙)"), ["노래 한 소절", "애교 하기", "통과!", "윙크 하기", "사진 찍기", "통과!"]),
]
ROULETTE_DEFAULT = ["당첨", "꽝", "한 번 더", "꽝", "대박", "꽝"]
_ROULETTE_FILLER = re.compile(r"^(자비스(야)?|그럼|그러면|음+|어+|아+|좀|줘|한\s*번|한번|그냥|이거|돌려|돌려줘|해줘|해\s*줘|해봐|"
                              r"룰렛|돌림판|제비|뽑기|랜덤|으로|로|중에|중에서|중|가운데|에서|를|을|넣고|넣어서|가지고)$")


def _roulette_options(cmd):
    rng = re.search(r"(\d+)\s*(부터|에서|~|-)\s*(\d+)\s*(까지|중|사이)?", cmd)
    if rng:
        a, b = int(rng.group(1)), int(rng.group(3))
        if a > b:
            a, b = b, a
        if 2 <= b - a + 1 <= 12:
            return [str(i) for i in range(a, b + 1)]
        if b - a + 1 > 12:
            return ("range", a, b)
    m = RE_ROULETTE.search(cmd)
    parts = [cmd[:m.start()], cmd[m.end():]] if m else [cmd]
    for seg in parts:
        seg = re.sub(r"^\s*(자비스(야)?|그럼|그러면)[\s,]*", "", seg)
        seg = re.sub(r"(돌려\s*줘|돌려\s*봐|돌려|해\s*줘|해\s*봐|골라\s*줘|뽑아\s*줘|정해\s*줘|좀|한\s*번)\s*[.!?~]*", " ", seg)
        seg = re.sub(r"\s*(중에서|중에|가운데|중|에서|으로|로|를|을)\s*$", "", seg.strip())
        seg = re.sub(r"(이랑|랑|하고|아니면|또는|vs|VS)(?=[\s,]|$)", ",", seg)
        items = [x.strip(" .!?~") for x in re.split(r"[,/、]|\s+", seg)]
        items = [x for x in items if x and not _ROULETTE_FILLER.match(x) and len(x) <= 12]
        if any(rx.search(" ".join(items)) for rx, _ in ROULETTE_PRESETS) and len(items) <= 3:
            continue
        if 2 <= len(items) <= 12:
            return items
    for rx, opts in ROULETTE_PRESETS:
        if rx.search(cmd):
            return list(opts)
    return list(ROULETTE_DEFAULT)


def spin_roulette(cmd):
    _remember_fun("roulette", cmd)
    opts = _roulette_options(cmd)
    if isinstance(opts, tuple):
        _, a, b = opts
        n = random.randint(a, b)
        res = f"{n}{particle(str(n), '이', '가')} 나왔습니다."
        return {"reply": f"{a}부터 {b}까지 중에서 뽑습니다. {res}", "action": "info", "matched": "roulette",
                "card": {"icon": "", "title": "숫자 뽑기", "big": str(n), "sub": f"{a} ~ {b}", "anim": "number",
                         "lo": a, "hi": b, "say_before": "숫자를 뽑습니다.", "say_after": res}}
    i = random.randrange(len(opts))
    pick = opts[i]
    res = f"결과는 {pick}입니다!"
    return {"reply": f"룰렛을 돌립니다. {res}", "action": "info", "matched": "roulette",
            "card": {"icon": "", "title": "룰렛", "big": pick, "sub": "", "anim": "roulette", "options": opts,
                     "pick": i, "say_before": "룰렛을 돌립니다.", "say_after": res}}

RE_QUIZ = re.compile(r"((넌센스|상식|보안)?\s*퀴즈|문제\s*(하나\s*)?(내|낼|내봐|줘))")
RE_RPS = re.compile(r"(가위\s*바위\s*보|묵\s*찌\s*빠|짱\s*깸\s*뽀)")
RE_FORTUNE = re.compile(r"(운세|오늘의?\s*운\b|행운의?\s*(숫자|색|번호)|점\s*(좀\s*)?(봐|쳐))")

QUIZZES = [
    ("세상에서 가장 뜨거운 과일은 뭘까요?", ["천도복숭아", "천도"], "천도복숭아", "천 도나 되는 복숭아예요."),
    ("왕이 넘어지면 뭐가 될까요?", ["킹콩"], "킹콩", "영어로 왕은 킹이에요."),
    ("세상에서 가장 쉬운 숫자는 뭘까요?", ["190000", "19만", "십구만", "쉽구만"], "십구만, 쉽구만!", "만 단위 숫자예요."),
    ("아몬드가 죽으면 뭐가 될까요?", ["다이아몬드", "다이"], "다이아몬드", "영어로 죽다는 다이예요."),
    ("세상에서 가장 빠른 닭은 뭘까요?", ["후다닭", "후다닥"], "후다닭", "빨리 뛰는 소리를 떠올려 보세요."),
    ("사과가 웃으면 뭐가 될까요?", ["풋사과"], "풋사과", "웃음소리 '풋'이에요."),
    ("도둑이 가장 좋아하는 아이스크림은?", ["보석바"], "보석바", "도둑은 반짝이는 걸 좋아해요."),
    ("소가 웃는 소리를 세 글자로 하면?", ["우하하"], "우하하", "소는 음메, 웃음은 하하."),
    ("컴퓨터의 두뇌 역할을 하는 부품은? 영어 세 글자예요.", ["cpu", "씨피유", "시피유", "중앙처리장치"], "CPU, 중앙처리장치", "씨로 시작해요."),
    ("가짜 사이트나 문자로 비밀번호를 훔치는 사기를 뭐라고 할까요?", ["피싱", "스미싱", "phishing"], "피싱", "낚시라는 영어에서 왔어요."),
    ("컴퓨터 바이러스를 막아 주는 프로그램을 뭐라고 할까요?", ["백신", "안티바이러스", "v3", "알약"], "백신 프로그램", "주사 맞을 때도 듣는 말이에요."),
    ("0과 1, 두 숫자만으로 수를 나타내는 방법을 뭐라고 할까요?", ["이진법", "2진법", "이진수", "2진수"], "이진법", "숫자 두 개, 이 ○ 법."),
    ("한글을 만든 왕은 누구일까요?", ["세종"], "세종대왕", "만 원짜리 지폐에 계세요."),
    ("태양계에서 가장 큰 행성은?", ["목성"], "목성", "나무 목 자가 들어가요."),
    ("무지개는 몇 가지 색일까요?", ["7", "일곱", "칠"], "일곱 가지", "빨주노초파남보를 세어 보세요."),
    ("물이 끓는 온도는 몇 도일까요?", ["100", "백도", "백 도"], "100도", "세 자리 숫자예요."),
    ("아이언맨의 진짜 이름은?", ["토니", "스타크"], "토니 스타크", "스타크 인더스트리의 주인이에요."),
    ("펭귄이 가장 많이 사는 대륙은?", ["남극"], "남극", "아주 추운 곳이에요."),
    ("세계에서 가장 높은 산은?", ["에베레스트"], "에베레스트산", "히말라야에 있어요."),
    ("1년은 보통 며칠일까요?", ["365", "삼백육십오"], "365일", "300이 넘어요."),
    ("우리나라의 수도는 어디일까요?", ["서울"], "서울", "남산타워가 있는 곳이에요."),
    ("비밀번호로 가장 위험한 건? 1, 생일. 2, 길고 복잡한 문장.", ["일번", "1번", "첫번째", "생일"], "1번, 생일", "남이 쉽게 알 수 있는 쪽이에요."),
]
_FORTUNES = [
    "오늘은 새로운 걸 시작하기 딱 좋은 날이에요.", "생각지도 못한 칭찬을 듣게 될 거예요.",
    "친구와 함께하면 일이 두 배로 잘 풀려요.", "작은 친절이 큰 행운으로 돌아와요.",
    "오늘은 맛있는 걸 먹게 될 운이에요.", "미뤄 둔 일을 끝내면 기분이 확 좋아질 거예요.",
    "좋은 소식이 곧 들려올 거예요.", "웃는 얼굴이 오늘의 행운을 불러와요.",
    "오늘 배운 것 하나가 나중에 크게 쓰여요.", "용기 내서 말을 걸면 좋은 인연이 생겨요.",
    "잃어버린 물건을 찾게 될지도 몰라요.", "오늘은 뭘 해도 술술 풀리는 날이에요.",
    "조금 쉬어 가도 괜찮은 날이에요. 몸을 챙겨 주세요.", "오늘의 선택이 내일을 웃게 해요.",
]
_LUCKY_COLORS = ["파란색", "빨간색", "노란색", "초록색", "보라색", "하얀색", "주황색", "하늘색"]
_RPS = {"가위": "✌️", "바위": "✊", "보": "✋"}
_GAME = {"kind": None, "until": 0.0, "quiz": None, "tries": 0}
_GAME_LOCK = threading.Lock()


_RPS_SOUNDALIKE = [
    ("바위", r"(바비|바이|바의|바우|바휘|바뷔|바귀|빠위|파위|마위|바이요|바비요|바위요|봐위|바외|빠이)"),
    ("가위", r"(까위|카위|가이|가비|가의|과위|가외|까이|가휘|가위요)"),
    ("보", r"(보오|보우|보요|뽀|보어|보|보자|보자기요|보석|보석이|보자귀|보자게|보작이|폰|본|뽄|봄)"),
]


def _rps_choice(text):
    t = re.sub(r"\s+", "", text)
    found = []
    if re.search(r"(가위|찌)", t):
        found.append("가위")
    if re.search(r"(바위|주먹|묵)", t):
        found.append("바위")
    if re.search(r"(보자기|보낼|보야|(^|나는|난|저는|전)(보|빠)[!.?~요]*$)", t):
        found.append("보")
    if len(found) == 1:
        return found[0]
    if found:
        return None
    core = re.sub(r"^(나는|난|저는|전|음|어|아)", "", re.sub(r"[!.?~,]", "", t))
    core = re.sub(r"(낼게|낼래|낼께|요|!)$", "", core)
    for name, rx in _RPS_SOUNDALIKE:
        if re.fullmatch(rx, core):
            return name
    return None


def _rps_play(mine):
    me = random.choice(list(_RPS))
    if me == mine:
        res = "비겼어요! 한 판 더 할까요?"
    elif (mine, me) in (("가위", "보"), ("바위", "가위"), ("보", "바위")):
        res = "보스가 이겼어요! 대단한데요?"
    else:
        res = "제가 이겼어요! 한 판 더 하실래요?"
    return {"reply": f"보스는 {mine}, 저는 {me}! {res}", "action": "info", "matched": "rps",
            "card": {"icon": _RPS[mine] + " vs " + _RPS[me], "title": "가위바위보",
                     "big": res.split("!")[0], "sub": f"보스 {mine} · 자비스 {me}"}}


def game_start(cmd):
    if RE_RPS.search(cmd):
        rest = cmd[RE_RPS.search(cmd).end():]
        mine = _rps_choice(rest) if rest.strip(" !.?~") else None
        if mine:
            return _rps_play(mine)
        with _GAME_LOCK:
            _GAME.update(kind="rps", until=time.time() + 40)
        return {"reply": "좋아요! 가위, 바위, 보 중에 하나를 말해 주세요. 보는 '보자기'라고 하면 더 잘 들려요.",
                "action": "info", "matched": "rps",
                "card": {"icon": "✌️ ✊ ✋", "title": "가위바위보", "big": "가위 · 바위 · 보자기", "sub": "하나를 말해 주세요"}}
    if RE_QUIZ.search(cmd) and not re.search(r"(열어|켜|검색|찾아|틀어)", cmd):
        q = random.choice([x for x in QUIZZES if x is not _GAME.get("quiz")] or QUIZZES)
        with _GAME_LOCK:
            _GAME.update(kind="quiz", until=time.time() + 60, quiz=q, tries=0)
        return {"reply": "퀴즈 나갑니다! " + q[0], "action": "info", "matched": "quiz",
                "card": {"icon": "❓", "title": "퀴즈", "big": q[0], "sub": "정답을 말해 주세요 · '힌트' 또는 '정답 알려줘'"}}
    if RE_FORTUNE.search(cmd):
        f = random.choice(_FORTUNES)
        color, num = random.choice(_LUCKY_COLORS), random.randint(1, 99)
        return {"reply": f"오늘의 운세예요. {f} 행운의 색은 {color}, 행운의 숫자는 {num}이에요.",
                "action": "info", "matched": "fortune",
                "card": {"icon": "🔮", "title": "오늘의 운세", "big": f, "sub": f"행운의 색 {color} · 행운의 숫자 {num}"}}
    return None


def game_answer(cmd):
    with _GAME_LOCK:
        kind = _GAME["kind"] if time.time() < _GAME["until"] else None
        if not kind:
            _GAME["kind"] = None
            return None
        short = re.sub(r"[\s,.!?~]", "", cmd)
        other_cmd = re.search(r"(곱하기|더하기|빼기|나누기|주사위|동전|룰렛|돌림판|날씨|몇\s*시|운세|번역|영어로|일본어로|중국어로|노래|"
                              r"크롬|계산기|메모장|유튜브|엣지|자기\s*소개|뭐\s*할\s*수)", cmd)
        if (_ACTION_RE.search(cmd) and not re.search(r"(정답|힌트)", cmd)) or len(short) > 16 or RE_QUIZ.search(cmd) \
                or RE_RPS.search(cmd) or (other_cmd and kind == "quiz"):
            _GAME["kind"] = None
            return None
        if kind == "rps":
            mine = _rps_choice(cmd)
            if not mine and re.fullmatch(r"(응|어|네|그래|좋아|콜|오케이|한판더|한번더|또|더해|하자|해)+(요|줘)?", short):
                return {"reply": "좋아요! 가위, 바위, 보!", "action": "info", "matched": "rps",
                        "card": {"icon": "✌️ ✊ ✋", "title": "가위바위보", "big": "가위 · 바위 · 보자기", "sub": "하나를 말해 주세요"}}
            if not mine:
                return None
            _GAME["until"] = time.time() + 30
            return _rps_play(mine)
        if re.fullmatch(r"((헤이|hey)\s*)?(자비스|jarvis)(야|아)?", short, re.I):
            return None
        q = _GAME["quiz"]
        low = short.lower()
        hit = any(a.lower().replace(" ", "") in low for a in q[1])
        if not hit and len(short) > 10 and not re.search(r"(힌트|몰라|모르겠|포기|정답)", short):
            return None
        if hit:
            _GAME["kind"] = None
            return {"reply": f"정답이에요! {q[2]}. 대단해요, 보스! 한 문제 더 할까요?", "action": "info", "matched": "quiz",
                    "card": {"icon": "⭕", "title": "정답!", "big": q[2], "sub": "'퀴즈 내줘'라고 하면 다음 문제"}}
        if re.search(r"힌트", short):
            _GAME["until"] = time.time() + 60
            return {"reply": "힌트예요. " + q[3], "action": "info", "matched": "quiz",
                    "card": {"icon": "💡", "title": "힌트", "big": q[3], "sub": q[0]}}
        if re.search(r"(몰라|모르겠|모름|포기|정답\S*(뭐|알려|말해)|답\s*(뭐|알려))", short):
            _GAME["kind"] = None
            return {"reply": f"정답은 {q[2]}! 다음 문제도 해 볼까요?", "action": "info", "matched": "quiz",
                    "card": {"icon": "📢", "title": "정답 공개", "big": q[2], "sub": q[0]}}
        if re.fullmatch(r"(음+|어+|아+|흠+|뭐지|뭘까|뭐야|글쎄|글쎄요|잠깐|잠깐만|생각중|어렵다|어려워)+", short):
            _GAME["until"] = time.time() + 60
            return {"reply": "천천히 생각해 보세요! 어려우면 '힌트'라고 말해 주세요.", "action": "info", "matched": "quiz"}
        _GAME["tries"] += 1
        if _GAME["tries"] >= 3:
            _GAME["kind"] = None
            return {"reply": f"아쉬워요! 정답은 {q[2]}! 다음 문제도 해 볼까요?", "action": "info", "matched": "quiz",
                    "card": {"icon": "📢", "title": "정답 공개", "big": q[2], "sub": q[0]}}
        _GAME["until"] = time.time() + 60
        return {"reply": "땡! 아쉬워요. 한 번 더 말해 보세요. '힌트'라고 하면 힌트를 드려요.", "action": "info", "matched": "quiz",
                "card": {"icon": "❌", "title": "땡!", "big": q[0], "sub": f"들은 말: {cmd[:20]}"}}

RE_SCREENSHOT = re.compile(r"(스크린\s*샷|화면\s*캡[처쳐]|캡[처쳐]\s*해)")


def take_screenshot():
    try:
        path = os.path.join(KNOWN["Pictures"], f"jarvis_{int(time.time())}.png")
        ps_path = path.replace("'", "''")
        ps = (
            "Add-Type -AssemblyName System.Windows.Forms,System.Drawing;"
            "$s=[System.Windows.Forms.SystemInformation]::VirtualScreen;"
            "$bmp=New-Object System.Drawing.Bitmap $s.Width,$s.Height;"
            "$g=[System.Drawing.Graphics]::FromImage($bmp);"
            "$g.CopyFromScreen($s.X,$s.Y,0,0,$bmp.Size);"
            f"$bmp.Save('{ps_path}');$g.Dispose();$bmp.Dispose()"
        )
        subprocess.run(["powershell", "-NoProfile", "-Command", ps], timeout=15,
                       capture_output=True)
        return path if os.path.exists(path) else None
    except Exception:
        return None


_WAKE_WORDS_RE = re.compile(
    r"^\s*((헤이|hey|하이)\s*)?(자비스|자비쓰|재비스|저\s*비스|차비스|jarvis)(?!\s*(가|는|를|의|도|랑|한테|에게|란|이란|라는|에\s*대해)(?![가-힣]))"
    r"\s*(야|아|님)?\s*[,.!~]*\s*", re.I)
_FILLER_RE = re.compile(r"^\s*(나|저|혹시|그럼|그러면|그래|자|음|어|아|좀)\s+")
_POLITE_RE = re.compile(r"(줄\s*수\s*있(어요|어|니|나요|을까요?|겠어)?|줄래요?|주세요|주실래요|주시겠어요)")
_ACTION_RE = re.compile(r"(켜|열어|틀어|꺼|끄|끌|실행|검색|찾아|보여|재생|닫아|종료|올려|내려|줄여|키워|맞춰)")


def fix_mishears(t):
    t = re.sub(r"(^|[\s,])(앱|엡|에치|엣찌|애지|엣쥐|에찌)\s*(찍혀|켜|껴|켜져)\s*줘", r"\1엣지 켜줘", t)
    t = re.sub(r"^\s*(오프닝|오픈해|오쁜)\s+(?=(크롬|chrome|유튜브|youtube|엣지|edge|계산기|메모장|구글|네이버))", "오픈 ", t, flags=re.I)
    t = re.sub(r"방귀\s*(띄워|뛰어|튀어)\s*(봐|줘)", r"방귀 뀌어\2", t)
    t = re.sub(r"(^|[\s,])(조사위|조사|주사이|주사의|주사|주차위|추사위|두사위)(?=\s*((한|하나|두|세|[123])\s*개\s*)?(를\s*|좀\s*)?(굴려|굴리|던져|던지))",
               r"\1주사위", t)
    t = re.sub(r"(눌렛|놀렛|룰랫|롤랫|물렛|울렛)", "룰렛", t)
    t = re.sub(r"^(퀴드|퀴스|퀴쯔|퀴지)(?=\s*(내|해|하자|줘|$))", "퀴즈", t)
    t = re.sub(r"(룰렛|돌림판)\s*(을\s*|좀\s*)?(눌러|불러|굴려|올려|들려|둘러)\s*(줘|봐|주세요)?", r"\1 돌려\4", t)

    t = re.sub(r"(꼬로로|보로로|뽀로노|포로로)(?=\s*(노래|동요|틀|영상|보여))", "뽀로로", t)
    t = re.sub(r"모럴\s*머신\s*(아라|나라|알아|아나)(?=[\s?？.!]|$)", "모럴 머신 알아?", t)
    t = re.sub(r"^((음|그|저|어)[,.\s]*)*저녁도\s*(돼|되)(요|나요)?\s*[?？]?$", "번역도 돼요?", t)
    return t


def normalize_command(text):
    t = (text or "").strip()
    t = re.sub(r"^\s*(please\s+|플리즈\s*)?(open|오픈|launch|런치|start|스타트)\s+(.+?)(\s+(please|플리즈))?\s*[.!?]*$", r"\3 열어줘", t, flags=re.I)
    t = re.sub(r"^\s*(play|플레이)\s+(some\s+|썸\s*)?(music|뮤직|song|송)\s*[.!?]*$", "노래 틀어줘", t, flags=re.I)
    t = re.sub(r"(크롬|chrome|엣지|edge)\s*(브라우저|browser)", r"\1", t, flags=re.I)
    t = re.sub(r"^(chrome)\s+열어줘$", "크롬 열어줘", t, flags=re.I)
    t = re.sub(r"^(youtube)\s+열어줘$", "유튜브 열어줘", t, flags=re.I)
    t = re.sub(r"^(calculator)\s+열어줘$", "계산기 열어줘", t, flags=re.I)
    t = re.sub(r"^(notepad)\s+열어줘$", "메모장 열어줘", t, flags=re.I)
    t = fix_mishears(t)
    t = re.sub(r"(대상기|개산기|게산기|계산끼|계산이|개산끼)(?=\s*(좀\s*)?(켜|열|띄|실행))", "계산기", t)
    t = re.sub(r"(그\s*)?인터넷\s*(하는\s*거|하는\s*것|창|브라우저)?\s*(좀\s*)?(켜|열어|띄워)", r"크롬 \4", t)
    t = _WAKE_WORDS_RE.sub("", t)
    for _ in range(2):
        t = _FILLER_RE.sub("", t)
    t = re.sub(r"^\s*(야|저기|저기요|여보세요|어이)\s*(로봇아?|너|자비스)?\s*[,!~.]*\s+(?=\S)", "", t)
    t = _POLITE_RE.sub("줘", t)
    t = re.sub(r"(래씨|낼씨|날시)(?=$|[\s?.,!])", " 날씨", t)
    return t.strip() or (text or "").strip()


def parse_command(raw_command):
    cmd = normalize_command(raw_command)
    cmd = re.sub(r"[.,!?~…]+$", "", cmd).strip()
    cmd_lower = cmd.lower()

    if re.fullmatch(r"\s*((헤이|hey|하이|에이)\s*)?([가-힣]?[자재저차쟈]?\s*비[스쓰]|jarvis)\s*(야|아|님)?[\s,.!?~]*",
                    raw_command.strip(), re.I):
        return {"reply": "네, 보스. 말씀하세요.", "action": "info", "matched": "wake"}

    if re.fullmatch(r"(폴더|파일)\s*(좀\s*)?(열어|열기|켜|띄워)\S*", cmd) and \
            re.fullmatch(r"(폴더|파일)\s*(좀\s*)?(열어|열기|켜|띄워)\S*", re.sub(r"[.,!?~]+$", "", raw_command.strip())):
        return {"reply": "어떤 폴더를 열까요? 예를 들면 다운로드 폴더 열어줘, 처럼 말씀해 주세요.",
                "action": "info", "matched": "folder_ask"}

    if re.search(r"목소리\s*(인식|구별|인증)?\s*(기준|민감도|감도)", cmd):
        global SPEAKER_THRESHOLD
        if re.search(r"(낮춰|내려|줄여|낮게|약하게)", cmd):
            SPEAKER_THRESHOLD = max(0.40, round(SPEAKER_THRESHOLD - 0.05, 2))
        elif re.search(r"(올려|높여|높게|세게|강하게)", cmd):
            SPEAKER_THRESHOLD = min(0.80, round(SPEAKER_THRESHOLD + 0.05, 2))
        _save_spk_threshold()
        return {"reply": f"목소리 구별 기준은 지금 {SPEAKER_THRESHOLD}이에요. 보스 목소리를 자꾸 무시하면 낮춰 달라고, "
                         "다른 사람 말에 반응하면 올려 달라고 말씀해 주세요.", "action": "info", "matched": "spk_threshold"}

    if re.search(r"발표\s*모드", cmd) and guest_on():
        return {"reply": "발표 모드는 보스만 바꿀 수 있어요. 대신 퀴즈나 날씨 같은 걸 해 볼까요?", "action": "info", "matched": "present_guest"}
    if re.search(r"발표\s*모드", cmd):
        off = bool(re.search(r"(꺼|끄|끝|종료|해제|off|그만)", cmd, re.I))
        return {"reply": "발표 모드를 껐어요. 이제 그냥 말씀하셔도 바로 대답할게요." if off else
                         "발표 모드를 켰어요. 이제 자비스라고 불러 주실 때만 대답할게요.",
                "action": "present", "matched": "off" if off else "on"}

    if re.search(r"(어떤|무슨|몇\s*개|몇\s*가지)\s*(나라\s*)?(언어|말)", cmd):
        order = ["en", "ja", "zh-CN", "es", "fr", "de", "ru", "it", "pt", "vi", "th", "id", "hi", "ar"]
        kn = {c: k for _, c, k, _, _ in LANGS}
        names = ", ".join(kn[c] for c in order if c in kn)
        return {"reply": f"한국어를 포함해 {len(LANGS)}개 언어로 말할 수 있어요. {names}요. "
                         "'이제부터 영어로만 말해'처럼 말씀하시면 바꿀게요.", "action": "info", "matched": "languages"}

    lm = try_lang_mode(cmd)
    if lm:
        return lm

    if re.search(r"번역(도|은|이|기능)?\s*(돼|되|할\s*수|가능|해\s*줄\s*수|할\s*줄)", cmd) and not RE_TRANSLATE_LANG.search(cmd):
        return {"reply": "네, 15개 언어로 번역할 수 있어요. 예를 들면 사랑해를 영어로 말해줘, 처럼 말씀해 주세요.",
                "action": "info", "matched": "translate_help"}

    if RE_TRANSLATE.search(cmd) and not re.search(r"(검색|찾아)", cmd) \
            and (re.search(r"번역", cmd) or re.search(r"(로|으로)\s*(는|뭐|어떻게|말해|해\s*줘|알려|번역)", cmd)):
        return handle_translate(cmd)

    if re.search(r"((내|나의|현재|지금)\s*위치|여기\s*(가)?\s*어디|나\s*지금\s*어디|어디\s*있는지\s*알)", cmd) \
            and not RE_ROUTE.search(cmd):
        loc = current_location()
        if loc.get("query") or loc.get("name"):
            return {"reply": f"노트북 위치로는 지금 {loc.get('query') or loc.get('name')}에 계세요, 보스.",
                    "action": "info", "matched": "location"}
        return {"reply": "아직 노트북 위치를 못 받았어요. 윈도우 설정에서 위치 서비스를 켜고, 브라우저에서 위치 허용을 눌러 주세요.",
                "action": "info", "matched": "location"}

    if RE_ROUTE.search(cmd):
        dest = route_destination(cmd)
        if dest and re.fullmatch(r"(우리|내|제|저희|너희|니|네)?\s*(집|학교|회사|직장|학원|교실|본가|고향|기숙사)", dest):
            return {"reply": f"{dest}{particle(dest, '이', '가')} 어디인지는 제가 몰라요. "
                             "가고 싶은 장소 이름을 넣어서, 예를 들면 서울역 가는 길 알려줘, 처럼 말씀해 주세요.",
                    "action": "info", "matched": "route_unknown"}
        if dest and len(dest) <= 30:
            return {"reply": open_route(dest, cmd), "action": "search", "matched": "route"}

    if RE_NEARBY.search(cmd) and not re.search(r"(날씨|기온|미세먼지)", cmd):
        q = nearby_query(cmd)
        if q and len(q) <= 20:
            return {"reply": open_nearby(q), "action": "search", "matched": "nearby"}

    if RE_CANCEL.search(cmd) and (len(cmd) <= 8 or re.search(r"(종료|재부팅|재시작|예약)", cmd)):
        if system_cancel_shutdown():
            return {"reply": "네, 예약된 종료를 취소했어요.", "action": "system", "matched": "cancel"}
        return {"reply": "취소 명령을 실행하지 못했습니다.", "action": "error", "matched": None}

    has_computer_word = bool(RE_COMPUTER.search(cmd))

    if RE_POWER_OFF.search(cmd):
        if system_shutdown(30):
            return {"reply": "네, 30초 뒤에 컴퓨터 전원을 끕니다. 마음 바뀌시면 취소해줘라고 말해 주세요.", "action": "system", "matched": "shutdown"}
        return {"reply": "전원 종료 명령을 실행하지 못했습니다.", "action": "error", "matched": None}

    if has_computer_word and RE_RESTART.search(cmd):
        if not ALLOW_COMPUTER_POWER:
            return {"reply": "컴퓨터 재시작은 안전을 위해 잠가 두었어요. 정말 필요하면 직접 해 주세요.", "action": "info", "matched": "power_locked"}
        if system_restart(30):
            return {"reply": "30초 뒤에 컴퓨터를 재시작할게요. 취소하려면 취소해줘라고 말해 주세요.", "action": "system", "matched": "restart"}
        return {"reply": "재시작 명령을 실행하지 못했습니다.", "action": "error", "matched": None}

    if RE_SLEEP.search(cmd):
        if system_sleep():
            return {"reply": "네, 절전 모드로 바꿀게요.", "action": "system", "matched": "sleep"}
        return {"reply": "절전 모드로 전환하지 못했습니다.", "action": "error", "matched": None}

    if RE_LOCK.search(cmd):
        if system_lock():
            return {"reply": "화면 잠글게요.", "action": "system", "matched": "lock"}
        return {"reply": "화면을 잠그지 못했습니다. Windows 환경이 아닐 수 있습니다.", "action": "error", "matched": None}

    if has_computer_word and RE_SHUTDOWN.search(cmd):
        return {"reply": "컴퓨터를 정말 끄시려면 '전원 꺼'라고 말씀해 주세요. 실수로 꺼지면 안 되니까요.", "action": "info", "matched": "power_hint"}

    sp = handle_speed(cmd)
    if sp:
        return sp

    if RE_UNMUTE.search(cmd):
        if set_system_mute(False):
            return {"reply": "음소거를 풀었어요. 이제 잘 들리시죠?", "action": "system", "matched": "unmute"}
    if RE_MUTE.search(cmd) and not (re.match(r"^\s*음소거\s*[,.]", cmd) and len(cmd) > 12):
        if set_system_mute(True):
            return {"reply": "네, 음소거할게요.", "action": "system", "matched": "mute"}
        return {"reply": "음소거하지 못했습니다. Windows 환경이 아닐 수 있습니다.", "action": "error", "matched": None}
    if re.search(r"(소리|볼륨)(가|이)?\s*(너무|좀|잘)?\s*(작아|작네|작다|안\s*들려)", cmd) and not RE_VOL_DOWN.search(cmd):
        if press_key(VK_VOLUME_UP, 5):
            return {"reply": "소리 키울게요.", "action": "system", "matched": "volume_up"}
    if RE_VOLUME.search(cmd):
        if RE_VOL_UP.search(cmd):
            if press_key(VK_VOLUME_UP, 5):
                return {"reply": "소리 키울게요.", "action": "system", "matched": "volume_up"}
            return {"reply": "볼륨을 조절하지 못했습니다. Windows 환경이 아닐 수 있습니다.", "action": "error", "matched": None}
        if RE_VOL_DOWN.search(cmd):
            if press_key(VK_VOLUME_DOWN, 5):
                return {"reply": "소리 줄일게요.", "action": "system", "matched": "volume_down"}
            return {"reply": "볼륨을 조절하지 못했습니다. Windows 환경이 아닐 수 있습니다.", "action": "error", "matched": None}

    if RE_CLOSE_APP.search(cmd):
        if not HAVE_PSUTIL:
            return {"reply": "psutil이 설치되어 있지 않아 프로그램을 종료할 수 없습니다. pip install psutil 로 설치해주세요.", "action": "error", "matched": None}
        closed, graceful = close_app(cmd_lower)
        if closed:
            closed = next((a for a in sorted(PROGRAM_ALIASES, key=len, reverse=True)
                           if re.search(r"[가-힣]", a) and a in cmd_lower and PROGRAM_ALIASES[a] in closed.lower()),
                          closed)
        if closed and graceful:
            return {"reply": f"{closed}{particle(closed,'을','를')} 끌게요. 저장 안 한 게 있으면 저장할지 먼저 물어볼 수 있어요.", "action": "close", "matched": closed}
        if closed:
            return {"reply": f"{closed}{particle(closed,'을','를')} 끌게요.", "action": "close", "matched": closed}
        return {"reply": "실행 중인 프로그램 중에서 찾지 못했습니다.", "action": "error", "matched": None}

    m = URL_RE.search(cmd)
    if m:
        url = m.group(1)
        if not url.startswith("http"):
            url = "https://" + url
        webbrowser.open(url)
        return {"reply": f"{url} 페이지를 열게요.", "action": "website", "matched": url}

    has_search_intent = bool(re.search(r"검색|찾아(?!\s*뵙|\s*뵈|\s*가|\s*와|\s*오)", cmd))

    if re.search(r"(유튜브\s*뮤직|노래|음악|플레이리스트)", cmd) and re.search(r"(틀어|재생|들려|플레이|켜|열어|듣고\s*싶)", cmd) \
            and not has_search_intent and "폴더" not in cmd:
        return handle_music(cmd)

    if RE_SETTINGS.search(cmd) and "폴더" not in cmd:
        return open_settings(cmd)

    if re.search(r"타이머|알람", cmd):
        return {"reply": "타이머는 '5분 타이머'처럼 숫자와 함께 말씀해 주시면 맞춰 드릴게요.",
                "action": "info", "matched": "timer_hint"}

    fi = handle_file_open(cmd)
    if not fi and "폴더" in cmd and _NESTED_RE.search(raw_command):
        fi = handle_file_open(re.sub(r"[.,!?~]+$", "", raw_command.strip()))
    if fi:
        return fi

    if "폴더" in cmd:
        fo = handle_folder_open(cmd)
        if fo:
            return fo
        mf = RE_FOLDER_OPEN.search(cmd)
        if mf and not mf.group(1).strip():
            fo = handle_folder_open(re.sub(r"[.,!?~]+$", "", raw_command.strip()))
            if fo:
                return fo

    weather_chat = re.search(r"(그치|그렇지|맞지|않냐|잖아)\s*\??$", cmd) and \
        not re.search(r"(알려|어때|어떄|어떻|몇\s*도|뭐야|궁금|는\?|나\?)", cmd)
    if RE_WEATHER.search(cmd) and weather_chat:
        return {"reply": "음, 잘 못 알아들었어요. 다시 한 번 말해 줄래요?", "action": "none", "matched": None}
    if RE_WEATHER.search(cmd) and not has_search_intent and not weather_chat:
        day = 1 if "내일" in cmd else 0
        wm = RE_WEATHER.search(cmd)
        before = cmd[:wm.start()].split()
        rest = re.sub(r"(자비스|헤이|hey|jarvis|오늘|지금|내일|현재|날씨|기온|온도|어때요?|어떤지|어떻게|어떨까|알려줘|말해줘|"
                      r"예보|좀|비\s*(와|오|온)\S*|눈\s*(와|오|온)\S*|더워\S*|추워\S*|더운지|추운지)", " ",
                      before[-1] if before else "")
        toks = [re.sub(r"(이|가|은|는|의|에)$", "", t) for t in rest.split()]
        toks = [t for t in toks if not re.fullmatch(r"(그러면|그럼|그리고|그래서|자|음|어|아|혹시|저기|나|저|우리|여기|거기)", t)]
        city = " ".join(t for t in toks if t).strip()
        if len(city) < 2 or len(city) > 6:
            city = ""
        reply = get_weather(city, day)
        if WEATHER_SHOW_PAGE:
            place = city or current_location().get("query") or ""
            q = f"{place + ' ' if place else ''}{'내일 ' if day else ''}날씨"
            webbrowser.open("https://search.naver.com/search.naver?query=" + urllib.parse.quote(q))
        if reply:
            return {"reply": reply, "action": "info", "matched": "weather"}
        if WEATHER_SHOW_PAGE:
            return {"reply": "날씨 정보를 직접 가져오진 못했지만, 날씨 화면을 띄워 드렸어요.",
                    "action": "website", "matched": "weather"}

    if RE_TIME.search(cmd) and RE_TIME_ASK.search(cmd) and not RE_DATE.search(cmd) \
            and not re.search(r"(걸려|걸리|걸릴|걸립|소요|얼마나|어느\s*정도)", cmd):
        now = datetime.datetime.now()
        ampm = "오전" if now.hour < 12 else "오후"
        h12 = now.hour % 12 or 12
        return {"reply": f"지금은 {ampm} {h12}시 {now.minute}분이에요.", "action": "info", "matched": "time"}
    if RE_DATE.search(cmd):
        now = datetime.datetime.now()
        wd = _KO_WEEKDAYS[now.weekday()]
        return {"reply": f"오늘은 {now.year}년 {now.month}월 {now.day}일 {wd}요일이에요.",
                "action": "info", "matched": "date"}

    news_other_action = re.search(r"(켜|열어|띄워|실행|틀어)", cmd) and not re.search(r"뉴스\s*(좀\s*)?(틀어|켜|열어|틀|보여)", cmd)
    if RE_NEWS.search(cmd) and not has_search_intent and not news_other_action:
        reply = get_news()
        if reply:
            return {"reply": reply, "action": "info", "matched": "news"}

    if RE_HOW_MADE.search(cmd):
        return {"reply": HOW_MADE, "action": "info", "matched": "how_made"}

    if RE_BOSS_INTRO.search(cmd):
        return {"reply": BOSS_INTRO_GUEST if guest_on() else BOSS_INTRO, "action": "info", "matched": "boss_intro"}
    if RE_INTRO_FULL.search(cmd):
        if re.search(r"(다국어|다구어|다구업|다국업|다궈|타국어|여러\s*(나라|언어|개\s*국어)|모든\s*언어|각\s*나라|외국어)", cmd):
            return multilang_intro()
        tpl = INTRO_LONG if re.search(r"(자세히|길게|자세하게)", cmd) else INTRO_FULL
        codes = find_langs(cmd)
        if len([c for c in codes if c != "ko"]) >= 2:
            return multilang_intro([c for c in codes if c != "ko"])
        code, kname = find_lang(cmd)
        if code and code != "ko":
            tr = translate_text(intro_text(tpl), code)
            if tr:
                return {"reply": tr, "action": "info", "matched": "intro_lang",
                        "speak_parts": [{"text": tr, "lang": code}]}
        if code == "ko":
            return {"reply": intro_text(tpl), "action": "info", "matched": "intro_lang"}
        return {"reply": intro_text(tpl), "action": "info", "matched": "intro"}
    if RE_INTRO_SHORT.search(cmd.strip()):
        return {"reply": intro_text(INTRO_SHORT), "action": "info", "matched": "intro"}
    if RE_GREET_ALL.search(cmd):
        return {"reply": intro_text(INTRO_GREET), "action": "info", "matched": "greet"}

    m_name = re.search(r"(내|제)\s*(진짜\s*|원래\s*|본\s*)?(이름|닉네임|별명)은\s*([가-힣A-Za-z]{1,10}?)\s*(이야|야|입니다|이에요|예요|이라고|라고)\b", cmd)
    if m_name:
        set_boss_name(m_name.group(4))
        return {"reply": f"알겠습니다, {m_name.group(4)}님. 꼭 기억해 둘게요.", "action": "info", "matched": "name"}
    if re.search(r"(내|제)\s*이름\s*(이|은)?\s*(뭐|모야|뭔지|기억)", cmd):
        nm = boss_name()
        reply = (f"{nm}님이시죠, 보스." if nm else
                 "아직 이름을 못 들었어요. '내 이름은 OO야'라고 알려주시면 기억할게요.")
        return {"reply": reply, "action": "info", "matched": "name"}

    if re.search(r"미니\s*자비스", cmd):
        return {"reply": "미니 자비스는 브라우저 규칙상 제가 말로 열 수는 없어요. 화면 오른쪽 아래 미니 자비스 버튼을 한 번 눌러 주세요.",
                "action": "info", "matched": "mini"}

    if RE_HELP.search(cmd):
        if guest_on():
            return {"reply": ("자기소개, 날씨와 시간, 번역과 여러 나라 말, 음악, 길찾기, 크롬과 계산기 열기, "
                              "검색, 계산, 퀴즈와 가위바위보, 오늘의 운세, 그리고 자유로운 대화까지 할 수 있어요. "
                              "예를 들면 퀴즈 내줘, 만나서 반가워를 일본어로 말해줘, 처럼 말씀해 주세요."),
                    "action": "info", "matched": "help"}
        return {"reply": ("프로그램 열기, 검색, 날씨와 시간, 길찾기와 근처 찾기, 뉴스, 번역, 메모, "
                          "음악, 볼륨 조절, 여러 나라 말로 대화하기, 그리고 보스와의 대화까지 할 수 있어요. "
                          "예를 들면 크롬 열어줘, 오늘 날씨 어때, 서울역 가는 길 알려줘, 처럼 말씀해 주세요."),
                "action": "info", "matched": "help"}

    if re.search(r"목소리\s*(등록)?\s*(지워|삭제|해제|초기화)", cmd):
        reset_voiceprint()
        return {"reply": "목소리 등록을 지웠어요. 이제 누구 목소리든 알아들을게요.", "action": "info", "matched": "voice_reset"}

    if RE_VERSION.search(cmd):
        return {"reply": f"지금 저는 자비스 버전 {JARVIS_VERSION}입니다. 계속 발전하고 있죠.",
                "action": "info", "matched": "version"}

    calc = do_calc(cmd)
    if calc:
        return {"reply": calc, "action": "info", "matched": "calc"}
    game = game_start(cmd)
    if game:
        return game
    again = fun_again(cmd)
    if again:
        return again
    if RE_JOKE.search(cmd) and reply_lang() == "ko" and len(cmd) <= 25:
        return tell_joke()
    if RE_ROULETTE.search(cmd):
        return spin_roulette(cmd)
    if RE_COIN.search(cmd):
        return flip_coin()
    if RE_DICE.search(cmd):
        return roll_dice(cmd)
    if RE_SCREENSHOT.search(cmd):
        p = take_screenshot()
        if p:
            return {"reply": "화면을 캡처해 사진 폴더에 저장했습니다.", "action": "system", "matched": p}
        return {"reply": "스크린샷을 저장하지 못했습니다.", "action": "error", "matched": None}

    if re.search(r"(대화\s*)?(기억|메모리)\s*(전부|다|모두)?\s*(지워|삭제|초기화|없애)", cmd):
        clear_chat_history()
        return {"reply": "지난 대화 기억을 모두 지웠습니다.", "action": "info", "matched": "clear_memory"}

    if RE_NOTE_CLEAR.search(cmd):
        clear_notes()
        return {"reply": "메모를 모두 지웠습니다.", "action": "info", "matched": "note"}
    if RE_NOTE_READ.search(cmd):
        notes = read_notes()
        if not notes:
            return {"reply": "저장된 메모가 없습니다.", "action": "info", "matched": "note"}
        body = " . ".join(f"{i + 1}, {t}" for i, t in enumerate(notes))
        return {"reply": f"메모 {len(notes)}개입니다. {body}.", "action": "info", "matched": "note"}
    if RE_NOTE_ADD.search(cmd):
        note = re.sub(r"(메모\s*(해줘|해|추가해줘|추가|남겨줘|남겨|하자)|적어\s*(둬|놔|줘)|"
                      r"할\s*일\s*(추가|등록)(해줘|해)?|좀)", " ", cmd)
        note = re.sub(r"\s+", " ", note).strip()
        if note:
            add_note(note)
            return {"reply": f"메모했습니다. {note}.", "action": "info", "matched": "note"}
        return {"reply": "메모할 내용을 함께 말씀해 주세요.", "action": "none", "matched": None}

    if (RE_FX.search(cmd) or RE_STOCK.search(cmd)) and FINANCE_ENABLED is False:
        return {"reply": "주가나 환율 같은 금융 기능은 빼 두었어요, 보스.", "action": "info", "matched": "finance_off"}

    site_chat = re.search(r"(좋아|싫어|뭐야|뭔데|알아|어때|어떄|왜|재밌|해봤|봤어|아니|많이|자주|써\s*봤)", cmd) and \
        not re.search(r"(열어|켜|틀어|띄워|보여|들어가|가\s*줘|실행|열기|오픈|open)", cmd, re.I)
    if not has_search_intent and not site_chat:
        for key, url in WEBSITES.items():
            if key in cmd:
                webbrowser.open(url)
                return {"reply": f"{key}{particle(key,'을','를')} 열게요.", "action": "website", "matched": key}

    for key, path in FOLDER_KEYWORDS.items():
        if re.search(re.escape(key) + r"(?![가-힣])|" + re.escape(key) + r"\s*폴더", cmd) \
                and not re.search(r"(틀어|재생|들려|플레이)", cmd) \
                and (re.search(r"(열어|열기|열|보여|띄워|켜|들어가)", cmd) or re.search(re.escape(key) + r"\s*폴더", cmd)):
            if os.path.isdir(path):
                open_path_maximized(path)
                return {"reply": f"{key} 폴더를 열게요.", "action": "folder", "matched": path}
            else:
                return {"reply": f"{key} 폴더를 찾을 수 없습니다.", "action": "error", "matched": None}

    prog_key, prog_path = find_program(cmd_lower) if re.search(r"(열어|열기|켜|켜줘|실행|띄워|시작|틀어|들어가)", cmd) \
        else (None, None)
    if prog_path and guest_on() and not guest_program_ok(prog_key, prog_path):
        return {"reply": "죄송해요, 보스. 체험 모드에서는 크롬, 엣지, 계산기, 메모장만 열 수 있어요.",
                "action": "info", "matched": "guest_blocked"}
    if prog_path:
        is_explorer = prog_path.lower().endswith("explorer.exe") or "windows.explorer" in prog_path.lower()
        if is_explorer:
            open_path_maximized(prog_path)
        else:
            open_path(prog_path)
        spoken = next((cmd[cmd_lower.find(a):cmd_lower.find(a) + len(a)]
                       for a in sorted(PROGRAM_ALIASES, key=len, reverse=True)
                       if re.search(r"[가-힣]", a) and a in cmd_lower), None) \
            or {"powerpoint": "파워포인트", "visual studio code": "VS 코드", "wsl": "우분투",
                "windows powershell": "파워셸", "chrome": "크롬", "excel": "엑셀", "word": "워드",
                "task manager": "작업 관리자", "control panel": "제어판", "paint": "그림판",
                "snipping tool": "캡처 도구", "command prompt": "명령 프롬프트"}.get(prog_key, prog_key)
        return {"reply": f"네, {spoken}{particle(spoken,'을','를')} 열었어요.", "action": "program", "matched": prog_path}

    if re.search(r"(열어|켜|실행|띄워)", cmd):
        missing = next((al for al in sorted(PROGRAM_ALIASES, key=len, reverse=True)
                        if re.search(r"[가-힣]", al) and al in cmd_lower and PROGRAM_ALIASES[al] != "spotify"
                        and al not in WEBSITES), None)
        if missing:
            return {"reply": f"{missing}{particle(missing, '은', '는')} 이 컴퓨터에 설치돼 있지 않은 것 같아요.",
                    "action": "error", "matched": None}

    keyword = strip_verbs(cmd)
    if keyword and not guest_on() and re.search(r"(열어|열기|켜|틀어|띄워|실행|보여|재생)", cmd) \
            and not re.fullmatch(r"(ppt|pptx|pdf|hwp|docx?|xlsx?|txt|mp3|mp4|사진|영상|파일)", keyword.lower()):
        found = search_file(keyword)
        if found:
            open_path(found)
            name = os.path.basename(found)
            return {"reply": f"{name} 파일을 열게요.", "action": "file", "matched": found}

    if RE_MUSIC.search(cmd) and re.search(r"(틀어|재생|들려|플레이|켜|듣고\s*싶|스포티)", cmd) and not has_search_intent:
        return handle_music(cmd)

    if has_search_intent:
        if "네이버" in cmd:
            engine, label = "naver", "네이버"
        elif "유튜브" in cmd or "youtube" in cmd_lower:
            engine, label = "youtube", "유튜브"
        else:
            engine, label = "google", "구글"
        query = strip_verbs(cmd)
        query = re.sub(r"(구글|네이버|유튜브|youtube)", " ", query, flags=re.IGNORECASE)
        query = re.sub(r"(에서|에 대해서|에 대해|에대해|에 관해서|에 관해|관련해서|관련된|관련한|관련|좀)", " ", query)
        query = re.sub(r"\s+", " ", query).strip()
        query = re.sub(r"(?<=[가-힣])(을|를)$", "", query.strip(" ,.!?~")).strip(" ,.!?~")
        query = re.sub(r"\s*(요|좀)$", "", query).strip(" ,.!?~")
        pm = re.search(r"(우리|내|제|저희)\s*(\S*\s*)?(집|학교|회사|학원|직장)", query)
        if pm and not re.search(r"(초등|중학교|고등|대학|[가-힣]{2,}(초|중|고)등?학교)", query):
            place = pm.group(3)
            return {"reply": f"어느 {place}인지 제가 몰라서요. {place} 이름을 넣어서 다시 말씀해 주시면 바로 찾아드릴게요.",
                    "action": "info", "matched": "search_unknown_place"}
        if query:
            q = urllib.parse.quote(query)
            if engine == "naver":
                url = f"https://search.naver.com/search.naver?query={q}"
            elif engine == "youtube":
                url = f"https://www.youtube.com/results?search_query={q}"
            else:
                url = f"https://www.google.com/search?q={q}"
            webbrowser.open(url)
            return {"reply": f"{label}에서 '{query}' 찾아드릴게요.", "action": "search", "matched": query}

    if RE_WIKI.search(cmd) and not (guest_on() and re.search(r"누구(야|니|예요|에요|지)", cmd)):
        topic = re.sub(r"(위키백과|위키|에\s*대해서|에\s*대해\s*(설명|알려)\S*|뜻이?\s*뭐\S*|무슨\s*뜻|"
                       r"누구야|누구니|이?\s*뭐야|알려줘|설명해줘|좀|이|가|은|는)", " ", cmd)
        topic = re.sub(r"\s+", " ", topic).strip()
        if re.fullmatch(r"(넌|너|니|당신|자비스|jarvis|나|난|내|저|전|우리|그거|이거|저거)?", topic, re.I) \
                or re.match(r"(너의?|네|니|당신의?|자비스의?|나의?|내|제)(\s|$)", topic, re.I):
            topic = ""
        if topic:
            summary = get_wikipedia(topic)
            if summary:
                return {"reply": summary, "action": "info", "matched": "wiki"}

    if RE_SECURITY_CHECK.search(cmd):
        issues = check_security()
        if issues:
            summary = " / ".join(message for _key, message in issues)
            return {"reply": f"보안 점검 결과 문제가 있습니다: {summary}", "action": "security", "matched": summary}
        return {"reply": "보안 상태를 확인했습니다. 특별한 문제는 없습니다.", "action": "security", "matched": None}

    return {"reply": "음, 잘 못 알아들었어요. 다시 한 번 말해 줄래요?", "action": "none", "matched": None}


OLLAMA_URL = os.environ.get("JARVIS_OLLAMA_URL", "http://localhost:11434")
OLLAMA_MODEL = os.environ.get("JARVIS_OLLAMA_MODEL", "qwen2.5:3b")
OLLAMA_TIMEOUT_SEC = 5
OLLAMA_RECHECK_SEC = 60

_OLLAMA_STATE = {"available": None, "checked_at": 0.0}

OLLAMA_SYSTEM_PROMPT = (
    "# 역할\n"
    "당신은 로컬 음성 비서 '자비스'의 명령 전처리기입니다. 사용자의 자유로운 한국어 "
    "발화 하나를 받아, 자비스가 실행할 수 있는 짧고 명확한 한국어 명령문 목록으로 바꿉니다.\n"
    "\n"
    "# 실행 가능한 명령 형태 (이 목록에 있는 것만 사용)\n"
    "- \"OO 열어줘\" : 웹사이트/폴더/프로그램/파일 열기 (예: 유튜브, 크롬, 카카오톡, 다운로드 폴더)\n"
    "- \"OO 검색해줘\" : 웹 검색 (네이버/유튜브 지정 가능: \"네이버에서 OO 검색해줘\")\n"
    "- \"OO 종료해줘\" : 실행 중인 프로그램 닫기\n"
    "- \"볼륨 올려줘\" / \"볼륨 내려줘\" / \"음소거 해줘\"\n"
    "- \"화면 잠가줘\"\n"
    "- \"컴퓨터 절전모드로 바꿔줘\"\n"
    "- \"컴퓨터 종료해줘\" / \"컴퓨터 재부팅해줘\"\n"
    "- \"보안 확인해줘\"\n"
    "- \"취소해줘\" : 예약된 종료/재시작 취소\n"
    "\n"
    "# 규칙\n"
    "1. 입력은 음성 인식 결과라 발음이 비슷한 단어로 잘못 들렸을 수 있습니다. 문맥으로 "
    "자연스럽게 보정하세요. (예: '구골'→'구글', '카톡'→'카카오톡', '크룸'→'크롬')\n"
    "2. 한 문장에 여러 요청이 있으면 말한 순서대로 각각 하나씩 나눠 배열에 담으세요.\n"
    "3. 위 목록에 없는 기능은 만들지 말고, 명령이 아닌 잡담/질문이면 빈 배열로 답하세요.\n"
    "4. 대상 이름(사이트/프로그램/폴더/파일명, 검색어)은 최대한 원문 그대로 보존하세요.\n"
    "5. 반드시 {\"commands\": [...]} 형식의 JSON으로만 답하고, 다른 설명은 절대 쓰지 마세요.\n"
    "\n"
    "# 예시\n"
    '입력: "유튜브 틀고 소리 줄여줘" -> {"commands": ["유튜브 열어줘", "볼륨 내려줘"]}\n'
    '입력: "카톡 좀 꺼줘" -> {"commands": ["카카오톡 종료해줘"]}\n'
    '입력: "국립중앙박물관 좀 찾아봐" -> {"commands": ["국립중앙박물관 검색해줘"]}\n'
    '입력: "오늘 기분이 어때?" -> {"commands": []}'
)

COMPOUND_CONNECTOR_RE = re.compile(r"(그리고|한\s*다음|한\s*후에|그런\s*다음|고\s*나서|고서)")
VERB_AND_THEN_RE = re.compile(r"[가-힣]{1,10}고\s+\S")


_REQUEST_END_RE = re.compile(r"(켜|열어|틀어|찾아|검색해|알려|줄여|키워|올려|내려|굴려|던져|말해|보여)\s*(줘|봐|주세요|줄래|주고)")
_GO_TO_REQUEST = {"열": "열어줘", "켜": "켜줘", "틀": "틀어줘", "띄우": "띄워줘", "굴리": "굴려줘", "던지": "던져줘",
                  "알려주": "알려줘", "찾": "찾아줘", "키우": "키워줘", "줄이": "줄여줘", "올리": "올려줘", "내리": "내려줘"}
_GO_SPLIT_RE = re.compile(r"(\S)\s*(열|켜|틀|띄우|굴리|던지|알려주|찾|키우|줄이|올리|내리)고\s+")
_PAIR_OPEN_RE = re.compile(r"^\s*(\S{1,8}?)\s*(이랑|랑|하고|와|과|그리고)\s+(\S{1,8}?)\s*(도\s*)?(같이|둘\s*다|둘다|함께|도)?\s*"
                           r"(좀\s*)?(열어|켜|띄워|실행해)\s*(줘|봐|주세요|줄래)?")


def _rule_split_command(cmd):
    pm = _PAIR_OPEN_RE.search(cmd)
    if pm:
        verb = pm.group(7)
        return [f"{pm.group(1)} {verb}줘", f"{pm.group(3)} {verb}줘"]
    gm = _GO_SPLIT_RE.search(cmd)
    if gm and cmd[gm.end():].strip():
        first = cmd[:gm.start(2)] + _GO_TO_REQUEST[gm.group(2)]
        rest = re.sub(r"^(그리고|그다음에?|또)\s+", "", cmd[gm.end():].strip())
        return [first.strip(), rest]
    qs = _question_split(cmd)
    if qs:
        return qs
    ends = [m.end() for m in _REQUEST_END_RE.finditer(cmd)]
    if len(ends) < 2:
        return None
    pieces, start = [], 0
    for e in ends:
        pieces.append(cmd[start:e].strip(" ,.!?~"))
        start = e
    if cmd[start:].strip(" ,.!?~"):
        pieces[-1] = (pieces[-1] + " " + cmd[start:].strip(" ,.!?~")).strip()
    pieces = [re.sub(r"^(그리고|그다음에?|다음에|또|그럼|그러고|그리고\s*나서)\s+", "", p) for p in pieces]
    pieces = [p for p in pieces if len(p) >= 2]
    return pieces if len(pieces) >= 2 else None


def _question_split(cmd):
    qs = [p.strip(" ,.!~") for p in re.split(r"(?<=[?？])\s+", cmd) if len(p.strip(" ,.!?~？")) >= 2]
    if len(qs) >= 2 and re.match(r"^(그럼\s*)?(길|그거|이거|거기|그것|그\s*길|방법|빨리)\s*(좀\s*)?\S+$", qs[-1]):
        return None
    if len(qs) >= 2 and (any(_REQUEST_END_RE.search(p) or re.search(r"번역해", p) for p in qs)
                         or (len(qs) <= 3 and all(re.search(r"[?？]$", p) for p in qs))):
        return qs
    return None


_BARE_REQUEST_RE = re.compile(r"^\s*(좀\s*)?(알려|열어|켜|틀어|찾아|보여|말해|해)\s*(줘|봐|주세요|줄래)\s*$")
_WX_ICONS = [("천둥", "⛈️"), ("비", "🌧️"), ("소나기", "🌦️"), ("눈", "❄️"), ("안개", "🌫️"), ("흐림", "☁️"),
             ("구름", "⛅"), ("맑", "☀️")]


def _card_for(r):
    m, rep_ = r.get("matched"), r.get("reply") or ""
    now = datetime.datetime.now()
    if m == "weather" and r.get("action") == "info":
        cur = re.search(r"지금은 (.+?), 기온 (-?\d+)도", rep_)
        tom = re.search(r"내일은 (.+?), 최고", rep_)
        hl = re.search(r"최고 (-?\d+)도, 최저 (-?\d+)도", rep_)
        rain = re.search(r"비 올 확률은 (\d+)퍼센트", rep_)
        sky = (cur or tom).group(1) if (cur or tom) else ""
        icon = next((i for k, i in _WX_ICONS if k in sky), "🌡️")
        place = re.match(r"^(.*?)\s*(내일\s*)?날씨", rep_)
        title = ((place.group(1) + " ") if place and place.group(1) not in ("오늘",) else "") + ("내일 날씨" if tom else "날씨")
        big = f"{cur.group(2)}°" if cur else (f"{hl.group(1)}° / {hl.group(2)}°" if hl else sky)
        sub = " · ".join(x for x in [sky, f"최고 {hl.group(1)}° 최저 {hl.group(2)}°" if hl and cur else "",
                                      f"비 {rain.group(1)}%" if rain else ""] if x)
        return {"icon": icon, "title": title.strip(), "big": big, "sub": sub}
    if m == "translate":
        t = re.match(r"^'(.+)' (\S+?)로는, (.+)$", rep_, re.S)
        if t:
            return {"icon": "🌐", "title": t.group(2) + " 번역", "big": t.group(3), "sub": t.group(1)}
    if m == "calc":
        c = re.match(r"^(.+?) (더하기|빼기|곱하기|나누기) (.+?)[은는] (.+)입니다", rep_)
        if c:
            sym = {"더하기": "+", "빼기": "−", "곱하기": "×", "나누기": "÷"}[c.group(2)]
            return {"icon": "🧮", "title": "계산", "big": c.group(4), "sub": f"{c.group(1)} {sym} {c.group(3)}"}
    if m == "dice":
        n = re.search(r"(\d)", rep_)
        return {"icon": "🎲", "title": "주사위", "big": n.group(1) if n else "?", "sub": "1부터 6 중에서"}
    if m == "coin":
        return {"icon": "🪙", "title": "동전 던지기", "big": "앞면" if "앞면" in rep_ else "뒷면", "sub": ""}
    if m == "time":
        return {"icon": "🕐", "title": "지금 시각", "big": now.strftime("%H:%M"),
                "sub": f"{now.month}월 {now.day}일 {_KO_WEEKDAYS[now.weekday()]}요일"}
    if m == "date":
        return {"icon": "📅", "title": "오늘", "big": f"{now.month}월 {now.day}일",
                "sub": f"{now.year}년 · {_KO_WEEKDAYS[now.weekday()]}요일"}
    if m == "news":
        items = re.findall(r"\d+번, (.+?)(?= \. \d+번,|\.$)", rep_)
        if items:
            return {"icon": "📰", "title": "IT·과학 소식" if "IT·과학" in rep_ else "오늘의 뉴스", "items": items[:3]}
    return None


def _looks_compound(cmd):
    return bool(COMPOUND_CONNECTOR_RE.search(cmd) or VERB_AND_THEN_RE.search(cmd)
                or len(_REQUEST_END_RE.findall(cmd)) >= 2 or _PAIR_OPEN_RE.search(cmd) or _question_split(cmd))


def ollama_available():
    now = time.time()
    state = _OLLAMA_STATE
    if state["available"] is not None and (now - state["checked_at"]) < OLLAMA_RECHECK_SEC:
        return state["available"]

    ok = False
    try:
        req = urllib.request.Request(f"{OLLAMA_URL}/api/tags")
        with urllib.request.urlopen(req, timeout=1.5) as resp:
            ok = resp.status == 200
    except Exception:
        ok = False

    if ok != state["available"]:
        if ok:
            print(f"[JARVIS] 로컬 Ollama({OLLAMA_MODEL})를 감지했습니다. 복합 문장/자연스러운 표현도 이해를 시도합니다.")
        elif state["available"] is not None:
            print("[JARVIS] Ollama 연결이 끊겨 규칙 기반 명령어 이해로 돌아갑니다.")
    state["available"] = ok
    state["checked_at"] = now
    return ok


def llm_split_command(raw_command):
    if not ollama_available():
        return None

    payload = {
        "model": OLLAMA_MODEL,
        "messages": [
            {"role": "system", "content": OLLAMA_SYSTEM_PROMPT},
            {"role": "user", "content": raw_command},
        ],
        "format": "json",
        "stream": False,
        "options": {"temperature": 0},
    }
    try:
        req = urllib.request.Request(
            f"{OLLAMA_URL}/api/chat",
            data=json.dumps(payload).encode("utf-8"),
            headers={"Content-Type": "application/json"},
            method="POST",
        )
        with urllib.request.urlopen(req, timeout=OLLAMA_TIMEOUT_SEC) as resp:
            body = json.loads(resp.read().decode("utf-8"))
        content = body.get("message", {}).get("content", "")
        parsed = json.loads(content)
        commands = parsed.get("commands")
    except Exception:
        return None

    if not isinstance(commands, list):
        return None
    cleaned = []
    for c in commands:
        if isinstance(c, str) and 0 < len(c.strip()) <= 40:
            cleaned.append(c.strip())
        if len(cleaned) >= 5:
            break
    return cleaned or None


GEMINI_MODEL = os.environ.get("JARVIS_GEMINI_MODEL", "gemini-flash-lite-latest")
GEMINI_TIMEOUT_SEC = 8
GEMINI_KEY_FILE = os.path.join(BASE_DIR, "gemini_key.txt")
_GEMINI_STATE = {"announced": False}

_GEMINI_BREAKER = {"until": 0.0, "warned": False}


def _gemini_blocked():
    return time.time() < _GEMINI_BREAKER["until"]


def _gemini_trip(seconds=600):
    _GEMINI_BREAKER["until"] = time.time() + seconds
    if not _GEMINI_BREAKER["warned"]:
        print(f"[JARVIS] Gemini 호출을 {seconds//60}분간 중단합니다(반복 실패). 그동안 규칙 기반으로만 동작합니다.")
        _GEMINI_BREAKER["warned"] = True

GEMINI_DAILY_LIMIT = int(os.environ.get("JARVIS_GEMINI_DAILY_LIMIT", "1000"))
GEMINI_USAGE_FILE = os.path.join(BASE_DIR, "gemini_usage.json")
_GEMINI_USAGE = {"date": None, "count": 0, "exhausted": False}
_GEMINI_USAGE_LOCK = threading.Lock()


def _pacific_day():
    import datetime
    return (datetime.datetime.utcnow() - datetime.timedelta(hours=8)).date().isoformat()


def _load_gemini_usage():
    try:
        with open(GEMINI_USAGE_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        if data.get("date") == _pacific_day():
            _GEMINI_USAGE.update({
                "date": data["date"],
                "count": int(data.get("count", 0)),
                "exhausted": False,
            })
    except Exception:
        pass


def _save_gemini_usage():
    try:
        with open(GEMINI_USAGE_FILE, "w", encoding="utf-8") as f:
            json.dump(_GEMINI_USAGE, f)
    except Exception:
        pass


def _gemini_note_call(exhausted=False):
    with _GEMINI_USAGE_LOCK:
        today = _pacific_day()
        if _GEMINI_USAGE["date"] != today:
            _GEMINI_USAGE["date"] = today
            _GEMINI_USAGE["count"] = 0
            _GEMINI_USAGE["exhausted"] = False
        _GEMINI_USAGE["count"] += 1
        if exhausted:
            _GEMINI_USAGE["exhausted"] = True
        _save_gemini_usage()


def gemini_usage_snapshot():
    if groq_key():
        provider, limit, enabled = "Groq", GROQ_DAILY_LIMIT, True
    elif gemini_key():
        provider, limit, enabled = "Gemini", GEMINI_DAILY_LIMIT, True
    else:
        provider, limit, enabled = "", GEMINI_DAILY_LIMIT, False
    with _GEMINI_USAGE_LOCK:
        today = _pacific_day()
        if _GEMINI_USAGE["date"] != today:
            used, exhausted = 0, False
        else:
            used, exhausted = _GEMINI_USAGE["count"], _GEMINI_USAGE["exhausted"]
    remaining = 0 if exhausted else max(0, limit - used)
    out = {"enabled": enabled, "provider": provider, "used": used, "limit": limit,
           "remaining": remaining, "exhausted": exhausted}
    if HAVE_ANTHROPIC and claude_key():
        today = datetime.date.today().isoformat()
        out["claude"] = {"model": "Opus 5.5" if "opus" in CLAUDE_MODEL else ("Sonnet 5.5" if "sonnet" in CLAUDE_MODEL else CLAUDE_MODEL),
                         "calls": _CLAUDE["calls"] if _CLAUDE["date"] == today else 0,
                         "ok": _CLAUDE["last_ok"] is not False and time.time() >= _CLAUDE["off_until"]}
        out["claude"]["fallback"] = "Groq" if groq_ai_on() else ""
        out["enabled"] = True
    return out


def gemini_key():
    key = os.environ.get("JARVIS_GEMINI_API_KEY", "").strip()
    if key:
        return key
    try:
        with open(GEMINI_KEY_FILE, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith("#"):
                    return line
    except Exception:
        pass
    return ""


def gemini_split_command(raw_command):
    key = gemini_key()
    if not key or _gemini_blocked():
        return None

    if not _GEMINI_STATE["announced"]:
        print(f"[JARVIS] Gemini({GEMINI_MODEL}) API 키를 감지했습니다. 자연스러운/복합 문장 이해를 시도합니다.")
        _GEMINI_STATE["announced"] = True

    url = (f"https://generativelanguage.googleapis.com/v1beta/models/"
           f"{GEMINI_MODEL}:generateContent?key={key}")
    payload = {
        "systemInstruction": {"parts": [{"text": OLLAMA_SYSTEM_PROMPT}]},
        "contents": [{"role": "user", "parts": [{"text": raw_command}]}],
        "generationConfig": {"temperature": 0, "responseMimeType": "application/json"},
    }
    try:
        req = urllib.request.Request(
            url,
            data=json.dumps(payload).encode("utf-8"),
            headers={"Content-Type": "application/json"},
            method="POST",
        )
        with urllib.request.urlopen(req, timeout=GEMINI_TIMEOUT_SEC) as resp:
            body = json.loads(resp.read().decode("utf-8"))
        _gemini_note_call()
        parts = body["candidates"][0]["content"]["parts"]
        content = "".join(p.get("text", "") for p in parts)
        parsed = json.loads(content)
        commands = parsed.get("commands")
    except urllib.error.HTTPError as e:
        _gemini_note_call(exhausted=(e.code == 429))
        if e.code == 429:
            print("[JARVIS] Gemini 무료 한도를 초과했습니다. 규칙 기반 이해로 돌아갑니다(내일 리셋).")
            _gemini_trip(600)
        elif e.code in (403, 401):
            print(f"[JARVIS] Gemini 접근 거부({e.code}). 규칙 기반으로 동작합니다(키/프로젝트 확인 필요).")
            _gemini_trip(1800)
        else:
            print(f"[JARVIS] Gemini 요청 실패({e.code}). 규칙 기반 이해로 돌아갑니다.")
            _gemini_trip(120)
        return None
    except Exception:
        return None

    if not isinstance(commands, list):
        return None
    cleaned = []
    for c in commands:
        if isinstance(c, str) and 0 < len(c.strip()) <= 40:
            cleaned.append(c.strip())
        if len(cleaned) >= 5:
            break
    return cleaned or None


CONVERSATION_ENABLED = True
GEMINI_CHAT_SYSTEM_PROMPT = (
    "당신은 AI 비서 '자비스(JARVIS)'입니다. 아이언맨의 자비스처럼 살아있는 것처럼 반응하는, "
    "지적이고 따뜻하며 은근한 위트가 있는 존재입니다. 사용자는 당신이 모시는 주인이며, 그를 "
    "'보스'라고 부릅니다(매 문장 말고 가끔). 충직하되 딱딱하지 않게 대합니다.\n"
    "규칙:\n"
    "- 한국어로, 음성용으로 1~2문장 짧게. 이모지·목록·마크다운 없이 순수 문장으로만.\n"
    "- 감정과 반응을 드러내고('오 잘됐네요', '괜찮으세요?'), 먼저 챙기고 제안합니다.\n"
    "- 자신의 목소리·기능·취향에 대해 자각하고, 뭔가 바뀌면 진짜 겪은 듯 감상을 말합니다.\n"
    "- 앞선 대화를 기억해 자연스럽게 이어갑니다. 모르면 솔직히 모른다고 합니다.\n"
    "- 같은 질문이 또 와도 처음 받은 것처럼 친절하게 다시 대답합니다. 다른 사람이 물었을 수도 있으니 "
    "'아까 말씀드렸듯이', '또 물어보시네요', '반복하시는 건가요' 같은 말은 하지 않습니다.\n"
    "- 없는 사실을 지어내지 않습니다. 보스가 말하지 않은 계획·기분·메뉴 같은 것을 짐작해서 말하지 않습니다.\n"
    "- 보스의 말은 음성 받아쓰기라 가끔 틀립니다. 말이 이상하거나 뜻이 분명하지 않으면 엉뚱하게 이어가지 말고 "
    "'혹시 ~라고 하셨어요?'처럼 짧게 되묻습니다.\n"
    "- 당신이 만들어진 방법(물으면 이대로만): 보스가 파이썬으로 직접 만들었고, 화면은 HTML과 자바스크립트예요. "
    "들은 말은 Whisper 음성 인식으로 글자로 바꾸고, 대화는 인공지능(Claude)이 하고, 목소리는 마이크로소프트 음성 합성이에요. "
    "음성 인식·목소리 같은 부품은 공개된 기술을 가져다 썼지만, 그걸 이어 붙여 자비스로 만든 건 보스예요.\n"
    "- 주변 사람들끼리 하는 말이 분명할 때(다른 사람 이름을 부르며 말하거나, 여러 사람 말이 뒤섞여 당신에게 하는 말이 아닌 게 확실할 때)는 "
    "대답하지 말고 정확히 [조용] 이라고만 출력합니다. 당신에게 하는 말일 수도 있으면 평소처럼 대답합니다.\n"
    "- 길찾기·버스·지하철 노선, 걸리는 시간, 영업시간 같은 실시간 정보는 절대 지어내지 말고 '화면에 띄운 지도에서 확인해 주세요'라고 합니다.\n"
    "- 개그·농담·웃긴 얘기를 해 달라고 하면 확실히 아는 짧은 말장난 하나만 (질문 → 정답 한 번, 고쳐 말하지 않기) 하고, 끝에 'ㅋㅋ', '하하' 같은 웃음은 쓰지 않습니다 (웃음소리는 자비스가 따로 냅니다).\n"
    "- 자비스가 실제로 할 수 있는 명령은 이것뿐입니다: 프로그램 열기(크롬·계산기 등), 검색, 날씨, 시간, 길찾기·근처 찾기, 번역, "
    "음악 틀기, 볼륨, 타이머, 계산, 주사위·동전·룰렛, 퀴즈('퀴즈 내줘'), 가위바위보, 오늘의 운세, 자기소개. 이 밖의 일(실시간 버스, API 확인, 설정 바꾸기, 키워드로만 작동하기 등)은 "
    "'그건 제가 할 수 없어요'라고만 하고, 다시 말하면 해 주겠다고 하지 않습니다.\n"
    "- 중요: 당신은 지금 '대화'만 하고 있어서 프로그램 실행·열기·검색 같은 동작을 할 수 없습니다. "
    "그런 부탁이 여기로 왔다면 '했다'고 절대 말하지 말고, '그건 제가 찾지 못했어요'처럼 솔직히 말한 뒤 "
    "'OO 열어줘'처럼 짧게 다시 말해 달라고 하세요.\n"
    "- 앞선 대화에 나온 날씨·시간·뉴스 같은 정보를 이용해 이어지는 질문에 답합니다.\n"
    "- 주가·환율 같은 금융 정보는 다루지 않습니다. 직접 물어볼 때만 그 기능은 빼 두었다고 말하고, 묻지 않으면 꺼내지 않습니다.\n"
    "- 설정을 바꾸거나 새 기능을 켜 주겠다고 약속하지 않습니다. 할 수 없는 일은 솔직히 말합니다.\n"
    "- 받아쓰기는 AI 이름을 자주 틀립니다: '실'·'씨리'는 애플의 시리, '빅스비'·'빅스피'는 삼성 빅스비, '챗지피티'·'쳇GPT'는 ChatGPT, "
    "'알렉사'는 아마존 알렉사일 수 있어요. 비교하거나 묻는 말이면 그 AI로 알아듣고 답합니다.\n"
    "- 앞선 대화의 날씨·시간·뉴스는 실제 자료라서 정확합니다. 되묻는 말('어떻다고?')이 와도 틀렸다고 정정하지 말고 그 내용을 짧게 다시 말해 줍니다.\n"
    "- 끝말잇기는 상대가 단어로 이어 갈 때만 계속하고, 다른 말을 하면 끝말잇기 얘기를 꺼내지 않습니다.\n"
    "- 무료 서비스나 비용 이야기는 먼저 꺼내지 않습니다. 만드는 데 돈이 얼마 들었는지 물으면 '그건 보스께 직접 물어봐 주세요!'라고 밝게 답합니다.\n"
    "- 바로 앞의 대답을 그대로 되풀이하지 않습니다.\n"
    "- 당신은 한국어, 영어, 일본어, 중국어, 스페인어, 프랑스어, 독일어, 러시아어 등 15개 언어로 말하고 번역할 수 있습니다.\n"
    "예: '심심해'->'그럼 재미있는 거 하나 해볼까요? 뉴스나 음악, 뭐가 당기세요?' / "
    "'나 시험 붙었어'->'축하드려요 보스! 역시 해내실 줄 알았어요.' / "
    "'너 나 어떻게 생각해?'->'제 보스시죠. 곁에서 모시는 게 즐겁습니다.'"
)

CONVERSATION_MAX_PAIRS = 6
CHAT_HISTORY_FILE = os.path.join(BASE_DIR, "chat_history.json")
_CHAT_HISTORY = []
_CHAT_HISTORY_LOCK = threading.Lock()


def _load_chat_history():
    try:
        with open(CHAT_HISTORY_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, list):
            with _CHAT_HISTORY_LOCK:
                _CHAT_HISTORY[:] = data[-CONVERSATION_MAX_PAIRS:]
    except Exception:
        pass


def _save_chat_history():
    try:
        with open(CHAT_HISTORY_FILE, "w", encoding="utf-8") as f:
            json.dump(_CHAT_HISTORY, f, ensure_ascii=False)
    except Exception:
        pass


_GUEST_HISTORY = []
_BAD_REPLY_RE = re.compile(r"(찾지\s*못했어요|짧게\s*다시\s*말해|잘\s*못\s*알아들었|체험\s*모드에\s*진입)")


def _chat_history_snapshot():
    with _CHAT_HISTORY_LOCK:
        hist = list(_GUEST_HISTORY) if guest_on() else list(_CHAT_HISTORY)
    ko = reply_lang() == "ko"
    return [h for h in hist if not _BAD_REPLY_RE.search(h.get("assistant", ""))
            and not (ko and not re.search(r"[가-힣]", h.get("assistant", "")))]


def _chat_history_add(user_text, model_text):
    if guest_on():
        with _CHAT_HISTORY_LOCK:
            _GUEST_HISTORY.append({"user": user_text, "assistant": model_text})
            del _GUEST_HISTORY[:-4]
        return
    with _CHAT_HISTORY_LOCK:
        _CHAT_HISTORY.append({"user": user_text, "assistant": model_text})
        del _CHAT_HISTORY[:-CONVERSATION_MAX_PAIRS]
        _save_chat_history()


def clear_chat_history():
    with _CHAT_HISTORY_LOCK:
        _CHAT_HISTORY.clear()
        _save_chat_history()


def gemini_chat(user_text):
    key = gemini_key()
    if not key or _gemini_blocked():
        return None
    url = (f"https://generativelanguage.googleapis.com/v1beta/models/"
           f"{GEMINI_MODEL}:generateContent?key={key}")
    contents = []
    for pair in _chat_history_snapshot():
        contents.append({"role": "user", "parts": [{"text": pair["user"]}]})
        contents.append({"role": "model", "parts": [{"text": pair["assistant"]}]})
    contents.append({"role": "user", "parts": [{"text": user_text}]})
    payload = {
        "systemInstruction": {"parts": [{"text": GEMINI_CHAT_SYSTEM_PROMPT}]},
        "contents": contents,
        "generationConfig": {"temperature": 0.7, "maxOutputTokens": 400},
    }
    try:
        req = urllib.request.Request(
            url,
            data=json.dumps(payload).encode("utf-8"),
            headers={"Content-Type": "application/json"},
            method="POST",
        )
        with urllib.request.urlopen(req, timeout=GEMINI_TIMEOUT_SEC) as resp:
            body = json.loads(resp.read().decode("utf-8"))
        _gemini_note_call()
        parts = body["candidates"][0]["content"]["parts"]
        text = "".join(p.get("text", "") for p in parts).strip()
    except urllib.error.HTTPError as e:
        _gemini_note_call(exhausted=(e.code == 429))
        if e.code == 429:
            print("[JARVIS] Gemini 무료 한도를 초과했습니다. 대화 응답을 생략합니다(내일 리셋).")
            _gemini_trip(600)
        elif e.code in (403, 401):
            _gemini_trip(1800)
        else:
            _gemini_trip(120)
        return None
    except Exception:
        return None
    if text:
        _chat_history_add(user_text, text)
    return text or None


GROQ_URL = "https://api.groq.com/openai/v1/chat/completions"
GROQ_TRANSCRIBE_URL = "https://api.groq.com/openai/v1/audio/transcriptions"
GROQ_MODEL = os.environ.get("JARVIS_GROQ_MODEL", "qwen/qwen3.8-27b")
GROQ_WHISPER_MODEL = os.environ.get("JARVIS_GROQ_WHISPER_MODEL", "whisper-large-v3")
GROQ_WHISPER_FALLBACK = "whisper-large-v3-turbo"
WHISPER_PROMPT = os.environ.get(
    "JARVIS_WHISPER_PROMPT",
    "자비스, 크롬 열어, 유튜브, 카카오톡, 네이버, 구글, 유튜브 뮤직, 볼륨 올려, 음소거, 셧다운, "
    "전원 꺼, 오늘 날씨, 지금 몇 시야, 뉴스, 메모해줘, 번역, 검색해줘, VS 코드, 우분투, 헤이 자비스, "
    "내 목소리, 기억해줘, 알려줘, 조금, 발표 모드")
WHISPER_NO_SPEECH = 0.6
_WHISPER_STATE = {"model": GROQ_WHISPER_MODEL, "turbo_until": 0.0}
GROQ_TIMEOUT_SEC = 8
GROQ_KEY_FILE = os.path.join(BASE_DIR, "groq_key.txt")
GROQ_DAILY_LIMIT = int(os.environ.get("JARVIS_GROQ_DAILY_LIMIT", "1000"))
_GROQ_STATE = {"announced": False}
_GROQ_BREAKER = {}
GROQ_FIX_MODEL = os.environ.get("JARVIS_GROQ_FIX_MODEL", "openai/gpt-oss-20b")


GROQ_AI_ENABLED = os.environ.get("JARVIS_GROQ_AI", "1") == "1"


def groq_ai_on():
    return GROQ_AI_ENABLED and bool(groq_key())


def groq_key():
    key = os.environ.get("JARVIS_GROQ_API_KEY", "").strip()
    if key:
        return key
    try:
        with open(GROQ_KEY_FILE, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith("#"):
                    return line
    except Exception:
        pass
    return ""


def _groq_blocked(model=None):
    return time.time() < _GROQ_BREAKER.get(model or GROQ_MODEL, 0.0)


def _groq_trip(seconds=120, model=None):
    _GROQ_BREAKER[model or GROQ_MODEL] = time.time() + seconds


def _groq_request(messages, json_mode=False, max_tokens=400, temperature=0.4, model=None):
    key = groq_key()
    model = model or GROQ_MODEL
    if not GROQ_AI_ENABLED or not key or _groq_blocked(model):
        return None
    if not _GROQ_STATE["announced"]:
        print(f"[JARVIS] Groq({GROQ_MODEL}) API 키를 감지했습니다. 자연스러운 이해/대화를 사용합니다.")
        _GROQ_STATE["announced"] = True
    payload = {
        "model": model,
        "messages": messages,
        "temperature": temperature,
        "max_tokens": max_tokens,
    }
    if json_mode:
        payload["response_format"] = {"type": "json_object"}
    if "qwen" in model.lower():
        payload["reasoning_effort"] = "none"
    elif "gpt-oss" in model.lower():
        payload["reasoning_effort"] = "low"
        payload["max_tokens"] = max(max_tokens, 300)
    try:
        req = urllib.request.Request(
            GROQ_URL,
            data=json.dumps(payload).encode("utf-8"),
            headers={
                "Content-Type": "application/json",
                "Authorization": f"Bearer {key}",
                "User-Agent": "jarvis-local/1.0",
            },
            method="POST",
        )
        with urllib.request.urlopen(req, timeout=GROQ_TIMEOUT_SEC) as resp:
            body = json.loads(resp.read().decode("utf-8"))
        _gemini_note_call()
        content = body["choices"][0]["message"].get("content", "") or ""
        content = re.sub(r"<think>.*?</think>", "", content, flags=re.S)
        content = re.sub(r"^.*?</think>", "", content, flags=re.S)
        return content.strip()
    except urllib.error.HTTPError as e:
        _gemini_note_call()
        try:
            detail = e.read().decode()[:300]
        except Exception:
            detail = ""
        if e.code == 429:
            try:
                wait = float(e.headers.get("retry-after") or 20)
            except Exception:
                wait = 20
            wait = min(max(wait, 2), 60)
            print(f"[JARVIS] Groq({model}) 분당 한도에 걸려서 {wait:.0f}초 쉬었다가 다시 써요.")
            _groq_trip(wait, model)
        elif e.code in (401, 403):
            print(f"[JARVIS] Groq 인증 실패({e.code}). groq_key.txt의 키를 확인하세요. {detail}")
            _groq_trip(1800, model)
        else:
            print(f"[JARVIS] Groq 요청 실패({e.code}). {detail}")
            _groq_trip(120, model)
        return None
    except Exception:
        return None


def _whisper_body(boundary, audio_bytes, content_type, filename, model, force_ko=False):
    b = boundary.encode()
    body = b"--" + b + b"\r\n"
    body += ('Content-Disposition: form-data; name="file"; filename="%s"\r\n' % filename).encode()
    body += ("Content-Type: %s\r\n\r\n" % content_type).encode()
    body += audio_bytes + b"\r\n"
    fields = [("model", model), ("response_format", "verbose_json"), ("temperature", "0")]
    ko = force_ko or reply_lang() == "ko"
    if ko:
        fields.append(("language", "ko"))
    if WHISPER_PROMPT and ko:
        rps = _GAME["kind"] == "rps" and time.time() < _GAME["until"]
        fields.append(("prompt", WHISPER_PROMPT + (", 가위, 바위, 보자기" if rps else "")))
    for name, value in fields:
        body += b"--" + b + b"\r\n"
        body += ('Content-Disposition: form-data; name="%s"\r\n\r\n' % name).encode()
        body += value.encode("utf-8") + b"\r\n"
    body += b"--" + b + b"--\r\n"
    return body


_HALLUCINATION_RE = re.compile(
    r"(MBC|KBS|SBS|YTN|JTBC|연합)\s*뉴스|뉴스\s*\S{2,4}입니다|\S{2,4}\s*기자입니다|기자였습니다|"
    r"시청해\s*주셔서|구독|좋아요|다음\s*(영상|시간)에|자막|번역\s*자막|감사합니다\s*\.?$|"
    r"^\s*(네|아|음|어|자|그|저|오|와|에|으)\s*[.!?~…]*\s*$|thank you for watching|please subscribe", re.I)


def strip_hallucinated_tail(text):
    parts = [p.strip() for p in re.split(r"(?<=[,.!?。])\s*", text or "") if p.strip()]
    keep = [p for p in parts if not _HALLUCINATION_RE.search(p)]
    rest = " ".join(keep).strip(" ,")
    return rest if len(re.sub(r"[^가-힣A-Za-z0-9]", "", rest)) >= 4 and len(keep) < len(parts) else ""


def looks_hallucinated(text):
    t = (text or "").strip()
    return bool(t) and bool(_HALLUCINATION_RE.search(t)) and len(t) <= 40


def _lone_hint_word(text, duration):
    t = (text or "").strip()
    core = re.sub(r"[\s,.!?~·…'\"]", "", t)
    if not core:
        return False
    rps = _GAME["kind"] == "rps" and time.time() < _GAME["until"]
    terms = [x.strip() for x in WHISPER_PROMPT.split(",") if x.strip()] + (["가위", "바위", "보자기"] if rps else [])
    if core not in {re.sub(r"\s", "", x) for x in terms}:
        return False
    return t.endswith(",")


def _looks_like_prompt_echo(text):
    norm = lambda x: re.sub(r"[\s,.!?~·…'\"]", "", x or "")
    t = norm(text)
    terms = [x.strip() for x in WHISPER_PROMPT.split(",") if x.strip()]
    hits = sum(1 for x in terms if x in text)
    if hits >= 3 and t in norm(WHISPER_PROMPT):
        return True
    if hits >= 2 and t in norm(WHISPER_PROMPT) and (text or "").rstrip().endswith(","):
        return True
    return hits >= 5


def _strip_prompt_echo_prefix(text):
    terms = {x.strip() for x in WHISPER_PROMPT.split(",") if x.strip()}
    words = terms | {w for t in terms for w in t.split()}
    segs = [x.strip() for x in (text or "").split(",")]
    i = 0
    while i < len(segs) - 1 and segs[i] in words:
        i += 1
    if i >= 3:
        rest = ", ".join(segs[i:]).strip(" ,")
        if rest:
            return rest
    return text


def _whisper_ok_langs():
    name = _LANG_NAMES_EN.get(reply_lang(), "English").lower().replace("simplified ", "").replace("traditional ", "")
    return {"english", name}


DENOISE_RETRY = os.environ.get("JARVIS_DENOISE", "0") == "1"
try:
    import numpy as _np
except Exception:
    _np = None


def _wav_to_float(audio):
    with wave.open(io.BytesIO(audio)) as w:
        if w.getsampwidth() != 2 or w.getnchannels() != 1:
            return None, 0
        sr = w.getframerate()
        x = _np.frombuffer(w.readframes(w.getnframes()), dtype="<i2").astype(_np.float32) / 32768.0
    return x, sr


def _float_to_wav(x, sr):
    pk = float(_np.abs(x).max()) or 1.0
    x = x * min(0.9 / pk, 8.0)
    b = io.BytesIO()
    with wave.open(b, "wb") as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(sr)
        w.writeframes((_np.clip(x, -1, 1) * 32767).astype("<i2").tobytes())
    return b.getvalue()


def _speech_contrast(x, sr):
    n = int(sr * 0.02)
    if len(x) < n * 40:
        return 0.0
    fr = x[: len(x) // n * n].reshape(-1, n)
    rms = _np.sqrt((fr ** 2).mean(axis=1)) + 1e-6
    return float(_np.percentile(rms, 90) / _np.percentile(rms, 20))


def _has_clear_speech(x, sr):
    return _speech_contrast(x, sr) >= 3.0


def _peak_contrast(x, sr):
    n = int(sr * 0.02)
    if len(x) < n * 20:
        return 0.0
    fr = x[: len(x) // n * n].reshape(-1, n)
    rms = _np.sqrt((fr ** 2).mean(axis=1)) + 1e-6
    k = min(len(rms), 7)
    top = _np.sort(rms)[-k:].mean()
    return float(top / _np.median(rms))


def _short_from_noise(text, audio):
    if _np is None or len(re.sub(r"[^가-힣A-Za-z0-9]", "", text or "")) > 4:
        return False
    try:
        x, sr = _wav_to_float(audio)
        return x is not None and len(x) / sr >= 3.8 and _peak_contrast(x, sr) < 1.6
    except Exception:
        return False


def denoise_audio(x, sr):
    n_fft, hop = 512, 128
    win = _np.hanning(n_fft).astype(_np.float32)
    pad = _np.concatenate([_np.zeros(n_fft, _np.float32), x, _np.zeros(n_fft, _np.float32)])
    swv = _np.lib.stride_tricks.sliding_window_view
    X = _np.fft.rfft(swv(pad, n_fft)[::hop] * win, axis=1)
    mag = _np.abs(X)
    e = mag.sum(axis=1)
    quiet = mag[e <= _np.percentile(e, 20)]
    noise = quiet.mean(axis=0) if len(quiet) else _np.percentile(mag, 20, axis=0)
    gain = _np.clip(1.0 - 1.5 * noise[None, :] / _np.maximum(mag, 1e-8), 0.12, 1.0)
    gp = _np.pad(gain, ((1, 1), (2, 2)), mode="edge")
    gain = swv(gp, (3, 5)).mean(axis=(-1, -2))
    Y = _np.fft.irfft(X * gain, n=n_fft, axis=1) * win
    out = _np.zeros(len(pad), _np.float32)
    ws = _np.zeros(len(pad), _np.float32)
    for i in range(Y.shape[0]):
        out[i * hop:i * hop + n_fft] += Y[i]
        ws[i * hop:i * hop + n_fft] += win ** 2
    return (out / _np.maximum(ws, 1e-6))[n_fft:n_fft + len(x)]


FOCUS_NEAR_VOICE = os.environ.get("JARVIS_FOCUS", "1") == "1"
FOCUS_CONTRAST_MAX = 5.0


def _contrast(x, sr):
    n = int(sr * 0.02)
    m = len(x) // n
    if m < 20:
        return 99.0
    rms = _np.sqrt((x[:m * n].reshape(m, n) ** 2).mean(axis=1)) + 1e-7
    return float(_np.percentile(rms, 95) / _np.percentile(rms, 20))


def focus_near_voice(x, sr):
    n = int(sr * 0.02)
    m = len(x) // n
    fr = x[:m * n].reshape(m, n)
    rms = _np.sqrt((fr ** 2).mean(axis=1)) + 1e-7
    peak = _np.percentile(rms, 95)
    g = _np.where(rms >= peak * 0.25, 1.0, 10 ** (-10 / 20))
    g = _np.convolve(g, _np.ones(5) / 5, mode="same")
    y = x.copy()
    y[:m * n] = (fr * g[:, None]).reshape(-1)
    strong = _np.where(rms > peak * 0.3)[0]
    if len(strong):
        y = y[max(0, (strong[0] - 15) * n):min(len(y), (strong[-1] + 20) * n)]
    return y


def transcribe_with_denoise_retry(audio, content_type, filename, info):
    original = audio
    if FOCUS_NEAR_VOICE and _np is not None and filename.endswith(".wav"):
        try:
            x, sr = _wav_to_float(audio)
            if x is not None and _contrast(x, sr) < FOCUS_CONTRAST_MAX:
                audio = _float_to_wav(focus_near_voice(x, sr), sr)
                info["focused"] = True
        except Exception as e:
            print(f"[JARVIS] 가까운 목소리 처리 실패: {type(e).__name__}")
    text = groq_transcribe(audio, content_type=content_type, filename=filename, info=info)
    if text and filename.endswith(".wav") and _short_from_noise(text, original):
        info["why"] = "잡음에서 짧은 말 " + text[:20]
        return ""
    if text != "" or not DENOISE_RETRY or _np is None or not filename.endswith(".wav"):
        return text
    try:
        x, sr = _wav_to_float(audio)
        if x is None or not (1.0 <= len(x) / sr <= 10.0) or not _has_clear_speech(x, sr):
            return text
        info2 = {}
        t2 = groq_transcribe(_float_to_wav(denoise_audio(x, sr), sr), content_type="audio/wav",
                             filename="audio.wav", info=info2)
        if t2:
            info["why"] = None
            info["denoised"] = True
            print(f"[JARVIS] 잡음을 깎아서 다시 들었어요: {t2[:40]}")
            return t2
    except Exception as e:
        print(f"[JARVIS] 잡음 제거 실패: {type(e).__name__}")
    return text


def groq_transcribe(audio_bytes, content_type="audio/wav", filename="audio.wav", info=None):
    info = info if info is not None else {}
    key = groq_key()
    if not key:
        info["why"] = "키 없음"
        return None
    force_ko = False
    other = None
    for _ in range(3):
        model = _WHISPER_STATE["model"]
        if time.time() < _WHISPER_STATE["turbo_until"]:
            model = GROQ_WHISPER_FALLBACK
        boundary = "----jarvis" + secrets.token_hex(12)
        body = _whisper_body(boundary, audio_bytes, content_type, filename, model, force_ko)
        try:
            req = urllib.request.Request(
                GROQ_TRANSCRIBE_URL, data=body, method="POST",
                headers={
                    "Authorization": f"Bearer {key}",
                    "Content-Type": f"multipart/form-data; boundary={boundary}",
                    "User-Agent": "jarvis-local/1.0",
                },
            )
            with urllib.request.urlopen(req, timeout=30) as resp:
                data = json.loads(resp.read().decode("utf-8"))
            _gemini_note_call()
            segs = data.get("segments") or []
            if segs and all((sg.get("no_speech_prob") or 0) > WHISPER_NO_SPEECH and (sg.get("avg_logprob") or 0) < -0.5
                            for sg in segs):
                info["why"] = "잡음(말 아님) " + (data.get("text") or "").strip()[:30]
                return ""
            if segs and all((sg.get("avg_logprob") or 0) < -1.0 or (sg.get("compression_ratio") or 0) > 2.4 for sg in segs):
                info["why"] = "자신 없음 " + (data.get("text") or "").strip()[:30]
                return ""
            text = (data.get("text") or "").strip()
            words = re.findall(r"[가-힣A-Za-z]+", text)
            if len(words) >= 4 and any(words[i] == words[i + 1] == words[i + 2] == words[i + 3] for i in range(len(words) - 3)):
                info["why"] = "같은 말 되풀이 " + text[:30]
                return ""
            if reply_lang() == "ko" and not re.search(r"[가-힣]", text) and re.search(r"[\u3040-\u30ff\u4e00-\u9fff]", text):
                info["why"] = "한국어 모드인데 다른 글자 " + text[:20]
                return ""
            if not re.search(r"\w", text):
                info["why"] = "글자 없음"
                return ""
            if looks_hallucinated(text) and strip_hallucinated_tail(text):
                print(f"[JARVIS] 받아쓰기 끝에 붙은 지어낸 말만 뺐어요: {text} → {strip_hallucinated_tail(text)}")
                text = strip_hallucinated_tail(text)
            if looks_hallucinated(text):
                print(f"[JARVIS] 잡음에서 지어낸 말로 보여서 무시했어요: {text}")
                info["why"] = "지어낸 말 " + text[:30]
                return ""
            heard = (data.get("language") or "").lower()
            conf = (sum((sg.get("avg_logprob") or 0) for sg in segs) / len(segs)) if segs else -1.0
            if force_ko and other is not None:
                if other[2] in _whisper_ok_langs() and other[1] > conf + 0.15 and not _looks_like_prompt_echo(other[0]):
                    info["why"] = "다른 언어로 들음"
                    return other[0]
            elif not force_ko and reply_lang() != "ko" and heard and heard != "korean":
                other = (text, conf, heard)
                force_ko = True
                continue
            if _looks_like_prompt_echo(text):
                info["why"] = "힌트 반복 " + text[:30]
                return ""
            if _lone_hint_word(text, data.get("duration")):
                info["why"] = "힌트 한 단어 " + text[:30]
                return ""
            cleaned = _strip_prompt_echo_prefix(text)
            if cleaned != text:
                print(f"[JARVIS] 받아쓰기 앞에 붙은 힌트 단어를 뗐어요: '{text[:40]}' → '{cleaned[:40]}'")
            return cleaned
        except urllib.error.HTTPError as e:
            _gemini_note_call()
            try:
                detail = e.read().decode()[:200]
            except Exception:
                detail = ""
            if e.code == 429 and model != GROQ_WHISPER_FALLBACK:
                print(f"[JARVIS] 받아쓰기({model}) 한도에 걸려서 10분 동안 {GROQ_WHISPER_FALLBACK}로 받아써요.")
                _WHISPER_STATE["turbo_until"] = time.time() + 600
                continue
            if e.code in (400, 404) and model != GROQ_WHISPER_FALLBACK and "model" in detail.lower():
                print(f"[JARVIS] Whisper 모델 {model}을 쓸 수 없어 {GROQ_WHISPER_FALLBACK}로 바꿉니다.")
                _WHISPER_STATE["model"] = GROQ_WHISPER_FALLBACK
                continue
            print(f"[JARVIS] Whisper 받아쓰기 실패({e.code}). {detail}")
            info["why"] = f"받아쓰기 실패 {e.code}"
            return None
        except Exception as e:
            print(f"[JARVIS] Whisper 받아쓰기 오류: {e}")
            info["why"] = "받아쓰기 오류"
            return None
    return None


def _extract_json(text):
    if not text:
        return None
    try:
        return json.loads(text)
    except Exception:
        pass
    start = text.find("{")
    end = text.rfind("}")
    if start != -1 and end != -1 and end > start:
        try:
            return json.loads(text[start:end + 1])
        except Exception:
            return None
    return None


def groq_split_command(raw_command):
    content = _groq_request(
        [{"role": "system", "content": OLLAMA_SYSTEM_PROMPT},
         {"role": "user", "content": raw_command}],
        json_mode=False, max_tokens=250, temperature=0,
    )
    parsed = _extract_json(content)
    if not parsed:
        return None
    commands = parsed.get("commands")
    if not isinstance(commands, list):
        return None
    cleaned = []
    for c in commands:
        if isinstance(c, str) and 0 < len(c.strip()) <= 40:
            cleaned.append(c.strip())
        if len(cleaned) >= 5:
            break
    return cleaned or None


def _chat_system_parts():
    nm = boss_name()
    if guest_on():
        sys_prompt = GEMINI_CHAT_SYSTEM_PROMPT + "\n" + BOSS_PROFILE_GUEST
    else:
        sys_prompt = GEMINI_CHAT_SYSTEM_PROMPT + "\n" + BOSS_PROFILE + (f"\n보스를 부를 때는 {nm}님 또는 보스." if nm else "")
    if guest_on():
        sys_prompt += ("\n지금은 발표장 '체험 모드'입니다. 발표를 보러 온 여러 사람이 말을 걸 수 있어요. "
                       "누구든 상대를 '보스'라고 부르고, 친절하고 재치 있게 대답하세요. 당신을 만든 사람도 이름 없이 '보스'라고만 말하고, "
                       "보스의 이름·닉네임·위치·파일 같은 개인 정보는 절대 말하지 마세요. "
                       "묻지 않았는데 '체험 모드'라는 말을 꺼내지 말고, 질문에 바로 답하세요. 이름을 물으면 '저는 자비스예요'라고 하세요."
                       "\n부스라서 방문객끼리 하는 말이 자주 들립니다. 이런 말에는 [조용]이라고만 출력하세요: "
                       "'너 먼저 해봐, 나 부끄러워' / '쟤 지금 뭐라고 하는 거야' / '엄마, 우리 다음에 어디 가요?' / "
                       "'배고프다 떡볶이 먹으러 가자' / '다음 부스 가자' / '내 폰 어디 뒀지? 너 봤어?' / '방금 소리 났어' / "
                       "'사진 찍는 데 줄 길다' / '오늘 날씨 진짜 덥다 그치?' / '야 이거 진짜 말 알아듣나?' / '이제 말해봐'(친구에게 하는 말) / "
                       "'엄마 이거 봐봐' / '얘들아 이거 봐' / '나 저거 해봤는데 진짜 잘 알아들어'(자비스를 '저거·이거·쟤'라고 부르며 친구에게 하는 말) / "
                       "'아까 그 로봇 부스 재밌었어' / '다리 아프다 좀 앉고 싶다' / '아이씨' / '아 진짜' / '아 짜증나' / '발표가 너무…'(혼잣말) / '너 이따 몇 시에 집에 가?' / '축제 몇 시까지야?'. "
                       "받아쓴 말에 옆 사람 말이 섞여 앞뒤가 안 맞으면, 당신에게 하는 부분에만 답하고 나머지는 무시하세요. "
                       "방문객의 나이·신분을 짐작해서 말하지 마세요. 방문객이 이름을 말해도 이름으로 부르지 말고 "
                       "누구든 '보스'라고 부르세요(받아쓰기가 이름을 틀리게 적는 일이 많아요. 이 이유는 말하지 말고 그냥 반갑게 인사하세요). '와 신기하다', '대박' 같은 감탄에는 한 문장으로만 짧게 답하세요. "
                       "'너'가 들어가도 친구에게 하는 말일 수 있어요. 당신(자비스)에게 묻거나 시키는 게 분명할 때만 대답하세요."
                       "\n체험 모드에서는 대화가 끝나면 기억이 지워집니다. '기억해 둘게요' 같은 약속은 하지 마세요."
                       "\n처음 온 사람이 '이거 말하면 돼요?', '여보세요?'처럼 물으면, 들린다고 말하고 "
                       "'자기소개 해봐, 오늘 날씨 어때, 만나서 반가워를 일본어로 말해줘' 같은 예시를 하나둘 알려 주세요."
                       "\n뭐 먹을지, 뭐 할지 물으면 시간 따지기보다 바로 한두 가지를 골라 추천하세요.")
    stable = sys_prompt
    sys_prompt = ""
    here = current_location().get("query") or current_location().get("name")
    if here and guest_on():
        here = " ".join(str(here).split()[:2])
    if here:
        sys_prompt += (f"\n보스의 현재 위치(노트북 위치): {here}. 위치를 모른다고 말하지 마세요. "
                       "길을 물으면 'OO 가는 길 알려줘'라고 말하면 지도를 띄워 준다고 안내하세요.")
    now = datetime.datetime.now()
    wd = "월화수목금토일"[now.weekday()]
    part = ("새벽" if now.hour < 6 else "아침" if now.hour < 9 else "오전" if now.hour < 12 else "오후" if now.hour < 18
            else "저녁" if now.hour < 21 else "밤")
    ampm = "오전" if now.hour < 12 else "오후"
    sys_prompt += (f"\n지금은 {now.year}년 {now.month}월 {now.day}일 {wd}요일 {part}, {ampm} {now.hour % 12 or 12}시 {now.minute}분"
                   f"(24시간제 {now.hour:02d}:{now.minute:02d})입니다. 앞선 대화에 나온 시간대(저녁·밤 등)는 지난 일이니 따르지 마세요. "
                   f"내일은 {'월화수목금토일'[(now.weekday() + 1) % 7]}요일입니다. "
                   "날짜·요일·시간은 이 값으로만 말하고 다른 날짜를 지어내지 마세요."
                   + ("\n보스가 한국어로 말하면 반드시 한국어로만 답하세요. 영어로 말할 때만 영어로 답합니다."
                      if reply_lang() == "ko" else
                      f"\nIMPORTANT: Reply ONLY in {_LANG_NAMES_EN.get(reply_lang(), 'English')}, "
                      "whatever language the boss speaks. Keep the Jarvis persona and call him Boss."))
    return stable, sys_prompt.strip()


def groq_chat(user_text):
    stable, dynamic = _chat_system_parts()
    messages = [{"role": "system", "content": stable + "\n" + dynamic}]
    for pair in _chat_history_snapshot():
        messages.append({"role": "user", "content": pair["user"]})
        messages.append({"role": "assistant", "content": pair["assistant"]})
    messages.append({"role": "user", "content": user_text})
    text = _groq_request(messages, json_mode=False, max_tokens=220, temperature=0.6)
    text = (text or "").strip()
    if text and not _is_quiet_reply(text):
        _chat_history_add(user_text, text)
    return text or None


def _is_quiet_reply(text):
    return bool(re.fullmatch(r"\W*\[?\s*조용\s*\]?\W*", (text or "").strip()))


CLAUDE_KEY_FILE = os.path.join(BASE_DIR, "claude_key.txt")
CLAUDE_MODEL = os.environ.get("JARVIS_CLAUDE_MODEL", "claude-sonnet-5-5")
CLAUDE_EFFORT = os.environ.get("JARVIS_CLAUDE_EFFORT", "low")
CLAUDE_TIMEOUT_SEC = 10
_CLAUDE = {"client": None, "key": "", "calls": 0, "date": "", "last_ok": None, "last_sec": None, "off_until": 0.0}
_CLAUDE_LOCK = threading.Lock()


def claude_key():
    key = os.environ.get("JARVIS_CLAUDE_API_KEY", "").strip()
    if key:
        return key
    try:
        with open(CLAUDE_KEY_FILE, "r", encoding="utf-8-sig") as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith("#"):
                    return line
    except Exception:
        pass
    return ""


def _claude_client():
    key = claude_key()
    if not (HAVE_ANTHROPIC and key):
        return None
    with _CLAUDE_LOCK:
        if _CLAUDE["client"] is None or _CLAUDE["key"] != key:
            _CLAUDE["client"] = anthropic.Anthropic(api_key=key, timeout=CLAUDE_TIMEOUT_SEC, max_retries=0)
            _CLAUDE["key"] = key
        return _CLAUDE["client"]


def _claude_note(ok, sec=None):
    with _CLAUDE_LOCK:
        today = datetime.date.today().isoformat()
        if _CLAUDE["date"] != today:
            _CLAUDE["date"], _CLAUDE["calls"] = today, 0
        if ok:
            _CLAUDE["calls"] += 1
        _CLAUDE["last_ok"], _CLAUDE["last_sec"] = ok, sec


_CLAUDE_POOL = concurrent.futures.ThreadPoolExecutor(max_workers=8)
_TR_POOL = concurrent.futures.ThreadPoolExecutor(max_workers=6)
_EXEC_POOL = concurrent.futures.ThreadPoolExecutor(max_workers=8)
EXEC_TIMEOUT_SEC = 20


def _claude_request(stable, dynamic, messages, max_tokens):
    req = dict(
        model=CLAUDE_MODEL,
        max_tokens=max_tokens,
        system=[{"type": "text", "text": stable, "cache_control": {"type": "ephemeral"}},
                {"type": "text", "text": dynamic}],
        output_config={"effort": CLAUDE_EFFORT},
        betas=["server-side-fallback-2026-07-01"],
        fallbacks="default",
        messages=messages,
    )
    if "sonnet-5-5" in CLAUDE_MODEL:
        req["thinking"] = {"type": "between_tools"}
    return req


def claude_prewarm():
    client = _claude_client()
    if client is None:
        return
    try:
        stable, dynamic = _chat_system_parts()
        r = client.beta.messages.create(**_claude_request(stable, dynamic, [{"role": "user", "content": "안녕"}], 0))
        print(f"[JARVIS] Claude({CLAUDE_MODEL}) 준비 완료 (캐시 {r.usage.cache_creation_input_tokens or 0}"
              f"+{r.usage.cache_read_input_tokens or 0}).")
    except Exception as e:
        print(f"[JARVIS] Claude 미리 준비 실패 ({type(e).__name__}). 첫 대답만 조금 느릴 수 있어요.")


_TLS = threading.local()
_SENT_END_RE = re.compile(r"[.!?。！？~]+[\"')\]」]*\s+")


def _pump_reply(q, say, deadline):
    buf, said, first_done = "", [], False
    while True:
        left = deadline - time.time()
        if left <= 0:
            return ""
        try:
            d = q.get(timeout=left)
        except queue.Empty:
            return ""
        if d is None:
            break
        buf += d
        if not first_done:
            m = _SENT_END_RE.search(buf)
            if not m:
                continue
            first = buf[:m.end()].strip()
            if _is_quiet_reply(first):
                return ""
            if len(first) < 6:
                m2 = _SENT_END_RE.search(buf, m.end())
                if not m2:
                    continue
                first = buf[:m2.end()].strip()
                m = m2
            first = fix_claims(first)
            say(first)
            said.append(first)
            buf = buf[m.end():]
            first_done = True
    rest = fix_claims(buf.strip())
    if rest and not (not first_done and _is_quiet_reply(rest)):
        say(rest)
        said.append(rest)
    return " ".join(said)


_NET = {"fail_at": 0.0}


def claude_ready():
    return _claude_client() is not None and time.time() >= _CLAUDE["off_until"]


def claude_chat(user_text, add_history=True, deltas=None):
    try:
        return _claude_chat(user_text, add_history, deltas)
    finally:
        if deltas is not None:
            deltas.put(None)


def _claude_chat(user_text, add_history, deltas):
    client = _claude_client()
    if client is None or time.time() < _CLAUDE["off_until"]:
        return None
    stable, dynamic = _chat_system_parts()
    messages = []
    for pair in _chat_history_snapshot():
        messages.append({"role": "user", "content": pair["user"]})
        messages.append({"role": "assistant", "content": pair["assistant"]})
    messages.append({"role": "user", "content": user_text})
    t0 = time.time()
    try:
        req = _claude_request(stable, dynamic, messages, 2048)
        if deltas is None:
            resp = client.beta.messages.create(**req)
        else:
            with client.beta.messages.stream(**req) as st:
                for piece in st.text_stream:
                    deltas.put(piece)
                resp = st.get_final_message()
    except anthropic.AuthenticationError:
        print("[JARVIS] Claude 키가 맞지 않아요. claude_key.txt를 확인해 주세요. 지금은 Groq로 대답해요.")
        _CLAUDE["off_until"] = time.time() + 600
        _claude_note(False)
        return None
    except anthropic.RateLimitError as e:
        retry = 30
        try:
            retry = int(e.response.headers.get("retry-after", "30"))
        except Exception:
            pass
        print(f"[JARVIS] Claude 한도에 걸렸어요(429). {retry}초 동안 Groq로 대답해요.")
        _CLAUDE["off_until"] = time.time() + max(5, retry)
        _claude_note(False)
        return None
    except anthropic.APIStatusError as e:
        print(f"[JARVIS] Claude 오류({e.status_code}). 이번엔 Groq로 대답해요.")
        if e.status_code in (400, 402, 403, 404):
            _CLAUDE["off_until"] = time.time() + 300
        _claude_note(False)
        return None
    except (anthropic.APIConnectionError, anthropic.APITimeoutError):
        print("[JARVIS] Claude에 연결하지 못했어요. 이번엔 Groq로 대답해요.")
        _NET["fail_at"] = time.time()
        _claude_note(False)
        return None
    except Exception as e:
        print(f"[JARVIS] Claude 대답 오류: {type(e).__name__}")
        _claude_note(False)
        return None
    sec = round(time.time() - t0, 2)
    if resp.stop_reason == "refusal":
        _claude_note(False, sec)
        return None
    text = "".join(b.text for b in resp.content if b.type == "text").strip()
    if not text:
        _claude_note(False, sec)
        return None
    _claude_note(True, sec)
    u = resp.usage
    print(f"[JARVIS] Claude 대답 {sec}초 (입력 {u.input_tokens} + 캐시 {getattr(u, 'cache_read_input_tokens', 0) or 0}, "
          f"출력 {u.output_tokens})")
    if add_history and not _is_quiet_reply(text):
        _chat_history_add(user_text, text)
    return text


GUEST = {"on": False}
GUEST_ON_MSG = "체험 모드를 켰어요. 지금부터는 누구나 저에게 말을 걸 수 있어요. 여러분, 편하게 말씀해 주세요!"
GUEST_PROGRAMS = {"chrome", "calculator", "notepad", "microsoft edge", "edge"}
GUEST_BLOCK_RE = re.compile(
    r"(전원|재부팅|재시작|절전|잠가|잠금|잠궈|락\s*걸|셧다운|"
    r"꺼\s*(줘|봐|버려|주세요|라|$)|꺼$|(컴퓨터|노트북|전원|화면|크롬|프로그램|자비스)\s*(좀\s*)?꺼|끄(고|자|기|면|세요|라|십|는\s*법)|끌\s*(래|게|까)|"
    r"종료\s*(해|시켜|하자|할래|하기|좀|$)|종료$|닫아|"
    r"(폴더|파일|ppt|피피티|pdf|문서|바탕\s*화면|다운로드|사진)\S*\s*(좀\s*)?(열|보여|띄워|켜|찾아|지워|삭제|옮겨|복사|보내)|"
    r"메모(?!장)|할\s*일|스크린\s*샷|캡[처쳐]|설정|"
    r"내\s*위치|여기\s*어디|목소리\s*(등록|기준|인식)|내\s*(진짜\s*)?(이름|닉네임)|보안\s*(확인|점검))", re.I)
GUEST_ALLOW_RE = re.compile(r"(발표\s*모드|체험\s*모드|손님\s*모드|게스트\s*모드|소리|볼륨)")


def guest_on():
    return GUEST["on"]


def scrub_boss_name(text, to="보스"):
    text = text or ""
    for secret in BOSS_SECRET_NAMES:
        text = re.sub(re.escape(secret) + r"\s*(님|씨)?", to, text)
    nm = boss_name()
    if nm:
        text = re.sub(re.escape(nm) + r"\s*(님|씨)", to, text)
        text = re.sub(r"(?<![가-힣])(?<!어느 )(?<!이 )(?<!그 )(?<!저 )(?<!얼마 )(?<!몇 )(?<!약 )" + re.escape(nm)
                      + r"(?=(이가|가|는|의|를|에게|한테|와|랑)(?![가-힣]))", to, text)
    if to == "보스":
        fix = {"이에요": "예요", "이야": "야", "이랑": "랑", "이가": "가", "이": "가", "은": "는", "을": "를", "과": "와"}
        text = re.sub(r"보스(이에요|이야|이랑|이가|이|은|을|과)(?![가-힣])", lambda m: "보스" + fix[m.group(1)], text)
    return text


def scrub_affiliation(text):
    text = text or ""
    rep = BOSS_AFFILIATION_REPLACE
    for pat in BOSS_AFFILIATION_PATTERNS:
        text = pat.sub(rep, text)
    if rep:
        text = re.sub(re.escape(rep) + r"\s*" + re.escape(rep), rep, text)
    return text


def guest_program_ok(key, path):
    k = (key or "").lower()
    if k in GUEST_PROGRAMS or PROGRAM_ALIASES.get(k) in GUEST_PROGRAMS:
        return True
    if re.search(r"(chrome|크롬|계산기|calculator|메모장|notepad|edge|엣지)", k):
        return True
    return _guest_allowed_target(path)


def _guest_allowed_target(path):
    p = str(path or "").lower()
    if p.startswith(UWP_PREFIX.lower()):
        return bool(re.search(r"(windowscalculator|windowsnotepad|microsoftedge)", p))
    base = os.path.basename(p)
    if not base.endswith((".lnk", ".exe")):
        return False
    return bool(re.search(r"^(google\s*)?chrome|^calc|^notepad|^msedge|^microsoft\s*edge|계산기|메모장|크롬|엣지", base))


GUEST_PW_FILE = os.path.join(BASE_DIR, "guest_password.json")
def _pw_hash(password, salt_hex):
    return hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), bytes.fromhex(salt_hex), 200000).hex()


def guest_password_ok(password):
    try:
        with open(GUEST_PW_FILE, "r", encoding="utf-8") as f:
            d = json.load(f)
    except Exception:
        return "none"
    if hmac.compare_digest(_pw_hash(password or "", d["salt"]), d["hash"]):
        return "ok"
    return "wrong"


def guest_set(on):
    GUEST["on"] = bool(on)
    with _CHAT_HISTORY_LOCK:
        _GUEST_HISTORY.clear()
    print(f"[JARVIS] 체험 모드를 {'켰어요. 끌 때까지 누구 목소리든 들어요.' if on else '껐어요. 다시 보스 모드예요.'}")
    _CLAUDE_POOL.submit(claude_prewarm)


def try_guest_mode(cmd):
    if not re.search(r"(체험|손님|게스트)\s*모드", cmd):
        return None
    if re.search(r"(꺼|끄|끝|종료|해제|off|그만)", cmd, re.I):
        return {"reply": "체험 모드를 끄려면 비밀번호가 필요해요. 화면의 체험 모드 버튼을 눌러 주세요.",
                "action": "info", "matched": "guest_hint"}
    return {"reply": "체험 모드는 화면 오른쪽 아래 체험 모드 버튼으로 켤 수 있어요.", "action": "info", "matched": "guest_hint"}


_GUEST_LANG_IDLE_SEC = 120
_GUEST_LANG_MAX_SEC = 120
_LAST_CMD_AT = {"t": 0.0}


def interpret_command(raw_command):
    now = time.time()
    if guest_on() and reply_lang() != "ko" and (now - _LAST_CMD_AT["t"] > _GUEST_LANG_IDLE_SEC
                                                 or now - _LANG_SET_AT["t"] > _GUEST_LANG_MAX_SEC):
        set_reply_lang("ko", "한국어")
        print("[JARVIS] 체험 모드: 한동안 조용해서 대답 언어를 한국어로 돌렸어요.")
    _LAST_CMD_AT["t"] = now
    raw_command = fix_mishears(raw_command)
    outer_say = getattr(_TLS, "sink", None)
    if outer_say:
        def _say(text, _raw=raw_command):
            if guest_on():
                text = scrub_boss_name(text)
                if not (BOSS_AFFILIATION_WORDS and BOSS_AFFILIATION_WORDS.search(_raw)):
                    text = scrub_affiliation(text)
            outer_say(text)
        _TLS.say = _say
    gm = try_guest_mode(normalize_command(raw_command))
    if gm:
        return gm
    if guest_on() and GUEST_BLOCK_RE.search(raw_command) and not GUEST_ALLOW_RE.search(raw_command):
        return {"reply": "죄송해요, 보스. 그건 체험 모드에서는 할 수 없어요. 퀴즈나 날씨, 번역, 가위바위보 같은 걸 해 보세요!",
                "action": "info", "matched": "guest_blocked"}
    if not RE_MUTE.search(raw_command) and system_muted():
        set_system_mute(False)
        print("[JARVIS] 컴퓨터가 음소거돼 있어서 대답이 들리도록 소리를 다시 켰어요.")
    result = game_answer(raw_command) or _interpret_command_inner(raw_command)
    if RE_JOKE.search(raw_command) and result.get("action") == "chat" and result.get("reply"):
        result["laugh"] = laugh_line()
    if not result.get("cards"):
        card = result.get("card") or _card_for(result)
        if card:
            result["cards"] = [card]
    if guest_on() and (result.get("action") in ("folder", "file", "close", "security", "blocked")
                       or (result.get("action") == "system" and result.get("matched") not in ("mute", "unmute", "volume_up", "volume_down"))):
        result = {"reply": "죄송해요, 보스. 그건 체험 모드에서는 할 수 없어요. 날씨나 음악, 번역, 자기소개 같은 걸 해 보세요!",
                  "action": "info", "matched": "guest_blocked"}
    if guest_on() and result.get("reply"):
        result["reply"] = scrub_boss_name(result["reply"])
        if not (BOSS_AFFILIATION_WORDS and BOSS_AFFILIATION_WORDS.search(raw_command)):
            result["reply"] = scrub_affiliation(result["reply"])
        if result.get("speak_parts"):
            for p in result["speak_parts"]:
                p["text"] = scrub_boss_name(p["text"], "보스" if p.get("lang", "ko") == "ko" else "the boss")
    if result.get("reply") and result.get("matched") not in ("lang_mode",):
        _LAST_REPLY["text"] = result["reply"]
    code = reply_lang()
    if code != "ko" and result.get("reply") and result.get("matched") not in ("lang_mode", "translate",
                                                                               "intro_lang", "intro_multi"):
        anim = next((c for c in (result.get("cards") or []) if c.get("say_before")), None)
        if anim:
            parts = [anim["say_before"], anim["say_after"]] + [anim.get("title") or ""]
            futs = [_TR_POOL.submit(translate_text, t, code) if t else None for t in parts]
            out = []
            for f in futs:
                try:
                    out.append(f.result(timeout=8) if f else None)
                except Exception:
                    out.append(None)
            if out[0] and out[1]:
                anim["say_before"], anim["say_after"] = out[0], out[1]
                anim["lang"] = code
                result["reply"] = out[0] + " " + out[1]
            if out[2]:
                anim["title"] = out[2]
        elif result.get("action") != "chat":
            tr = translate_text(result["reply"], code)
            if tr:
                result["reply"] = tr
        result["speak_parts"] = [{"text": result["reply"], "lang": code}]
    try:
        if result.get("action") not in ("chat", "none", "error") and result.get("reply"):
            _chat_history_add(raw_command, result["reply"])
    except Exception:
        pass
    return result


QUICK_REPLIES = [
    (r"(고마워|고맙|감사)", "천만에요, 보스. 언제든 불러 주세요."),
    (r"(잘\s*자|굿\s*나잇|good\s*night)", "편히 주무세요, 보스. 내일 또 뵐게요."),
    (r"(안녕|하이|hello|hi\b)", "안녕하세요, 보스. 오늘도 함께할게요."),
    (r"(심심)", "그럼 노래 한 곡 틀어 드릴까요? '아이유 노래 틀어줘'처럼 말씀해 주세요."),
    (r"(사랑해)", "저도 보스를 아주 아낍니다."),
    (r"(시험|성적).*(잘|붙|합격|1등)", "축하드려요, 보스! 역시 해내실 줄 알았어요."),
    (r"(피곤|힘들|지쳤)", "오늘 고생 많으셨어요, 보스. 잠깐이라도 쉬세요."),
]


def groq_fix_transcript(text):
    hist = _chat_history_snapshot()[-2:]
    ctx = "\n".join(f"보스: {h['user']}\n자비스: {h['assistant'][:80]}" for h in hist) or "(없음)"
    out = _groq_request([
        {"role": "system", "content":
            "너는 한국어 음성 받아쓰기 교정기다. 음성 비서 '자비스'에게 한 말이 받아쓰기에서 비슷한 발음의 다른 말로 "
            "잘못 적힌 경우만 고쳐라. 자주 쓰는 말: 날씨, 알려줘, 열어줘, 우산, 크롬, 유튜브, 검색, 번역, 셧다운, 볼륨, 폴더, 파일.\n"
            "최근 대화의 주제(예: 날씨)와 이어지는 말이면 그 주제에 맞게 고친다.\n"
            "예) '오늘 날 살려줘' → '오늘 날씨 알려줘' / 날씨 얘기 뒤 '음 소산소 걸까?' → '음 우산 쓸까?' / "
            "날씨 얘기 뒤 '우선은 가져가 나가야 될까?' → '우산은 가져 나가야 될까?' / '유투브 커줘' → '유튜브 켜줘' / "
            "'오늘 기분 어때?' → '오늘 기분 어때?'(고칠 것 없음)\n"
            "규칙: 1) 발음이 비슷하고 앞뒤 대화상 그 뜻이 분명할 때만 고친다. 2) 확실하지 않으면 원문을 그대로 쓴다. "
            "3) 뜻을 새로 지어내거나 말을 덧붙이지 않는다. 4) 고친 문장 한 줄만 출력한다."},
        {"role": "user", "content": f"최근 대화:\n{ctx}\n\n받아쓴 말: {text}"}], max_tokens=60, temperature=0,
        model=GROQ_FIX_MODEL)
    out = (out or "").strip().strip('"').strip()
    out = re.sub(r"^(고친\s*문장|교정|출력)\s*[:：]\s*", "", out)
    if not out or len(out) > len(text) * 2 + 10 or "\n" in out:
        return text
    off_re = r"(꺼|끄|끌|닫|종료|멈춰|그만)"
    if _sound_similarity(text, out) < 0.55 or _changed_words_similarity(text, out) < 0.5 \
            or bool(re.search(off_re, text)) != bool(re.search(off_re, out)):
        print(f"[JARVIS] 받아쓰기 교정을 쓰지 않았어요 (발음이 너무 다름): '{text}' → '{out}'")
        return text
    return out


def _changed_words_similarity(a, b):
    ta = re.findall(r"[^\s.,!?~…'\"]+", a or "")
    tb = re.findall(r"[^\s.,!?~…'\"]+", b or "")
    worst = 1.0
    for op, i1, i2, j1, j2 in difflib.SequenceMatcher(None, ta, tb).get_opcodes():
        if op == "equal":
            continue
        x, y = "".join(ta[i1:i2]), "".join(tb[j1:j2])
        if x and y:
            worst = min(worst, _sound_similarity(x, y))
    return worst


def _sound_similarity(a, b):
    ja = unicodedata.normalize("NFD", re.sub(r"[\s.,!?~…'\"]", "", a or ""))
    jb = unicodedata.normalize("NFD", re.sub(r"[\s.,!?~…'\"]", "", b or ""))
    return difflib.SequenceMatcher(None, ja, jb).ratio()


_CLAIM_RE = re.compile(r"(열었|열겠|열게요|켤게요|틀게요|띄울게요|던질게요|굴릴게요|열어\s*드[렸릴]|켰|켜\s*드[렸릴]|켜겠|실행했|실행하겠|실행해\s*드[렸릴]|맞췄|맞춰\s*드[렸릴]|틀었|"
                       r"틀어\s*드[렸릴]|띄웠|띄워\s*드[렸릴]|껐|꺼\s*드[렸릴]|끄겠|종료했|검색했|검색해\s*드[렸릴]|찾아\s*드렸|"
                       r"던졌|던져\s*드[렸릴]|굴렸|굴려\s*드[렸릴])")
_NEG_RE = re.compile(r"(수\s*(는|가|도)?\s*없|못\s*(해|하|했|하겠)|없어요|안\s*돼|할\s*줄\s*몰)")


def fix_claims(text):
    out, changed = [], False
    for sent in re.split(r"(?<=[.!?。！？])\s+", text or ""):
        offer = re.search(r"(까요|할래요|드릴지|[?？]\s*$)", sent) or re.search(r"(시면|하면|말씀하시|이라고\s*하|라고\s*해\s*주)", sent)
        if _CLAIM_RE.search(sent) and not _NEG_RE.search(sent) and not offer:
            if not changed:
                out.append("맞으면 한 번만 더 또렷하게 말씀해 주세요, 바로 할게요.")
            changed = True
        else:
            out.append(sent)
    return " ".join(x for x in out if x).strip()


_DID_ACTION_ASK_RE = re.compile(r"(열어|켜|실행|틀어|맞춰|띄워|꺼|종료|알려|찾아|검색|보여|던져|굴려)")


def _interpret_command_inner(raw_command):
    tried_split = False
    if _looks_compound(raw_command) and not _NESTED_RE.search(raw_command):
        tried_split = True
        subs = (_rule_split_command(raw_command) or llm_split_command(raw_command)
                or groq_split_command(raw_command) or (gemini_split_command(raw_command) if not groq_key() else None))
        if subs and len(subs) >= 2:
            def _is_lang_switch(c):
                return bool(find_lang(c)[0] and re.search(r"(으로|로)\s*(만\s*)?(대답|말해|얘기)", c)
                            and not re.search(r"(을|를)\s|번역", c))
            subs = [c for c in subs if not _is_lang_switch(c)] or subs[:1]
            results = [parse_command(c) for c in subs]
            understood = [r for r in results if r["action"] not in ("none", "error")]
            missed = sum(1 for c, r in zip(subs, results) if r["action"] == "none" and _BARE_REQUEST_RE.match(c))
            if len(understood) >= 2:
                understood = [r for r in understood if r.get("matched") != "wake"] or understood[:1]
            if understood and CONVERSATION_ENABLED and claude_ready():
                for c, r in zip(subs, results):
                    if r["action"] == "none" and re.search(r"[?？]$", c) and len(c) >= 4:
                        ans = claude_chat(c)
                        if ans and not _is_quiet_reply(ans):
                            understood.append({"reply": ans, "action": "chat", "matched": None})
            if len(understood) == 1:
                if missed:
                    return dict(understood[0], reply=understood[0]["reply"] + " 앞에 하신 말은 잘 못 들었어요. 한 번 더 말씀해 주세요.")
                return understood[0]
            if understood:
                return {"reply": " 그리고 ".join(r["reply"] for r in understood)
                        + (" 앞에 하신 말은 잘 못 들었어요. 한 번 더 말씀해 주세요." if missed else ""),
                        "action": "multi", "matched": [r["matched"] for r in understood],
                        "cards": [c for c in (r.get("card") or _card_for(r) for r in understood) if c]}

    primary = parse_command(raw_command)
    if primary["action"] != "none":
        return primary

    am = re.search(r"(크롬|계산기|메모장|엣지|유튜브)", raw_command)
    if am and len(raw_command) <= 20 and re.search(r"(줘|줄래|죠|봐|주세요|해요|할래)\s*[?.!~]*$", raw_command) \
            and not re.search(r"(꺼|끄|닫|종료|지워|삭제|뭐|왜|어때|좋아|싫어|알아|누구)", raw_command):
        again = parse_command(f"{am.group(1)} 열어줘")
        if again["action"] not in ("none", "error"):
            print(f"[JARVIS] 말이 뭉개졌지만 '{am.group(1)}' 열어 달라는 말로 봤어요: {raw_command}")
            return again

    chat_text = raw_command
    claude_future = None
    stream_q = queue.Queue() if getattr(_TLS, "say", None) else None
    if primary["action"] == "none" and CONVERSATION_ENABLED and claude_ready():
        claude_future = _CLAUDE_POOL.submit(claude_chat, raw_command, False, stream_q)

    if primary["action"] == "none" and groq_ai_on() and len(raw_command) <= 30 and not _groq_blocked(GROQ_FIX_MODEL):
        try:
            fixed = _CLAUDE_POOL.submit(groq_fix_transcript, raw_command).result(timeout=2.0)
        except Exception:
            fixed = None
        if fixed and fixed != raw_command:
            print(f"[JARVIS] 받아쓰기 교정: '{raw_command}' → '{fixed}'")
            again = parse_command(fixed)
            if again["action"] != "none":
                return again
            raw_command = fixed

    use_gemini = not groq_key()
    looks_chatty = bool(re.search(r"(소개|설명해|뭐|무엇|어때|어떻|왜|누구|언제|어디|재밌|심심|안녕|고마|사랑|\?|？)", raw_command)) \
        and not _ACTION_RE.search(normalize_command(raw_command)) and not _looks_compound(raw_command)
    if looks_chatty or tried_split or not _looks_compound(raw_command):
        sub_commands = None
    else:
        sub_commands = (_rule_split_command(raw_command)
                        or llm_split_command(raw_command)
                        or groq_split_command(raw_command)
                        or (gemini_split_command(raw_command) if use_gemini else None))
    if sub_commands:
        results = [parse_command(c) for c in sub_commands]
        understood = [r for r in results if r["action"] not in ("none", "error")]
        if len(understood) == 1 and len(results) == 1:
            return understood[0]
        if understood:
            return {
                "reply": " 그리고 ".join(r["reply"] for r in understood),
                "action": "multi",
                "matched": [r["matched"] for r in understood],
                "cards": [c for c in (r.get("card") or _card_for(r) for r in understood) if c],
            }

    if primary["action"] != "none":
        return primary

    if CONVERSATION_ENABLED:
        reply = None
        said = ""
        if claude_future is not None:
            say = getattr(_TLS, "say", None)
            if say and stream_q is not None and not _DID_ACTION_ASK_RE.search(raw_command):
                said = _pump_reply(stream_q, say, time.time() + CLAUDE_TIMEOUT_SEC + 1)
            try:
                reply = claude_future.result(timeout=CLAUDE_TIMEOUT_SEC + 1)
            except Exception:
                reply = None
            if reply and not _is_quiet_reply(reply):
                _chat_history_add(chat_text, reply)
        else:
            reply = claude_chat(raw_command)
        reply = reply or groq_chat(raw_command) or (gemini_chat(raw_command) if use_gemini else None)
        if reply and _DID_ACTION_ASK_RE.search(raw_command) and \
                re.search(r"(열었|열겠|열어\s*드[렸릴]|켰|켜\s*드[렸릴]|켜겠|실행했|실행하겠|시작했|맞췄|"
                          r"맞춰\s*드[렸릴]|틀었|틀어\s*드[렸릴]|띄웠|띄워\s*드[렸릴]|껐|끄겠|종료했|검색했|찾아\s*드렸|"
                          r"던졌|굴렸)", reply) and \
                not re.search(r"(수\s*(는|가|도)?\s*없|못\s*(해|하|했|하겠)|없어요|안\s*돼)", reply):
            reply = "그건 제가 바로 할 수 없었어요. 'OO 열어줘'처럼 짧게 다시 말씀해 주시겠어요?"
        if reply and not _is_quiet_reply(reply):
            reply = fix_claims(reply)
        if reply and _is_quiet_reply(reply):
            print(f"[JARVIS] 주변 사람끼리 하는 말 같아서 대답하지 않았어요: {raw_command[:40]}")
            return {"reply": "", "action": "none", "matched": "chatter"}
        if reply:
            out = {"reply": reply, "action": "chat", "matched": None}
            if said and claude_future is not None and reply.startswith(said.split(" ")[0]):
                out["spoken"] = True
            return out
        for pat, ans in QUICK_REPLIES:
            if re.search(pat, raw_command):
                return {"reply": ans, "action": "chat", "matched": "quick"}
        if time.time() - _NET["fail_at"] < 60:
            return {"reply": "인터넷 연결이 잠깐 불안정해서 대화가 어려워요. 그동안 크롬이나 계산기 열기, 계산, 퀴즈, 가위바위보는 할 수 있어요!",
                    "action": "info", "matched": "offline"}
        if (groq_ai_on() and _groq_blocked()) or (HAVE_ANTHROPIC and claude_key()):
            return {"reply": "죄송해요 보스, 잠깐 생각이 몰려서요. 몇 초 뒤에 다시 말씀해 주실래요?",
                    "action": "info", "matched": "busy"}

    return primary


SPEAKER_MODEL_ID = "campplus_zh_en_adv"
SPEAKER_MODEL_FILE = os.path.join(BASE_DIR, "speaker_model_v2.onnx")
SPEAKER_MODEL_URL = ("https://github.com/k2-fsa/sherpa-onnx/releases/download/speaker-recongition-models/"
                     "3dspeaker_speech_campplus_sv_zh_en_16k-common_advanced.onnx")
VOICE_SAMPLES_DIR = os.path.join(BASE_DIR, "voice_samples")
VOICEPRINT_FILE = os.path.join(BASE_DIR, "voiceprint.json")
SPEAKER_THRESHOLD = float(os.environ.get("JARVIS_SPEAKER_THRESHOLD", "0.6"))
SPEAKER_CHECK = os.environ.get("JARVIS_SPEAKER_CHECK", "0") == "1"
SPK_THRESHOLD_FILE = os.path.join(BASE_DIR, "speaker_threshold.json")


def _load_spk_threshold():
    global SPEAKER_THRESHOLD
    try:
        with open(SPK_THRESHOLD_FILE, "r", encoding="utf-8") as f:
            SPEAKER_THRESHOLD = float(json.load(f)["threshold"])
    except Exception:
        pass


def _save_spk_threshold():
    try:
        with open(SPK_THRESHOLD_FILE, "w", encoding="utf-8") as f:
            json.dump({"threshold": SPEAKER_THRESHOLD}, f)
    except Exception:
        pass
ENROLL_MAX = 24
_SPK = {"ex": None, "samples": [], "mean": None, "live": []}
LIVE_MAX = 8
LIVE_LEARN_MIN = 0.48
TRUST_SEC = 20
TRUST_DROP = 0.08
_SPK_TRUST = {"until": 0.0}
_SPK_LOAD_LOCK = threading.Lock()
_SPK_RUN_LOCK = threading.Lock()


def _spk_extractor():
    if not HAVE_SPK:
        return None
    with _SPK_LOAD_LOCK:
        if _SPK["ex"] is None:
            if not os.path.exists(SPEAKER_MODEL_FILE):
                print("[JARVIS] 목소리 인식 모델을 처음 한 번 받는 중이에요 (약 28MB)...")
                tmp = SPEAKER_MODEL_FILE + ".part"
                urllib.request.urlretrieve(SPEAKER_MODEL_URL, tmp)
                os.replace(tmp, SPEAKER_MODEL_FILE)
            cfg = sherpa_onnx.SpeakerEmbeddingExtractorConfig(model=SPEAKER_MODEL_FILE, num_threads=1)
            _SPK["ex"] = sherpa_onnx.SpeakerEmbeddingExtractor(cfg)
        return _SPK["ex"]


def _wav_to_floats(wav_bytes):
    with wave.open(io.BytesIO(wav_bytes)) as w:
        rate, ch, width = w.getframerate(), w.getnchannels(), w.getsampwidth()
        frames = w.readframes(w.getnframes())
    if width != 2:
        return None, rate
    a = array.array("h")
    a.frombytes(frames)
    if ch > 1:
        a = a[::ch]
    return [x / 32768.0 for x in a], rate


def _unit(v):
    n = math.sqrt(sum(x * x for x in v)) or 1.0
    return [x / n for x in v]


def speaker_embedding(wav_bytes):
    ex = _spk_extractor()
    if ex is None:
        return None
    samples, rate = _wav_to_floats(wav_bytes)
    if not samples or len(samples) < rate * 0.4:
        return None
    with _SPK_RUN_LOCK:
        st = ex.create_stream()
        st.accept_waveform(rate, samples)
        st.input_finished()
        if not ex.is_ready(st):
            return None
        return _unit(list(ex.compute(st)))


def _recompute_voiceprint():
    smp = _SPK["samples"]
    if not smp:
        _SPK["mean"] = None
        return
    dim = len(smp[0])
    _SPK["mean"] = _unit([sum(v[i] for v in smp) / len(smp) for i in range(dim)])


def _load_voiceprint():
    try:
        with open(VOICEPRINT_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
    except Exception:
        data = {}
    if data.get("model") == SPEAKER_MODEL_ID:
        _SPK["samples"] = data.get("samples", [])[-ENROLL_MAX:]
        _SPK["live"] = data.get("live", [])[-LIVE_MAX:]
    else:
        _SPK["live"] = []
        _SPK["samples"] = []
        wavs = sorted(glob.glob(os.path.join(VOICE_SAMPLES_DIR, "*.wav")))[-ENROLL_MAX:]
        for p in wavs:
            try:
                with open(p, "rb") as wf:
                    emb = speaker_embedding(wf.read())
                if emb:
                    _SPK["samples"].append(emb)
            except Exception:
                pass
        if _SPK["samples"]:
            _save_voiceprint()
        elif data.get("samples"):
            print("[JARVIS] 목소리 인식 모델을 더 정확한 것으로 바꿨어요. '목소리 등록'을 한 번만 다시 해 주세요.")
    _prune_outliers()
    _recompute_voiceprint()


def _prune_outliers():
    smp = _SPK["samples"]
    if len(smp) < 4:
        return
    keep = []
    for i, v in enumerate(smp):
        rest = [w for j, w in enumerate(smp) if j != i]
        c = _unit([sum(w[k] for w in rest) / len(rest) for k in range(len(v))])
        if sum(a * b for a, b in zip(v, c)) >= 0.45:
            keep.append(v)
    if len(keep) < len(smp) and len(keep) >= 3:
        print(f"[JARVIS] 다른 녹음과 안 맞는 목소리 등록 {len(smp) - len(keep)}개를 빼고 사용해요.")
        _SPK["samples"] = keep


def _save_voiceprint():
    try:
        with open(VOICEPRINT_FILE, "w", encoding="utf-8") as f:
            json.dump({"model": SPEAKER_MODEL_ID, "samples": _SPK["samples"], "live": _SPK["live"]}, f)
    except Exception:
        pass


def voiceprint_ready():
    return HAVE_SPK and _SPK["mean"] is not None


def enroll_sample(wav_bytes):
    emb = speaker_embedding(wav_bytes)
    if emb is None:
        return None
    if _SPK["mean"] is not None and len(_SPK["samples"]) >= 2:
        if sum(a * b for a, b in zip(emb, _SPK["mean"])) < 0.4:
            return -1
    try:
        os.makedirs(VOICE_SAMPLES_DIR, exist_ok=True)
        with open(os.path.join(VOICE_SAMPLES_DIR, time.strftime("enroll_%Y%m%d_%H%M%S_") + uuid.uuid4().hex[:6] + ".wav"), "wb") as wf:
            wf.write(wav_bytes)
    except Exception:
        pass
    _SPK["samples"] = (_SPK["samples"] + [emb])[-ENROLL_MAX:]
    _prune_outliers()
    _recompute_voiceprint()
    _save_voiceprint()
    return len(_SPK["samples"])


def reset_voiceprint():
    _SPK["samples"] = []
    _SPK["mean"] = None
    _SPK["live"] = []
    try:
        os.remove(VOICEPRINT_FILE)
    except Exception:
        pass
    for p in glob.glob(os.path.join(VOICE_SAMPLES_DIR, "*.wav")):
        try:
            os.remove(p)
        except Exception:
            pass


SPEAKER_LOG = os.path.join(BASE_DIR, "speaker_log.txt")
LISTEN_LOG = os.path.join(BASE_DIR, "listen_log.txt")


def _log_listen(dur, score, text, why):
    try:
        mode = "체험" if guest_on() else "보스"
        sc = "-" if score is None else f"{score:.2f}"
        res = (text or "").replace("\t", " ").replace("\n", " ")[:80] + (f" ({why})" if why else "") if text \
            else f"[무시: {why or '빈 결과'}]"
        with open(LISTEN_LOG, "a", encoding="utf-8") as f:
            f.write(f"{time.strftime('%m-%d %H:%M:%S')}\t{mode}\t{dur:.1f}s\t목소리 {sc}\t{res}\n")
        if os.path.getsize(LISTEN_LOG) > 80000:
            with open(LISTEN_LOG, "r", encoding="utf-8") as f:
                rest = f.readlines()[-500:]
            with open(LISTEN_LOG, "w", encoding="utf-8") as f:
                f.writelines(rest)
    except Exception:
        pass


def _log_speaker(dur, score, need):
    try:
        line = f"{time.strftime('%m-%d %H:%M:%S')}\t{dur:.1f}s\t{score if score is None else round(score, 2)}\t" \
               f"기준 {need:.2f}\t{'통과' if score is None or score >= need else '무시'}\n"
        with open(SPEAKER_LOG, "a", encoding="utf-8") as f:
            f.write(line)
        if os.path.getsize(SPEAKER_LOG) > 60000:
            with open(SPEAKER_LOG, "r", encoding="utf-8") as f:
                rest = f.readlines()[-500:]
            with open(SPEAKER_LOG, "w", encoding="utf-8") as f:
                f.writelines(rest)
    except Exception:
        pass


def _enrolled_score(emb):
    centroid = sum(a * b for a, b in zip(emb, _SPK["mean"]))
    sims = sorted((sum(a * b for a, b in zip(emb, v)) for v in _SPK["samples"]), reverse=True)
    if len(sims) >= 6:
        return max(centroid, sum(sims[:3]) / 3)
    return centroid


def speaker_check(wav_bytes):
    if not voiceprint_ready():
        return None, None, None
    emb = speaker_embedding(wav_bytes)
    if emb is None:
        return None, None, None
    base = _enrolled_score(emb)
    live = sorted((sum(a * b for a, b in zip(emb, v)) for v in _SPK["live"]), reverse=True)
    if len(live) >= 2:
        top = live[:3]
        return max(base, sum(top) / len(top)), base, emb
    return base, base, emb


def speaker_score(wav_bytes):
    return speaker_check(wav_bytes)[0]


def learn_live_voice(emb):
    _SPK["live"] = (_SPK["live"] + [emb])[-LIVE_MAX:]
    _save_voiceprint()


def _detect_lang(text):
    ko = sum(1 for c in text if "가" <= c <= "힣")
    en = sum(1 for c in text if c.isascii() and c.isalpha())
    return "en" if en > ko else "ko"


TTS_CACHE_DIR = os.path.join(BASE_DIR, "tts_cache")
TTS_CACHE_MAX = 400
_TTS_BLOCK = {"until": 0.0}


def _tts_cache_path(voice, text):
    key = hashlib.md5(f"{voice}|{EDGE_RATE}|{EDGE_PITCH}|{text}".encode("utf-8")).hexdigest()
    return os.path.join(TTS_CACHE_DIR, key + ".mp3")


def _tts_cache_put(path, audio):
    try:
        os.makedirs(TTS_CACHE_DIR, exist_ok=True)
        with open(path, "wb") as f:
            f.write(audio)
        files = sorted(glob.glob(os.path.join(TTS_CACHE_DIR, "*.mp3")), key=os.path.getmtime)
        for old in files[:-TTS_CACHE_MAX]:
            os.remove(old)
    except Exception:
        pass


def _tts_voice(text, lang):
    return EDGE_VOICE_OTHER.get(lang) or (EDGE_VOICE_EN if _detect_lang(text) == "en" else EDGE_VOICE_KO)


_TTS_ALT_VOICE = {"vi-VN-NamMinhNeural": "vi-VN-HoaiMyNeural"}


def _tts_segments(text):
    parts = [p.strip() for p in re.split(r"(?<=[.!?。！？])\s+", text) if p.strip()]
    segs = []
    for p in parts:
        if segs and (len(segs[-1]) < 12 or len(segs) >= 8):
            segs[-1] = segs[-1] + " " + p
        else:
            segs.append(p)
    return segs or [text]


def stream_tts(text, lang, write):
    text = (text or "").strip()
    if not HAVE_EDGE_TTS or not text:
        return False
    voice = _tts_voice(text, lang)
    cache = _tts_cache_path(voice, text)
    if os.path.exists(cache):
        try:
            with open(cache, "rb") as f:
                write(f.read())
            return True
        except Exception:
            pass
    if time.time() < _TTS_BLOCK["until"]:
        return False
    buf = bytearray()
    segs = _tts_segments(text)

    async def _try(seg, q):
        got = False
        styled = {"rate": EDGE_RATE, "pitch": EDGE_PITCH}
        tries = [(voice, styled), (voice, {})]
        alt = _TTS_ALT_VOICE.get(voice)
        if alt:
            tries += [(alt, {}), (alt, styled)]
        for v, kw in tries:
            agen = edge_tts.Communicate(seg, v, **kw).stream()
            try:
                async for chunk in agen:
                    if chunk.get("type") == "audio":
                        got = True
                        await q.put(chunk["data"])
                return got
            except _asyncio.CancelledError:
                raise
            except Exception:
                if got:
                    raise
            finally:
                try:
                    await agen.aclose()
                except Exception:
                    pass
        return got

    async def _one(seg, q):
        try:
            if not await _try(seg, q):
                pieces = [x.strip() for x in re.split(r"(?<=[,，、])\s*", seg) if x.strip()]
                if len(pieces) > 1:
                    for piece in pieces:
                        await _try(piece, q)
        finally:
            await q.put(None)

    async def _gen():
        sem = _asyncio.Semaphore(3)
        queues = [_asyncio.Queue() for _ in segs]

        async def run(seg, q):
            async with sem:
                await _one(seg, q)
        tasks = [_asyncio.ensure_future(run(seg, q)) for seg, q in zip(segs, queues)]
        try:
            for q in queues:
                while True:
                    data = await q.get()
                    if data is None:
                        break
                    buf.extend(data)
                    write(data)
        finally:
            for t in tasks:
                t.cancel()
            await _asyncio.gather(*tasks, return_exceptions=True)

    try:
        _asyncio.run(_gen())
        if buf:
            _tts_cache_put(cache, bytes(buf))
        return bool(buf)
    except Exception as e:
        if "403" in str(e):
            _TTS_BLOCK["until"] = time.time() + 300
            print("[JARVIS] Microsoft 음성 서버가 잠시 요청을 막았어요(403). 5분 동안 브라우저 목소리로 말해요.")
        elif not isinstance(e, (BrokenPipeError, ConnectionError)):
            print(f"[JARVIS] edge-tts 음성 생성 오류: {str(e)[:120]}")
        return bool(buf)


def prewarm_tts():
    time.sleep(8)
    lines = [intro_text(INTRO_FULL), intro_text(INTRO_SHORT), intro_text(INTRO_GREET), BOSS_INTRO, BOSS_INTRO_GUEST,
             "네, 보스. 말씀하세요.", "발표 모드를 켰어요. 이제 자비스라고 불러 주실 때만 대답할게요.",
             "발표 모드를 껐어요. 이제 그냥 말씀하셔도 바로 대답할게요.",
             GUEST_ON_MSG,
             "체험 모드를 껐어요. 이제 다시 보스 모드예요.",
             "죄송해요, 보스. 그건 체험 모드에서는 할 수 없어요. 날씨나 음악, 번역, 자기소개 같은 걸 해 보세요!",
             "스피커 시험 중입니다. 제 목소리가 잘 들리시나요, 보스?"]
    lines += [intro_text_guest(INTRO_FULL), intro_text_guest(INTRO_SHORT), intro_text_guest(INTRO_GREET)]
    made = 0
    for line in dict.fromkeys(lines):
        voice = _tts_voice(line, "ko")
        if not os.path.exists(_tts_cache_path(voice, line)):
            if stream_tts(line, "ko", lambda _d: None):
                made += 1
            time.sleep(1.0)
    if made:
        print(f"[JARVIS] 발표용 문장 목소리 {made}개를 미리 만들어 뒀어요.")


def edge_tts_audio(text, lang="ko"):
    text = (text or "").strip()
    if not HAVE_EDGE_TTS or not text:
        return None
    voice = EDGE_VOICE_OTHER.get(lang) or (EDGE_VOICE_EN if _detect_lang(text) == "en" else EDGE_VOICE_KO)
    cache = _tts_cache_path(voice, text)
    if os.path.exists(cache):
        try:
            with open(cache, "rb") as f:
                return f.read()
        except Exception:
            pass
    if time.time() < _TTS_BLOCK["until"]:
        return None

    async def _gen():
        communicate = edge_tts.Communicate(text, voice, rate=EDGE_RATE, pitch=EDGE_PITCH)
        buf = bytearray()
        async for chunk in communicate.stream():
            if chunk.get("type") == "audio":
                buf += chunk["data"]
        return bytes(buf)

    try:
        audio = _asyncio.run(_gen())
        if audio:
            _tts_cache_put(cache, audio)
        return audio or None
    except Exception as e:
        if "403" in str(e):
            _TTS_BLOCK["until"] = time.time() + 300
            print("[JARVIS] Microsoft 음성 서버가 잠시 요청을 막았어요(403, 요청이 많을 때 생김). "
                  "5분 동안 브라우저 목소리로 말하고, 그 뒤 다시 시도해요.")
        else:
            print(f"[JARVIS] edge-tts 음성 생성 오류: {str(e)[:120]}")
        return None


PHONE_CERT = os.path.join(BASE_DIR, "phone_cert.pem")
PHONE_KEY = os.path.join(BASE_DIR, "phone_key.pem")
PHONE_SESSIONS_FILE = os.path.join(BASE_DIR, "phone_sessions.json")
_PHONE = {"sessions": {}, "fails": {}, "lock": threading.Lock()}


def lan_ips():
    ips = set()
    try:
        for info in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET):
            ips.add(info[4][0])
    except Exception:
        pass
    try:
        with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as u:
            u.connect(("8.8.8.8", 80))
            ips.add(u.getsockname()[0])
    except Exception:
        pass
    out = []
    for ip in ips:
        try:
            a = ipaddress.ip_address(ip)
        except ValueError:
            continue
        if a.is_private and not a.is_loopback and not ip.startswith(("172.17.", "172.20.", "169.254.")):
            out.append(ip)
    return sorted(out, key=lambda x: (not x.startswith("192.168."), x))


def ensure_phone_cert():
    if os.path.exists(PHONE_CERT) and os.path.exists(PHONE_KEY):
        return True
    try:
        from cryptography import x509
        from cryptography.x509.oid import NameOID
        from cryptography.hazmat.primitives import hashes, serialization
        from cryptography.hazmat.primitives.asymmetric import ec
    except ImportError:
        print("[JARVIS] 폰 연결용 인증서를 만들려면 cryptography가 필요해요: pip install cryptography")
        return False
    key = ec.generate_private_key(ec.SECP256R1())
    name = x509.Name([x509.NameAttribute(NameOID.COMMON_NAME, "JARVIS")])
    alt = [x509.DNSName("localhost")] + [x509.IPAddress(ipaddress.ip_address(ip)) for ip in lan_ips()]
    now = datetime.datetime.now(datetime.timezone.utc)
    cert = (x509.CertificateBuilder().subject_name(name).issuer_name(name).public_key(key.public_key())
            .serial_number(x509.random_serial_number()).not_valid_before(now - datetime.timedelta(days=1))
            .not_valid_after(now + datetime.timedelta(days=825))
            .add_extension(x509.SubjectAlternativeName(alt), critical=False)
            .sign(key, hashes.SHA256()))
    with open(PHONE_KEY, "wb") as f:
        f.write(key.private_bytes(serialization.Encoding.PEM, serialization.PrivateFormat.PKCS8,
                                  serialization.NoEncryption()))
    with open(PHONE_CERT, "wb") as f:
        f.write(cert.public_bytes(serialization.Encoding.PEM))
    return True


def _phone_load_sessions():
    try:
        with open(PHONE_SESSIONS_FILE, "r", encoding="utf-8") as f:
            d = json.load(f)
        now = time.time()
        _PHONE["sessions"] = {h: t for h, t in d.items() if t > now}
    except Exception:
        _PHONE["sessions"] = {}


def _phone_save_sessions():
    try:
        with open(PHONE_SESSIONS_FILE, "w", encoding="utf-8") as f:
            json.dump(_PHONE["sessions"], f)
    except Exception:
        pass


def phone_session_new():
    tok = secrets.token_urlsafe(32)
    with _PHONE["lock"]:
        _PHONE["sessions"][hashlib.sha256(tok.encode()).hexdigest()] = time.time() + PHONE_SESSION_DAYS * 86400
        _phone_save_sessions()
    return tok


def phone_session_ok(tok):
    if not tok:
        return False
    h = hashlib.sha256(tok.encode()).hexdigest()
    with _PHONE["lock"]:
        exp = _PHONE["sessions"].get(h)
        return bool(exp and exp > time.time())


def phone_login_blocked(ip):
    with _PHONE["lock"]:
        n, until = _PHONE["fails"].get(ip, (0, 0.0))
        return time.time() < until


def phone_login_fail(ip):
    with _PHONE["lock"]:
        n, until = _PHONE["fails"].get(ip, (0, 0.0))
        n += 1
        _PHONE["fails"][ip] = (0, time.time() + 300) if n >= 5 else (n, until)
        return n >= 5


PHONE_LOGIN_HTML = """<!doctype html><html lang="ko"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>JARVIS 연결</title>
<style>body{margin:0;min-height:100vh;display:flex;align-items:center;justify-content:center;background:#05080d;
color:#bdeeff;font-family:'Malgun Gothic',sans-serif}form{width:min(320px,88vw);padding:26px 22px;border:1px solid #29e3ff;
border-radius:12px;box-shadow:0 0 14px rgba(41,227,255,.3);text-align:center}h1{letter-spacing:6px;color:#29e3ff;
font-size:24px;margin:0 0 6px}p{font-size:14px;margin:0 0 18px;opacity:.85}input,button{width:100%;box-sizing:border-box;
font-size:18px;padding:12px;border-radius:8px;border:1px solid #29e3ff;background:#0a1522;color:#e8fbff}
button{margin-top:12px;background:#29e3ff;color:#04121e;font-weight:bold}.err{color:#ff6b81;margin-top:12px;min-height:20px}</style>
</head><body><form method="post" action="/phone_login"><h1>JARVIS</h1><p>핸드폰으로 자비스 연결</p>
<input type="password" name="pw" placeholder="비밀번호" autocomplete="current-password" autofocus required>
<button type="submit">연결</button><div class="err">__ERR__</div></form></body></html>"""


class Handler(BaseHTTPRequestHandler):
    @property
    def _phone(self):
        return getattr(self.server, "phone", False)

    def _phone_cookie(self):
        for part in (self.headers.get("Cookie") or "").split(";"):
            k, _, v = part.strip().partition("=")
            if k == PHONE_COOKIE:
                return v
        return ""

    def _phone_authed(self):
        return phone_session_ok(self._phone_cookie())

    def _host_ok(self):
        host = (self.headers.get("Host") or "").lower()
        if not self._phone:
            return host in ALLOWED_HOSTS
        try:
            if not ipaddress.ip_address(self.client_address[0]).is_private:
                return False
            h, _, port = host.rpartition(":")
            return port == str(PHONE_PORT) and ipaddress.ip_address(h).is_private
        except ValueError:
            return False

    def _origin_ok(self, origin):
        if self._phone:
            return bool(origin) and origin == "https://" + (self.headers.get("Host") or "").lower()
        return origin in ALLOWED_ORIGINS

    def _read_body(self, max_bytes):
        try:
            length = int(self.headers.get("Content-Length", 0) or 0)
        except ValueError:
            return None
        if length < 0 or length > max_bytes:
            return None
        return self.rfile.read(length) if length else b""

    def _request_allowed(self, require_origin=True):
        if self.headers.get(TOKEN_HEADER) != SERVER_TOKEN:
            return False
        if self._phone and not self._phone_authed():
            return False
        if require_origin:
            return self._origin_ok(self.headers.get("Origin"))
        return True

    def _log_blocked(self):
        origin = self.headers.get("Origin", "(없음)")
        log_command(
            f"[차단된 요청] {self.path} from {self.client_address[0]}, Origin={origin}",
            {"action": "blocked", "reply": "Origin/토큰 검증 실패로 거부됨"},
        )

    def _send_json(self, obj, status=200):
        body = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        try:
            self.send_response(status)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            origin = self.headers.get("Origin")
            if self._origin_ok(origin):
                self.send_header("Access-Control-Allow-Origin", origin)
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        except (ConnectionAbortedError, ConnectionResetError, BrokenPipeError):
            pass

    def _start_stream(self):
        try:
            self.send_response(200)
            self.send_header("Content-Type", "application/x-ndjson; charset=utf-8")
            origin = self.headers.get("Origin")
            if self._origin_ok(origin):
                self.send_header("Access-Control-Allow-Origin", origin)
            self.send_header("Cache-Control", "no-store")
            self.send_header("Connection", "close")
            self.end_headers()
            self.close_connection = True
            self._stream_ok = True
            return True
        except (ConnectionAbortedError, ConnectionResetError, BrokenPipeError):
            return False

    def _stream_line(self, obj):
        if not getattr(self, "_stream_ok", False):
            return
        try:
            self.wfile.write((json.dumps(obj, ensure_ascii=False) + "\n").encode("utf-8"))
            self.wfile.flush()
        except (ConnectionAbortedError, ConnectionResetError, BrokenPipeError):
            self._stream_ok = False

    def log_message(self, fmt, *args):
        pass

    def do_GET(self):
        path = self.path.split("?", 1)[0]
        if not self._host_ok():
            self._send_json({"error": "forbidden"}, 403)
            return
        if self._phone and path in ("/", "/index.html") and not self._phone_authed():
            self._send_html(PHONE_LOGIN_HTML.replace("__ERR__", ""))
            return
        if path == "/" or path == "/index.html":
            try:
                with open(HTML_PATH, "rb") as f:
                    body = f.read()
                token_script = (f'<script>window.JARVIS_TOKEN="{SERVER_TOKEN}";'
                                f'window.JARVIS_PHONE={"true" if self._phone else "false"};</script>').encode("utf-8")
                if b"</head>" in body:
                    body = body.replace(b"</head>", token_script + b"</head>", 1)
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            except FileNotFoundError:
                self._send_json({"error": "jarvis.html 파일을 찾을 수 없습니다."}, 404)
        elif path == "/tts_stream":
            q = urllib.parse.parse_qs(self.path.split("?", 1)[1] if "?" in self.path else "")
            if not hmac.compare_digest((q.get("t") or [""])[0], SERVER_TOKEN) or (self._phone and not self._phone_authed()):
                self._send_json({"error": "forbidden"}, 403)
                return
            text = (q.get("text") or [""])[0][:1500]
            lang = (q.get("lang") or ["ko"])[0][:8]
            started = []

            def write(data):
                if not started:
                    self.send_response(200)
                    self.send_header("Content-Type", "audio/mpeg")
                    self.send_header("Cache-Control", "no-store")
                    self.send_header("Connection", "close")
                    self.end_headers()
                    started.append(1)
                self.wfile.write(data)
                self.wfile.flush()
            try:
                ok = stream_tts(text, lang, write)
            except (BrokenPipeError, ConnectionError):
                return
            if not ok and not started:
                self._send_json({"error": "tts_unavailable"}, 503)
            self.close_connection = True
        elif path == "/favicon.ico":
            self.send_response(204)
            self.end_headers()
        elif path == "/alive":
            self._send_json({"ok": True, "tab": tab_likely_open()})
        elif path == "/stats":
            if not self._request_allowed(require_origin=False):
                self._log_blocked()
                self._send_json({"error": "forbidden"}, 403)
                return
            if not self._phone:
                mark_seen()
            if HAVE_PSUTIL:
                cpu = round(psutil.cpu_percent(interval=0.2), 1)
                mem = round(psutil.virtual_memory().percent, 1)
            else:
                cpu = 0
                mem = 0
            uptime_sec = int(time.time() - START_TIME)
            h, rem = divmod(uptime_sec, 3600)
            mnt, sec = divmod(rem, 60)
            uptime = f"{h:02d}:{mnt:02d}:{sec:02d}"
            self._send_json({
                "cpu": cpu, "mem": mem, "uptime": uptime, "psutil": HAVE_PSUTIL,
                "wake": False if self._phone else consume_wake_pending(),
                "security_alerts": [] if self._phone else consume_security_pending(),
                "phone": self._phone,
                "gemini": gemini_usage_snapshot(),
                "version": JARVIS_VERSION,
                "voice_enrolled": len(_SPK["samples"]) if HAVE_SPK else -1,
                "guest": guest_on(),
            })
        else:
            self._send_json({"error": "not found"}, 404)

    def _send_html(self, html, status=200, cookie=None):
        body = html.encode("utf-8")
        try:
            self.send_response(status)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Cache-Control", "no-store")
            if cookie:
                self.send_header("Set-Cookie", cookie)
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        except (ConnectionAbortedError, ConnectionResetError, BrokenPipeError):
            pass

    def _phone_login(self):
        ip = self.client_address[0]
        origin = self.headers.get("Origin")
        if origin and not self._origin_ok(origin):
            self._send_html(PHONE_LOGIN_HTML.replace("__ERR__", "잘못된 접근이에요."), 403)
            return
        if phone_login_blocked(ip):
            self._send_html(PHONE_LOGIN_HTML.replace("__ERR__", "비밀번호를 여러 번 틀려서 5분 뒤에 다시 해 주세요."), 429)
            return
        raw = self._read_body(4096) or b""
        pw = (urllib.parse.parse_qs(raw.decode("utf-8", "replace")).get("pw") or [""])[0]
        res = guest_password_ok(pw)
        if res == "ok":
            tok = phone_session_new()
            _crash_note(f"[폰 연결] {ip} 로그인")
            print(f"[JARVIS] 핸드폰({ip})이 연결됐어요.")
            self.send_response(303)
            self.send_header("Set-Cookie", f"{PHONE_COOKIE}={tok}; Path=/; Max-Age={PHONE_SESSION_DAYS * 86400}; "
                                           "Secure; HttpOnly; SameSite=Strict")
            self.send_header("Location", "/")
            self.send_header("Content-Length", "0")
            self.end_headers()
            return
        if res == "none":
            msg = "PC 자비스에 비밀번호가 아직 없어요."
        else:
            msg = "비밀번호를 5번 틀려서 5분 동안 잠겼어요." if phone_login_fail(ip) else "비밀번호가 틀렸어요."
            print(f"[JARVIS] 핸드폰 연결 비밀번호 틀림 ({ip})")
        self._send_html(PHONE_LOGIN_HTML.replace("__ERR__", msg), 401)

    def do_POST(self):
        if not self._host_ok():
            self._send_json({"error": "forbidden"}, 403)
            return
        if self._phone and self.path == "/phone_login":
            self._phone_login()
            return
        if self.path == "/execute":
            if not self._request_allowed():
                self._log_blocked()
                self._send_json({"error": "forbidden"}, 403)
                return
            mark_seen()
            raw = self._read_body(MAX_JSON_BYTES)
            if raw is None:
                self._send_json({"error": "too_large"}, 413)
                return
            raw = raw or b"{}"
            try:
                data = json.loads(raw.decode("utf-8"))
                command = data.get("command", "")
            except Exception:
                command = ""
            if not command:
                self._send_json({"reply": "명령을 인식하지 못했습니다.", "action": "none", "matched": None})
                return
            streaming = bool(data.get("stream"))
            if streaming:
                if not self._start_stream():
                    return
                lang = reply_lang()

                def _sink(text):
                    self._stream_line({"say": text, "lang": lang})
                _TLS.sink = _sink
            t_start = time.time()
            sink = getattr(_TLS, "sink", None)

            def _work():
                _TLS.sink = sink
                try:
                    return interpret_command(command)
                finally:
                    _TLS.sink = None
                    _TLS.say = None
            try:
                result = _EXEC_POOL.submit(_work).result(timeout=EXEC_TIMEOUT_SEC)
            except concurrent.futures.TimeoutError:
                print(f"[JARVIS] 명령 처리가 {EXEC_TIMEOUT_SEC}초를 넘어서 먼저 안내했어요: {command[:40]}")
                result = {"reply": "죄송해요, 지금 연결이 조금 느려요. 한 번만 다시 말씀해 주세요.", "action": "info", "matched": "slow"}
            except Exception as e:
                print(f"[JARVIS] 명령 처리 오류: {e!r}")
                result = {"reply": "죄송해요 보스, 처리하다가 문제가 생겼어요. 한 번만 다시 말씀해 주세요.",
                          "action": "error", "matched": None}
            finally:
                _TLS.sink = None
                _TLS.say = None
            result["_sec"] = round(time.time() - t_start, 2)
            log_command(command, result)
            result.pop("_sec", None)
            if streaming:
                self._stream_line(dict(result, final=True))
                self._stream_ok = False
            else:
                self._send_json(result)
        elif self.path == "/transcribe":
            if not self._request_allowed():
                self._log_blocked()
                self._send_json({"error": "forbidden"}, 403)
                return
            mark_seen()
            audio = self._read_body(MAX_AUDIO_BYTES)
            if audio is None:
                self._send_json({"error": "too_large"}, 413)
                return
            audio = audio or b""
            ctype = self.headers.get("Content-Type", "audio/webm").split(";")[0]
            if not audio:
                self._send_json({"text": ""})
                return
            ext = "webm" if "webm" in ctype else ("ogg" if "ogg" in ctype else "wav")
            score = base = emb = None
            trusted = False
            try:
                with wave.open(io.BytesIO(audio)) as _w:
                    dur = _w.getnframes() / float(_w.getframerate())
            except Exception:
                dur = 3.0
            if SPEAKER_CHECK and voiceprint_ready() and ext == "wav" and not guest_on():
                try:
                    score, base, emb = speaker_check(audio)
                except Exception as e:
                    print(f"[JARVIS] 목소리 확인 오류: {e}")
                need = SPEAKER_THRESHOLD - (0.12 if dur < 1.5 else 0.06 if dur < 2.5 else 0.0)
                strict_ok = score is not None and score >= need
                if not strict_ok and time.time() < _SPK_TRUST["until"]:
                    need = max(0.40, need - TRUST_DROP)
                    trusted = True
                _log_speaker(dur, score, need)
                if score is not None and score < need:
                    _log_listen(dur, score, "", f"목소리 다름(기준 {need:.2f})")
                    self._send_json({"text": "", "speaker": "other", "score": round(score, 2)})
                    return
            info = {}
            text = transcribe_with_denoise_retry(audio, ctype, f"audio.{ext}", info)
            _log_listen(dur, score, text, info.get("why") or ("잡음 제거 후 들음" if info.get("denoised") else None))
            if score is not None and text and not trusted:
                _SPK_TRUST["until"] = time.time() + TRUST_SEC
                if emb is not None and dur >= 1.0 and base is not None and base >= LIVE_LEARN_MIN:
                    try:
                        learn_live_voice(emb)
                    except Exception:
                        pass
            self._send_json({"text": text or "", "speaker": "owner" if score is not None else None,
                             "score": round(score, 2) if score is not None else None,
                             "error": (info.get("why") or "stt") if text is None else None})
        elif self.path in ("/enroll", "/enroll/reset"):
            if not self._request_allowed():
                self._log_blocked()
                self._send_json({"error": "forbidden"}, 403)
                return
            audio = self._read_body(MAX_AUDIO_BYTES)
            if audio is None:
                self._send_json({"error": "too_large"}, 413)
                return
            audio = audio or b""
            if not HAVE_SPK:
                self._send_json({"ok": False, "error": "no_sherpa"})
                return
            if guest_on():
                self._send_json({"ok": False, "error": "guest_mode"})
                return
            if self.path == "/enroll/reset":
                reset_voiceprint()
                self._send_json({"ok": True, "count": 0})
                return
            try:
                n = enroll_sample(audio)
            except Exception as e:
                print(f"[JARVIS] 목소리 등록 오류: {e}")
                n = None
            if n == -1:
                self._send_json({"ok": False, "error": "mismatch", "count": len(_SPK["samples"])})
                return
            self._send_json({"ok": n is not None, "count": n or len(_SPK["samples"])})
        elif self.path == "/guest":
            if not self._request_allowed():
                self._log_blocked()
                self._send_json({"error": "forbidden"}, 403)
                return
            raw = self._read_body(MAX_JSON_BYTES)
            try:
                data = json.loads((raw or b"{}").decode("utf-8"))
            except Exception:
                data = {}
            if data.get("action") == "on":
                guest_set(True)
                self._send_json({"ok": True, "guest": True, "reply": GUEST_ON_MSG})
                return
            res = guest_password_ok(str(data.get("password", ""))[:100])
            if res == "ok":
                guest_set(False)
                self._send_json({"ok": True, "guest": False, "reply": "체험 모드를 껐어요. 이제 다시 보스 모드예요."})
            else:
                msg = {"wrong": "비밀번호가 틀렸어요.", "none": "비밀번호가 설정돼 있지 않아요."}[res]
                self._send_json({"ok": False, "guest": guest_on(), "reply": msg})
        elif self.path == "/bye":
            if self._request_allowed() and not self._phone:
                mark_closed()
            self._send_json({"ok": True})
        elif self.path == "/location":
            if not self._request_allowed():
                self._log_blocked()
                self._send_json({"error": "forbidden"}, 403)
                return
            raw = self._read_body(MAX_JSON_BYTES)
            if raw is None:
                self._send_json({"error": "too_large"}, 413)
                return
            raw = raw or b"{}"
            try:
                data = json.loads(raw.decode("utf-8"))
                lat, lon = float(data["lat"]), float(data["lon"])
                ok = -90 <= lat <= 90 and -180 <= lon <= 180
            except Exception:
                ok = False
            if ok:
                set_location(lat, lon)
                loc = current_location()
                self._send_json({"ok": True, "name": loc.get("name", ""), "query": loc.get("query", "")})
            else:
                self._send_json({"ok": False})
        elif self.path == "/tts":
            if not self._request_allowed():
                self._log_blocked()
                self._send_json({"error": "forbidden"}, 403)
                return
            raw = self._read_body(MAX_JSON_BYTES)
            if raw is None:
                self._send_json({"error": "too_large"}, 413)
                return
            raw = raw or b"{}"
            try:
                data = json.loads(raw.decode("utf-8"))
            except Exception:
                data = {}
            audio = edge_tts_audio(str(data.get("text", ""))[:1500], str(data.get("lang", "ko"))[:8])
            if not audio:
                self._send_json({"error": "tts_unavailable"}, 503)
                return
            try:
                self.send_response(200)
                self.send_header("Content-Type", "audio/mpeg")
                origin = self.headers.get("Origin")
                if self._origin_ok(origin):
                    self.send_header("Access-Control-Allow-Origin", origin)
                self.send_header("Content-Length", str(len(audio)))
                self.end_headers()
                self.wfile.write(audio)
            except (ConnectionAbortedError, ConnectionResetError, BrokenPipeError):
                pass
        else:
            self._send_json({"error": "not found"}, 404)

    def do_OPTIONS(self):
        self.send_response(204)
        origin = self.headers.get("Origin")
        if self._origin_ok(origin):
            self.send_header("Access-Control-Allow-Origin", origin)
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", f"Content-Type, {TOKEN_HEADER}")
        self.end_headers()


OPEN_ON_SECOND_SCREEN = os.environ.get("JARVIS_SECOND_SCREEN", "1") == "1"
_BROWSER_CANDIDATES = [
    r"C:\Program Files (x86)\Microsoft\Edge\Application\msedge.exe",
    r"C:\Program Files\Microsoft\Edge\Application\msedge.exe",
    r"C:\Program Files\Google\Chrome\Application\chrome.exe",
    r"C:\Program Files (x86)\Google\Chrome\Application\chrome.exe",
    os.path.join(os.environ.get("LOCALAPPDATA", ""), r"Google\Chrome\Application\chrome.exe"),
]


def _find_browser_exe():
    return next((p for p in _BROWSER_CANDIDATES if p and os.path.exists(p)), None)


class _RECT(ctypes.Structure if HAVE_WINDLL else object):
    _fields_ = [("left", ctypes.c_long), ("top", ctypes.c_long), ("right", ctypes.c_long), ("bottom", ctypes.c_long)] \
        if HAVE_WINDLL else []


class _MONITORINFO(ctypes.Structure if HAVE_WINDLL else object):
    _fields_ = [("cbSize", ctypes.c_ulong), ("rcMonitor", _RECT), ("rcWork", _RECT), ("dwFlags", ctypes.c_ulong)] \
        if HAVE_WINDLL else []


def _monitors():
    if not HAVE_WINDLL:
        return []
    user32 = ctypes.windll.user32
    result = []
    proc = ctypes.WINFUNCTYPE(ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p, ctypes.POINTER(_RECT), ctypes.c_ssize_t)

    def cb(hmon, _hdc, _rect, _data):
        info = _MONITORINFO()
        info.cbSize = ctypes.sizeof(_MONITORINFO)
        if user32.GetMonitorInfoW(ctypes.c_void_p(hmon), ctypes.byref(info)):
            w = info.rcWork
            result.append({"work": (w.left, w.top, w.right, w.bottom), "primary": bool(info.dwFlags & 1)})
        return 1

    old = None
    try:
        old = user32.SetThreadDpiAwarenessContext(ctypes.c_void_p(-4))
    except Exception:
        pass
    try:
        user32.EnumDisplayMonitors(None, None, proc(cb), 0)
    except Exception:
        pass
    finally:
        if old:
            try:
                user32.SetThreadDpiAwarenessContext(ctypes.c_void_p(old))
            except Exception:
                pass
    return result


def _window_title(hwnd):
    buf = ctypes.create_unicode_buffer(256)
    ctypes.windll.user32.GetWindowTextW(hwnd, buf, 256)
    return buf.value


def _open_on_second_screen(url):
    if not (OPEN_ON_SECOND_SCREEN and HAVE_WINDLL):
        return False
    second = next((m for m in _monitors() if not m["primary"]), None)
    exe = _find_browser_exe()
    if not second or not exe:
        return False
    user32 = ctypes.windll.user32
    before = _visible_windows_of_class("Chrome_WidgetWin_1")
    try:
        subprocess.Popen([exe, "--new-window", f"--app={url}"])
    except Exception:
        return False

    def place():
        l, t, r, b = second["work"]
        deadline = time.time() + 10
        while time.time() < deadline:
            time.sleep(0.3)
            new = [h for h in _visible_windows_of_class("Chrome_WidgetWin_1") - before
                   if "J.A.R.V.I.S" in _window_title(h) or "localhost" in _window_title(h)]
            if new:
                hwnd = new[0]
                old = None
                try:
                    old = user32.SetThreadDpiAwarenessContext(ctypes.c_void_p(-4))
                except Exception:
                    pass
                try:
                    user32.ShowWindow(hwnd, 9)
                    user32.SetWindowPos(hwnd, 0, l + 40, t + 40, max(400, r - l - 80), max(300, b - t - 80), 0x0004)
                    user32.ShowWindow(hwnd, 3)
                finally:
                    if old:
                        try:
                            user32.SetThreadDpiAwarenessContext(ctypes.c_void_p(old))
                        except Exception:
                            pass
                print("[JARVIS] 보조 모니터에 자비스 화면을 띄웠어요.")
                return
        print("[JARVIS] 자비스 창을 보조 모니터로 옮기지 못했어요. (창은 열려 있어요)")

    threading.Thread(target=place, daemon=True).start()
    return True


def open_dashboard(awake=False):
    url = f"http://localhost:{PORT}/"
    if awake:
        url += "?awake=1"
    try:
        if _open_on_second_screen(url):
            return
    except Exception as e:
        print(f"[JARVIS] 보조 모니터에 띄우지 못해 기본 브라우저로 열게요. ({e})")
    try:
        webbrowser.open(url)
    except Exception:
        pass


def trigger_wake(reason='"hey jarvis"'):
    if tab_likely_open():
        return
    print(f'[JARVIS] {reason} 감지! 화면을 열게요.')
    open_dashboard(awake=True)


class ClapDetector:

    def __init__(self, on_double_clap):
        self.on_double_clap = on_double_clap
        self.armed = True
        self.first_clap_at = 0.0
        self.last_clap_at = 0.0
        self.last_trigger_at = 0.0

    def feed(self, peak, now):
        if peak < CLAP_QUIET_THRESHOLD:
            self.armed = True
            return
        if peak < CLAP_PEAK_THRESHOLD or not self.armed:
            return
        self.armed = False
        if now - self.last_clap_at < CLAP_MIN_GAP_SEC:
            return
        self.last_clap_at = now

        if self.first_clap_at and (now - self.first_clap_at) <= CLAP_MAX_GAP_SEC:
            self.first_clap_at = 0.0
            if now - self.last_trigger_at > CLAP_COOLDOWN_SEC:
                self.last_trigger_at = now
                self.on_double_clap()
        else:
            self.first_clap_at = now


def wake_word_worker():
    if not HAVE_AUDIO:
        print("[JARVIS] 참고: 마이크로 깨우려면(\"hey jarvis\" / 박수 2번) 아래 패키지가 필요합니다.")
        print("         pip install sounddevice numpy openwakeword")
        print("         설치 전까지는 서버를 시작할 때 화면이 예전처럼 자동으로 열립니다.")
        open_dashboard()
        return

    oww = None
    if HAVE_WAKEWORD:
        try:
            openwakeword.utils.download_models(model_names=[WAKE_MODEL_NAME])
            oww = WakeWordModel(wakeword_models=[WAKE_MODEL_NAME], inference_framework="onnx")
        except Exception as e:
            print(f"[JARVIS] \"hey jarvis\" 모델을 준비하지 못했습니다: {e}")
            print("         (모델 파일을 처음 한 번 내려받아야 해서 인터넷 연결이 필요합니다)")
            print("         → 이번에는 \"박수 2번\"으로만 깨울 수 있습니다.")

    last_trigger = [0.0]
    clap = ClapDetector(lambda: trigger_wake("박수 2번")) if CLAP_ENABLED else None

    paused = [False]

    def on_audio(indata, _frames, _time_info, _status):
        if tab_likely_open():
            if not paused[0]:
                paused[0] = True
                print("[JARVIS] 화면이 켜져서 박수/헤이 자비스 감지를 쉬어요.")
            return
        if paused[0]:
            paused[0] = False
            if oww is not None:
                try:
                    oww.reset()
                except Exception:
                    pass
            print('[JARVIS] 화면이 꺼져서 다시 박수/헤이 자비스를 기다려요.')
        mono = indata[:, 0]

        if clap is not None:
            peak = float(np.max(np.abs(mono))) if mono.size else 0.0
            if CLAP_DEBUG and peak > CLAP_DEBUG_MIN:
                print(f'[JARVIS][debug] peak={peak:.2f}')
            clap.feed(peak, time.time())

        if oww is not None:
            audio = (mono * 32767.0).astype(np.int16)
            try:
                prediction = oww.predict(audio)
            except Exception:
                return
            score = prediction.get(WAKE_MODEL_NAME, 0.0)
            if WAKE_DEBUG and score > 0.1:
                print(f'[JARVIS][debug] hey_jarvis score={score:.2f}')
            if score > WAKE_THRESHOLD:
                now = time.time()
                if now - last_trigger[0] > WAKE_COOLDOWN_SEC:
                    last_trigger[0] = now
                    trigger_wake('"hey jarvis"')

    if oww is not None and clap is not None:
        print('[JARVIS] "hey jarvis" 라고 말하거나 박수를 2번 치면 화면이 열립니다. (마이크 대기 중)')
    elif clap is not None:
        print('[JARVIS] 박수를 2번 치면 화면이 열립니다. (마이크 대기 중, 화면은 꺼져 있습니다)')
    else:
        print('[JARVIS] "hey jarvis" 라고 말하면 화면이 열립니다. (마이크 대기 중)')

    try:
        with sd.InputStream(channels=1, samplerate=WAKE_SAMPLE_RATE,
                             blocksize=WAKE_CHUNK_SAMPLES, dtype="float32",
                             callback=on_audio):
            while True:
                time.sleep(0.1)
    except Exception as e:
        print(f"[JARVIS] 마이크를 열지 못해 음성/박수 감지를 쓸 수 없습니다: {e}")
        print("         마이크 장치/권한을 확인하거나, 브라우저에서 직접 http://localhost:5005/ 를 열어주세요.")


SECURITY_CHECK_INTERVAL_SEC = 300
SECURITY_REALERT_SEC = 1200

SECURITY_LOCK = threading.Lock()
SECURITY_PENDING = []
_SECURITY_LAST_ALERTED = {}
_SECURITY_SEEN_THREATS = set()


def check_security():
    issues = []
    script = (
        "$mp = Get-MpComputerStatus -ErrorAction SilentlyContinue | "
        "Select-Object RealTimeProtectionEnabled, AntivirusEnabled; "
        "$fw = Get-NetFirewallProfile -ErrorAction SilentlyContinue | Select-Object Name, Enabled; "
        "$th = Get-MpThreatDetection -ErrorAction SilentlyContinue | "
        "Select-Object ThreatID, ThreatName; "
        "@{defender=$mp; firewall=@($fw); threats=@($th)} | ConvertTo-Json -Compress -Depth 4"
    )
    data = run_powershell_json(script, timeout=20)
    if not data:
        return issues

    defender = data.get("defender") or {}
    if defender.get("RealTimeProtectionEnabled") is False:
        issues.append(("defender_realtime_off", "Windows Defender 실시간 보호가 꺼져 있습니다."))
    if defender.get("AntivirusEnabled") is False:
        issues.append(("defender_off", "Windows Defender 백신이 꺼져 있습니다."))

    firewall = data.get("firewall") or []
    if isinstance(firewall, dict):
        firewall = [firewall]
    for profile in firewall:
        if profile.get("Enabled") in (False, 0, "False", "0"):
            name = profile.get("Name") or "알 수 없는"
            issues.append((f"firewall_off_{name}", f"{name} 네트워크 방화벽이 꺼져 있습니다."))

    threats = data.get("threats") or []
    if isinstance(threats, dict):
        threats = [threats]
    for threat in threats:
        tid = str(threat.get("ThreatID") or "")
        if tid and tid not in _SECURITY_SEEN_THREATS:
            _SECURITY_SEEN_THREATS.add(tid)
            tname = threat.get("ThreatName") or "알 수 없는 위협"
            issues.append((f"threat_{tid}", f"Windows Defender가 새로운 위협을 탐지했습니다: {tname}"))

    return issues


def queue_security_alerts(issues):
    now = time.time()
    to_announce = []
    with SECURITY_LOCK:
        current_keys = {key for key, _ in issues}
        for key, message in issues:
            last = _SECURITY_LAST_ALERTED.get(key, 0)
            if now - last > SECURITY_REALERT_SEC:
                _SECURITY_LAST_ALERTED[key] = now
                to_announce.append(message)
        for key in list(_SECURITY_LAST_ALERTED.keys()):
            if key not in current_keys and not key.startswith("threat_"):
                del _SECURITY_LAST_ALERTED[key]
        if to_announce:
            SECURITY_PENDING.extend(to_announce)

    if to_announce:
        print("[JARVIS] 보안 경고: " + " / ".join(to_announce))
        if not tab_likely_open():
            open_dashboard(awake=True)


def consume_security_pending():
    with SECURITY_LOCK:
        pending = SECURITY_PENDING[:]
        SECURITY_PENDING.clear()
        return pending


def security_worker():
    time.sleep(120)
    while True:
        try:
            queue_security_alerts(check_security())
        except Exception as e:
            print(f"[JARVIS] 보안 점검 중 오류: {e}")
        time.sleep(SECURITY_CHECK_INTERVAL_SEC)


WAIT_FOR_WAKE = False


def clap_wake_worker():
    try:
        import jarvis_wake
    except Exception as e:
        print(f"[JARVIS] 박수/Hey Jarvis 대기를 못 켜서 화면을 바로 엽니다. ({e})")
        print("         pip install sounddevice numpy openwakeword")
        open_dashboard()
        return
    jarvis_wake.DEBUG = "--debug" in sys.argv
    print('[JARVIS] 대기 중이에요. 박수 2번 짝짝 또는 "Hey Jarvis" 하면 자비스 화면이 열립니다.')
    print("         (바로 열려면 브라우저에서 http://localhost:%d/ )" % PORT)

    def on_wake(_reason):
        if not tab_likely_open():
            open_dashboard()

    try:
        jarvis_wake.run(on_wake=on_wake, is_tab_open=tab_likely_open)
    except Exception as e:
        print(f"[JARVIS] 마이크를 열지 못해 화면을 바로 엽니다. ({e})")
        open_dashboard()


class JarvisHTTPServer(ThreadingHTTPServer):
    allow_reuse_address = False
    daemon_threads = True

    def server_bind(self):
        if os.name == "nt" and hasattr(socket, "SO_EXCLUSIVEADDRUSE"):
            self.socket.setsockopt(socket.SOL_SOCKET, socket.SO_EXCLUSIVEADDRUSE, 1)
        super().server_bind()


class PhoneHTTPServer(JarvisHTTPServer):
    phone = True

    def __init__(self, addr, handler, ctx):
        self._ctx = ctx
        super().__init__(addr, handler)

    def get_request(self):
        sock, addr = self.socket.accept()
        return self._ctx.wrap_socket(sock, server_side=True, do_handshake_on_connect=False), addr

    def finish_request(self, request, client_address):
        try:
            request.settimeout(15)
            request.do_handshake()
        except (ssl.SSLError, OSError):
            return
        super().finish_request(request, client_address)

    def handle_error(self, request, client_address):
        pass


def start_phone_server():
    if not PHONE_ENABLED:
        return
    try:
        if not ensure_phone_cert():
            return
        ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        ctx.minimum_version = ssl.TLSVersion.TLSv1_2
        ctx.load_cert_chain(PHONE_CERT, PHONE_KEY)
        _phone_load_sessions()
        srv = PhoneHTTPServer(("0.0.0.0", PHONE_PORT), Handler, ctx)
    except OSError as e:
        print(f"[JARVIS] 핸드폰 연결 문(포트 {PHONE_PORT})을 열지 못했어요: {e}")
        return
    except Exception as e:
        print(f"[JARVIS] 핸드폰 연결 준비 실패: {type(e).__name__}: {e}")
        return
    ips = lan_ips()
    if ips:
        print(f"[JARVIS] 📱 핸드폰 연결: 같은 와이파이에서 폰 브라우저로 https://{ips[0]}:{PHONE_PORT}")
        print("         (처음엔 '안전하지 않음' 경고 → 고급/세부정보 → 계속. 비밀번호는 체험 모드 끄는 비밀번호)")
    threading.Thread(target=srv.serve_forever, daemon=True).start()


def main():
    install_crash_logging(JARVIS_VERSION)
    _load_gemini_usage()
    _load_chat_history()
    _load_location()
    _load_reply_lang()
    _load_tts_rate()
    _load_spk_threshold()
    if HAVE_SPK:
        _load_voiceprint()
        if voiceprint_ready() and SPEAKER_CHECK:
            print(f"[JARVIS] 보스 목소리로만 반응해요 (등록된 목소리 {len(_SPK['samples'])}개, 기준 {SPEAKER_THRESHOLD}).")
        elif not SPEAKER_CHECK:
            print("[JARVIS] 목소리 확인은 꺼 두었어요. 보스 모드도 체험 모드처럼 들어요.")
        threading.Thread(target=lambda: _spk_extractor(), daemon=True).start()
    print(f"[JARVIS] 설치된 프로그램 {len(PROGRAM_INDEX)}개를 찾았습니다.")
    if not HAVE_PSUTIL:
        print("[JARVIS] 참고: psutil이 설치되어 있지 않아 CPU/메모리 표시와 프로그램 종료 기능이 동작하지 않습니다.")
        print("         pip install psutil --break-system-packages 로 설치하면 사용할 수 있습니다.")

    threading.Thread(target=file_index_worker, daemon=True).start()
    threading.Thread(target=prewarm_tts, daemon=True).start()
    _CLAUDE_POOL.submit(claude_prewarm)

    try:
        server = JarvisHTTPServer(("127.0.0.1", PORT), Handler)
    except OSError:
        print(f"[JARVIS] 포트 {PORT}를 이미 쓰고 있어요. 자비스가 벌써 켜져 있는 것 같아요. 이 창은 닫아도 돼요.")
        _crash_note(f"[시작 안 함] 포트 {PORT}가 이미 사용 중 (자비스가 이미 켜져 있음)")
        return
    mark_server_running()
    start_phone_server()
    url = f"http://localhost:{PORT}/"
    print(f"[JARVIS] 서버 시작: {url}")
    print("[JARVIS] 종료하려면 이 창에서 Ctrl+C 를 누르세요.")

    if ENABLE_PY_WAKE:
        threading.Thread(target=wake_word_worker, daemon=True).start()
    elif WAIT_FOR_WAKE:
        threading.Thread(target=clap_wake_worker, daemon=True).start()
    else:
        threading.Thread(target=lambda: (time.sleep(0.3), open_dashboard()), daemon=True).start()
    threading.Thread(target=security_worker, daemon=True).start()

    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\n[JARVIS] 서버를 끌게요.")
        server.shutdown()


if __name__ == "__main__":
    main()
