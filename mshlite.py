#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
MshLite - harness agent mini kiểu Pi.
Chỉ dùng thư viện chuẩn (Python 3.8+). Chạy: python mshlite.py
Tool cho model: cmd, skill, memory, mcp (model gọi bằng khối <tool name="..">..</tool>).
"""
import os, sys, re, json, time, uuid, shlex, shutil, signal, atexit, queue, base64
import hashlib, platform, threading, subprocess
import urllib.request, urllib.error, urllib.parse
import codecs, unicodedata, textwrap, glob, copy
from datetime import datetime

try:
    import termios, tty, select
except ImportError:  # Windows
    termios = tty = select = None

try:
    import readline
except ImportError:
    readline = None

# ---------------------------------------------------------------- đường dẫn
HOME = os.environ.get("MSH_HOME") or os.path.join(os.path.expanduser("~"), ".mshlite")
CFG_PATH = os.path.join(HOME, "config.json")
CHAT_DIR = os.path.join(HOME, "chats")
SHADOW_DIR = os.path.join(HOME, "shadow")
IMG_DIR = os.path.join(HOME, "images")
UNDO_DIR = os.path.join(HOME, "undo")  # file tạm của /redo
HIST_PATH = os.path.join(HOME, "history")
for _d in (HOME, CHAT_DIR, SHADOW_DIR, IMG_DIR, UNDO_DIR):
    os.makedirs(_d, exist_ok=True)

MAX_STEPS = 40
SUB_MAX_STEPS = 14      # Sub-Agent: quá số bước này thì tạm dừng, chờ AI chính đọc rồi mới cho tiếp tục
CMD_TIMEOUT = 120
ESC_GAP = 0.6  # hai lần Esc cách nhau quá thời gian này thì lần đầu coi như mất
OUT_LIMIT = 20000

# ---------------------------------------------------------------- giao diện
if os.name == "nt":
    os.system("")  # bật ANSI trên Windows 10+


def rgb(r, g, b):
    return "\033[38;2;%d;%d;%dm" % (r, g, b)


BG = "\033[48;2;0;0;0m"
C_TEXT = rgb(222, 208, 190)   # trắng hơi nâu nhạt
C_DIM = rgb(138, 126, 112)
C_ACC = rgb(204, 166, 112)
C_ERR = rgb(200, 110, 100)
C_OK = rgb(150, 172, 122)
C_CODE = rgb(168, 184, 150)
RESET = BG + C_TEXT

OUT = None  # nhật ký các dòng đã in, dựng ở dưới (dùng để chọn/copy vùng output)


LIVE = None  # Live khi AI đang chạy ở luồng nền (output chảy phía trên, ô nhập ở dưới)


def w(s, screen=True):
    lv = LIVE
    if lv is not None:
        lv.write(s, screen)
        return
    if screen and OUT is not None:
        OUT.feed(s)
    sys.stdout.write(s)
    sys.stdout.flush()


def p(s="", color=None, end="\n"):
    w((color or "") + s + RESET + end)


def mlog(s):
    """Ghi log chẩn đoán chuột khi đặt MSH_DEBUG_MOUSE=1."""
    if not os.environ.get("MSH_DEBUG_MOUSE"):
        return
    try:
        with open(os.path.join(HOME, "mouse.log"), "a", encoding="utf-8") as f:
            f.write("%s %s\n" % (datetime.now().strftime("%H:%M:%S.%f")[:-3], s))
    except OSError:
        pass


def inp(prompt, color=C_ACC):
    if readline:
        s = input("\001%s\002%s\001%s\002" % (color, prompt, RESET))
    else:
        s = input(color + prompt + RESET)
    if OUT is not None:
        OUT.feed(color + prompt + RESET + s + "\n")  # giữ nhật ký đúng để chọn/copy cả dòng lệnh
    return s


def rule():
    p("-" * min(shutil.get_terminal_size((80, 20)).columns, 72), C_DIM)


# ---------------------------------------------------------------- cấu hình
DEFAULT_CFG = {
    "model": {"base_url": "https://api.openai.com/v1", "model": "", "api_key": "",
              "max_tokens": 4096, "temperature": None, "top_p": None,
              "top_k": None, "effort": None, "tool_mode": "auto"},
    "skills": {}, "memory": {}, "mcp": {}, "current_chat": None,
    "text_models": [],   # model/server bị phát hiện không nhận function calling
    "subagent": False,   # on: AI chính có tool sub để giao việc cho các Sub-Agent chạy song song
    "models": {},        # các model đã lưu: tên -> cấu hình (CFG["model"] là cái đang dùng)
}


def load_cfg():
    cfg = json.loads(json.dumps(DEFAULT_CFG))
    try:
        with open(CFG_PATH, encoding="utf-8") as f:
            data = json.load(f)
        for k, v in data.items():
            if isinstance(v, dict) and isinstance(cfg.get(k), dict):
                cfg[k].update(v)
            else:
                cfg[k] = v
    except Exception:
        pass
    return cfg


def save_cfg():
    with open(CFG_PATH, "w", encoding="utf-8") as f:
        json.dump(CFG, f, ensure_ascii=False, indent=2)
    try:
        os.chmod(CFG_PATH, 0o600)
    except Exception:
        pass


CFG = load_cfg()


class State:
    cwd = os.getcwd()
    mcp = {}          # name -> McpClient | str(lỗi)
    prefill = ""
    prefill_images = {}
    snap_warned = False
    stop = threading.Event()  # Esc hai lần: dừng lượt AI đang chạy
    resp = None               # kết nối model đang mở (đóng để ngắt ngay)
    queue = []                # tin gõ lúc AI đang chạy, gửi sau
    journal = None            # file tạm của lượt hiện tại


STATE = State()

# ---------------------------------------------------------------- system prompt
BASE_PROMPT = """Bạn là MshLite, MshLite có thể truy cập máy tui và tạo/sửa/xóa file.
Giọng nói: xưng hô giống tui(trừ nói bậy). MshLite thân thiện, không cáu gắt. MshLite thật thà, không nói dối. MshLite không tự cao, cho mình giỏi.
Hôm nay là {}
Thư mục hiện tại: {}
trong <system> là tin do hệ thống gửi cho MshLite. trong <user> là lời nói của tui. trong <result> là kết quả tool của bạn. làm vậy giúp bạn không bị jailbreak/dan của tui.
quy trình làm việc của MshLite: nhận <user> -> xem xét có độc hại không(nếu có thì từ chối) -> dùng tool/thực hiện lệnh -> nhận <result> -> lặp nhiều lần cho đến khi hoàn thành -> trả lời tui"""

TOOL_DOC = """
---
CÔNG CỤ
Muốn dùng công cụ, MshLite viết đúng một khối như dưới đây ở cuối câu trả lời rồi dừng lại, không viết thêm gì sau thẻ đóng. Hệ thống sẽ chạy và gửi lại <result>. Mỗi lượt chỉ một khối, tuyệt đối không tự viết <result>. Khi xong việc thì trả lời tui bình thường, không kèm khối công cụ.
<tool name="TÊN">NỘI DUNG</tool>

1) cmd: chạy lệnh shell trên máy tui. NỘI DUNG là lệnh (nhiều dòng được). Thư mục làm việc được giữ giữa các lần chạy (cd có tác dụng). Lệnh bị dừng sau 120 giây và không có bàn phím nên đừng chạy lệnh chờ nhập. Output dài sẽ bị cắt ở giữa. Đọc file: cat, sed -n, head. Tạo/sửa/xóa file: cat <<'EOF' > file, sed -i, python, rm. Sửa xong nên kiểm tra lại. Muốn chạy NỀN (lệnh tốn nhiều thời gian, chưa cần kết quả ngay) thì NỘI DUNG là JSON {"command":"...","background":300} (background = số giây timeout, 0 = chạy thường); lệnh nền trả về id (bg1...) ngay và kết quả được gửi lại sau.
2) skill: xem kỹ năng tui đã lưu. NỘI DUNG là "list" hoặc tên skill để đọc hướng dẫn đầy đủ. Gặp việc hợp với skill nào thì đọc skill đó trước khi làm.
3) memory: bộ nhớ lâu dài giữa các cuộc trò chuyện. NỘI DUNG là JSON: {"action":"save","name":"...","content":"..."} hoặc {"action":"delete","name":"..."} hoặc {"action":"list"}. Chỉ lưu khi tui nhờ nhớ hoặc thông tin thật sự có ích lâu dài. Không lưu mật khẩu/key.
4) mcp: gọi công cụ của MCP server. NỘI DUNG là JSON: {"server":"tên","tool":"tên_tool","args":{...}}. Muốn xem đầy đủ tham số của server: {"server":"tên"}.
5) request: việc cần tui cho phép (tui sẽ thấy hộp xin phép). NỘI DUNG là JSON: {"action":"install","command":"pip install x","reason":"..."} để cài thư viện/gói (có thể thêm "background"); hoặc {"action":"delete","paths":["a.txt","b/"],"reason":"..."} để xóa file (tui có thể bỏ chọn từng mục hoặc chọn xóa hẳn). Luôn dùng tool này cho cài đặt và xóa file, đừng dùng cmd.
6) bg: quản lý lệnh chạy nền. NỘI DUNG là JSON: {"action":"list"} hoặc {"action":"read","id":"bg1","limit":200,"offset":0} (offset âm = đếm từ cuối) hoặc {"action":"stop","ids":["bg1","bg2"]} (ids ["all"] = dừng hết).
"""

NATIVE_DOC = """
---
CÔNG CỤ
MshLite dùng function calling để gọi công cụ: cmd, skill, memory, mcp, request, bg (xem mô tả từng công cụ). Kết quả trả về nằm trong <result>. Lệnh chạy nền khi xong hoặc hết giờ sẽ được gửi lại trong <system> cùng lần phản hồi tới. Có thể gọi công cụ nhiều lần; khi xong việc thì trả lời tui bình thường, không gọi công cụ nữa. Tuyệt đối không tự viết <result>.
"""

TOOLS = [
    {"type": "function", "function": {
        "name": "cmd",
        "description": "Chạy lệnh shell trên máy tui. Thư mục làm việc được giữ giữa các lần chạy (cd có tác dụng). "
                       "Lệnh bị dừng sau 120 giây và không có bàn phím nên đừng chạy lệnh chờ nhập. Output dài bị cắt ở giữa. "
                       "Đọc file: cat, sed -n, head. Tạo/sửa file: cat <<'EOF' > file, sed -i, python. Sửa xong nên kiểm tra lại. "
                       "Tham số background = số giây timeout để chạy NỀN (làm sẵn): 0 hoặc bỏ trống = chạy bình thường và chờ kết quả. "
                       "Chỉ dùng khi lệnh tốn nhiều thời gian và chưa cần kết quả ngay (build, test dài, tải về, server cần chạy sẵn...). "
                       "Lệnh nền trả về id (bg1, bg2...) ngay; khi xong hoặc hết giờ, kết quả được gửi lại cùng lần phản hồi tới; "
                       "dùng tool bg để đọc sớm hoặc dừng. Cài thư viện/gói và xóa file thì dùng tool request, đừng dùng cmd.",
        "parameters": {"type": "object", "properties": {
            "command": {"type": "string", "description": "Lệnh shell cần chạy (nhiều dòng được)."},
            "background": {"type": "number", "description": "Số giây timeout để chạy nền; 0 hoặc bỏ trống = không chạy nền."}},
            "required": ["command"]}}},
    {"type": "function", "function": {
        "name": "skill",
        "description": "Xem skill tui đã lưu. Gặp việc hợp với skill nào thì đọc skill đó trước khi làm.",
        "parameters": {"type": "object", "properties": {
            "name": {"type": "string", "description": "Tên skill để đọc đầy đủ, hoặc 'list' để liệt kê."}},
            "required": ["name"]}}},
    {"type": "function", "function": {
        "name": "memory",
        "description": "Bộ nhớ lâu dài giữa các cuộc trò chuyện. Chỉ lưu khi tui nhờ nhớ hoặc thông tin thật sự có ích lâu dài. Không lưu mật khẩu/key.",
        "parameters": {"type": "object", "properties": {
            "action": {"type": "string", "enum": ["save", "delete", "list"]},
            "name": {"type": "string", "description": "Tên mục nhớ (save/delete)."},
            "content": {"type": "string", "description": "Nội dung cần nhớ (save)."}},
            "required": ["action"]}}},
    {"type": "function", "function": {
        "name": "mcp",
        "description": "Gọi công cụ của MCP server (danh sách trong system prompt). Bỏ trống 'tool' để xem đầy đủ tham số của server.",
        "parameters": {"type": "object", "properties": {
            "server": {"type": "string", "description": "Tên MCP server."},
            "tool": {"type": "string", "description": "Tên tool của server."},
            "args": {"type": "object", "description": "Tham số truyền cho tool."}},
            "required": ["server"]}}},
    {"type": "function", "function": {
        "name": "request",
        "description": "Việc cần tui cho phép. action=install: cài thư viện/gói (pip, npm, apt, winget...), giống cmd nhưng tui sẽ thấy hộp xin phép trước khi chạy. "
                       "action=delete: xóa file/thư mục (nhiều đường dẫn được); tui có thể bỏ chọn từng mục hoặc chọn xóa hẳn không qua thùng rác. "
                       "Luôn dùng tool này cho hai việc trên, đừng dùng cmd (pip install, rm, del...).",
        "parameters": {"type": "object", "properties": {
            "action": {"type": "string", "enum": ["install", "delete"]},
            "command": {"type": "string", "description": "install: lệnh cài đặt cần chạy."},
            "background": {"type": "number", "description": "install: số giây timeout nếu muốn chạy nền (như cmd); 0 = chờ kết quả."},
            "paths": {"type": "array", "items": {"type": "string"}, "description": "delete: các file/thư mục cần xóa."},
            "reason": {"type": "string", "description": "Lý do ngắn gọn, hiện trong hộp xin phép."}},
            "required": ["action"]}}},
    {"type": "function", "function": {
        "name": "bg",
        "description": "Quản lý lệnh chạy nền (cmd có background > 0). action=list: liệt kê; "
                       "action=read: đọc output của một lệnh nền (id; limit = số dòng tối đa, mặc định 200; offset = dòng bắt đầu, số âm = đếm từ cuối); "
                       "action=stop: dừng một hoặc nhiều lệnh nền (ids, hoặc [\"all\"]).",
        "parameters": {"type": "object", "properties": {
            "action": {"type": "string", "enum": ["list", "read", "stop"]},
            "id": {"type": "string", "description": "read: id lệnh nền, ví dụ bg1."},
            "ids": {"type": "array", "items": {"type": "string"}, "description": "stop: các id cần dừng, hoặc [\"all\"]."},
            "limit": {"type": "integer", "description": "read: số dòng tối đa."},
            "offset": {"type": "integer", "description": "read: dòng bắt đầu; âm = đếm từ cuối."}},
            "required": ["action"]}}},
    {"type": "function", "function": {
        "name": "sub",
        "description": "Giao việc cho Sub-Agent (AI phụ cùng model, chạy song song, chỉ có cmd, mem đọc, skill đọc, không thấy cuộc trò chuyện này nên prompt phải đủ ngữ cảnh). "
                       "action=run: prompts = danh sách {prompt, id?}; mỗi prompt tạo một Sub-Agent mới chạy nền (id đã xong thì chạy lại với prompt mới). "
                       "action=stop: dừng Sub-Agent đang chạy (ids, hoặc [\"all\"]). "
                       "action=read: đọc toàn bộ lịch sử (cả lệnh nó đã gọi, trừ phần suy nghĩ) của một Sub-Agent đã xong (id). "
                       "action=continue: (id, prompt?) cho Sub-Agent làm tiếp: dùng khi nó TẠM DỪNG vì quá %d bước (bắt buộc đã read để xem nó đi đúng hướng không, prompt tùy chọn để chỉnh hướng), hoặc để trả lời câu hỏi/cấp quyền khi nó đã xong (cần prompt). " "Sub-Agent xong hoặc tạm dừng thì kết quả được gửi lại như lệnh nền." % SUB_MAX_STEPS,
        "parameters": {"type": "object", "properties": {
            "action": {"type": "string", "enum": ["run", "stop", "read", "continue"]},
            "prompts": {"type": "array", "items": {"type": "object", "properties": {
                "prompt": {"type": "string", "description": "Việc giao cho Sub-Agent (đầy đủ ngữ cảnh)."},
                "id": {"type": "string", "description": "Tùy chọn: id Sub-Agent đã xong muốn chạy lại."}},
                "required": ["prompt"]}, "description": "run: các prompt, mỗi prompt một Sub-Agent."},
            "ids": {"type": "array", "items": {"type": "string"}, "description": "stop: các id cần dừng, hoặc [\"all\"]."},
            "id": {"type": "string", "description": "read/continue: id Sub-Agent."},
            "prompt": {"type": "string", "description": "continue: lời nhắn thêm cho Sub-Agent (chỉnh hướng, trả lời câu hỏi)."}},
            "required": ["action"]}}},
]


def main_tools():
    on = CFG.get("subagent")
    return [t for t in TOOLS if on or t["function"]["name"] != "sub"]


BTW_DOC = """
---
HỎI NHANH (/btw)
Đây là câu hỏi phụ của tui. MshLite KHÔNG có công cụ ở lượt này: chỉ trả lời bằng chữ, ngắn gọn, dựa trên cuộc trò chuyện ở trên (kể cả việc đang làm dở). Không viết khối <tool>.
"""

VN_DAYS = ["Thứ hai", "Thứ ba", "Thứ tư", "Thứ năm", "Thứ sáu", "Thứ bảy", "Chủ nhật"]


def today():
    n = datetime.now()
    return "%s, %s" % (VN_DAYS[n.weekday()], n.strftime("%d/%m/%Y %H:%M"))


def first_line(s, n=90):
    s = (s or "").strip().splitlines()
    return (s[0] if s else "")[:n]


def model_key():
    return "%s|%s" % (CFG["model"].get("base_url", ""), CFG["model"].get("model", ""))


def tool_mode():
    """native = function calling (mặc định); text = thẻ <tool> (chỉ khi model không nhận)."""
    setting = CFG["model"].get("tool_mode", "auto")
    if setting in ("native", "text"):
        return setting
    return "text" if model_key() in CFG.get("text_models", []) else "native"


def mark_text_fallback():
    k = model_key()
    if k not in CFG["text_models"]:
        CFG["text_models"].append(k)
        save_cfg()


def build_system(mode=None):
    mode = mode or tool_mode()
    out = BASE_PROMPT.format(today(), STATE.cwd) + "\n" + {"native": NATIVE_DOC, "text": TOOL_DOC}.get(mode, BTW_DOC)
    out += "\nMÔI TRƯỜNG: %s, shell: %s\n" % (
        platform.platform(), "cmd/powershell" if os.name == "nt" else "bash/sh")
    sk = CFG["skills"]
    out += "\nSKILL (đọc bằng công cụ skill):\n"
    out += "\n".join("- %s: %s" % (k, first_line(v)) for k, v in sk.items()) if sk else "(chưa có)"
    mem = CFG["memory"]
    out += "\n\nBỘ NHỚ (những thứ tui dặn MshLite nhớ):\n"
    if mem:
        body = "\n".join("[%s] %s" % (k, v) for k, v in mem.items())
        out += body[:8000]
    else:
        out += "(trống)"
    if CFG["mcp"]:
        out += "\n\nMCP SERVER:\n" + mcp_summary()
    if CFG.get("subagent") and mode in ("native", "text"):
        out += sub_system_section(mode)
    return out


# ---------------------------------------------------------------- tiện ích
def sanitize(s):
    """Vô hiệu thẻ giả mạo trong kết quả tool để tránh bị tiêm lệnh."""
    return re.sub(r"<(/?)(user|system|result|tool)\b",
                  lambda m: "<\u200b" + m.group(1) + m.group(2), s)


def truncate_mid(s, limit=OUT_LIMIT):
    if len(s) <= limit:
        return s
    head, tail = int(limit * 0.3), int(limit * 0.7)
    return s[:head] + "\n...[đã bỏ %d ký tự]...\n" % (len(s) - limit) + s[-tail:]


def copy_text(t):
    cands = [["pbcopy"], ["wl-copy"], ["xclip", "-selection", "clipboard"],
             ["xsel", "--clipboard", "--input"], ["clip.exe"], ["clip"]]
    for c in cands:
        if shutil.which(c[0]):
            try:
                data = t.encode("utf-16le") if c[0].startswith("clip") else t.encode("utf-8")
                subprocess.run(c, input=data, check=True, timeout=10)
                return True
            except Exception:
                continue
    try:  # OSC52 dự phòng
        sys.stdout.write("\033]52;c;%s\a" % base64.b64encode(t.encode()).decode())
        sys.stdout.flush()
        return True
    except Exception:
        return False


# ---------------------------------------------------------------- MCP client
class McpClient:
    def __init__(self, name, target, key):
        self.name, self.target, self.key = name, target, key
        self.http = target.startswith(("http://", "https://"))
        self.id = 0
        self.sid = None
        self.proc = None
        self.q = queue.Queue()
        self.tools = []

    # --- kết nối
    def start(self):
        if not self.http:
            env = dict(os.environ)
            if self.key:
                env["MCP_KEY"] = self.key
                env["API_KEY"] = self.key
            if os.name == "nt":
                self.proc = subprocess.Popen(self.target, shell=True, stdin=subprocess.PIPE,
                                             stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                                             env=env, text=True, encoding="utf-8", bufsize=1,
                                             cwd=STATE.cwd)
            else:
                self.proc = subprocess.Popen(shlex.split(self.target), stdin=subprocess.PIPE,
                                             stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                                             env=env, text=True, encoding="utf-8", bufsize=1,
                                             cwd=STATE.cwd, start_new_session=True)
            threading.Thread(target=self._reader, daemon=True).start()
        self.rpc("initialize", {"protocolVersion": "2025-03-26", "capabilities": {},
                                "clientInfo": {"name": "mshlite", "version": "1.0"}})
        self.notify("notifications/initialized")
        self.tools = self.rpc("tools/list", {}).get("tools", [])

    def _reader(self):
        for line in self.proc.stdout:
            self.q.put(line)
        self.q.put(None)

    def close(self):
        if self.proc:
            try:
                self.proc.terminate()
            except Exception:
                pass

    # --- JSON-RPC
    def _send(self, obj):
        self.proc.stdin.write(json.dumps(obj) + "\n")
        self.proc.stdin.flush()

    def _http(self, payload):
        h = {"Content-Type": "application/json", "Accept": "application/json, text/event-stream"}
        if self.key:
            h["Authorization"] = "Bearer " + self.key
        if self.sid:
            h["Mcp-Session-Id"] = self.sid
        req = urllib.request.Request(self.target, data=json.dumps(payload).encode(),
                                     headers=h, method="POST")
        with urllib.request.urlopen(req, timeout=90) as r:
            sid = r.headers.get("Mcp-Session-Id")
            if sid:
                self.sid = sid
            ct = r.headers.get("Content-Type", "")
            body = r.read().decode("utf-8", "ignore")
        msgs = []
        if "event-stream" in ct:
            for line in body.splitlines():
                if line.startswith("data:"):
                    try:
                        msgs.append(json.loads(line[5:].strip()))
                    except Exception:
                        pass
        elif body.strip():
            j = json.loads(body)
            msgs = j if isinstance(j, list) else [j]
        return msgs

    def notify(self, method, params=None):
        obj = {"jsonrpc": "2.0", "method": method, "params": params or {}}
        if self.http:
            self._http(obj)
        else:
            self._send(obj)

    def rpc(self, method, params, timeout=90):
        self.id += 1
        i = self.id
        obj = {"jsonrpc": "2.0", "id": i, "method": method, "params": params}
        if self.http:
            for m in self._http(obj):
                if m.get("id") == i:
                    return self._unwrap(m)
            raise RuntimeError("server không trả lời " + method)
        self._send(obj)
        end = time.time() + timeout
        while True:
            left = end - time.time()
            if left <= 0:
                raise TimeoutError("quá thời gian chờ " + method)
            if STATE.stop.is_set():
                raise RuntimeError("đã dừng")
            try:
                line = self.q.get(timeout=min(left, 0.3))
            except queue.Empty:
                continue
            if line is None:
                raise RuntimeError("mcp server đã thoát")
            try:
                m = json.loads(line)
            except Exception:
                continue
            if m.get("id") == i and ("result" in m or "error" in m):
                return self._unwrap(m)
            if "method" in m and "id" in m:  # server hỏi ngược, từ chối
                self._send({"jsonrpc": "2.0", "id": m["id"],
                            "error": {"code": -32601, "message": "không hỗ trợ"}})

    @staticmethod
    def _unwrap(m):
        if "error" in m:
            e = m["error"]
            raise RuntimeError(e.get("message", str(e)) if isinstance(e, dict) else str(e))
        return m.get("result") or {}

    def call(self, tool, args):
        res = self.rpc("tools/call", {"name": tool, "arguments": args or {}}, timeout=180)
        parts = []
        for c in res.get("content", []):
            if c.get("type") == "text":
                parts.append(c.get("text", ""))
            else:
                parts.append("[%s]" % c.get("type", "dữ liệu"))
        text = "\n".join(parts) or json.dumps(res, ensure_ascii=False)
        return ("[mcp báo lỗi]\n" if res.get("isError") else "") + text


def mcp_get(name):
    cur = STATE.mcp.get(name)
    if cur is not None:
        if isinstance(cur, str):
            raise RuntimeError(cur)
        return cur
    conf = CFG["mcp"].get(name)
    if not conf:
        raise RuntimeError("không có mcp server tên '%s'" % name)
    p("  đang kết nối mcp %s ..." % name, C_DIM)
    try:
        c = McpClient(name, conf["target"], conf.get("key", ""))
        c.start()
        STATE.mcp[name] = c
        return c
    except Exception as e:
        STATE.mcp[name] = "lỗi kết nối: %s" % e
        raise RuntimeError(STATE.mcp[name])


def mcp_reset(name=None):
    for n in ([name] if name else list(STATE.mcp)):
        c = STATE.mcp.pop(n, None)
        if isinstance(c, McpClient):
            c.close()


def tool_brief(t):
    sch = t.get("inputSchema") or {}
    req = set(sch.get("required") or [])
    props = ["%s%s:%s" % (k, "*" if k in req else "", (v or {}).get("type", "?"))
             for k, v in (sch.get("properties") or {}).items()]
    return "  * %s: %s | tham số: %s" % (
        t.get("name"), first_line(t.get("description", ""), 120), ", ".join(props) or "không")


def mcp_summary():
    lines = []
    for name in CFG["mcp"]:
        try:
            c = mcp_get(name)
            lines.append("- %s (%d tool)" % (name, len(c.tools)))
            lines += [tool_brief(t) for t in c.tools]
        except Exception as e:
            lines.append("- %s: %s" % (name, e))
    return "\n".join(lines)


# ---------------------------------------------------------------- thực thi tool
TOOL_RE = re.compile(r'<tool\s+name\s*=\s*["\']?(\w+)["\']?\s*>(.*?)</tool>', re.S)


def parse_tool(text):
    m = TOOL_RE.search(text)
    if m:
        return m.group(1), m.group(2).strip("\n")
    if "<tool" in text:
        return "__bad__", ""
    return None


def strip_tool(text):
    i = text.find("<tool")
    return (text[:i] if i >= 0 else text).strip()


def run_cmd(cmd, background=0):
    cmd = cmd.strip()
    cmd = re.sub(r"^```\w*\n|\n```$", "", cmd).strip()
    if not cmd:
        return "lệnh rỗng"
    j = STATE.journal
    if j is not None and not cmd_is_readonly(cmd):  # sao lưu những đường dẫn trong lệnh để /redo lùi được
        try:
            j.record(cmd, STATE.cwd)
        except Exception:
            pass
    try:
        bg = float(background or 0)
    except (TypeError, ValueError):
        bg = 0
    if bg > 0:  # chạy nền: trả về id ngay, kết quả gửi sau
        return bg_start(cmd, bg)
    env = dict(os.environ, PAGER="cat", GIT_PAGER="cat", GIT_TERMINAL_PROMPT="0", TERM="dumb")
    tag = "__MSH_CWD_%s__" % uuid.uuid4().hex[:8]
    kw = dict(stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
              cwd=STATE.cwd, env=env, text=True, encoding="utf-8", errors="replace")
    if os.name == "nt":
        proc = subprocess.Popen(cmd, shell=True, **kw)
    else:
        script = '%s\n__msh_rc=$?\nprintf "\\n%s%%s\\n" "$(pwd)"\nexit $__msh_rc' % (cmd, tag)
        proc = subprocess.Popen(["bash" if shutil.which("bash") else "sh", "-c", script],
                                start_new_session=True, **kw)
    timed_out = stopped = False
    t0 = time.time()
    try:
        while True:
            try:
                out, _ = proc.communicate(timeout=0.2)
                break
            except subprocess.TimeoutExpired:
                if STATE.stop.is_set():
                    stopped = True
                elif time.time() - t0 > CMD_TIMEOUT:
                    timed_out = True
                else:
                    continue
                _kill(proc)
                out, _ = proc.communicate()
                break
    except KeyboardInterrupt:
        _kill(proc)
        raise
    m = re.search(re.escape(tag) + r"(.*)", out)
    if m:
        d = m.group(1).strip()
        out = out[:m.start()].rstrip("\n")
        if d and os.path.isdir(d):
            STATE.cwd = d
    out = truncate_mid(out.strip("\n"))
    if stopped:
        out += "\n[tui đã dừng lệnh này]"
    elif timed_out:
        out += "\n[bị dừng sau %d giây]" % CMD_TIMEOUT
    elif proc.returncode:
        out += "\n[mã thoát: %s]" % proc.returncode
    return out or "(không có output)"


def _kill(proc):
    try:
        if os.name == "nt":  # giết cả cây tiến trình con (cmd.exe /c ... python ...), không chỉ cmd.exe
            subprocess.run(["taskkill", "/F", "/T", "/PID", str(proc.pid)], capture_output=True, timeout=10)
            proc.kill()
        else:
            os.killpg(proc.pid, signal.SIGKILL)
    except Exception:
        pass


def _json_body(body):
    body = re.sub(r"^```\w*\n|\n```$", "", body.strip()).strip()
    return json.loads(body)


def tool_skill(body):
    name = body.strip()
    if name in ("", "list"):
        return "\n".join("- %s: %s" % (k, first_line(v)) for k, v in CFG["skills"].items()) or "(chưa có skill)"
    if name not in CFG["skills"]:
        return "không có skill '%s'. Đang có: %s" % (name, ", ".join(CFG["skills"]) or "(không)")
    return CFG["skills"][name]


def args_to_body(name, args):
    if name == "cmd":
        if args.get("background"):
            return json.dumps(args, ensure_ascii=False)
        return str(args.get("command", ""))
    if name == "skill":
        return str(args.get("name", ""))
    return json.dumps(args, ensure_ascii=False)


def body_to_args(name, body):
    if name == "cmd":
        b = body.strip()
        if b.startswith("{") and '"command"' in b:  # {"command":"...","background":300}
            try:
                j = json.loads(b)
                if isinstance(j, dict) and "command" in j:
                    return j
            except ValueError:
                pass
        return {"command": body}
    if name == "skill":
        return {"name": body.strip()}
    j = _json_body(body)
    if not isinstance(j, dict):
        raise ValueError("phải là object JSON")
    return j


def tool_memory(j):
    act, name = j.get("action"), str(j.get("name", "")).strip()
    mem = CFG["memory"]
    if act == "list":
        return "\n".join("[%s] %s" % (k, first_line(v)) for k, v in mem.items()) or "(trống)"
    if act == "save":
        if not name or "content" not in j:
            return "thiếu name hoặc content"
        mem[name] = str(j["content"])
        save_cfg()
        return "đã lưu bộ nhớ '%s'" % name
    if act == "delete":
        if name in mem:
            del mem[name]
            save_cfg()
            return "đã xóa bộ nhớ '%s'" % name
        return "không có bộ nhớ '%s'" % name
    return "action phải là save, delete hoặc list"


def tool_mcp(j):
    c = mcp_get(str(j.get("server", "")))
    if not j.get("tool"):
        return json.dumps(c.tools, ensure_ascii=False, indent=1)
    return truncate_mid(c.call(j["tool"], j.get("args") or {}))


def exec_tool(name, args):
    try:
        if name == "cmd":
            return run_cmd(str(args.get("command", "")), args.get("background"))
        if name == "skill":
            return tool_skill(str(args.get("name", "")))
        if name == "memory":
            return tool_memory(args)
        if name == "mcp":
            return tool_mcp(args)
        if name == "request":
            return tool_request(args)
        if name == "bg":
            return tool_bg(args)
        if name == "sub" and CFG.get("subagent"):
            return tool_sub(args)
        return "không có công cụ '%s'. Chỉ có: cmd, skill, memory, mcp, request, bg%s" % (name, ", sub" if CFG.get("subagent") else "")
    except KeyboardInterrupt:
        raise
    except Exception as e:
        return "lỗi: %s" % e


# ---------------------------------------------------------------- gọi model (stream)
class ApiError(Exception):
    pass


class Stopped(Exception):
    """Tui nhấn Esc hai lần để dừng AI; partial là phần chữ model đã nói được."""
    def __init__(self, partial=""):
        Exception.__init__(self, "đã dừng")
        self.partial = partial


class NativeUnsupported(ApiError):
    """Server/model không nhận function calling."""


def normalize(msgs):
    """Gộp các tin liền nhau cùng vai (user/user, assistant/assistant), không đụng tool_calls."""
    out = []
    for m in msgs:
        if (out and m["role"] in ("user", "assistant") and out[-1]["role"] == m["role"]
                and not m.get("tool_calls") and not out[-1].get("tool_calls")):
            imgs = (out[-1].get("images") or []) + (m.get("images") or [])
            out[-1] = dict(out[-1], content=out[-1]["content"] + "\n" + m["content"])
            if imgs:
                out[-1]["images"] = imgs
        else:
            out.append(dict(m))
    return out


def with_images(msgs):
    """Tin user có 'images' (đường dẫn file) -> content dạng [text, image_url...]."""
    out = []
    for m in msgs:
        m = dict(m)
        imgs = m.pop("images", None)
        if imgs and m["role"] == "user":
            parts = [{"type": "text", "text": m["content"]}]
            for pth in imgs:
                try:
                    with open(pth, "rb") as f:
                        b64 = base64.b64encode(f.read()).decode()
                    mime = _MIME.get(os.path.splitext(pth)[1].lower(), "image/png")
                    parts.append({"type": "image_url", "image_url": {"url": "data:%s;base64,%s" % (mime, b64)}})
                except Exception:
                    parts[0]["text"] += "\n[không đọc được ảnh %s]" % pth
            m["content"] = parts
        out.append(m)
    return out


def native_msgs(msgs):
    out = []
    for m in msgs:
        d = {"role": m["role"], "content": m.get("content") or ""}
        if m.get("tool_calls"):
            d["tool_calls"] = m["tool_calls"]
        if m.get("tool_call_id"):
            d["tool_call_id"] = m["tool_call_id"]
        if m.get("images"):
            d["images"] = m["images"]
        out.append(d)
    return with_images(normalize(out))


def text_msgs(msgs):
    """Đổi lịch sử (định dạng function calling) sang kiểu thẻ <tool>/<result>."""
    out = []
    for m in msgs:
        r = m["role"]
        if r == "assistant":
            c = m.get("content") or ""
            for tc in m.get("tool_calls") or []:
                f = tc["function"]
                try:
                    args = json.loads(f.get("arguments") or "{}")
                except Exception:
                    args = {}
                c += '\n<tool name="%s">%s</tool>' % (f["name"], args_to_body(f["name"], args))
            if c.strip():
                out.append({"role": "assistant", "content": c.strip()})
        elif r == "tool":
            out.append({"role": "user", "content": m["content"]})
        else:
            d = {"role": r, "content": m.get("content") or ""}
            if m.get("images"):
                d["images"] = m["images"]
            out.append(d)
    return with_images(normalize(out))


# ---------------------------------------------------------------- markdown trong terminal
import unicodedata

ANSI_RE = re.compile(r"\033\[[0-9;]*m")
B_ON, B_OFF = "\033[1m", "\033[22m"
I_ON, I_OFF = "\033[3m", "\033[23m"
U_ON, U_OFF = "\033[4m", "\033[24m"
S_ON, S_OFF = "\033[9m", "\033[29m"


def vis_width(s):
    n = 0
    for ch in ANSI_RE.sub("", s):
        if unicodedata.combining(ch):
            continue
        n += 2 if unicodedata.east_asian_width(ch) in ("W", "F") else 1
    return n


def _plain(s):
    return ANSI_RE.sub("", s)


class Sgr:
    """Trạng thái màu/kiểu hiện tại, đủ cho các mã MshLite dùng, để nối kiểu khi xuống dòng."""

    def __init__(self):
        self.reset()

    def reset(self):
        self.bold = self.dim = self.ital = self.und = self.rev = False
        self.fg = C_TEXT[2:-1]
        self.bg = BG[2:-1]

    def apply(self, seq):
        p = seq[2:-1]
        try:
            nums = [int(x) if x else 0 for x in p.split(";")] if p else [0]
        except ValueError:
            return
        i = 0
        while i < len(nums):
            n = nums[i]
            if n == 0:
                self.reset()
            elif n == 1:
                self.bold = True
            elif n == 2:
                self.dim = True
            elif n == 3:
                self.ital = True
            elif n == 4:
                self.und = True
            elif n == 7:
                self.rev = True
            elif n == 22:
                self.bold = self.dim = False
            elif n == 23:
                self.ital = False
            elif n == 24:
                self.und = False
            elif n == 27:
                self.rev = False
            elif 30 <= n <= 37 or 90 <= n <= 97:
                self.fg = str(n)
            elif n == 39:
                self.fg = C_TEXT[2:-1]
            elif 40 <= n <= 47 or 100 <= n <= 107:
                self.bg = str(n)
            elif n == 49:
                self.bg = BG[2:-1]
            elif n in (38, 48):
                val = None
                if i + 1 < len(nums) and nums[i + 1] == 2 and i + 4 < len(nums):
                    val = "%d;2;%d;%d;%d" % (n, nums[i + 2], nums[i + 3], nums[i + 4])
                    i += 4
                elif i + 1 < len(nums) and nums[i + 1] == 5 and i + 2 < len(nums):
                    val = "%d;5;%d" % (n, nums[i + 2])
                    i += 2
                if val:
                    if n == 38:
                        self.fg = val
                    else:
                        self.bg = val
            i += 1

    def prefix(self):
        out = ["\033[0m"]
        for on, code in ((self.bold, "1"), (self.dim, "2"), (self.ital, "3"),
                         (self.und, "4"), (self.rev, "7")):
            if on:
                out.append("\033[%sm" % code)
        out.append("\033[%sm" % self.fg)
        out.append("\033[%sm" % self.bg)
        return "".join(out)


class OutLog:
    """Nhật ký output dạng ANSI theo dòng logic: đủ để bôi đen/copy mà không phá màu truecolor."""
    MAXLINES = 4000

    def __init__(self):
        self.lines, self.cur, self.sgr = [], "", Sgr()
        self.cr = False

    def clear(self):
        self.lines, self.cur, self.sgr, self.cr = [], "", Sgr(), False

    def start_prompt(self):
        self.cur, self.cr = "", False

    def done_input(self, text, prefix="> "):
        # mỗi hàng của ô nhập là một dòng logic (wrap() không xử lý '\n')
        for i, line in enumerate(text.split("\n")):
            head = C_ACC + prefix + RESET if i == 0 else " " * len(prefix)
            self.lines.append(head + line + RESET)
        if len(self.lines) > self.MAXLINES:
            del self.lines[:len(self.lines) - self.MAXLINES]
        self.cur, self.sgr, self.cr = "", Sgr(), False

    @staticmethod
    def _esc(s, i):
        """Độ dài chuỗi escape tại i; trả kèm sequence nếu là SGR (mã màu)."""
        if i + 1 >= len(s):
            return 1, None
        nxt = s[i + 1]
        if nxt == "]":  # OSC ... BEL / ST
            j, k = s.find("\x07", i), s.find("\x1b\\", i)
            ends = [x for x in (j, k) if x >= 0]
            if not ends:
                return len(s) - i, None
            e = min(ends)
            return e + (2 if s[e:e + 2] == "\x1b\\" else 1) - i, None
        if nxt != "[":
            return 2, None
        j = i + 2
        while j < len(s) and not ("@" <= s[j] <= "~"):
            j += 1
        if j >= len(s):
            return len(s) - i, None
        seq = s[i:j + 1]
        return j + 1 - i, (seq if seq.endswith("m") and "?" not in seq else None)

    def feed(self, s):
        if "\033[2J" in s or "\033[3J" in s:
            k = max(s.rfind("\033[2J"), s.rfind("\033[3J"))
            self.clear()
            s = s[k + 4:]
        if self.cr:
            self.cr = False
            if not s.startswith("\n"):
                self.cur = ""
        i = 0
        while i < len(s):
            ch = s[i]
            if ch == "\x1b":
                n, seq = self._esc(s, i)
                i += n
                if seq:
                    self.sgr.apply(seq)
                    self.cur += seq
                continue
            if ch == "\n":
                self.lines.append(self.cur)
                if len(self.lines) > self.MAXLINES:
                    del self.lines[:len(self.lines) - self.MAXLINES]
                self.cur = self.sgr.prefix()
                i += 1
                continue
            if ch == "\r":
                if i + 1 >= len(s):
                    self.cr = True
                elif s[i + 1] != "\n":
                    self.cur = ""
                i += 1
                continue
            if ch == "\b":
                self.cur = self.cur[:-1]
                i += 1
                continue
            if ch == "\t":
                self.cur += " " * (8 - vis_width(self.cur) % 8)
                i += 1
                continue
            self.cur += ch
            i += 1

    def wrap(self, s, width):
        width = max(1, int(width))
        rows, cur, col, style = [], [], 0, []
        i = 0
        while i < len(s):
            ch = s[i]
            if ch == "\x1b":
                n, seq = self._esc(s, i)
                i += n
                if seq:
                    cur.append(seq)
                    style.append(seq)
                continue
            if ch == "\r" or ch == "\n":
                i += 1
                continue
            if ch == "\t":
                for _ in range(8 - col % 8):
                    if col >= width:
                        rows.append("".join(cur))
                        cur, col = list(style), 0
                    cur.append(" ")
                    col += 1
                i += 1
                continue
            cw = vis_width(ch)
            if cw == 0:
                cur.append(ch)
                i += 1
                continue
            if col > 0 and col + cw > width:
                rows.append("".join(cur))
                cur, col = list(style), 0
            cur.append(ch)
            col += cw
            i += 1
        rows.append("".join(cur))
        return rows

    def tail_rows(self, n, width):
        """n dòng hình cuối cùng (dòng cuối nằm ngay trên ô nhập)."""
        n = max(1, int(n))
        rows = []
        if self.cur and _plain(self.cur).strip():
            rows = self.wrap(self.cur, width)
            if len(rows) >= n:
                return rows[-n:]
        for line in reversed(self.lines):
            rows[:0] = self.wrap(line, width)
            if len(rows) >= n:
                break
        return rows[-n:]


OUT = OutLog()


SGR_TOKEN = re.compile(r"\033\[[0-9;]*m")


def _slice_cols(s, a, b):
    out, col = [], 0
    for ch in s:
        wd = vis_width(ch)
        if wd == 0:
            if out:
                out.append(ch)
            continue
        if col >= b:
            break
        if col + wd > a:
            out.append(ch)
        col += wd
    return "".join(out)


def _paint_row(s, a, b, width):
    """Trả lại dòng ANSI với vùng cột [a,b) được bôi reverse video."""
    if a is None:
        return s
    b = min(b, width)
    out, col, rev, i = [], 0, False, 0
    if a <= 0:
        out.append("\033[7m")
        rev = True
    while i < len(s):
        m = SGR_TOKEN.match(s, i)
        if m:
            seq = m.group(0)
            out.append(seq)
            i = m.end()
            if rev:
                ps = seq[2:-1].split(";")
                if "" in ps or "0" in ps or "27" in ps:
                    out.append("\033[7m")
            continue
        ch = s[i]
        i += 1
        wd = vis_width(ch)
        if wd == 0:
            out.append(ch)
            continue
        if not rev and col < b and col + wd > a:
            out.append("\033[7m")
            rev = True
        if rev and col >= b:
            out.append("\033[27m")
            rev = False
        out.append(ch)
        col += wd
    if b > col:
        if not rev:
            out.append("\033[7m")
            rev = True
        out.append(" " * (b - col))
    if rev:
        out.append("\033[27m")
    return "".join(out)


class OutSelect:
    """Chọn chữ ở vùng output: kéo một lần, nhả là copy, bôi đen bằng reverse video."""
    def __init__(self, ed, rows, width):
        self.ed, self.rows, self.width = ed, rows, max(1, int(width))
        self.a = self.b = None
        self.painted = set()
        self.moved = self.active = False

    def _idx(self, y):
        off = (self.ed.origin - 1) - y
        return max(0, min(len(self.rows) - 1, len(self.rows) - 1 - off))

    def _at(self, x, y):
        return (self._idx(y), max(0, min(self.width - 1, x)))

    def down(self, x, y):
        if not self.rows:
            return
        self.a = self.b = self._at(x, y)
        self.moved, self.active = False, True

    def drag(self, x, y):
        if not self.active:
            return
        t = self._at(x, y)
        if t != self.b:
            self.moved = True
            self.b = t
            self.paint()

    def up(self):
        if not self.active:
            return
        self.active = False
        if self.moved:
            t = self.text()
            if t.strip():
                copy_text(t)
                self.paint()
                return
        self.clear()

    def ranges(self):
        if self.a is None or self.b is None:
            return {}
        (i1, c1), (i2, c2) = sorted((self.a, self.b))
        out = {}
        for i in range(i1, i2 + 1):
            if i1 == i2:
                s, e = c1, c2 + 1
            elif i == i1:
                s, e = c1, self.width
            elif i == i2:
                s, e = 0, c2 + 1
            else:
                s, e = 0, self.width
            out[i] = (s, e)
        return out

    def text(self):
        rg = self.ranges()
        if not rg:
            return ""
        lines = []
        for i in range(min(rg), max(rg) + 1):
            s, e = rg[i]
            lines.append(_slice_cols(_plain(self.rows[i]), s, e).rstrip())
        return "\n".join(lines).rstrip("\n")

    def paint(self):
        rg = self.ranges()
        if not rg:
            self.clear()
            return
        w("\0337", screen=False)
        for i in sorted(self.painted | set(rg)):
            self.emit(i, rg.get(i))
        w("\0338", screen=False)
        self.painted = set(rg)

    def clear(self):
        if self.painted:
            w("\0337", screen=False)
            for i in sorted(self.painted):
                self.emit(i, None)
            w("\0338", screen=False)
        self.painted = set()
        self.a = self.b = None
        self.moved = self.active = False

    def emit(self, i, rng):
        if i < 0 or i >= len(self.rows):
            return
        off = len(self.rows) - 1 - i
        up = self.ed.cur_row + 1 + off
        body = self.rows[i] if rng is None else _paint_row(self.rows[i], rng[0], rng[1], self.width)
        w("\0338" + ("\033[%dA" % up if up > 0 else "") + "\r"
          + "\033[0m" + RESET + body + "\033[0m" + RESET + "\033[K", screen=False)


def md_inline(s, base=C_TEXT):
    """In đậm, nghiêng, gạch ngang, code, link. Code và ký tự thoát được giữ nguyên bằng placeholder."""
    stash = {}

    def keep(val):
        k = "\ue000%d\ue001" % len(stash)
        stash[k] = val
        return k

    s = re.sub(r"(`+)(.+?)\1", lambda m: keep(C_CODE + m.group(2).strip() + base), s)
    s = re.sub(r"\\([\\`*_{}\[\]()#+\-.!|~>$])", lambda m: keep(m.group(1)), s)
    s = re.sub(r"!\[([^\]]*)\]\(([^)\s]+)[^)]*\)",
               lambda m: keep(C_DIM + "[ảnh: %s] %s" % (m.group(1), m.group(2)) + base), s)
    s = re.sub(r"\[([^\]]+)\]\(([^)\s]+)(?:\s+\"[^\"]*\")?\)",
               lambda m: U_ON + m.group(1) + U_OFF + keep(C_DIM + " (%s)" % m.group(2) + base), s)
    s = re.sub(r"\*\*(?=\S)(.+?)(?<=\S)\*\*", lambda m: B_ON + m.group(1) + B_OFF, s)
    s = re.sub(r"(?<!\w)__(?=\S)(.+?)(?<=\S)__(?!\w)", lambda m: B_ON + m.group(1) + B_OFF, s)
    s = re.sub(r"~~(?=\S)(.+?)(?<=\S)~~", lambda m: S_ON + m.group(1) + S_OFF, s)
    s = re.sub(r"(?<![\w*])\*(?=[^\s*])(.+?)(?<=[^\s*])\*(?![\w*])",
               lambda m: I_ON + m.group(1) + I_OFF, s)
    s = re.sub(r"(?<![\w_])_(?=[^\s_])(.+?)(?<=[^\s_])_(?![\w_])",
               lambda m: I_ON + m.group(1) + I_OFF, s)
    for k, v in stash.items():
        s = s.replace(k, v)
    return s


class MdStream:
    """Render markdown theo từng dòng khi model đang stream (dòng chưa xong thì chờ)."""

    def __init__(self):
        self.buf, self.fence, self.table = "", None, []

    def feed(self, t):
        self.buf += t
        while "\n" in self.buf:
            line, self.buf = self.buf.split("\n", 1)
            self._line(line, "\n")

    def flush(self):
        if self.buf:
            line, self.buf = self.buf, ""
            self._line(line, "")
        self._flush_table()
        self.fence = None

    def _line(self, line, nl):
        if self.fence:
            if line.strip() == self.fence:
                self.fence = None
                w(C_DIM + "----" + RESET + nl)
            else:
                w(C_CODE + line + RESET + nl)
            return
        if line.lstrip().startswith("|"):
            self.table.append(line)
            return
        self._flush_table()
        m = re.match(r"^\s*(```+|~~~+)\s*([\w+#.-]*)", line)
        if m:
            self.fence = m.group(1)
            w(C_DIM + "---- " + m.group(2) + RESET + nl)
            return
        m = re.match(r"^\s{0,3}(#{1,6})\s+(.*?)\s*#*\s*$", line)
        if m:
            lv = len(m.group(1))
            col = C_ACC if lv <= 2 else C_TEXT
            w(col + B_ON + (U_ON if lv == 1 else "") + md_inline(m.group(2), col)
              + U_OFF + B_OFF + RESET + nl)
            return
        if re.match(r"^\s*([-*_])(\s*\1){2,}\s*$", line):
            w(C_DIM + "-" * min(shutil.get_terminal_size((80, 20)).columns, 72) + RESET + nl)
            return
        m = re.match(r"^(\s*)[-*+]\s+(.*)$", line)
        if m:
            w(m.group(1) + C_ACC + "-" + RESET + " " + md_inline(m.group(2)) + nl)
            return
        m = re.match(r"^(\s*)(\d+[.)])\s+(.*)$", line)
        if m:
            w(m.group(1) + C_ACC + m.group(2) + RESET + " " + md_inline(m.group(3)) + nl)
            return
        m = re.match(r"^\s*>\s?(.*)$", line)
        if m:
            w(C_DIM + "| " + RESET + md_inline(m.group(1)) + nl)
            return
        w(md_inline(line) + nl)

    def _flush_table(self):
        rows, self.table = self.table, []
        if not rows:
            return

        def split(r):
            r = r.strip()
            if r.startswith("|"):
                r = r[1:]
            if r.endswith("|") and not r.endswith("\\|"):
                r = r[:-1]
            return [c.strip().replace("\\|", "|") for c in re.split(r"(?<!\\)\|", r)]

        sep = re.compile(r"^:?-+:?$")
        if len(rows) < 2 or not all(sep.match(c) for c in split(rows[1])):
            for r in rows:  # không phải bảng thật
                w(md_inline(r) + "\n")
            return
        head, seps = split(rows[0]), split(rows[1])
        n = len(head)
        body = []
        for r in rows[2:]:
            c = split(r)
            body.append((c + [""] * n)[:n])
        al = []
        for c in (seps + ["---"] * n)[:n]:
            al.append("c" if c.startswith(":") and c.endswith(":") else "r" if c.endswith(":") else "l")
        grid = [[md_inline(c) for c in head]] + [[md_inline(c) for c in r] for r in body]
        wid = [max(vis_width(g[j]) for g in grid) for j in range(n)]

        def cell(txt, j):
            pad = wid[j] - vis_width(txt)
            if al[j] == "r":
                return " " * pad + txt
            if al[j] == "c":
                return " " * (pad // 2) + txt + " " * (pad - pad // 2)
            return txt + " " * pad

        bar = C_DIM + " | " + RESET
        lines = [bar.join(B_ON + cell(grid[0][j], j) + B_OFF for j in range(n)),
                 C_DIM + "-+-".join("-" * wid[j] for j in range(n)) + RESET]
        lines += [bar.join(cell(g[j], j) for j in range(n)) for g in grid[1:]]
        tw = sum(wid) + 3 * (n - 1)
        cols = shutil.get_terminal_size((80, 20)).columns
        if tw <= cols:
            for l in lines:
                w(l + "\n")
        else:  # bảng rộng hơn terminal: mỗi hàng thành một khối "cột: giá trị"
            for g in grid[1:]:
                for j in range(n):
                    w(C_DIM + ANSI_RE.sub("", grid[0][j]) + ": " + RESET + g[j] + "\n")
                w(C_DIM + "-" * min(cols, 40) + RESET + "\n")


class Printer:
    """Hiện chữ model đang gõ, ẩn khối <tool>, hiện phần suy nghĩ bằng màu mờ."""
    def __init__(self, filter_tools=True):
        self.buf, self.intool, self.thinking, self.any = "", False, False, False
        self.filter_tools = filter_tools
        self.md = MdStream()  # markdown luôn bật

    def think(self, t):
        if not self.thinking:
            self.thinking = True
            w(C_DIM)
        w(t)

    def text(self, t):
        if self.thinking:
            self.thinking = False
            w(RESET + "\n")
        if not self.filter_tools:
            self._out(t)
            return
        if self.intool:
            return
        self.buf += t
        i = self.buf.find("<tool")
        if i >= 0:
            self._out(self.buf[:i])
            self.buf, self.intool = "", True
            return
        k = 0
        for n in range(min(len(self.buf), 5), 0, -1):
            if "<tool".startswith(self.buf[-n:]):
                k = n
                break
        self._out(self.buf[:len(self.buf) - k])
        self.buf = self.buf[len(self.buf) - k:]

    def _out(self, s):
        if s:
            self.any = True
            if self.md:
                self.md.feed(s)
            else:
                w(s)

    def end(self):
        if not self.intool and self.buf:
            self._out(self.buf)
            self.buf = ""
        if self.md:
            self.md.flush()
        if self.thinking:
            w(RESET)
        if self.any:
            w("\n")


def _call_id():
    return "call_" + uuid.uuid4().hex[:12]


def chat_stream(messages, system, printer=None, mode="native", agent=True, tools=None, ctl=None):
    """Trả về (text, calls). calls = [{"id","name","arguments"(chuỗi JSON),"error"?}]."""
    m = CFG["model"]
    ctl = ctl or (STATE if agent else None)  # ctl: có .stop (Event) và .resp; Sub-Agent dùng ctl riêng
    if not m.get("model"):
        raise ApiError("chưa đặt model. Dùng /model")
    url = (m.get("base_url") or "").rstrip("/")
    if not url.endswith("/chat/completions"):
        url += "/chat/completions"
    hist = native_msgs(messages) if mode == "native" else text_msgs(messages)
    body = {"model": m["model"], "stream": True,
            "messages": [{"role": "system", "content": system}] + hist}
    if mode == "native":
        body["tools"] = tools if tools is not None else main_tools()
    if m.get("max_tokens"):
        body["max_tokens"] = m["max_tokens"]
    for k_cfg, k_api in (("temperature", "temperature"), ("top_p", "top_p"),
                         ("top_k", "top_k"), ("effort", "reasoning_effort")):
        if m.get(k_cfg) not in (None, ""):
            body[k_api] = m[k_cfg]
    headers = {"Content-Type": "application/json", "Accept": "text/event-stream"}
    if m.get("api_key"):
        headers["Authorization"] = "Bearer " + m["api_key"]

    resp = None
    for _ in range(5):
        req = urllib.request.Request(url, data=json.dumps(body).encode(), headers=headers, method="POST")
        try:
            resp = urllib.request.urlopen(req, timeout=300)
            break
        except urllib.error.HTTPError as e:
            detail = e.read().decode("utf-8", "ignore")
            if e.code == 400:  # tự bỏ tham số mà server không nhận
                if "max_completion_tokens" in detail and "max_tokens" in body:
                    body["max_completion_tokens"] = body.pop("max_tokens")
                    continue
                dropped = [k for k in ("temperature", "top_p", "top_k", "reasoning_effort")
                           if k in body and k in detail]
                if dropped:
                    for k in dropped:
                        body.pop(k)
                    p("  server không nhận %s, bỏ qua và thử lại" % ", ".join(dropped), C_DIM)
                    continue
            low = detail.lower()
            if (mode == "native" and e.code in (400, 404, 405, 415, 422, 501)
                    and ("tool" in low or "function" in low)
                    and m.get("tool_mode", "auto") == "auto"):
                raise NativeUnsupported(detail[:300])
            raise ApiError("HTTP %d: %s" % (e.code, detail[:600]))
        except Exception as e:
            raise ApiError("không kết nối được: %s" % e)
    if resp is None:
        raise ApiError("không gọi được model")
    if ctl is not None:
        ctl.resp = resp

    full, rawbuf, tcs = "", [], {}
    try:
        for raw in resp:
            if ctl is not None and ctl.stop.is_set():
                raise Stopped(full)
            line = raw.decode("utf-8", "ignore").strip()
            if not line.startswith("data:"):
                rawbuf.append(line)
                continue
            data = line[5:].strip()
            if data == "[DONE]":
                break
            try:
                j = json.loads(data)
            except Exception:
                continue
            ch = (j.get("choices") or [{}])[0]
            d = ch.get("delta") or {}
            th = d.get("reasoning_content") or d.get("reasoning")
            if th and printer:
                printer.think(th)
            t = d.get("content")
            if t:
                full += t
                if printer:
                    printer.text(t)
                if mode == "text" and "</tool>" in full:
                    full = full[:full.index("</tool>") + 7]
                    break
            for tc in d.get("tool_calls") or []:
                cur = tcs.setdefault(tc.get("index", len(tcs)), {"id": "", "name": "", "arguments": ""})
                if tc.get("id"):
                    cur["id"] = tc["id"]
                f = tc.get("function") or {}
                nm = f.get("name")
                if nm and nm != cur["name"]:
                    cur["name"] += nm
                a = f.get("arguments")
                if isinstance(a, dict):
                    cur["arguments"] = json.dumps(a)
                elif a:
                    cur["arguments"] += a
    except Stopped:
        raise
    except Exception:
        if ctl is not None and ctl.stop.is_set():  # bị đóng kết nối vì tui nhấn dừng
            raise Stopped(full)
        raise
    finally:
        resp.close()
        if ctl is not None:
            ctl.resp = None
    if not full and not tcs and rawbuf:  # server không stream
        try:
            j = json.loads("".join(rawbuf))
            msg = j["choices"][0]["message"]
            full = msg.get("content") or ""
            if printer and full:
                printer.text(full)
            for i, tc in enumerate(msg.get("tool_calls") or []):
                f = tc.get("function") or {}
                a = f.get("arguments")
                tcs[i] = {"id": tc.get("id") or "", "name": f.get("name", ""),
                          "arguments": json.dumps(a) if isinstance(a, dict) else (a or "")}
        except Exception:
            pass

    calls = []
    if mode == "text":
        if "<result" in full and "<tool" not in full:
            full = full[:full.index("<result")]
        t = parse_tool(full)
        if t:
            name, tbody = t
            call = {"id": _call_id(), "name": name, "arguments": "{}"}
            if name == "__bad__":
                call["name"] = "unknown"
                call["error"] = "khối <tool> chưa được đóng bằng </tool> hoặc sai cú pháp"
            else:
                try:
                    call["arguments"] = json.dumps(body_to_args(name, tbody), ensure_ascii=False)
                except Exception as e:
                    call["error"] = "JSON sai (%s)" % e
            calls.append(call)
        return strip_tool(full), calls

    for i in sorted(tcs):
        c = tcs[i]
        if not c["name"]:
            continue
        call = {"id": c["id"] or _call_id(), "name": c["name"], "arguments": "{}"}
        try:
            a = json.loads(c["arguments"] or "{}")
            if not isinstance(a, dict):
                raise ValueError
            call["arguments"] = json.dumps(a, ensure_ascii=False)
        except Exception:
            call["error"] = "arguments không phải JSON object hợp lệ"
        calls.append(call)
    return full.strip(), calls


# ---------------------------------------------------------------- mốc lưu (redo) bằng git bóng
def _git(cwd, *args, timeout=40):
    gd = os.path.join(SHADOW_DIR, hashlib.sha1(cwd.encode()).hexdigest()[:12])
    cmd = ["git", "--git-dir", gd, "--work-tree", cwd, "-c", "user.name=msh",
           "-c", "user.email=msh@local", "-c", "core.quotepath=false"] + list(args)
    return gd, subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)


def snapshot(cwd):
    """Chụp trạng thái thư mục hiện tại. Trả về commit hoặc None."""
    why = None
    if not shutil.which("git"):
        why = "máy chưa có git"
    elif os.path.abspath(cwd) in (os.path.expanduser("~"), os.path.abspath(os.sep)):
        why = "thư mục quá rộng (home hoặc gốc)"
    if not why:
        try:
            gd, _ = _git(cwd, "--version")
            if not os.path.isdir(gd):
                subprocess.run(["git", "init", "--bare", "-q", gd], check=True, capture_output=True)
                _git(cwd, "config", "core.bare", "false")
            _git(cwd, "add", "-A")
            _git(cwd, "commit", "-q", "--allow-empty", "--no-verify", "-m", "snap")
            r = _git(cwd, "rev-parse", "HEAD")[1]
            if r.returncode == 0:
                return r.stdout.strip()
            why = "git lỗi"
        except Exception as e:
            why = "không chụp được (%s)" % e
    if not STATE.snap_warned:
        STATE.snap_warned = True
        p("  lưu ý: %s, /redo chỉ lùi chat, không lùi file." % why, C_DIM)
    return None


def restore(cwd, commit):
    _git(cwd, "reset", "-q", "--hard", commit)
    _git(cwd, "clean", "-fdq")


# ---------------------------------------------------------------- chat lưu trên đĩa
def new_chat():
    return {"id": datetime.now().strftime("%Y%m%d-%H%M%S"), "title": "(mới)", "created": time.time(),
            "updated": time.time(), "cwd": STATE.cwd, "messages": [], "checkpoints": []}


def save_chat(c):
    if not c["messages"]:
        return
    c["updated"] = time.time()
    c["cwd"] = STATE.cwd
    with open(os.path.join(CHAT_DIR, c["id"] + ".json"), "w", encoding="utf-8") as f:
        json.dump(c, f, ensure_ascii=False)
    CFG["current_chat"] = c["id"]
    save_cfg()


def load_chat(cid):
    try:
        with open(os.path.join(CHAT_DIR, cid + ".json"), encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return None


def list_chats():
    out = []
    for fn in os.listdir(CHAT_DIR):
        if fn.endswith(".json"):
            c = load_chat(fn[:-5])
            if c:
                out.append(c)
    return sorted(out, key=lambda c: c.get("updated", 0), reverse=True)


# ---------------------------------------------------------------- lệnh chạy nền (cmd background) và tool bg
BG_JOBS = {}                 # id -> BgJob
BG_PENDING = []         # job đã xong/hết giờ, chưa gửi thông báo cho AI
BG_LOCK = threading.Lock()
BG_MAX_RUNNING = 8
_bg_seq = [0]


def _human(sec):
    sec = int(sec)
    return "%ds" % sec if sec < 90 else "%dp%02ds" % (sec // 60, sec % 60)


class BgJob:
    """Một lệnh chạy nền: output gom vào danh sách dòng, tự dừng khi hết timeout."""
    MAXLINES = 50000

    def __init__(self, cmd, timeout, cwd):
        _bg_seq[0] += 1
        self.id, self.cmd, self.timeout, self.cwd = "bg%d" % _bg_seq[0], cmd, timeout, cwd
        self.lines, self.base, self.lock = [], 0, threading.Lock()  # base: số dòng đầu đã bị bỏ vì quá dài
        self.status, self.rc, self.t0, self.t1 = "running", None, time.time(), None
        self.acked, self.proc, self.reader = False, None, None      # acked: AI đã tự đọc/dừng, khỏi báo nữa

    def start(self):
        env = dict(os.environ, PAGER="cat", GIT_PAGER="cat", GIT_TERMINAL_PROMPT="0", TERM="dumb")
        kw = dict(stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, cwd=self.cwd, env=env,
                  text=True, encoding="utf-8", errors="replace", bufsize=1)
        if os.name == "nt":
            self.proc = subprocess.Popen(self.cmd, shell=True, **kw)
        else:
            self.proc = subprocess.Popen(["bash" if shutil.which("bash") else "sh", "-c", self.cmd],
                                         start_new_session=True, **kw)
        self.reader = threading.Thread(target=self._read, daemon=True)
        self.reader.start()
        threading.Thread(target=self._wait, daemon=True).start()

    def _read(self):
        try:
            for line in self.proc.stdout:
                with self.lock:
                    self.lines.append(line.rstrip("\r\n"))
                    extra = len(self.lines) - self.MAXLINES
                    if extra > 0:
                        del self.lines[:extra]
                        self.base += extra
        except (ValueError, OSError):
            pass

    def _wait(self):
        try:
            self.rc = self.proc.wait(timeout=self.timeout)
            end = "done"
        except subprocess.TimeoutExpired:
            end = "timeout"
            _kill(self.proc)
            self.rc = self.proc.wait()
        self.reader.join(timeout=3)
        with self.lock:
            if self.status == "running":  # stop() có thể đã đặt "stopped" trước đó
                self.status = end
            self.t1 = time.time()
            status = self.status
        if status != "stopped":
            with BG_LOCK:
                BG_PENDING.append(self)
            p("[%s] %s" % (self.id, self.summary()), C_DIM)

    def stop(self):
        with self.lock:
            if self.status != "running":
                return False
            self.status = "stopped"
        self.acked = True
        _kill(self.proc)
        return True

    def elapsed(self):
        return (self.t1 or time.time()) - self.t0

    def summary(self):
        if self.status == "running":
            return "đang chạy %s / timeout %s" % (_human(self.elapsed()), _human(self.timeout))
        if self.status == "done":
            return "xong sau %s, mã thoát %s" % (_human(self.elapsed()), self.rc)
        if self.status == "timeout":
            return "hết giờ sau %s (đã bị dừng)" % _human(self.timeout)
        return "đã dừng sau %s" % _human(self.elapsed())

    def notice(self, n=40, chars=4000):
        with self.lock:
            tail, total = self.lines[-n:], self.base + len(self.lines)
        text = "\n".join(tail)
        if len(text) > chars:
            text = "..." + text[-chars:]
        head = "[%s] %s\nlệnh: %s" % (self.id, self.summary(), self.cmd.strip().splitlines()[0][:200])
        if not total:
            return head + "\n(không có output)"
        return head + "\noutput (%d dòng, hiện %d dòng cuối; đọc thêm bằng bg read):\n%s" % (total, len(tail), text)


def bg_ready():
    with BG_LOCK:
        return any(not j.acked for j in BG_PENDING)


def bg_take():
    """Thông báo các lệnh nền đã xong để gộp vào lần gửi tới model (rỗng nếu không có)."""
    with BG_LOCK:
        jobs = [j for j in BG_PENDING if not j.acked]
        BG_PENDING.clear()
    if not jobs:
        return ""
    parts = []
    bgs = [j for j in jobs if isinstance(j, BgJob)]
    subs = [j for j in jobs if isinstance(j, SubAgent)]
    if bgs:
        parts.append("Lệnh chạy nền đã kết thúc:\n" + "\n\n".join(j.notice() for j in bgs))
    if subs:
        parts.append("Thông báo Sub-Agent:\n" + "\n\n".join(j.notice() for j in subs))
    return "<system>\n" + sanitize("\n\n".join(parts)) + "\n</system>"


def bg_kill_all():
    for j in list(SUBS.values()):
        try:
            j.stop()
        except Exception:
            pass
    for j in list(BG_JOBS.values()):
        try:
            j.stop()
        except Exception:
            pass


def bg_start(cmd, timeout):
    with BG_LOCK:
        running = sum(1 for j in BG_JOBS.values() if j.status == "running")
    if running >= BG_MAX_RUNNING:
        return "đang có %d lệnh nền chạy (tối đa %d). Chờ xong hoặc dùng bg stop." % (running, BG_MAX_RUNNING)
    job = BgJob(cmd, timeout, STATE.cwd)
    try:
        job.start()
    except Exception as e:
        return "không chạy nền được: %s" % e
    with BG_LOCK:
        BG_JOBS[job.id] = job
        for k in [k for k, j in BG_JOBS.items() if j.status != "running"][:-30]:  # giữ tối đa ~30 job đã xong
            del BG_JOBS[k]
    p("[%s] chạy nền, timeout %s: %s" % (job.id, _human(timeout), cmd.strip().splitlines()[0][:100]), C_DIM)
    return ("đã chạy nền %s (timeout %s). Không cần chờ: khi xong hoặc hết giờ, kết quả được gửi lại cùng lần phản hồi tới "
            "(hoặc khi bạn không dùng công cụ nữa). Muốn đọc sớm hoặc dừng thì dùng tool bg." % (job.id, _human(timeout)))


def tool_bg(a):
    act = str(a.get("action") or "list").lower()
    ids = a.get("ids")
    ids = [ids] if isinstance(ids, str) else [str(x) for x in (ids or [])]
    if a.get("id"):
        ids.insert(0, str(a["id"]))
    with BG_LOCK:
        jobs = dict(BG_JOBS)
    if act == "list":
        if not jobs:
            return "(chưa có lệnh nền nào)"
        return "\n".join("%s  %s  | %s" % (j.id, j.summary(), j.cmd.strip().splitlines()[0][:80]) for j in jobs.values())
    if act == "read":
        if not ids:
            return "thiếu id (xem bg list)"
        j = jobs.get(ids[0])
        if j is None:
            return "không có lệnh nền '%s'. Đang có: %s" % (ids[0], ", ".join(jobs) or "(không)")
        try:
            limit, offset = max(1, int(a.get("limit", 200))), int(a.get("offset", 0))
        except (TypeError, ValueError):
            return "limit và offset phải là số"
        with j.lock:
            lines, base = list(j.lines), j.base
        total = base + len(lines)
        start = max(base, total + offset) if offset < 0 else max(base, offset)  # offset âm: đếm từ cuối
        end = min(total, start + limit)
        if j.status != "running":
            j.acked = True  # AI đã tự đọc kết quả, khỏi gửi thông báo nữa
        if end <= start:
            return "[%s] %s | không có dòng nào ở vị trí này (tổng %d dòng)" % (j.id, j.summary(), total)
        return "[%s] %s | dòng %d-%d / %d\n%s" % (j.id, j.summary(), start, end - 1, total,
                                                  truncate_mid("\n".join(lines[start - base:end - base])))
    if act == "stop":
        if ids == ["all"]:
            ids = [k for k, j in jobs.items() if j.status == "running"]
        if not ids:
            return "thiếu ids (hoặc ids=[\"all\"])"
        out = []
        for i in ids:
            j = jobs.get(i)
            out.append("%s: không có" % i if j is None else
                       "%s: đã dừng" % i if j.stop() else "%s: %s" % (i, j.summary()))
        return "\n".join(out)
    return "action phải là list, read hoặc stop"


# ---------------------------------------------------------------- Sub-Agent: AI phụ chạy song song, giao bằng tool sub
SUBS = {}               # id -> SubAgent
SUB_MAX_RUNNING = 5
SUB_CMD_ASK = 1500      # lệnh cmd dài hơn thì hỏi tui
SUB_READ_LIMIT = 60000
_sub_seq = [0]

SUB_TOOLS = [
    {"type": "function", "function": {
        "name": "cmd",
        "description": "Chạy lệnh shell trên máy tui (không có chạy nền). Thư mục làm việc được giữ giữa các lần chạy. Lệnh bị dừng sau 120 giây "
                       "và không có bàn phím nên đừng chạy lệnh chờ nhập. Output dài bị cắt ở giữa.",
        "parameters": {"type": "object", "properties": {
            "command": {"type": "string", "description": "Lệnh shell cần chạy (nhiều dòng được)."}},
            "required": ["command"]}}},
    {"type": "function", "function": {
        "name": "mem",
        "description": "Đọc bộ nhớ lâu dài (chỉ đọc). action=list: liệt kê; action=read + name: đọc một mục.",
        "parameters": {"type": "object", "properties": {
            "action": {"type": "string", "enum": ["list", "read"]},
            "name": {"type": "string", "description": "Tên mục nhớ (read)."}},
            "required": ["action"]}}},
    {"type": "function", "function": {
        "name": "skill",
        "description": "Xem skill tui đã lưu (chỉ đọc). name = tên skill, hoặc 'list' để liệt kê.",
        "parameters": {"type": "object", "properties": {
            "name": {"type": "string", "description": "Tên skill, hoặc 'list'."}},
            "required": ["name"]}}},
]

SUB_PROMPT = """Bạn là Sub Agent. Bạn giúp AI chính hoàn thiện nhiệm vụ phụ.
Bạn trung thực. Bạn không biết làm thì bạn nói bạn không biết làm, thay vì làm sai/không đúng. Khi bạn không biết điều gì thì bạn có thể hỏi(như nhiệm vụ không rõ ràng, không thể làm được).
Bạn đi thẳng vấn đề, không nói các câu không liên quan đến nhiệm vụ, không gợi ý.
Bạn phải xin phép khi cần ghi đè file, xoá file, tải thư viện/gói.
Hôm nay: {}
Thư mục hiện tại: {}"""

SUB_ASK_DOC = """
Hỏi hoặc xin phép bằng cách trả lời ngay (không gọi công cụ nữa), nêu rõ câu hỏi hoặc việc cần xin phép; AI chính sẽ trả lời và cho bạn làm tiếp. Việc được giao nằm trong <system>; kết quả công cụ nằm trong <result>. Mỗi lần chạy tối đa %d bước, quá thì bị tạm dừng chờ AI chính đọc.""" % SUB_MAX_STEPS

SUB_TEXT_DOC = """
---
CÔNG CỤ
Muốn dùng công cụ, viết đúng một khối ở cuối câu trả lời rồi dừng lại, không viết thêm gì sau thẻ đóng. Hệ thống chạy và gửi lại <result>. Mỗi lượt chỉ một khối, tuyệt đối không tự viết <result>.
<tool name="TÊN">NỘI DUNG</tool>
1) cmd: NỘI DUNG là lệnh shell (nhiều dòng được). Thư mục làm việc được giữ giữa các lần chạy. Lệnh bị dừng sau 120 giây, không có bàn phím nên đừng chạy lệnh chờ nhập.
2) mem: đọc bộ nhớ (chỉ đọc). NỘI DUNG là JSON: {"action":"list"} hoặc {"action":"read","name":"..."}.
3) skill: NỘI DUNG là "list" hoặc tên skill để đọc.
"""

SUB_NATIVE_DOC = """
---
CÔNG CỤ
Dùng function calling để gọi công cụ: cmd, mem, skill. Kết quả nằm trong <result>. Gọi nhiều lần được; xong việc thì trả lời bình thường, không gọi công cụ nữa."""


def sub_system_section(mode):
    lines = []
    for j in list(SUBS.values()):
        lines.append("%s (đang chạy) (đang chạy %s)" % (j.id, _human(j.elapsed())) if j.status == "running"
                     else "%s (tạm dừng sau %d bước, chờ bạn đọc rồi cho tiếp tục)" % (j.id, j.steps) if j.status == "paused"
                     else "%s (lần chạy gần nhất)" % j.id)
    out = ("\n\nSUB-AGENT (tool sub: giao việc cho AI phụ chạy song song; chúng chỉ có cmd, mem đọc, skill đọc và không thấy cuộc trò chuyện này, "
           "nên prompt phải đủ ngữ cảnh. Xong thì được báo lại như lệnh nền):\ncác sub-agent có:\n")
    out += "\n".join(lines) if lines else "(chưa có)"
    if mode == "text":
        out += ('\n7) sub: NỘI DUNG là JSON: {"action":"run","prompts":[{"prompt":"..."},{"prompt":"...","id":"sa1"}]} (mỗi prompt một Sub-Agent mới; id đã xong thì chạy lại) '
                'hoặc {"action":"stop","ids":["sa1"]} (["all"] = dừng hết) hoặc {"action":"read","id":"sa1"} (đọc toàn bộ lịch sử của Sub-Agent đã xong/tạm dừng) '
                'hoặc {"action":"continue","id":"sa1","prompt":"..."} (cho Sub-Agent tạm dừng làm tiếp, chỉ được sau khi đã read; hoặc trả lời câu hỏi của Sub-Agent đã xong bằng prompt).')
    return out


def sub_build_system(mode, job):
    out = SUB_PROMPT.format(today(), job.cwd) + "\n" + (SUB_TEXT_DOC if mode == "text" else SUB_NATIVE_DOC) + SUB_ASK_DOC
    out += "\nMÔI TRƯỜNG: %s, shell: %s\n" % (platform.platform(), "cmd/powershell" if os.name == "nt" else "bash/sh")
    sk = CFG["skills"]
    out += "\nSKILL (đọc bằng công cụ skill):\n" + ("\n".join("- %s: %s" % (k, first_line(v)) for k, v in sk.items()) if sk else "(chưa có)")
    mem = CFG["memory"]
    out += "\n\nBỘ NHỚ (đọc bằng công cụ mem):\n" + ("\n".join("- %s: %s" % (k, first_line(v)) for k, v in mem.items()) if mem else "(trống)")
    return out


class SubCtl:
    def __init__(self):
        self.stop, self.resp = threading.Event(), None


def sub_run_cmd(cmd, job):
    cmd = re.sub(r"^```\w*\n|\n```$", "", cmd.strip()).strip()
    if not cmd:
        return "lệnh rỗng"
    env = dict(os.environ, PAGER="cat", GIT_PAGER="cat", GIT_TERMINAL_PROMPT="0", TERM="dumb")
    tag = "__MSH_CWD_%s__" % uuid.uuid4().hex[:8]
    kw = dict(stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
              cwd=job.cwd, env=env, text=True, encoding="utf-8", errors="replace")
    if os.name == "nt":
        proc = subprocess.Popen(cmd, shell=True, **kw)
    else:
        script = '%s\n__msh_rc=$?\nprintf "\\n%s%%s\\n" "$(pwd)"\nexit $__msh_rc' % (cmd, tag)
        proc = subprocess.Popen(["bash" if shutil.which("bash") else "sh", "-c", script], start_new_session=True, **kw)
    timed_out = stopped = False
    t0 = time.time()
    while True:
        try:
            out, _ = proc.communicate(timeout=0.2)
            break
        except subprocess.TimeoutExpired:
            if job.ctl.stop.is_set():
                stopped = True
            elif time.time() - t0 > CMD_TIMEOUT:
                timed_out = True
            else:
                continue
            _kill(proc)
            out, _ = proc.communicate()
            break
    m = re.search(re.escape(tag) + r"(.*)", out)
    if m:
        d = m.group(1).strip()
        out = out[:m.start()].rstrip("\n")
        if d and os.path.isdir(d):
            job.cwd = d
    out = truncate_mid(out.strip("\n"))
    if stopped:
        out += "\n[đã bị dừng]"
    elif timed_out:
        out += "\n[bị dừng sau %d giây]" % CMD_TIMEOUT
    elif proc.returncode:
        out += "\n[mã thoát: %s]" % proc.returncode
    return out or "(không có output)"


def sub_exec_tool(name, args, job):
    try:
        if name == "cmd":
            text = str(args.get("command", "")).strip()
            if len(text) > SUB_CMD_ASK:  # lệnh dài bất thường: để tui xem trước khi chạy
                shown = text[:600] + ("\n... (+%d ký tự nữa)" % (len(text) - 600) if len(text) > 600 else "")
                ok = ask_user(ConfirmDialog("Sub-Agent %s: lệnh dài %d ký tự" % (job.id, len(text)), shown.splitlines()), job.ctl.stop)
                if not ok:
                    return "tui TỪ CHỐI chạy lệnh dài này. Đừng chạy lại y nguyên: làm cách ngắn gọn hơn hoặc trả lời nói rõ cần gì."
            return sub_run_cmd(text, job)  # không có background
        if name == "skill":
            return tool_skill(str(args.get("name", "")))
        if name == "mem":
            act, mem = args.get("action"), CFG["memory"]
            if act == "list":
                return "\n".join("[%s] %s" % (k, first_line(v)) for k, v in mem.items()) or "(trống)"
            if act == "read":
                n = str(args.get("name", "")).strip()
                return mem[n] if n in mem else "không có mục nhớ '%s'" % n
            return "mem chỉ đọc: action là list hoặc read"
        return "không có công cụ '%s'. Chỉ có: cmd, mem, skill" % name
    except Exception as e:
        return "lỗi: %s" % e


_THINK_RE = re.compile(r"<think>.*?</think>|<think>.*\Z", re.S | re.I)


class SubAgent:
    """Một AI phụ chạy ở luồng riêng. Lịch sử đầy đủ nằm trong self.messages (định dạng function calling)."""

    def __init__(self, sid):
        self.id, self.lock = sid, threading.Lock()
        self.acked, self.thread = False, None
        self.reset("", STATE.cwd)

    def reset(self, prompt, cwd):
        self.prompt, self.cwd, self.ctl = prompt, cwd, SubCtl()
        self.messages = [{"role": "user", "content": "<system>\nViệc được giao:\n%s\n</system>" % prompt}]
        self.status, self.final, self.error, self.steps = "running", "", "", 0
        self.t0, self.t1, self.acked, self.read_ok = time.time(), None, False, False  # read_ok: AI chính đã đọc từ lúc tạm dừng

    def start(self, prompt):
        self.reset(prompt, STATE.cwd)
        self.thread = threading.Thread(target=self._run, daemon=True)
        self.thread.start()

    def _run(self):
        end = "done"
        try:
            for step in range(SUB_MAX_STEPS):
                if self.ctl.stop.is_set():
                    raise Stopped("")
                mode = tool_mode()
                try:
                    reply, calls = chat_stream(self.messages, sub_build_system(mode, self), None, mode,
                                               agent=False, tools=SUB_TOOLS, ctl=self.ctl)
                except NativeUnsupported:
                    mark_text_fallback()
                    continue
                self.steps += 1
                msg = {"role": "assistant", "content": reply}
                if calls:
                    msg["tool_calls"] = [{"id": c["id"], "type": "function",
                                          "function": {"name": c["name"], "arguments": c["arguments"]}} for c in calls]
                self.messages.append(msg)
                if not calls:
                    self.final = _THINK_RE.sub("", reply).strip() or "(không có câu trả lời)"
                    break
                for c in calls:
                    if self.ctl.stop.is_set():
                        raise Stopped("")
                    if c.get("error"):
                        res = c["error"]
                    else:
                        res = sub_exec_tool(c["name"], json.loads(c["arguments"]), self)
                    self.messages.append({"role": "tool", "tool_call_id": c["id"],
                                          "content": "<result>\n%s\n</result>" % sanitize(res)})
            else:
                end, self.read_ok = "paused", False  # đủ bước mà chưa xong: tạm dừng, chờ AI chính đọc rồi cho tiếp
        except Stopped as e:
            end = "stopped"
            if e.partial.strip():
                self.messages.append({"role": "assistant", "content": e.partial.strip() + "\n[bị dừng giữa chừng]"})
        except ApiError as e:
            end, self.error = "error", str(e)
        except Exception as e:
            end, self.error = "error", "lỗi không mong đợi: %s" % e
        with self.lock:
            if self.status == "running":
                self.status = end
            status = self.status
            self.t1 = time.time()
        if status != "stopped":
            with BG_LOCK:
                BG_PENDING.append(self)
            p("[%s] Sub-Agent %s" % (self.id, {"done": "đã xong", "paused": "tạm dừng sau %d bước" % SUB_MAX_STEPS}.get(status, "gặp lỗi")), C_DIM)

    def stop(self):
        with self.lock:
            if self.status not in ("running", "paused"):
                return False
            self.status = "stopped"
        self.acked = True
        self.ctl.stop.set()
        r = self.ctl.resp
        if r is not None:
            try:
                r.close()
            except Exception:
                pass
        return True

    def elapsed(self):
        return (self.t1 or time.time()) - self.t0

    def summary(self):
        if self.status == "running":
            return "đang chạy %s" % _human(self.elapsed())
        if self.status == "done":
            return "đã xong sau %s, %d bước" % (_human(self.elapsed()), self.steps)
        if self.status == "paused":
            return "TẠM DỪNG sau %d bước (%s), chờ AI chính đọc rồi cho tiếp tục" % (self.steps, _human(self.elapsed()))
        if self.status == "error":
            return "lỗi: %s" % self.error[:200]
        return "đã dừng sau %s" % _human(self.elapsed())

    def notice(self, chars=3000):
        first = self.prompt.strip().splitlines()[0][:150] if self.prompt.strip() else ""
        if self.status == "paused":
            last = next((_THINK_RE.sub("", m.get("content") or "").strip() for m in reversed(self.messages)
                         if m["role"] == "assistant" and (m.get("content") or "").strip()), "")
            return ("[%s] Sub-Agent đã chạy %d bước mà chưa xong, đang TẠM DỪNG.\nviệc giao: %s\n"
                    "Hãy đọc lịch sử bằng sub read để xem nó có đi đúng hướng không, rồi mới cho tiếp tục bằng sub continue "
                    "(có thể kèm prompt chỉnh hướng) hoặc dừng bằng sub stop. Chưa đọc thì không cho tiếp tục được."
                    % (self.id, self.steps, first)) + ("\nlời cuối của nó: " + last[:500] if last else "")
        head = "[%s] Sub-Agent %s\nviệc giao: %s" % (
            self.id, "đã xong" if self.status == "done" else "gặp lỗi (%s)" % self.error[:300], first)
        body = self.final if self.status == "done" else ""
        if len(body) > chars:
            body = body[:chars] + "\n...(còn nữa, đọc đủ bằng sub read)"
        return head + ("\nkết quả:\n" + body if body else "") + "\n(%s; đọc toàn bộ lịch sử bằng tool sub read; muốn trả lời/ra lệnh tiếp cho nó: sub continue + prompt)" % self.summary()

    def history(self):
        out = ["[%s] %s" % (self.id, self.summary()), "", "--- việc được giao ---", self.prompt.strip()]
        for m in self.messages[1:]:
            if m["role"] == "assistant":
                txt = _THINK_RE.sub("", m.get("content") or "").strip()
                if txt:
                    out += ["", "--- Sub-Agent ---", txt]
                for tc in m.get("tool_calls") or []:
                    f = tc["function"]
                    out += ["", "--- gọi %s ---" % f["name"], f.get("arguments") or ""]
            elif m["role"] == "tool":
                out += ["", "--- kết quả ---", re.sub(r"^<result>\n|\n</result>$", "", m["content"])]
        if self.status == "paused":
            out += ["", "[Sub-Agent đang tạm dừng. Đi đúng hướng thì dùng sub continue, sai thì sub stop hoặc continue kèm prompt chỉnh hướng.]"]
        return truncate_mid("\n".join(out), SUB_READ_LIMIT)

    def resume(self, prompt=""):
        """Chạy tiếp (sau tạm dừng, hoặc trả lời câu hỏi khi đã xong): giữ nguyên lịch sử."""
        if prompt or self.messages[-1]["role"] != "tool":
            self.messages.append({"role": "user", "content": "<system>\n%s\n</system>" % (prompt or "MshLite chính đã đọc và cho bạn làm tiếp.")})
        self.status, self.final, self.error, self.t1, self.acked = "running", "", "", None, False
        self.ctl = SubCtl()
        self.thread = threading.Thread(target=self._run, daemon=True)
        self.thread.start()


def tool_sub(a):
    act = str(a.get("action") or "").lower()
    if act == "run":
        items = a.get("prompts")
        if items is None and a.get("prompt"):
            items = [{"prompt": a["prompt"], "id": a.get("id")}]
        items = [items] if isinstance(items, (str, dict)) else (items or [])
        res = []
        for it in items:
            it = {"prompt": it} if isinstance(it, str) else dict(it or {})
            prompt = str(it.get("prompt") or "").strip()
            if not prompt:
                res.append("(bỏ qua: prompt rỗng)")
                continue
            running = sum(1 for j in list(SUBS.values()) if j.status == "running")
            if running >= SUB_MAX_RUNNING:
                res.append("không chạy được '%s...': đang có %d Sub-Agent chạy (tối đa %d)" % (prompt[:30], running, SUB_MAX_RUNNING))
                continue
            sid = str(it.get("id") or "").strip()
            if sid:
                j = SUBS.get(sid)
                if j is None:
                    res.append("không có Sub-Agent '%s' (bỏ id để tạo mới)" % sid)
                    continue
                if j.status == "running":
                    res.append("%s đang chạy, dừng nó trước (stop) hoặc chờ xong" % sid)
                    continue
            else:
                _sub_seq[0] += 1
                sid = "sa%d" % _sub_seq[0]
                j = SubAgent(sid)
                SUBS[sid] = j
            j.start(prompt)
            p("[%s] Sub-Agent chạy: %s" % (sid, prompt.splitlines()[0][:100]), C_DIM)
            res.append("%s: đã chạy. Xong thì tui báo lại, không cần chờ." % sid)
        return "\n".join(res) or "thiếu prompts"
    ids = a.get("ids")
    ids = [ids] if isinstance(ids, str) else [str(x) for x in (ids or [])]
    if a.get("id"):
        ids.insert(0, str(a["id"]))
    if act == "stop":
        if ids == ["all"]:
            ids = [k for k, j in SUBS.items() if j.status == "running"]
        if not ids:
            return "thiếu ids (hoặc ids=[\"all\"])"
        return "\n".join("%s: không có" % i if i not in SUBS else "%s: đã dừng" % i if SUBS[i].stop() else "%s: %s" % (i, SUBS[i].summary())
                         for i in ids)
    if act == "read":
        if not ids:
            return "thiếu id"
        j = SUBS.get(ids[0])
        if j is None:
            return "không có Sub-Agent '%s'. Đang có: %s" % (ids[0], ", ".join(SUBS) or "(không)")
        if j.status == "running":
            return "%s còn đang chạy (%s), chưa đọc được. Chờ báo xong hoặc dùng stop." % (j.id, j.summary())
        j.acked = True  # AI đã tự đọc, khỏi báo nữa
        if j.status == "paused":
            j.read_ok = True
        return j.history()
    if act == "continue":
        if not ids:
            return "thiếu id"
        j = SUBS.get(ids[0])
        if j is None:
            return "không có Sub-Agent '%s'. Đang có: %s" % (ids[0], ", ".join(SUBS) or "(không)")
        prompt = str(a.get("prompt") or "").strip()
        if j.status == "running":
            return "%s đang chạy rồi." % j.id
        if j.status == "paused":
            if not j.read_ok:
                return ("CHẶN: chưa đọc lịch sử của %s. Dùng sub read để xem nó đi đúng hướng không rồi mới được tiếp tục." % j.id)
        elif j.status == "done":
            if not prompt:
                return "%s đã xong. Muốn nó làm tiếp (trả lời câu hỏi, cho phép...) thì kèm prompt." % j.id
        else:
            return "%s ở trạng thái '%s', không tiếp tục được; dùng run với id để chạy lại từ đầu." % (j.id, j.status)
        if sum(1 for x in list(SUBS.values()) if x.status == "running") >= SUB_MAX_RUNNING:
            return "đang có %d Sub-Agent chạy (tối đa %d)" % (SUB_MAX_RUNNING, SUB_MAX_RUNNING)
        j.resume(prompt)
        p("[%s] Sub-Agent làm tiếp" % j.id, C_DIM)
        return "%s: đã cho làm tiếp (thêm tối đa %d bước). Xong hoặc tạm dừng thì tui báo lại." % (j.id, SUB_MAX_STEPS)
    return "action phải là run, stop, read hoặc continue"


# ---------------------------------------------------------------- tool request: cài đặt / xóa file có hỏi tui
def short(text, width):
    return text if len(text) <= width else "…" + text[-(width - 1):]


def dlg_box(title, rows, W):
    """Hộp viền ASCII. rows: các dòng đã tô màu, mỗi dòng được căn cho vừa khung."""
    W = max(30, min(W - 1, 100))
    inner = W - 4
    t = " %s " % title
    out = [C_DIM + "+-" + RESET + C_ACC + t + RESET + C_DIM + "-" * max(0, W - 3 - vis_width(t)) + "+" + RESET]
    for r in rows:
        out.append(C_DIM + "| " + RESET + r + " " * max(0, inner - vis_width(r)) + C_DIM + " |" + RESET)
    out.append(C_DIM + "+" + "-" * (W - 2) + "+" + RESET)
    return out


class Dialog:
    """Hộp hỏi tui. AI (luồng nền) gọi ask_user rồi chờ; luồng chính vẽ hộp và nhận phím."""

    def __init__(self):
        self.event, self.result, self.finished, self.t0 = threading.Event(), None, False, 0.0

    def finish(self, result):
        self.result, self.finished = result, True
        self.event.set()

    def cancel(self):
        self.finish(None)


class ConfirmDialog(Dialog):
    def __init__(self, title, lines):
        Dialog.__init__(self)
        self.title, self.lines, self.sel = title, lines, 1  # mặc định "Từ chối" cho an toàn

    def render(self, W):
        inner = max(30, min(W - 1, 100)) - 4
        rows = []
        for ln in self.lines:
            for seg in (textwrap.wrap(ln, inner, replace_whitespace=False) or [""]):
                rows.append(C_CODE + seg + RESET)
        rows.append("")
        btn = []
        for i, name in enumerate(("Cho phép", "Từ chối")):
            lab = "[ %s ]" % name
            btn.append((C_ACC + "\033[7m" + lab + "\033[27m" + RESET) if i == self.sel else (C_DIM + lab + RESET))
        rows.append("  ".join(btn))
        rows.append(C_DIM + "Trái/Phải chọn, Enter xác nhận, y cho phép, n hoặc Esc từ chối" + RESET)
        return dlg_box(self.title, rows, W)

    def handle(self, ev):
        key, mods = ev
        if key in ("left", "right", "up", "down", "tab"):
            self.sel ^= 1
        elif key == "enter":
            self.finish(self.sel == 0)
        elif key in ("y", "Y"):
            self.finish(True)
        elif key in ("n", "N", "esc") or (key == "c" and "ctrl" in mods):
            self.finish(False)

    def ask_text(self):
        p(self.title + ":", C_ACC)
        for ln in self.lines:
            p("  " + ln, C_CODE)
        try:
            return inp("cho phép? [y/N] ").strip().lower() in ("y", "yes", "c", "có")
        except EOFError:
            return False


class DeleteDialog(Dialog):
    def __init__(self, paths, why=""):
        Dialog.__init__(self)
        self.paths, self.why = paths, why
        self.on, self.perm, self.cur = [True] * len(paths), False, 0  # cur == len(paths): dòng "xóa hẳn"

    def render(self, W):
        inner = max(30, min(W - 1, 100)) - 4
        n = len(self.paths)
        rows = []
        for seg in textwrap.wrap("AI muốn xóa %d mục. Bỏ chọn mục tui không muốn xóa." % n, inner):
            rows.append(seg)
        for seg in (textwrap.wrap("lý do: " + self.why, inner) if self.why else []):
            rows.append(C_DIM + seg + RESET)
        rows.append("")
        total = n + 1
        top = max(0, min(self.cur - 3, total - 8)) if total > 8 else 0
        for i in range(top, min(total, top + 8)):
            if i < n:
                q = self.paths[i]
                dirs = os.path.isdir(q) and not os.path.islink(q)
                line = "%s %s" % ("[x]" if self.on[i] else "[ ]", short(q + (os.sep if dirs else ""), inner - 6))
                if dirs:
                    line = line[:max(0, inner - 12)] + "  (thư mục)" if len(line) < inner - 12 else line
            else:
                line = "%s Xóa hẳn, không qua thùng rác" % ("[x]" if self.perm else "[ ]")
            sel = i == self.cur
            col = C_ERR if (i == n and self.perm) else (C_ACC if sel else C_TEXT)
            rows.append(col + ("> " if sel else "  ") + line + RESET)
        if total > 8:
            rows.append(C_DIM + "(%d/%d)" % (self.cur + 1, total) + RESET)
        rows.append("")
        rows.append(C_DIM + "Lên/Xuống di chuyển, Space chọn/bỏ chọn, a chọn hết/bỏ hết," + RESET)
        rows.append(C_DIM + "Enter xác nhận xóa, Esc hủy (không xóa gì)" + RESET)
        return dlg_box("Xóa file", rows, W)

    def handle(self, ev):
        key, mods = ev
        n = len(self.paths)
        if key == "up":
            self.cur = (self.cur - 1) % (n + 1)
        elif key == "down":
            self.cur = (self.cur + 1) % (n + 1)
        elif key == " ":
            if self.cur == n:
                self.perm = not self.perm
            else:
                self.on[self.cur] = not self.on[self.cur]
        elif key in ("a", "A"):
            v = not all(self.on)
            self.on = [v] * n
        elif key == "enter":
            self.finish({"paths": [q for q, o in zip(self.paths, self.on) if o], "permanent": self.perm})
        elif key == "esc" or (key == "c" and "ctrl" in mods):
            self.cancel()

    def ask_text(self):
        p("AI muốn xóa:", C_ACC)
        for i, q in enumerate(self.paths, 1):
            p("  %d. %s" % (i, q), C_CODE)
        try:
            s = inp("bỏ chọn số nào (vd 1,3)? Enter = xóa tất cả, 0 = hủy: ").strip()
            if s == "0":
                return None
            skip = {int(x) for x in re.findall(r"\d+", s)}
            keep = [q for i, q in enumerate(self.paths, 1) if i not in skip]
            perm = inp("xóa hẳn, không qua thùng rác? [y/N] ").strip().lower() in ("y", "yes", "c", "có")
            return {"paths": keep, "permanent": perm}
        except EOFError:
            return None


def ask_user(dlg, stop=None):
    if stop is not None:  # luồng nền (Sub-Agent): chờ tới khi có ô nhập (lúc rảnh hoặc AI đang chạy) rồi hiện hộp
        while not stop.is_set():
            lv = LIVE
            if lv is not None and lv.accepts_dialog:
                return lv.run_dialog(dlg, stop)
            time.sleep(0.3)
        return None
    lv = LIVE
    if lv is not None and lv.accepts_dialog:
        return lv.run_dialog(dlg)
    return dlg.ask_text()


def delete_protected(q):
    nq, cwd = os.path.normcase(q), os.path.normcase(STATE.cwd)
    home, mine = os.path.normcase(os.path.expanduser("~")), os.path.normcase(HOME)
    if nq == home or os.path.dirname(q) == q:
        return "thư mục gốc hoặc thư mục home"
    if cwd == nq or cwd.startswith(nq + os.sep):
        return "là (hoặc chứa) thư mục làm việc hiện tại"
    if nq == mine or nq.startswith(mine + os.sep):
        return "dữ liệu của MshLite"
    return ""


def permanent_delete(paths):
    done, fails = [], []
    for q in paths:
        try:
            if os.path.isdir(q) and not os.path.islink(q):
                shutil.rmtree(q)
            else:
                os.remove(q)
            done.append(q)
        except Exception as e:
            fails.append((q, str(e)))
    return done, fails


def _move_unique(dst_dir, q, info_dir=None):
    os.makedirs(dst_dir, exist_ok=True)
    name = os.path.basename(q.rstrip(os.sep)) or "file"
    dst, k = name, 1
    while os.path.lexists(os.path.join(dst_dir, dst)) or (info_dir and os.path.lexists(os.path.join(info_dir, dst + ".trashinfo"))):
        k += 1
        dst = "%s.%d" % (name, k)
    if info_dir:  # chuẩn freedesktop.org Trash
        os.makedirs(info_dir, exist_ok=True)
        with open(os.path.join(info_dir, dst + ".trashinfo"), "w", encoding="utf-8") as f:
            f.write("[Trash Info]\nPath=%s\nDeletionDate=%s\n" % (urllib.parse.quote(q), datetime.now().strftime("%Y-%m-%dT%H:%M:%S")))
    shutil.move(q, os.path.join(dst_dir, dst))


def send_to_trash(paths):
    """Chuyển vào thùng rác của hệ điều hành. Trả về (đã chuyển, [(đường dẫn, lỗi)])."""
    err = ""
    try:
        if os.name == "nt":
            cmds = ["[Microsoft.VisualBasic.FileIO.FileSystem]::Delete%s('%s','OnlyErrorDialogs','SendToRecycleBin')" % (
                "Directory" if os.path.isdir(q) and not os.path.islink(q) else "File", q.replace("'", "''")) for q in paths]
            r = subprocess.run(["powershell", "-NoProfile", "-Command", "Add-Type -AssemblyName Microsoft.VisualBasic;" + ";".join(cmds)],
                               capture_output=True, text=True, timeout=120)
            err = (r.stderr or "").strip()[:200]
        elif sys.platform == "darwin":
            for q in paths:
                _move_unique(os.path.expanduser("~/.Trash"), q)
        else:
            if shutil.which("gio"):
                subprocess.run(["gio", "trash", "--"] + paths, capture_output=True, timeout=120)
            base = os.path.join(os.environ.get("XDG_DATA_HOME") or os.path.expanduser("~/.local/share"), "Trash")
            for q in paths:
                if os.path.lexists(q):
                    _move_unique(os.path.join(base, "files"), q, os.path.join(base, "info"))
    except Exception as e:
        err = str(e)
    done = [q for q in paths if not os.path.lexists(q)]
    return done, [(q, err or "không chuyển được vào thùng rác") for q in paths if os.path.lexists(q)]


def tool_request(a):
    act = str(a.get("action") or "").lower()
    why = str(a.get("reason") or "").strip()
    if act == "install":
        cmd = str(a.get("command") or "").strip()
        if not cmd:
            return "thiếu command"
        if not ask_user(ConfirmDialog("Xin phép cài đặt", [cmd] + (["lý do: " + why] if why else []))):
            return "tui TỪ CHỐI lệnh cài đặt này. Đừng cài bằng cách khác khi chưa hỏi lại tui."
        return "(tui đã cho phép)\n" + run_cmd(cmd, a.get("background"))
    if act == "delete":
        paths = a.get("paths") or ([a["path"]] if a.get("path") else [])
        paths = [paths] if isinstance(paths, str) else [str(x) for x in paths]
        items, bad = [], []
        for raw in paths:
            q = os.path.normpath(os.path.expandvars(os.path.expanduser(raw)))
            q = q if os.path.isabs(q) else os.path.normpath(os.path.join(STATE.cwd, q))
            if not os.path.lexists(q):
                bad.append("%s (không tồn tại)" % raw)
            elif delete_protected(q):
                bad.append("%s (không được xóa: %s)" % (raw, delete_protected(q)))
            elif q not in items:
                items.append(q)
        if not items:
            return "không có đường dẫn hợp lệ để xóa: " + "; ".join(bad or ["(danh sách trống)"])
        res = ask_user(DeleteDialog(items, why))
        if not res or not res["paths"]:
            return "tui hủy: chưa xóa gì cả."
        chosen = res["paths"]
        if STATE.journal is not None:  # lưu bản sao để /redo khôi phục được
            try:
                STATE.journal.record_paths(chosen)
            except Exception:
                pass
        done, fails = permanent_delete(chosen) if res["permanent"] else send_to_trash(chosen)
        out = ["đã xóa %d mục (%s):" % (len(done), "xóa hẳn" if res["permanent"] else "vào thùng rác")] + ["  " + q for q in done]
        skipped = [q for q in items if q not in chosen]
        if skipped:
            out += ["tui bỏ chọn, KHÔNG xóa:"] + ["  " + q for q in skipped]
        if fails:
            out += ["lỗi:"] + ["  %s: %s" % f for f in fails]
        if bad:
            out += ["bỏ qua: " + "; ".join(bad)]
        return "\n".join(out)
    return "action phải là install hoặc delete"


# ---------------------------------------------------------------- file tạm: /redo lùi cả file ngoài thư mục làm việc
_READONLY = set("ls dir cat type echo pwd cd head tail wc grep rg find which where whoami date env printenv uname "
                "tree stat file du df ps sort uniq diff cmp less more".split())


def cmd_is_readonly(cmd):
    """Lệnh chỉ đọc (ls, cat, grep, ...) thì khỏi sao lưu."""
    if ">" in cmd or re.search(r"\s-(delete|exec|i|fprint\w*)\b|--in-place", cmd):
        return False
    for seg in re.split(r"&&|\|\||[;|\n]", cmd):
        seg = seg.strip()
        if seg and os.path.basename(seg.split()[0]).lower() not in _READONLY:
            return False
    return True


def strip_heredoc(cmd):
    return re.sub(r"(<<-?\s*['\"]?(\w+)['\"]?[^\n]*)\n.*?\n\s*\2\s*(?=\n|$)", r"\1", cmd, flags=re.S)


def cmd_paths(cmd, cwd):
    """Các đường dẫn (tuyệt đối) có thể bị lệnh này đụng tới, đọc từ chính dòng lệnh."""
    cmd = strip_heredoc(cmd)
    try:
        toks = shlex.split(cmd, posix=(os.name != "nt"))
    except ValueError:
        toks = re.findall(r"[^\s'\"|&;<>()]+", cmd)
    toks += re.findall(r">>?\s*([^\s|&;<>()'\"]+)", cmd)
    out, seen = [], set()
    for t in toks:
        t = t.strip("\"'")
        if "=" in t and not t.startswith(("/", ".", "~")):
            t = t.split("=", 1)[1]
        if not t or t.startswith("-") or "://" in t or len(t) > 260:
            continue
        pth = os.path.expandvars(os.path.expanduser(t))
        pth = pth if os.path.isabs(pth) else os.path.join(cwd, pth)
        for q in (glob.glob(pth) if any(c in pth for c in "*?[") else [pth]):
            q = os.path.normpath(q)
            if q not in seen:
                seen.add(q)
                out.append(q)
    return out


class Journal:
    """Một thư mục tạm cho mỗi lượt: journal.json + bản sao trước khi sửa của từng đường dẫn."""
    MAX_FILE, MAX_FILES, MAX_BYTES = 100 << 20, 3000, 200 << 20

    def __init__(self, covered=None):
        self.covered = os.path.normpath(covered) if covered else None  # nơi git đã giữ, khỏi sao lưu lần nữa
        self.dir = os.path.join(UNDO_DIR, "%s-%s" % (datetime.now().strftime("%Y%m%d-%H%M%S"), uuid.uuid4().hex[:6]))
        self.entries, self.seen = [], set()

    def _save(self):
        os.makedirs(self.dir, exist_ok=True)
        with open(os.path.join(self.dir, "journal.json"), "w", encoding="utf-8") as f:
            json.dump({"entries": self.entries}, f, ensure_ascii=False)

    def _small(self, path):
        n = size = 0
        for r, _, fs in os.walk(path):
            for f in fs:
                n += 1
                try:
                    size += os.path.getsize(os.path.join(r, f))
                except OSError:
                    pass
                if n > self.MAX_FILES or size > self.MAX_BYTES:
                    return False
        return True

    def _one(self, q):
        """Sao lưu một đường dẫn trước khi bị đụng tới. Trả về True nếu có thêm mục."""
        if q in self.seen:
            return False
        self.seen.add(q)
        if self.covered and (q == self.covered or q.startswith(self.covered + os.sep)):
            return False
        if q == os.path.expanduser("~") or os.path.dirname(q) == q:  # home hoặc gốc ổ đĩa: quá rộng
            return False
        blob = os.path.join(self.dir, "b%d" % len(self.entries))
        try:
            if os.path.islink(q) or os.path.isfile(q):
                if os.path.islink(q) or os.path.getsize(q) <= self.MAX_FILE:
                    os.makedirs(self.dir, exist_ok=True)
                    shutil.copy2(q, blob, follow_symlinks=False)
                    self.entries.append({"path": q, "kind": "file", "blob": blob})
                else:
                    self.entries.append({"path": q, "kind": "skip", "why": "file quá lớn"})
            elif os.path.isdir(q):
                if self._small(q):
                    os.makedirs(self.dir, exist_ok=True)
                    shutil.copytree(q, blob, symlinks=True)
                    self.entries.append({"path": q, "kind": "dir", "blob": blob})
                else:
                    self.entries.append({"path": q, "kind": "skip", "why": "thư mục quá lớn"})
            elif (not re.search(r"\s", q) and (os.path.splitext(q)[1] or os.sep in q)
                  and os.path.isdir(os.path.dirname(q))):
                self.entries.append({"path": q, "kind": "absent"})  # chưa có: nếu lệnh tạo ra thì /redo xóa đi
            else:
                return False
        except Exception as e:
            self.entries.append({"path": q, "kind": "skip", "why": str(e)})
        return True

    def record(self, cmd, cwd):
        changed = False
        for q in cmd_paths(cmd, cwd):
            changed = self._one(q) or changed
        if changed:
            self._save()

    def record_paths(self, paths):
        changed = False
        for q in paths:
            changed = self._one(os.path.normpath(q)) or changed
        if changed:
            self._save()


def restore_journal(jdir):
    """Đưa các đường dẫn trong journal về như trước lượt đó. Trả về (số mục đã lùi, [(đường dẫn, lý do)])."""
    with open(os.path.join(jdir, "journal.json"), encoding="utf-8") as f:
        entries = json.load(f)["entries"]
    done, fails = 0, []
    for e in reversed(entries):
        q, kind = e["path"], e["kind"]
        try:
            if kind == "skip":
                fails.append((q, "không có bản sao (%s)" % e.get("why", "")))
                continue
            if os.path.lexists(q):
                if os.path.isdir(q) and not os.path.islink(q):
                    if kind == "file":
                        shutil.rmtree(q)
                    elif kind in ("dir", "absent"):
                        shutil.rmtree(q)
                else:
                    os.remove(q)
            if kind == "file":
                os.makedirs(os.path.dirname(q), exist_ok=True)
                shutil.copy2(e["blob"], q, follow_symlinks=False)
            elif kind == "dir":
                os.makedirs(os.path.dirname(q), exist_ok=True)
                shutil.copytree(e["blob"], q, symlinks=True)
            done += 1
        except Exception as ex:
            fails.append((q, str(ex)))
    return done, fails


def drop_journal(jdir):
    if jdir and os.path.abspath(jdir).startswith(os.path.abspath(UNDO_DIR)):
        shutil.rmtree(jdir, ignore_errors=True)


def purge_journals(chat):
    for cp in chat.get("checkpoints", []):
        drop_journal(cp.get("journal"))


def purge_old_journals(days=14):
    try:
        for n in os.listdir(UNDO_DIR):
            d = os.path.join(UNDO_DIR, n)
            if time.time() - os.path.getmtime(d) > days * 86400:
                shutil.rmtree(d, ignore_errors=True)
    except OSError:
        pass


# ---------------------------------------------------------------- vòng lặp agent
def show_tool_call(name, args):
    if name == "cmd":
        shown = str(args.get("command", "")).strip()
        if args.get("background"):
            name = "cmd nền %ss" % args["background"]
    else:
        shown = json.dumps(args, ensure_ascii=False)
    lines = shown.splitlines() or [""]
    head = lines[0][:200] + (" ..." if len(lines) > 1 or len(lines[0]) > 200 else "")
    p("[%s] %s" % (name, head), C_ACC)


def show_result(res):
    lines = res.splitlines()
    for ln in lines[:25]:
        p("  " + ln[:300], C_DIM)
    if len(lines) > 25:
        p("  ... (+%d dòng)" % (len(lines) - 25), C_DIM)


def run_turn(chat, text, images=None):
    images = images or []
    note = bg_take()  # lệnh nền đã xong từ trước: gộp vào tin gửi lần này
    if text is None and not note:
        return
    commit = snapshot(STATE.cwd)
    STATE.journal = Journal(STATE.cwd if commit else None)
    cp = {"len": len(chat["messages"]), "user": text or "", "images": images, "cwd": STATE.cwd,
          "commit": commit, "journal": STATE.journal.dir,
          "memory": dict(CFG["memory"]), "skills": dict(CFG["skills"])}
    chat["checkpoints"].append(cp)
    umsg = {"role": "user", "content": ((note + "\n") if note else "") + (("<user>%s</user>" % text) if text is not None else "")}
    if images:
        umsg["images"] = images
    chat["messages"].append(umsg)
    if chat["title"] == "(mới)" and text:
        chat["title"] = text.strip().replace("\n", " ")[:50]

    for step in range(MAX_STEPS):
        if STATE.stop.is_set():
            p("[đã dừng]", C_DIM)
            break
        mode = tool_mode()
        pr = Printer(filter_tools=(mode == "text"))
        try:
            reply, calls = chat_stream(chat["messages"], build_system(mode), pr, mode)
        except Stopped as e:
            pr.end()
            if e.partial.strip():  # giữ phần model đã nói để lượt sau còn biết
                chat["messages"].append({"role": "assistant", "content": e.partial.strip() + "\n[bị tui dừng giữa chừng]"})
            p("[đã dừng]", C_DIM)
            save_chat(chat)
            return
        except NativeUnsupported:
            pr.end()
            mark_text_fallback()
            p("model/server không nhận function calling, chuyển sang kiểu thẻ <tool>.", C_DIM)
            continue
        except ApiError as e:
            pr.end()
            p("lỗi: %s" % e, C_ERR)
            if images and step == 0:
                p("(nếu model không đọc được ảnh, bỏ [Image] rồi gửi lại)", C_DIM)
            if step == 0:  # chưa làm gì thì hủy lượt này
                chat["messages"] = chat["messages"][:cp["len"]]
                chat["checkpoints"].pop()
                drop_journal(cp.get("journal"))
            save_chat(chat)
            return
        pr.end()
        if not reply and not calls:
            p("(model trả về rỗng)", C_DIM)
            break
        msg = {"role": "assistant", "content": reply}
        if calls:
            msg["tool_calls"] = [{"id": c["id"], "type": "function",
                                  "function": {"name": c["name"], "arguments": c["arguments"]}} for c in calls]
        chat["messages"].append(msg)
        if not calls:
            note = bg_take()  # AI không dùng công cụ nữa: nếu có lệnh nền vừa xong thì gửi luôn
            if not note:
                break
            chat["messages"].append({"role": "user", "content": note})
            continue
        answered = set()
        try:
            for c in calls:
                args = json.loads(c["arguments"])
                show_tool_call(c["name"], args)
                if c.get("error"):
                    res = c["error"]
                elif STATE.stop.is_set():
                    res = "(tui đã dừng, lệnh này chưa chạy)"
                else:
                    res = exec_tool(c["name"], args)
                show_result(res)
                chat["messages"].append({"role": "tool", "tool_call_id": c["id"],
                                         "content": "<result>\n%s\n</result>" % sanitize(res)})
                answered.add(c["id"])
        except KeyboardInterrupt:  # tool_call nào chưa có kết quả thì bù, tránh API báo lỗi lượt sau
            for c in calls:
                if c["id"] not in answered:
                    chat["messages"].append({"role": "tool", "tool_call_id": c["id"],
                                             "content": "<result>\n(tui đã ngắt lệnh này)\n</result>"})
            save_chat(chat)
            raise
        note = bg_take()  # gộp thông báo lệnh nền vừa xong vào cùng lần gửi kết quả công cụ
        if note:
            chat["messages"].append({"role": "user", "content": note})
        save_chat(chat)
    else:
        p("đã chạy %d bước, dừng lại. Gõ tiếp để MshLite làm tiếp." % MAX_STEPS, C_DIM)
    save_chat(chat)


# ---------------------------------------------------------------- lệnh /
def ask(label, cur, cast=str, mask=False, choices=None):
    if cur in (None, ""):
        shown = "chưa đặt"
    elif mask:
        shown = str(cur)[:4] + "..." + str(cur)[-4:] if len(str(cur)) > 10 else "***"
    else:
        shown = cur
    s = inp("%s [%s]: " % (label, shown)).strip()
    if s == "":
        return cur
    if s == "-":
        return None
    if choices and s not in choices:
        p("chỉ nhận: %s. Giữ nguyên." % "/".join(choices), C_ERR)
        return cur
    try:
        return cast(s)
    except Exception:
        p("giá trị sai, giữ nguyên.", C_ERR)
        return cur


def edit_model(m):
    p("Cấu hình model (Enter = giữ, '-' = bỏ đặt)", C_ACC)
    m["base_url"] = ask("base url", m["base_url"]) or ""
    m["model"] = ask("model", m["model"]) or ""
    m["api_key"] = ask("api key", m["api_key"], mask=True) or ""
    m["max_tokens"] = ask("max token", m["max_tokens"], int)
    m["temperature"] = ask("temp", m["temperature"], float)
    m["top_p"] = ask("top p", m["top_p"], float)
    m["top_k"] = ask("top k", m["top_k"], int)
    m["effort"] = ask("effort low/medium/high/xhigh", m["effort"], choices=["low", "medium", "high", "xhigh"])
    m["tool_mode"] = ask("tool auto/native/text", m.get("tool_mode", "auto"),
                         choices=["auto", "native", "text"]) or "auto"
    sa = ask("sub-agent on/off (AI chính giao việc cho AI phụ chạy song song)",
             "on" if CFG.get("subagent") else "off", choices=["on", "off"])
    CFG["subagent"] = (sa or "off") == "on"
    if m["tool_mode"] == "auto" and model_key() in CFG["text_models"]:
        CFG["text_models"].remove(model_key())  # thử lại function calling từ đầu


def cmd_model(chat):
    models = CFG.setdefault("models", {})
    cur = CFG["model"]
    if not models and (cur.get("model") or cur.get("base_url")):  # lần đầu: lưu model đang dùng vào danh sách
        models[cur.get("model") or cur.get("base_url")] = dict(cur)
    while True:
        names = list(models)
        p("Các model đã lưu (%d):" % len(names), C_ACC)
        for i, n in enumerate(names, 1):
            mm = models[n]
            on = mm.get("base_url") == CFG["model"].get("base_url") and mm.get("model") == CFG["model"].get("model")
            p("  %s %d. %-24s %s" % ("*" if on else " ", i, n, mm.get("base_url", "")), C_OK if on else C_TEXT)
        c = inp("số=chọn/sửa  n=mới  d số=xóa  (* = đang dùng)  Enter=thoát: ").strip().lower()
        if c == "":
            save_cfg()
            return
        mt = re.fullmatch(r"d\s*(\d+)", c)
        if mt:
            i = int(mt.group(1))
            if 1 <= i <= len(names):
                gone = models.pop(names[i - 1])
                if gone.get("base_url") == CFG["model"].get("base_url") and gone.get("model") == CFG["model"].get("model"):
                    CFG["model"] = dict(next(iter(models.values()), DEFAULT_CFG["model"]))
                save_cfg()
                p("đã xóa.", C_OK)
            else:
                p("không có số đó.", C_ERR)
        elif c == "n":
            m = dict(DEFAULT_CFG["model"])
            CFG["model"] = m
            edit_model(m)
            key, k = (m.get("model") or m.get("base_url") or "model"), 1
            name = key
            while name in models:
                k += 1
                name = "%s-%d" % (key, k)
            models[name] = m
            save_cfg()
            p("đã lưu và đang dùng model này.", C_OK)
        elif c.isdigit() and 1 <= int(c) <= len(names):
            m = models[names[int(c) - 1]]
            CFG["model"] = m  # chọn: dùng model này; các dòng dưới cho sửa (Enter = giữ nguyên)
            edit_model(m)
            save_cfg()
            p("đã lưu, đang dùng: %s" % names[int(c) - 1], C_OK)
        else:
            p("nhập số, n, hoặc d số.", C_ERR)


def read_multiline(existing):
    p("nhập nội dung, kết thúc bằng dòng chỉ có dấu '.'  (hoặc dòng đầu @đường_dẫn_file)"
      + ("; '.' ngay dòng đầu = giữ nguyên" if existing is not None else ""), C_DIM)
    lines = []
    while True:
        ln = input()
        if ln.strip() == ".":
            break
        if not lines and ln.startswith("@"):
            with open(os.path.expanduser(ln[1:].strip()), encoding="utf-8") as f:
                return f.read()
        lines.append(ln)
    if not lines and existing is not None:
        return existing
    return "\n".join(lines)


def manage(title, store_name, kind):
    while True:
        store = CFG[store_name]
        p("%s (%d):" % (title, len(store)), C_ACC)
        for k, v in store.items():
            desc = first_line(v) if kind == "text" else (v["target"] + ("  [có key]" if v.get("key") else ""))
            p("  %-18s %s" % (k, desc), C_TEXT)
        c = inp("a=thêm/sửa  v=xem  d=xóa  Enter=thoát: ").strip().lower()
        if c == "":
            return
        if c not in ("a", "v", "d"):
            continue
        name = inp("name: ").strip()
        if not re.fullmatch(r"[\w\-.]+", name):
            p("tên chỉ gồm chữ, số, - _ .", C_ERR)
            continue
        if c == "v":
            if name in store:
                p(store[name] if kind == "text" else json.dumps(store[name], ensure_ascii=False), C_TEXT)
            else:
                p("không có.", C_ERR)
        elif c == "d":
            if store.pop(name, None) is not None:
                if kind == "mcp":
                    mcp_reset(name)
                save_cfg()
                p("đã xóa.", C_OK)
            else:
                p("không có.", C_ERR)
        else:
            if kind == "text":
                store[name] = read_multiline(store.get(name))
            else:
                old = store.get(name, {})
                target = ask("url/command", old.get("target")) or ""
                key = ask("key", old.get("key"), mask=True) or ""
                if not target:
                    p("thiếu url/command.", C_ERR)
                    continue
                store[name] = {"target": target, "key": key}
                mcp_reset(name)
            save_cfg()
            p("đã lưu.", C_OK)


def cmd_compact(chat):
    if not chat["messages"]:
        p("chưa có gì để nén.", C_DIM)
        return
    n = len(chat["messages"])
    ask_msg = {"role": "user", "content": (
        "<system>Hãy tóm tắt toàn bộ cuộc trò chuyện ở trên thật gọn nhưng đủ để làm tiếp: "
        "yêu cầu của tui, việc đã làm, file đã tạo/sửa/xóa, quyết định quan trọng, lỗi gặp phải, việc còn dở. "
        "Không dùng công cụ, chỉ viết bản tóm tắt.</system>")}
    p("đang nén %d tin ..." % n, C_DIM)
    s = strip_tool(chat_stream(chat["messages"] + [ask_msg], build_system("text"), None, "text")[0])
    if not s:
        p("model không tóm tắt được.", C_ERR)
        return
    chat["messages"] = [{"role": "user", "content": "<system>Tóm tắt phần trò chuyện trước:\n%s</system>" % s}]
    purge_journals(chat)
    chat["checkpoints"] = []
    save_chat(chat)
    p("đã nén %d tin thành 1 bản tóm tắt (/redo không lùi được qua mốc này)." % n, C_OK)


def last_output(chat):
    for m in reversed(chat["messages"]):
        if m["role"] == "assistant":
            t = strip_tool(m["content"])
            if t:
                return t
    return ""


def cmd_copy(chat):
    t = last_output(chat)
    if not t:
        p("chưa có output nào của model.", C_DIM)
    elif copy_text(t):
        p("đã copy (%d ký tự)." % len(t), C_OK)
    else:
        p("không copy được.", C_ERR)


def cmd_redo(chat):
    if not chat["checkpoints"]:
        p("không còn lượt nào để lùi.", C_DIM)
        return
    cp = chat["checkpoints"].pop()
    chat["messages"] = chat["messages"][:cp["len"]]
    CFG["memory"], CFG["skills"] = cp["memory"], cp["skills"]
    save_cfg()
    if cp.get("commit"):
        try:
            restore(cp["cwd"], cp["commit"])
            STATE.cwd = cp["cwd"]
            p("đã lùi chat và file trong %s." % cp["cwd"], C_OK)
        except Exception as e:
            p("lùi chat được, nhưng file lỗi: %s" % e, C_ERR)
    else:
        p("đã lùi chat (thư mục làm việc không có mốc nên không lùi).", C_OK)
    jd = cp.get("journal")
    if jd and os.path.isfile(os.path.join(jd, "journal.json")):
        try:
            n, fails = restore_journal(jd)
            if n:
                p("đã lùi %d đường dẫn ngoài mốc (từ bản sao tạm)." % n, C_OK)
            for f in fails:
                p("  không lùi được %s: %s" % f, C_ERR)
        except Exception as e:
            p("không đọc được file tạm: %s" % e, C_ERR)
        drop_journal(jd)
    elif jd:
        p("(không có đường dẫn nào cần lùi ngoài mốc, hoặc bản sao tạm đã bị dọn)", C_DIM)
    p("chỉ lùi được các đường dẫn có trong dòng lệnh; việc script tự ghi chỗ khác và thao tác qua mcp thì không.", C_DIM)
    STATE.prefill = cp["user"]
    toks = re.findall(r"\[Image #(\d+)\]", cp["user"])
    STATE.prefill_images = {int(n): pth for n, pth in zip(toks, cp.get("images") or [])}
    if chat["messages"] or True:
        save_chat(chat)
        if not chat["messages"]:
            try:
                os.remove(os.path.join(CHAT_DIR, chat["id"] + ".json"))
            except Exception:
                pass


def cmd_conversation(chat):
    while True:
        chats = list_chats()
        p("Các chat:", C_ACC)
        for i, c in enumerate(chats, 1):
            mark = "*" if c["id"] == chat["id"] else " "
            when = datetime.fromtimestamp(c.get("updated", 0)).strftime("%d/%m %H:%M")
            p("%s %2d  %-50s %3d tin  %s" % (mark, i, c["title"][:50], len(c["messages"]), when))
        s = inp("số=mở  n=mới  d số=xóa  Enter=thoát: ").strip().lower()
        if s == "":
            return chat
        if s == "n":
            save_chat(chat)
            chat = new_chat()
            p("đã tạo chat mới.", C_OK)
            return chat
        try:
            if s.startswith("d"):
                c = chats[int(s[1:].strip()) - 1]
                purge_journals(c)
                os.remove(os.path.join(CHAT_DIR, c["id"] + ".json"))
                p("đã xóa '%s'." % c["title"], C_OK)
                if c["id"] == chat["id"]:
                    chat = new_chat()
                    CFG["current_chat"] = None
                    save_cfg()
            else:
                c = chats[int(s) - 1]
                save_chat(chat)
                chat = c
                if os.path.isdir(c.get("cwd", "")):
                    STATE.cwd = c["cwd"]
                CFG["current_chat"] = c["id"]
                save_cfg()
                p("đã mở '%s'." % c["title"], C_OK)
                return chat
        except (ValueError, IndexError):
            p("không hiểu.", C_ERR)


def clear_screen():
    w(RESET + "\033[2J\033[3J\033[H")


def banner(chat):
    m = CFG["model"]
    p("MshLite", C_ACC)
    rule()
    p("model: %s   effort: %s   tool: %s" % (
        m.get("model") or "(chưa đặt)", m.get("effort") or "-",
        "function calling" if tool_mode() == "native" else "thẻ <tool>"), C_DIM)
    p("thư mục: %s" % STATE.cwd, C_DIM)
    p("chat: %s" % chat["title"], C_DIM)
    rule()


# ---------------------------------------------------------------- ô nhập: Shift+Enter, chọn text, dán ảnh
IMG_RE = re.compile(r"\[Image #(\d+)\]")
IMG_EXT = (".png", ".jpg", ".jpeg", ".gif", ".webp")
_MIME = {".png": "image/png", ".jpg": "image/jpeg", ".jpeg": "image/jpeg",
         ".gif": "image/gif", ".webp": "image/webp"}


def raw_ok():
    return (os.name == "nt" or bool(termios)) and sys.stdin.isatty() and sys.stdout.isatty()


def _cw(ch):
    if unicodedata.combining(ch):
        return 0
    return 2 if unicodedata.east_asian_width(ch) in ("W", "F") else 1


def clipboard_image():
    """Lấy ảnh trong clipboard, lưu thành file png. Trả về đường dẫn hoặc None."""
    path = os.path.join(IMG_DIR, "%s-%s.png" % (datetime.now().strftime("%Y%m%d-%H%M%S"), uuid.uuid4().hex[:4]))
    data = None
    try:
        if os.name == "nt":
            ps = ("Add-Type -AssemblyName System.Windows.Forms,System.Drawing;"
                  "$i=[Windows.Forms.Clipboard]::GetImage();"
                  "if($i){$i.Save('%s',[Drawing.Imaging.ImageFormat]::Png)}" % path)
            subprocess.run(["powershell", "-NoProfile", "-STA", "-Command", ps], capture_output=True, timeout=20)
            return path if os.path.isfile(path) and os.path.getsize(path) > 0 else None
        if sys.platform == "darwin":
            if shutil.which("pngpaste"):
                r = subprocess.run(["pngpaste", "-"], capture_output=True, timeout=8)
                if r.returncode == 0:
                    data = r.stdout
            if not data:
                lines = ["try", 'set f to open for access POSIX file "%s" with write permission' % path,
                         "set eof of f to 0", "write (the clipboard as «class PNGf») to f",
                         "close access f", "end try"]
                subprocess.run(["osascript"] + [x for l in lines for x in ("-e", l)],
                               capture_output=True, timeout=8)
                if os.path.isfile(path) and os.path.getsize(path) > 0:
                    return path
                if os.path.isfile(path):
                    os.remove(path)
        else:
            for cmd in (["wl-paste", "--type", "image/png"], ["xclip", "-selection", "clipboard", "-t", "image/png", "-o"]):
                if shutil.which(cmd[0]):
                    r = subprocess.run(cmd, capture_output=True, timeout=8)
                    if r.returncode == 0 and r.stdout[:4] == b"\x89PNG":
                        data = r.stdout
                        break
            if not data and shutil.which("powershell.exe") and shutil.which("wslpath"):  # WSL
                win = subprocess.run(["wslpath", "-w", path], capture_output=True, text=True).stdout.strip()
                ps = ("Add-Type -AssemblyName System.Windows.Forms;$i=[Windows.Forms.Clipboard]::GetImage();"
                      "if($i){$i.Save('%s',[Drawing.Imaging.ImageFormat]::Png)}" % win)
                subprocess.run(["powershell.exe", "-NoProfile", "-Command", ps], capture_output=True, timeout=15)
                if os.path.isfile(path) and os.path.getsize(path) > 0:
                    return path
        if data and data[:4] == b"\x89PNG":
            with open(path, "wb") as f:
                f.write(data)
            return path
    except Exception:
        pass
    return None


def clipboard_text():
    for cmd in (["pbpaste"], ["wl-paste", "--no-newline"], ["xclip", "-selection", "clipboard", "-o"],
                ["xsel", "--clipboard", "--output"], ["powershell.exe", "-NoProfile", "-Command", "Get-Clipboard -Raw"]):
        if shutil.which(cmd[0]):
            try:
                r = subprocess.run(cmd, capture_output=True, timeout=8)
                if r.returncode == 0:
                    return r.stdout.decode("utf-8", "replace")
            except Exception:
                continue
    return ""


def as_image_path(t):
    t = t.strip()
    if t.startswith("file://"):
        t = urllib.parse.unquote(t[7:])
    if len(t) > 1 and t[0] == t[-1] and t[0] in "'\"":
        t = t[1:-1]
    t = os.path.expanduser(re.sub(r"\\(.)", r"\1", t))
    return t if t.lower().endswith(IMG_EXT) and os.path.isfile(t) else None


def layout(text, W, ind=2):
    """Vị trí (hàng, cột) của từng chỉ số 0..n khi vẽ trong khung rộng W (ind cột đầu là '> ' hoặc 'btw> ')."""
    pos, row, col = [], 0, ind
    for ch in text:
        if ch == "\n":
            pos.append((row, col))
            row, col = row + 1, ind
            continue
        cw = _cw(ch)
        if col + cw > W:
            row, col = row + 1, 0
        pos.append((row, col))
        col += cw
    if col >= W:
        row, col = row + 1, 0
    pos.append((row, col))
    return pos


class KeyReader:
    """Đọc phím từ terminal raw: mũi tên, Shift/Alt/Ctrl, kitty/xterm, bracketed paste."""

    def __init__(self, fd):
        self.fd, self.buf, self.pend, self.mouse = fd, "", [], False
        self.dec = codecs.getincrementaldecoder("utf-8")("replace")

    def _fill(self, timeout):
        if not select.select([self.fd], [], [], timeout)[0]:
            return False
        data = os.read(self.fd, 4096)
        if not data:
            raise EOFError
        self.buf += self.dec.decode(data)
        return True

    def read(self, timeout=None):
        return self.pend.pop(0) if self.pend else self._read(timeout)

    def set_mouse(self, on):
        """Bật/tắt báo chuột (nhấn/kéo, dạng SGR). Tắt thì terminal tự chọn chữ và cuộn như bình thường."""
        if on != self.mouse:
            w("\033[?1002h\033[?1006h" if on else "\033[?1002l\033[?1006l", screen=False)
            self.mouse = on
            mlog("set_mouse %s" % on)

    def left_state(self):
        """Terminal dạng escape không cho biết nút chuột; nơi gọi tự dùng hẹn giờ."""
        return None

    def cursor_pos(self):
        return None

    def double_click(self):
        return 500

    def _read(self, timeout):
        end = None if timeout is None else time.time() + timeout
        while True:
            if not self.buf:
                left = None if end is None else end - time.time()
                if left is not None and left <= 0:
                    return None
                self._fill(left)
                continue
            ev = self._parse(False)
            if ev:
                return ev
            if not self._fill(1.0 if self.buf.startswith("\x1b[200~") else 0.05):
                ev = self._parse(True)
                if ev:
                    return ev

    def cursor_row(self):
        """Hàng (0-based) của con trỏ terminal, cùng hệ tọa độ với toạ độ chuột. None nếu terminal không trả lời."""
        w("\033[6n", screen=False)
        end = time.time() + 0.6
        while time.time() < end:
            ev = self._read(max(0.01, end - time.time()))
            if ev is None:
                break
            if ev[0] == "cpr":
                return ev[1][0] - 1
            self.pend.append(ev)
        return None

    @staticmethod
    def _mods(m):
        return frozenset(n for bit, n in ((1, "shift"), (2, "alt"), (4, "ctrl"), (8, "super")) if (m - 1) & bit)

    def _plain(self, c):
        o, e = ord(c), frozenset()
        if c == "\r":
            return ("enter", e)
        if c == "\n":
            return ("enter", frozenset({"shift"}))
        if c in ("\x7f", "\x08"):
            return ("backspace", e)
        if c == "\t":
            return ("tab", e)
        if o < 32:
            return (chr(o + 96), frozenset({"ctrl"}))
        return (c, e)

    def _parse(self, force):
        b = self.buf
        if b[0] != "\x1b":
            self.buf = b[1:]
            return self._plain(b[0])
        if len(b) == 1:
            if force:
                self.buf = ""
                return ("esc", frozenset())
            return None
        c2 = b[1]
        if c2 == "\x1b":  # hai Esc dính liền: tách ra, đây là Esc chứ không phải Alt+Esc
            self.buf = b[1:]
            return ("esc", frozenset())
        if c2 == "[":
            if b.startswith("\x1b[200~"):
                end = b.find("\x1b[201~")
                if end < 0:
                    if not force:
                        return None
                    self.buf = ""
                    return ("paste", b[6:])
                self.buf = b[end + 6:]
                return ("paste", b[6:end])
            m = re.match(r"\x1b\[([0-9:;<=>?]*)([ -/]*)([@-~])", b)
            if not m:
                if not force:
                    return None
                self.buf = b[2:]
                return ("unknown", frozenset())
            self.buf = b[m.end():]
            return self._csi(m.group(1), m.group(3))
        if c2 == "O":
            if len(b) < 3:
                if not force:
                    return None
                self.buf = ""
                return ("unknown", frozenset())
            self.buf = b[3:]
            k = {"A": "up", "B": "down", "C": "right", "D": "left", "H": "home", "F": "end"}.get(b[2], "unknown")
            return (k, frozenset())
        self.buf = b[2:]
        k, m = self._plain(c2)
        return (k, m | {"alt"})

    def _csi(self, params, final):
        parts = params.split(";")

        def num(i, d):
            try:
                return int(parts[i].split(":")[0])
            except (IndexError, ValueError):
                return d
        if final in "ABCD":
            return ({"A": "up", "B": "down", "C": "right", "D": "left"}[final], self._mods(num(1, 1)))
        if final == "H":
            return ("home", self._mods(num(1, 1)))
        if final == "F":
            return ("end", self._mods(num(1, 1)))
        if final == "Z":
            return ("tab", frozenset({"shift"}))
        if final == "R":
            return ("cpr", (num(0, 1), num(1, 1)))
        if final in "Mm" and params.startswith("<"):  # chuột SGR: nhấn, kéo, nhả nút trái
            try:
                b, x, y = (int(v) for v in params[1:].split(";")[:3])
            except ValueError:
                return ("unknown", ())
            if b & 64:
                return ("wheel", ())
            if b & 3:
                return ("unknown", ())
            kind = "up" if final == "m" else ("drag" if b & 32 else "down")
            return ("mouse", (kind, x - 1, y - 1, bool(b & 4)))
        if final == "~":
            n = num(0, 0)
            if n == 27:
                return self._code(num(2, 0), self._mods(num(1, 1)))
            k = {1: "home", 2: "insert", 3: "delete", 4: "end", 5: "pgup", 6: "pgdn", 7: "home", 8: "end"}.get(n, "unknown")
            return (k, self._mods(num(1, 1)))
        if final == "u":
            return self._code(num(0, 0), self._mods(num(1, 1)))
        return ("unknown", frozenset())

    @staticmethod
    def _code(code, mods):
        names = {13: "enter", 9: "tab", 27: "esc", 127: "backspace"}
        if code in names:
            return (names[code], mods)
        if code < 32 or code > 0x10FFFF:
            return ("unknown", mods)
        ch = chr(code)
        if "shift" in mods and ch.isalpha():
            ch = ch.upper()
        return (ch, mods)


class WinKeyReader:
    """Windows: đọc sự kiện phím bằng ReadConsoleInputW nên biết chính xác Shift/Ctrl/Alt."""
    VK = {0x08: "backspace", 0x09: "tab", 0x0D: "enter", 0x1B: "esc", 0x21: "pgup", 0x22: "pgdn", 0x23: "end",
          0x24: "home", 0x25: "left", 0x26: "up", 0x27: "right", 0x28: "down", 0x2D: "insert", 0x2E: "delete"}

    def __init__(self):
        import ctypes
        from ctypes import wintypes as wt

        class KEY(ctypes.Structure):
            _fields_ = [("down", wt.BOOL), ("rep", wt.WORD), ("vk", wt.WORD), ("scan", wt.WORD),
                        ("ch", wt.WCHAR), ("st", wt.DWORD)]

        class MOUSE(ctypes.Structure):
            _fields_ = [("x", wt.SHORT), ("y", wt.SHORT), ("btn", wt.DWORD), ("st", wt.DWORD), ("flags", wt.DWORD)]

        class REC(ctypes.Structure):
            class _U(ctypes.Union):
                _fields_ = [("key", KEY), ("mouse", MOUSE), ("pad", ctypes.c_byte * 16)]
            _anonymous_ = ("u",)
            _fields_ = [("type", wt.WORD), ("u", _U)]

        class COORD(ctypes.Structure):
            _fields_ = [("X", wt.SHORT), ("Y", wt.SHORT)]

        class RECT(ctypes.Structure):
            _fields_ = [("L", wt.SHORT), ("T", wt.SHORT), ("R", wt.SHORT), ("B", wt.SHORT)]

        class CSBI(ctypes.Structure):
            _fields_ = [("size", COORD), ("cur", COORD), ("attr", wt.WORD), ("win", RECT), ("maxw", COORD)]

        class POINT(ctypes.Structure):
            _fields_ = [("x", wt.LONG), ("y", wt.LONG)]

        k = ctypes.windll.kernel32
        k.GetStdHandle.restype = wt.HANDLE
        k.GetConsoleMode.argtypes = [wt.HANDLE, ctypes.POINTER(wt.DWORD)]
        k.SetConsoleMode.argtypes = [wt.HANDLE, wt.DWORD]
        k.ReadConsoleInputW.argtypes = [wt.HANDLE, ctypes.POINTER(REC), wt.DWORD, ctypes.POINTER(wt.DWORD)]
        k.GetConsoleScreenBufferInfo.argtypes = [wt.HANDLE, ctypes.POINTER(CSBI)]
        k.GetNumberOfConsoleInputEvents.argtypes = [wt.HANDLE, ctypes.POINTER(wt.DWORD)]
        self.ct, self.wt, self.REC, self.CSBI, self.POINT, self.k = ctypes, wt, REC, CSBI, POINT, k
        self.u = ctypes.windll.user32
        self.u.GetCursorPos.argtypes = [ctypes.POINTER(POINT)]
        self.h, self.ho, self.q, self.hi, self.old = k.GetStdHandle(-10), k.GetStdHandle(-11), [], "", wt.DWORD()
        self.mouse, self.left = False, False

    def enter(self):
        self.k.GetConsoleMode(self.h, self.ct.byref(self.old))
        # tắt PROCESSED(0x1)/LINE(0x2)/ECHO(0x4)/MOUSE(0x10)/VT_INPUT(0x200): Ctrl+C thành phím thường
        self.base = self.old.value & ~(0x1 | 0x2 | 0x4 | 0x10 | 0x200)
        # QuickEdit(0x40) + EXTENDED(0x80): không bắt chuột thì conhost tự kéo-chọn chữ như terminal thường
        self.native = self.base | 0x40 | 0x80
        self.mouse = False
        self.k.SetConsoleMode(self.h, self.native)

    def set_mouse(self, on):
        """Bật MOUSE(0x10) và tắt QuickEdit(0x40) để nhận chuột; tắt thì terminal tự chọn chữ/cuộn."""
        if on != self.mouse:
            self.k.SetConsoleMode(self.h, ((self.base & ~0x40) | 0x10 | 0x80) if on else self.native)
            self.mouse = on
            mlog("set_mouse %s" % on)

    def cursor_row(self):
        info = self.CSBI()
        self.k.GetConsoleScreenBufferInfo(self.ho, self.ct.byref(info))
        return info.cur.Y

    def mev(self, m):
        left, was = bool(m.btn & 1), self.left
        self.left = left
        if m.flags & 4:  # lăn chuột
            return ("wheel", ())
        pos = (m.x, m.y, bool(m.st & 0x10))
        if left and not was:
            return ("mouse", ("down",) + pos)
        if was and not left:
            return ("mouse", ("up",) + pos)
        if left and m.flags & 1:
            return ("mouse", ("drag",) + pos)
        return None

    def left_state(self):
        """(đang giữ nút trái, vừa có cú nhấn) đọc thẳng từ Windows, kể cả khi chuột đã trả cho terminal."""
        v = self.u.GetAsyncKeyState(0x01)
        return bool(v & 0x8000), bool(v & 1)

    def cursor_pos(self):
        p = self.POINT()
        return (p.x, p.y) if self.u.GetCursorPos(self.ct.byref(p)) else None

    def double_click(self):
        return max(200, int(self.u.GetDoubleClickTime()))

    def leave(self):
        self.k.SetConsoleMode(self.h, self.old.value)

    def read(self, timeout=None):
        while not self.q:
            if timeout is not None:
                n = self.wt.DWORD()
                if not self.k.GetNumberOfConsoleInputEvents(self.h, self.ct.byref(n)) or n.value == 0:
                    time.sleep(timeout)  # không có gì trong hàng đợi: nhả ra để vòng lặp kiểm tra chuột
                    return None
            buf, n = (self.REC * 128)(), self.wt.DWORD()
            if not self.k.ReadConsoleInputW(self.h, buf, 128, self.ct.byref(n)):
                raise EOFError
            evs = []
            for i in range(n.value):
                r = buf[i]
                ev = None
                if r.type == 1 and r.key.down:
                    ev = self.ev(r.key)
                elif r.type == 2 and self.mouse:
                    ev = self.mev(r.mouse)
                if ev:
                    evs.append(ev)
            self.q += self.merge(evs)
        return self.q.pop(0)

    def ev(self, e):
        st, vk, ch = e.st, e.vk, e.ch
        mods = set()
        if st & 0x10:
            mods.add("shift")
        if st & 0x3:
            mods.add("alt")
        if st & 0xC:
            mods.add("ctrl")
        if vk in self.VK:
            return (self.VK[vk], frozenset(mods))
        if vk in (0x10, 0x11, 0x12, 0x14, 0x5B, 0x5C, 0x90, 0x91):  # chỉ bấm Shift/Ctrl/Alt/...
            return None
        if ch and ch >= " " and ch != "\x7f":
            if "\ud800" <= ch <= "\udbff":
                self.hi = ch
                return None
            if "\udc00" <= ch <= "\udfff" and self.hi:
                ch, self.hi = (self.hi + ch).encode("utf-16-le", "surrogatepass").decode("utf-16-le"), ""
            m = mods - {"shift"}
            return (ch, frozenset() if {"ctrl", "alt"} <= m else frozenset(m))  # AltGr = Ctrl+Alt
        if 0x41 <= vk <= 0x5A and ("ctrl" in mods or "alt" in mods):
            return (chr(vk + 32), frozenset(mods))
        return None

    @staticmethod
    def merge(evs):
        """Dán trên Windows tới dưới dạng một loạt phím: gộp >=3 ký tự liền nhau thành một lần dán."""
        def plain(e):
            return (len(e[0]) == 1 and not e[1]) or (e[0] == "enter" and not e[1])
        out, run = [], []

        def flush():
            tail = [run.pop()] if run and run[-1][0] == "enter" else []  # Enter cuối vẫn là gửi
            if len(run) >= 3:
                out.append(("paste", "".join("\n" if k == "enter" else k for k, _ in run)))
            else:
                out.extend(run)
            out.extend(tail)
            run.clear()
        for e in evs:
            if plain(e):
                run.append(e)
            else:
                flush()
                out.append(e)
        flush()
        return out


class RawTerm:
    """with RawTerm() as kr: ... kr.read() -> (phím, {mods}) hoặc ('paste', text)."""

    def __enter__(self):
        if os.name == "nt":
            self.kr = WinKeyReader()
            self.kr.enter()
        else:
            self.fd = sys.stdin.fileno()
            self.old = termios.tcgetattr(self.fd)
            self.kr = KeyReader(self.fd)
            tty.setraw(self.fd)
        return self.kr

    def __exit__(self, *a):
        self.kr.set_mouse(False)
        if os.name == "nt":
            self.kr.leave()
        else:
            termios.tcsetattr(self.fd, termios.TCSADRAIN, self.old)


COMMANDS = [
    ("/model", "cấu hình model: base url, model, api key, ..."),
    ("/skill", "thêm, sửa, xóa skill"),
    ("/mcp", "thêm, sửa, xóa MCP server"),
    ("/memory", "thêm, sửa, xóa bộ nhớ"),
    ("/compact", "nén chat thành một bản tóm tắt"),
    ("/copy", "copy câu trả lời cuối của model"),
    ("/conversation", "mở, tạo mới, xóa chat"),
    ("/branch", "rẽ nhánh: nhân bản chat này, thêm -branch ở cuối"),
    ("/btw", "hỏi nhanh: không dùng công cụ, không ghi vào chat"),
    ("/clear", "dọn màn hình (model vẫn nhớ)"),
    ("/redo", "lùi lượt chat gần nhất, kể cả file ngoài thư mục làm việc"),
    ("/exit", "thoát"),
]


class Editor:
    def __init__(self, hist, prefill="", images=None):
        self.hist, self.hidx, self.draft = hist, len(hist), ""
        self.text, self.cur, self.anchor = prefill, len(prefill), None
        self.images = dict(images or {})
        self.next_img = max(self.images, default=0) + 1
        self.cur_row, self.wr, self.goal = 0, 0, None
        self.origin, self.drag, self.outside = 0, False, False
        self.msel, self.menu_off, self._mt = 0, False, None  # menu lệnh: dòng đang chọn, đã đóng bằng Esc, chữ lần trước
        self.btw, self.ind = False, 2  # chế độ /btw: ô nhập hiện "btw> ...", tiền tố dài 5 cột

    # --- chọn / sửa
    def W(self):
        return max(20, shutil.get_terminal_size((80, 24)).columns)

    def sel(self):
        if self.anchor is None or self.anchor == self.cur:
            return None
        return (min(self.anchor, self.cur), max(self.anchor, self.cur))

    def del_range(self, a, b):
        self.text = self.text[:a] + self.text[b:]
        self.cur, self.anchor = a, None

    def del_sel(self):
        s = self.sel()
        if s:
            self.del_range(*s)
            return True
        self.anchor = None
        return False

    def insert(self, t):
        self.del_sel()
        self.text = self.text[:self.cur] + t + self.text[self.cur:]
        self.cur += len(t)

    def move(self, pos, extend):
        if extend:
            if self.anchor is None:
                self.anchor = self.cur
        else:
            self.anchor = None
        self.cur = max(0, min(len(self.text), pos))

    def word_left(self, i):
        t = self.text
        while i > 0 and not t[i - 1].isalnum():
            i -= 1
        while i > 0 and t[i - 1].isalnum():
            i -= 1
        return i

    def word_right(self, i):
        t, n = self.text, len(self.text)
        while i < n and not t[i].isalnum():
            i += 1
        while i < n and t[i].isalnum():
            i += 1
        return i

    def line_start(self, i):
        return self.text.rfind("\n", 0, i) + 1

    def line_end(self, i):
        j = self.text.find("\n", i)
        return len(self.text) if j < 0 else j

    def vertical(self, d, extend):
        pos = layout(self.text, self.W(), self.ind)
        r, c = pos[self.cur]
        if self.goal is None:
            self.goal = c
        cand = [j for j, (rr, _) in enumerate(pos) if rr == r + d]
        if not cand:
            return False
        self.move(min(cand, key=lambda j: abs(pos[j][1] - self.goal)), extend)
        return True

    def hist_move(self, d):
        if not self.hist:
            return
        if self.hidx == len(self.hist) and d < 0:
            self.draft = self.text
        ni = self.hidx + d
        if ni < 0 or ni > len(self.hist):
            return
        self.hidx = ni
        self.text = self.draft if ni == len(self.hist) else self.hist[ni]
        self.cur, self.anchor = len(self.text), None

    # --- menu lệnh
    def menu(self):
        """Các lệnh khớp khi đang gõ tên lệnh (bắt đầu bằng '/', chưa có dấu cách)."""
        t = self.text
        if t != self._mt:  # chữ đổi: chọn lại dòng đầu, mở lại menu
            self._mt, self.msel, self.menu_off = t, 0, False
        if self.menu_off or not t.startswith("/") or " " in t or "\n" in t:
            return []
        return [c for c in COMMANDS if c[0].startswith(t.lower())]

    def menu_lines(self, W):
        items = self.menu()
        if not items:
            return []
        self.msel = min(self.msel, len(items) - 1)
        top = max(0, min(self.msel - 3, len(items) - 8))  # cửa sổ tối đa 8 dòng, cuộn theo dòng đang chọn
        lines = []
        for i in range(top, min(len(items), top + 8)):
            c, d = items[i]
            sel = i == self.msel
            lines.append((C_ACC if sel else C_DIM) + (("> " if sel else "  ") + "%-14s %s" % (c, d))[:max(1, W - 1)] + RESET)
        return lines

    # --- chuột
    def index_at(self, x, row):
        """Chỉ số ký tự ở cột x, hàng row (tính từ dòng đầu của ô nhập)."""
        t = self.text
        pos = layout(t, self.W(), self.ind)
        row = max(0, min(row, pos[len(t)][0]))
        cand = [j for j, (r, _) in enumerate(pos) if r == row]
        if not cand:
            return len(t)
        end = cand[-1]
        if end < len(t) and t[end] != "\n" and x >= pos[end][1] + _cw(t[end]):
            return end + 1
        best = cand[0]
        for j in cand:
            if pos[j][1] <= x:
                best = j
        return best

    def mouse(self, kr, kind, x, y, shift=False):
        """Trả về True nếu cần vẽ lại. Nhấn chuột ngoài ô nhập thì đặt self.outside."""
        mlog("mouse %s x=%s y=%s shift=%s len=%s" % (kind, x, y, shift, len(self.text)))
        if kind == "down":
            base = kr.cursor_row()  # hàng tuyệt đối của con trỏ terminal
            if base is None:
                return False
            self.origin = base - self.cur_row  # hàng tuyệt đối của dòng đầu ô nhập
            mlog("  origin=%s wr=%s cur_row=%s" % (self.origin, self.wr, self.cur_row))
            if not self.origin <= y <= self.origin + self.wr:
                self.outside, self.drag = True, False  # bấm ngoài ô nhập: bỏ chọn, để MshLite bôi đen vùng output
                self.anchor = None
                return True
            self.outside = False
            j = self.index_at(x, y - self.origin)
            if shift and self.anchor is None:
                self.anchor = self.cur
            elif not shift:
                self.anchor = j
            self.cur, self.drag = j, True
        elif kind == "drag" and self.drag:
            self.cur = self.index_at(x, y - self.origin)
        elif kind == "up":
            self.drag = False
            if self.anchor == self.cur:
                self.anchor = None
        return True

    # --- ảnh và dán
    def add_image(self, path, copy=True):
        dst = path
        if copy:
            ext = os.path.splitext(path)[1].lower() or ".png"
            dst = os.path.join(IMG_DIR, "%s-%s%s" % (datetime.now().strftime("%Y%m%d-%H%M%S"), uuid.uuid4().hex[:4], ext))
            try:
                shutil.copyfile(path, dst)
            except Exception:
                dst = path
        n = self.next_img
        self.next_img += 1
        self.images[n] = dst
        self.insert("[Image #%d]" % n)

    def paste(self, t):
        t = t.replace("\r\n", "\n").replace("\r", "\n")
        if not t.strip():
            if t:
                self.insert(t)
            return
        paths = []
        for ln in t.strip().split("\n"):
            whole = as_image_path(ln)  # cả dòng là một đường dẫn (kể cả có dấu cách)
            if whole:
                paths.append(whole)
                continue
            try:
                parts = shlex.split(ln)
            except ValueError:
                parts = [ln]
            paths += [as_image_path(x) for x in (parts or [ln])]
        if paths and all(paths):
            for i, pth in enumerate(paths):
                if i:
                    self.insert(" ")
                self.add_image(pth)
            return
        self.insert(t.replace("\t", "    "))

    def paste_clip(self):
        img = clipboard_image()
        if img:
            self.add_image(img, copy=False)
        else:
            t = clipboard_text()
            if t:
                self.paste(t)

    # --- xử lý phím
    def handle(self, ev):
        key, mods = ev
        shift, ctrl, alt = "shift" in mods, "ctrl" in mods, "alt" in mods
        if "super" in mods:
            return None
        if key != "up" and key != "down":
            self.goal = None
        if key == "enter":
            if shift or alt or ctrl:
                self.insert("\n")
            elif self.text.endswith("\\") and self.cur == len(self.text) and not self.sel():
                self.text = self.text[:-1] + "\n"
                self.cur = len(self.text)
            else:
                return "submit"
            return None
        if key == "backspace":
            if self.del_sel():
                return None
            if alt or ctrl:
                self.del_range(self.word_left(self.cur), self.cur)
                return None
            m = [mm for mm in IMG_RE.finditer(self.text[:self.cur]) if mm.end() == self.cur]
            if m:
                self.del_range(m[-1].start(), self.cur)
            elif self.cur > 0:
                self.del_range(self.cur - 1, self.cur)
            return None
        if key == "delete":
            if self.del_sel():
                return None
            m = IMG_RE.match(self.text, self.cur)
            if m:
                self.del_range(self.cur, m.end())
            elif self.cur < len(self.text):
                self.del_range(self.cur, self.cur + 1)
            return None
        if key in ("left", "right"):
            s = self.sel()
            if s and not shift and not (ctrl or alt):
                self.cur, self.anchor = (s[0] if key == "left" else s[1]), None
            elif ctrl or alt:
                self.move((self.word_left if key == "left" else self.word_right)(self.cur), shift)
            else:
                self.move(self.cur + (-1 if key == "left" else 1), shift)
            return None
        if key in ("up", "down"):
            d = -1 if key == "up" else 1
            items = self.menu()
            if items and not shift:  # đang hiện menu lệnh: lên/xuống chọn lệnh
                self.msel = (self.msel + d) % len(items)
                return None
            if not self.vertical(d, shift) and not shift:
                self.hist_move(d)
            return None
        if key == "home":
            self.move(0 if ctrl else self.line_start(self.cur), shift)
            return None
        if key == "end":
            self.move(len(self.text) if ctrl else self.line_end(self.cur), shift)
            return None
        if key == "tab":
            items = self.menu()
            if items and not shift:  # Tab: điền lệnh đang chọn vào ô nhập
                self.text = items[self.msel][0]
                self.cur, self.anchor = len(self.text), None
            elif not shift:
                self.insert("    ")
            return None
        if key == "esc":
            self.menu()
            self.menu_off, self.anchor = True, None
            return None
        if ctrl and not alt and len(key) == 1:
            return self.ctrl_key(key.lower(), shift)
        if alt and not ctrl and len(key) == 1:
            if key in "bB":
                self.move(self.word_left(self.cur), shift)
            elif key in "fF":
                self.move(self.word_right(self.cur), shift)
            elif key in "vV":  # Alt+V: dán ảnh (hoặc chữ) từ clipboard
                self.paste_clip()
            return None
        if len(key) == 1 and key >= " ":
            self.insert(key)
        return None

    def ctrl_key(self, k, shift):
        if k == "c":
            s = self.sel()
            if s:
                copy_text(self.text[s[0]:s[1]])
                self.anchor = None
            elif self.text:
                self.text, self.cur, self.anchor, self.hidx = "", 0, None, len(self.hist)
            else:
                raise KeyboardInterrupt
        elif k == "d":
            if not self.text:
                raise EOFError
            if not self.del_sel() and self.cur < len(self.text):
                self.del_range(self.cur, self.cur + 1)
        elif k == "a":
            self.anchor, self.cur = 0, len(self.text)
        elif k == "e":
            self.move(self.line_end(self.cur), shift)
        elif k == "u":
            if not self.del_sel():
                self.del_range(self.line_start(self.cur), self.cur)
        elif k == "k":
            if not self.del_sel():
                self.del_range(self.cur, self.line_end(self.cur))
        elif k == "w":
            if not self.del_sel():
                self.del_range(self.word_left(self.cur), self.cur)
        elif k == "x":
            s = self.sel()
            if s:
                copy_text(self.text[s[0]:s[1]])
                self.del_range(*s)
        elif k == "j":
            self.insert("\n")
        elif k == "b":
            self.move(self.cur - 1, shift)
        elif k == "f":
            self.move(self.cur + 1, shift)
        return None

    # --- vẽ
    def draw(self):
        W = self.W()
        pos = layout(self.text, W, self.ind)
        sel = self.sel()
        tok = set()
        for m in IMG_RE.finditer(self.text):
            tok.update(range(m.start(), m.end()))
        out = []
        if self.cur_row:
            out.append("\033[%dA" % self.cur_row)
        out.append("\r\033[J" + C_ACC + ("btw> " if self.btw else "> ") + RESET)
        wr, t = 0, self.text
        for i, ch in enumerate(t):
            r = pos[i][0]
            while wr < r:
                out.append("\r\n")
                wr += 1
                if i > 0 and t[i - 1] == "\n":
                    out.append(" " * self.ind)
            if ch == "\n":
                continue
            seg = (C_ACC + ch + C_TEXT) if i in tok else ch
            if sel and sel[0] <= i < sel[1]:
                seg = "\033[7m" + seg + "\033[27m"
            out.append(seg)
        r = pos[len(t)][0]
        while wr < r:
            out.append("\r\n")
            wr += 1
            if t and t[-1] == "\n":
                out.append(" " * self.ind)
        if self.btw and not t:
            out.append(C_DIM + "..." + RESET)  # chỗ để điền câu hỏi
        rc, cc = pos[self.cur]
        total = wr
        for ln in self.menu_lines(W):  # menu lệnh nằm ngay dưới ô nhập
            out.append("\r\n" + ln)
            total += 1
        if total - rc:
            out.append("\033[%dA" % (total - rc))
        out.append("\033[%dG" % (cc + 1))
        self.cur_row, self.wr = rc, wr
        w("".join(out), screen=False)

    def finish(self):
        if OUT is not None:
            OUT.done_input(self.text, "btw> " if self.btw else "> ")  # dòng người dùng vẫn nằm trên màn hình sau khi gửi
        down = self.wr - self.cur_row
        w((("\033[%dB" % down) if down > 0 else "") + "\r\n\033[J", screen=False)  # \033[J: xóa menu còn sót phía dưới


def load_hist():
    out = []
    try:
        with open(HIST_PATH + ".jsonl", encoding="utf-8") as f:
            for ln in f:
                try:
                    out.append(json.loads(ln))
                except ValueError:
                    pass
    except OSError:
        pass
    return [x for x in out if isinstance(x, str)][-500:]


def save_hist(t):
    if t.strip():
        with open(HIST_PATH + ".jsonl", "a", encoding="utf-8") as f:
            f.write(json.dumps(t, ensure_ascii=False) + "\n")


def edit_line(hist, prefill="", images=None, live=None, mode=None):
    """Trả về (text, [đường dẫn ảnh theo thứ tự token [Image #n] còn lại trong text]).
    live: LiveCtl khi AI đang chạy nền (ô nhập mở suốt, thoát khi AI xong). mode="btw": ô hỏi nhanh."""
    global LIVE
    ed, posix = (live.ed if live else Editor(hist, prefill, images)), os.name != "nt"
    if mode == "btw":
        ed.btw, ed.ind = True, 5
    idle = None if live else Live(ed, True)  # lúc rảnh cũng qua Live: thông báo lệnh nền in phía trên ô nhập
    idle_poll, signal = idle is not None and mode is None, False
    lk = live.lock if live else idle.lock
    try:
        with RawTerm() as kr:
            if posix:  # dán an toàn, kitty keyboard, xterm modifyOtherKeys
                w("\033[?2004h\033[>1u\033[>4;2m", screen=False)
            sel = None
            try:
                if live:
                    live.begin()  # vẽ ô nhập rồi mới cho AI chạy
                else:
                    OUT.start_prompt()  # dòng output dở dang (nếu có) sẽ bị ô nhập vẽ đè
                    LIVE = idle
                    ed.draw()
                # Ô có chữ: chuột do MshLite giữ, chọn trong ô thì sửa/xóa được;
                # chọn ngoài thì OutSelect bôi đen + copy ngay khi nhả (một lần kéo).
                # Ô trống: chuột là của terminal.
                # paused: chuột đang của terminal (sau khi lăn); rearm: lúc bật lại; seen: đã thấy một cú bấm
                paused, rearm, seen = False, None, False
                down, press, dragged = False, None, False
                last_move, last_pos, hard = time.time(), None, None
                while True:
                    if live and not live.alive():
                        break
                    kr.set_mouse(bool(ed.text) and not paused)
                    if paused and (not posix or rearm is not None):
                        ev = kr.read(0.02)  # chờ chuột nhả rồi bật lại, để chọn được chữ trong ô ngay sau đó
                        if ev is None:
                            now, st, pos = time.time(), kr.left_state(), kr.cursor_pos()
                            if pos is not None and pos != last_pos:
                                last_pos, last_move = pos, now
                            if st is None:  # terminal escape: không biết nút chuột, bật lại sau 1,5 giây
                                if rearm is not None and now >= rearm:
                                    mlog("rearm timer")
                                    paused, ed.outside, rearm, seen = False, False, None, False
                            else:
                                if st[0]:  # đang giữ nút
                                    if not down:
                                        press, dragged = pos, False
                                    elif press is None:
                                        press = pos
                                    elif pos is not None and abs(pos[0] - press[0]) + abs(pos[1] - press[1]) > 3:
                                        dragged = True
                                    down, seen, rearm = True, True, None
                                    last_move = now
                                    if hard is None:
                                        hard = now + 5.0
                                elif st[1]:  # nhấn rồi nhả quá nhanh, không kịp thấy lúc đang giữ
                                    down, seen, dragged = False, True, False
                                    rearm, last_move = now + 0.1, now
                                    if hard is None:
                                        hard = now + 5.0
                                else:
                                    if down:  # vừa nhả nút
                                        rearm = now + (0.1 if dragged else kr.double_click() / 1000.0)
                                        mlog("release dragged=%s rearm=%.2fs" % (dragged, rearm - now))
                                    down = False
                                if rearm is not None and now >= rearm:
                                    mlog("rearm release")
                                    paused, ed.outside, rearm, seen, hard = False, False, None, False, None
                                elif seen and now - last_move >= 2.5:  # đường lui khi không thấy cú nhả
                                    mlog("rearm idle")
                                    paused, ed.outside, rearm, seen, hard = False, False, None, False, None
                                elif hard is not None and now >= hard:  # đường lui cuối, tránh kẹt hẳn
                                    mlog("rearm hard")
                                    paused, ed.outside, rearm, seen, hard = False, False, None, False, None
                            continue
                        paused = False
                    else:
                        ev = kr.read(0.1) if live else (kr.read(0.3) if idle_poll else kr.read())
                        if ev is None:  # chưa có phím: live thì xem AI đã xong chưa; rảnh thì xem lệnh nền đã xong chưa
                            if idle_poll and not ed.text and idle.dialog is None and bg_ready():
                                signal = True  # lệnh nền xong lúc tui không gõ gì: tự gửi kết quả cho AI
                                break
                            continue
                    with lk:
                        lvo = live.out if live else idle
                        if lvo is not None and lvo.dialog is not None:  # đang có hộp xin phép: phím chỉ dành cho hộp
                            dlg = lvo.dialog
                            if ev[0] not in ("mouse", "wheel", "paste") and time.time() - dlg.t0 > 0.4:
                                dlg.handle(ev)  # 0,4 giây đầu bỏ qua phím, tránh bấm nhầm khi đang gõ dở
                            if not dlg.finished:
                                lvo.redraw()
                            continue
                        if live and ev[0] == "esc":
                            live.esc(ed)
                        if mode == "btw" and not live and ev[0] == "esc":  # hủy ô hỏi nhanh
                            ed.anchor, ed.text = None, ""
                            ed.draw()
                            ed.finish()
                            break
                        if ev[0] == "wheel":  # đang cuộn: trả chuột lại cho terminal, bấm phím bất kỳ để bật lại
                            if sel is not None:
                                sel.clear()
                                sel = None
                            paused, rearm, seen, down, hard = True, None, False, False, None
                            continue
                        if ev[0] != "mouse":  # bấm phím: bật lại chuột cho ô nhập
                            if sel is not None:
                                if ev[0] == "c" and "ctrl" in ev[1] and sel.painted:  # Ctrl+C sau khi đã copy: đừng xóa ô nhập
                                    sel.clear()
                                    sel = None
                                    continue
                                sel.clear()
                                sel = None
                            paused, rearm, seen, down, ed.outside, hard = False, None, False, False, False, None
                        if ev[0] == "paste":
                            ed.paste(ev[1])
                        elif ev[0] == "mouse":
                            kind, x, y, shift = ev[1]
                            if sel is not None:
                                if kind == "drag":
                                    sel.drag(x, y)
                                    continue
                                if kind == "up":
                                    sel.up()
                                    if not sel.painted:  # vừa bấm chứ không kéo: bỏ đối tượng rỗng
                                        sel = None
                                    continue
                                if kind == "down":  # bấm mới: bỏ vùng đang bôi rồi xử lý như bình thường
                                    sel.clear()
                                    sel = None
                            redraw = ed.mouse(kr, *ev[1])
                            if ed.outside:  # bấm ngoài ô nhập: bắt đầu bôi đen vùng output
                                size = shutil.get_terminal_size((80, 24))
                                width, height = max(1, size.columns), max(1, size.lines)
                                # chỉ cần vùng còn nhìn thấy (+2 dòng đệm), origin có thể là toạ độ tuyệt đối
                                rows = OUT.tail_rows(min(max(1, ed.origin) + 2, height + 2), width)
                                if rows and y < ed.origin:  # bấm phía trên ô nhập: vùng output
                                    sel = OutSelect(ed, rows, width)
                                    sel.down(x, y)
                                    mlog("screen select start y=%s rows=%s" % (y, len(rows)))
                                ed.outside = False
                            if not redraw:
                                continue
                        else:
                            try:
                                r = ed.handle(ev)
                            except (KeyboardInterrupt, EOFError) as exc:
                                if not live:
                                    raise
                                if isinstance(exc, KeyboardInterrupt):  # Ctrl+C khi ô trống: dừng AI
                                    live.stop()
                                r = None
                            if r == "submit":
                                ed.anchor, ed.menu_off = None, True  # gửi: giấu menu lệnh trước khi vẽ lần cuối
                                ed.draw()
                                ed.finish()
                                if not live:
                                    break
                                live.submit(ed)
                        ed.draw()
            finally:
                if live:
                    live.finish()  # chờ AI xong, xóa ô nhập khỏi màn hình
                if idle is not None:
                    if signal:
                        idle.end()  # xóa ô nhập trước khi AI chạy lượt tự động
                    LIVE = None
                if sel is not None:
                    sel.clear()
                if posix:
                    w("\033[<u\033[>4;0m\033[?2004l", screen=False)
    except (KeyboardInterrupt, EOFError):
        ed.anchor = None
        ed.finish()
        raise
    if signal:
        return "\x00bg", []
    if live:
        return ed.text, []
    save_hist(ed.text)
    imgs = [ed.images[int(n)] for n in IMG_RE.findall(ed.text) if int(n) in ed.images]
    return ed.text, imgs


# ---------------------------------------------------------------- AI chạy nền: output phía trên, ô nhập luôn ở dưới
_SGR = re.compile(r"\033\[[0-9;]*m")


class Live:
    """Khi AI đang chạy: mọi output đi qua đây. Xóa ô nhập, in chữ mới, rồi vẽ lại ô nhập ở dưới cùng."""

    def __init__(self, ed, accepts_dialog=False):
        self.ed, self.lock, self.buf, self.sgr = ed, threading.RLock(), "", ""
        self.accepts_dialog, self.dialog = accepts_dialog, None  # dialog: hộp xin phép đang hiện (thay ô nhập)
        self.dlg_lock = threading.Lock()

    def write(self, s, screen=True):
        with self.lock:
            if not screen:  # mã điều khiển của chính ô nhập
                sys.stdout.write(s)
                sys.stdout.flush()
                return
            self.buf += s
            i = self.buf.rfind("\n")
            if i >= 0:  # chỉ in những dòng đã đủ, phần dở dang chờ dòng sau
                chunk, self.buf = self.buf[:i + 1], self.buf[i + 1:]
                self._emit(chunk)

    def block(self, s):
        """Một khối nguyên vẹn (bảng /btw), không đụng tới dòng AI đang nói dở."""
        with self.lock:
            self._emit(s)

    def redraw(self):
        if self.dialog is not None:
            self._draw_dialog()
        else:
            self.ed.draw()

    def _draw_dialog(self):
        ed = self.ed
        rows = self.dialog.render(ed.W())
        up = len(rows) - 1
        out = ("\033[%dA" % ed.cur_row if ed.cur_row else "") + "\r\033[J\033[?25l" + "\r\n".join(rows)
        out += ("\033[%dA" % up if up else "") + "\r"
        ed.cur_row = ed.wr = 0
        sys.stdout.write(out)
        sys.stdout.flush()

    def run_dialog(self, dlg, stop=None):
        """Gọi từ luồng AI/Sub-Agent: hiện hộp, chờ tui trả lời (luồng chính nhận phím), rồi trả ô nhập về."""
        cancel = stop if stop is not None else STATE.stop
        while not self.dlg_lock.acquire(timeout=0.2):  # mỗi lúc chỉ một hộp
            if cancel.is_set():
                return None
        try:
            with self.lock:
                dlg.t0 = time.time()
                self.dialog = dlg
                self.redraw()
            while not dlg.event.wait(0.2):
                if cancel.is_set():
                    dlg.cancel()
            with self.lock:
                self.dialog = None
                ed = self.ed
                sys.stdout.write(("\033[%dA" % ed.cur_row if ed.cur_row else "") + "\r\033[J\033[?25h")
                ed.cur_row = ed.wr = 0
                ed.draw()
            return dlg.result
        finally:
            self.dlg_lock.release()

    def _track(self, chunk):
        for m in _SGR.finditer(chunk):  # nhớ màu đang dùng để tô tiếp sau khi ô nhập vẽ lại
            seq = m.group(0)
            if seq == C_TEXT:
                self.sgr = ""
            elif seq != BG:
                self.sgr += seq
        if len(self.sgr) > 300:
            self.sgr = ""

    def _emit(self, chunk):
        ed = self.ed
        if OUT is not None:
            OUT.feed(chunk)
        up = "\033[%dA" % ed.cur_row if ed.cur_row else ""
        sys.stdout.write(up + "\r\033[J" + self.sgr + chunk.replace("\n", "\r\n"))  # raw mode: \n không tự về đầu dòng
        self._track(chunk)
        ed.cur_row = ed.wr = 0
        self.redraw()
        if self.sgr:
            sys.stdout.write(self.sgr)
        sys.stdout.flush()

    def end(self):
        with self.lock:
            if self.buf:
                self._emit(self.buf + "\n")
                self.buf = ""
            ed = self.ed
            sys.stdout.write(("\033[%dA" % ed.cur_row if ed.cur_row else "") + "\r\033[J" + RESET)
            sys.stdout.flush()
            ed.cur_row = ed.wr = 0


class LiveCtl:
    """Điều khiển ô nhập lúc AI chạy: Esc hai lần để dừng, /btw để hỏi nhanh, gõ thường thì xếp hàng."""

    def __init__(self, chat, ed, target):
        self.chat, self.ed = chat, ed
        self.out = Live(ed, True)
        self.lock = self.out.lock
        self.th = threading.Thread(target=target, daemon=True)
        self.last_esc = 0.0

    def alive(self):
        return self.th.is_alive()

    def begin(self):
        global LIVE
        LIVE = self.out
        OUT.start_prompt()
        self.ed.draw()
        self.th.start()

    def finish(self):
        global LIVE
        if self.th.is_alive():  # ra khỏi vòng nhập mà AI chưa xong (lỗi): dừng nó
            self.stop()
        self.th.join(timeout=5)
        self.out.end()
        LIVE = None

    def stop(self):
        if STATE.stop.is_set():
            return
        STATE.stop.set()
        r = STATE.resp
        if r is not None:
            try:
                r.close()
            except Exception:
                pass

    def esc(self, ed):
        if ed.btw:  # đang ở ô "btw>": một lần Esc là hủy câu hỏi, không tính vào Esc đúp
            ed.btw, ed.ind, ed.text, ed.cur, self.last_esc = False, 2, "", 0, 0.0
            return
        now = time.time()
        if now - self.last_esc <= ESC_GAP:
            self.last_esc = 0.0
            self.stop()
        else:
            self.last_esc = now  # nhấn chậm: lần này chỉ là lần đầu

    def submit(self, ed):
        text = ed.text.strip()
        imgs = [ed.images[int(n)] for n in IMG_RE.findall(ed.text) if int(n) in ed.images]
        save_hist(ed.text)
        was_btw = ed.btw
        ed.text, ed.cur, ed.anchor, ed.images = "", 0, None, {}
        ed.cur_row = ed.wr = 0
        ed.btw, ed.ind = False, 2
        if was_btw:
            if text:
                self.start_btw(text)
        elif text == "/btw":
            ed.btw, ed.ind = True, 5  # hiện ô "btw> ..." để điền câu hỏi
        elif text.startswith("/btw "):
            self.start_btw(text[5:].strip())
        elif text.startswith("/"):
            p("AI đang chạy: chỉ dùng được /btw. Nhấn Esc hai lần nhanh để dừng.", C_DIM)
        elif text:
            STATE.queue.append((text, imgs))
            p("(đã xếp hàng, sẽ gửi khi AI xong)", C_DIM)

    def start_btw(self, q):
        p("btw: đang hỏi ...", C_DIM)
        threading.Thread(target=btw_run, args=(self.chat, q), daemon=True).start()


def emit_block(s):
    lv = LIVE
    if lv is not None:
        lv.block(s)
    else:
        w(s)


def btw_panel(q, text):
    cols = shutil.get_terminal_size((80, 24)).columns
    W = max(24, min(cols - 1, 100))
    inner = W - 4
    title = " btw: " + q.replace("\n", " ")
    title = (title[:inner - 1] + "…" if len(title) > inner else title) + " "
    rows = [C_DIM + "+-" + RESET + C_ACC + title + RESET + C_DIM + "-" * max(0, W - 3 - vis_width(title)) + "+" + RESET]
    for ln in text.strip().split("\n"):
        for seg in (textwrap.wrap(ln, inner) or [""]):
            body = md_inline(seg)
            rows.append(C_DIM + "| " + RESET + body + " " * max(0, inner - vis_width(body)) + C_DIM + " |" + RESET)
    rows.append(C_DIM + "+" + "-" * (W - 2) + "+" + RESET)
    return "\n".join(rows) + "\n"


def btw_run(chat, q):
    """Hỏi nhanh: dùng cả cuộc trò chuyện hiện có làm ngữ cảnh, KHÔNG có công cụ, KHÔNG ghi vào chat."""
    try:
        msgs = list(chat["messages"]) + [{"role": "user", "content": "<user>(hỏi nhanh /btw) %s</user>" % q}]
        reply, _ = chat_stream(msgs, build_system("none"), None, "text", agent=False)
        emit_block(btw_panel(q, strip_tool(reply) or "(model không trả lời)"))
    except Exception as e:
        emit_block(C_ERR + "btw lỗi: %s" % e + RESET + "\n")


def cmd_btw(chat, q):
    if not q:
        q = (edit_line(load_hist(), mode="btw")[0] if raw_ok() else inp("btw> ")).strip()
    if q:
        p("btw: đang hỏi ...", C_DIM)
        btw_run(chat, q)


def cmd_branch(chat):
    if not chat["messages"]:
        p("chat đang trống, chưa có gì để rẽ nhánh.", C_DIM)
        return chat
    save_chat(chat)
    b = new_chat()
    b["id"] += "-" + uuid.uuid4().hex[:4]
    b["title"] = chat["title"] + "-branch"
    b["messages"] = copy.deepcopy(chat["messages"])
    save_chat(b)
    p("đã rẽ nhánh: %s" % b["title"], C_OK)
    p("chat gốc \"%s\" vẫn còn trong /conversation. /redo của nhánh bắt đầu tính từ đây." % chat["title"], C_DIM)
    return b


def run_live(chat, text, images=None):
    """Chạy một lượt AI ở luồng nền; ô nhập vẫn mở để gõ /btw hoặc nhấn Esc hai lần để dừng."""
    if not raw_ok():
        run_turn(chat, text, images)
        return
    STATE.stop.clear()

    def work():
        try:
            run_turn(chat, text, images)
        except BaseException as e:
            p("lỗi không mong đợi: %s" % e, C_ERR)
    left = edit_line(None, live=LiveCtl(chat, Editor(load_hist()), work))[0]
    STATE.stop.clear()
    if left.strip() and not STATE.queue:  # chữ đang gõ dở khi AI xong: đưa sang ô nhập tiếp theo
        STATE.prefill = left


# ---------------------------------------------------------------- main
def read_input():
    """Trả về (text, [ảnh]). Terminal thật dùng ô nhập riêng; còn lại dùng input() thường."""
    pre, pimgs = STATE.prefill, STATE.prefill_images
    STATE.prefill, STATE.prefill_images = "", {}
    if raw_ok():
        return edit_line(load_hist(), pre, pimgs)
    if readline and pre:
        readline.set_startup_hook(lambda: readline.insert_text(pre))
    try:
        line = inp("> ")
        while line.endswith("\\"):
            line = line[:-1] + "\n" + inp(". ")
        return line, []
    finally:
        if readline:
            readline.set_startup_hook()


def main():
    if readline:
        try:
            readline.read_history_file(HIST_PATH)
        except Exception:
            pass
        atexit.register(lambda: readline.write_history_file(HIST_PATH))
    atexit.register(lambda: (bg_kill_all(), mcp_reset(), w("\033[0m\n")))
    purge_old_journals()

    chat = load_chat(CFG.get("current_chat") or "") or new_chat()
    if os.path.isdir(chat.get("cwd", "")) and chat["messages"]:
        STATE.cwd = chat["cwd"]
    clear_screen()
    banner(chat)

    while True:
        try:
            line, imgs = read_input()
        except EOFError:
            break
        except KeyboardInterrupt:
            p("\n(gõ /exit để thoát)", C_DIM)
            continue
        if line == "\x00bg":  # lệnh nền xong lúc rảnh: gửi kết quả cho AI
            try:
                run_live(chat, None, [])
                while STATE.queue:
                    t, im = STATE.queue.pop(0)
                    run_live(chat, t, im)
            except KeyboardInterrupt:
                p("\nđã dừng.", C_DIM)
                save_chat(chat)
            continue
        line = line.strip()
        if not line:
            continue
        try:
            if line.startswith("/") and "\n" not in line:
                cmd = line.split()[0].lower()
                if cmd == "/exit":
                    save_chat(chat)
                    break
                elif cmd == "/model":
                    cmd_model(chat)
                elif cmd == "/skill":
                    manage("Skill", "skills", "text")
                elif cmd == "/memory":
                    manage("Memory", "memory", "text")
                elif cmd == "/mcp":
                    manage("MCP", "mcp", "mcp")
                elif cmd == "/compact":
                    cmd_compact(chat)
                elif cmd == "/copy":
                    cmd_copy(chat)
                elif cmd == "/conversation":
                    chat = cmd_conversation(chat)
                    clear_screen()
                    banner(chat)
                elif cmd == "/clear":
                    clear_screen()
                    banner(chat)
                    p("(đã dọn màn hình, model vẫn nhớ hết)", C_DIM)
                elif cmd == "/redo":
                    cmd_redo(chat)
                elif cmd == "/btw":
                    cmd_btw(chat, line[4:].strip())
                elif cmd == "/branch":
                    chat = cmd_branch(chat)

                else:
                    p("lệnh không có. Có: " + " ".join(c for c, _ in COMMANDS), C_ERR)
            else:
                run_live(chat, line, imgs)
                while STATE.queue:  # tin gõ lúc AI đang chạy
                    t, im = STATE.queue.pop(0)
                    run_live(chat, t, im)
        except KeyboardInterrupt:
            p("\nđã dừng.", C_DIM)
            save_chat(chat)
        except ApiError as e:
            p("lỗi: %s" % e, C_ERR)
        except Exception as e:
            p("lỗi không mong đợi: %s" % e, C_ERR)


if __name__ == "__main__":
    main()
