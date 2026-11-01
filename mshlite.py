#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
MshLite - harness agent mini kiểu Pi.
Chỉ dùng thư viện chuẩn (Python 3.8+). Chạy: python mshlite.py
Tool cho model: cmd, skill, memory, mcp (model gọi bằng khối <tool name="..">..</tool>).
"""
import os, sys, re, json, time, uuid, shlex, shutil, signal, atexit, queue, base64
import hashlib, platform, threading, subprocess
import urllib.request, urllib.error
from datetime import datetime

try:
    import readline
except ImportError:
    readline = None

# ---------------------------------------------------------------- đường dẫn
HOME = os.environ.get("MSH_HOME") or os.path.join(os.path.expanduser("~"), ".mshlite")
CFG_PATH = os.path.join(HOME, "config.json")
CHAT_DIR = os.path.join(HOME, "chats")
SHADOW_DIR = os.path.join(HOME, "shadow")
HIST_PATH = os.path.join(HOME, "history")
for _d in (HOME, CHAT_DIR, SHADOW_DIR):
    os.makedirs(_d, exist_ok=True)

MAX_STEPS = 40
CMD_TIMEOUT = 120
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


def w(s):
    sys.stdout.write(s)
    sys.stdout.flush()


def p(s="", color=None, end="\n"):
    w((color or "") + s + RESET + end)


def inp(prompt, color=C_ACC):
    if readline:
        return input("\001%s\002%s\001%s\002" % (color, prompt, RESET))
    return input(color + prompt + RESET)


def rule():
    p("-" * min(shutil.get_terminal_size((80, 20)).columns, 72), C_DIM)


# ---------------------------------------------------------------- cấu hình
DEFAULT_CFG = {
    "model": {"base_url": "https://api.openai.com/v1", "model": "", "api_key": "",
              "max_tokens": 4096, "temperature": None, "top_p": None,
              "top_k": None, "effort": None, "tool_mode": "auto"},
    "skills": {}, "memory": {}, "mcp": {}, "current_chat": None,
    "text_models": [],   # model/server bị phát hiện không nhận function calling
    "markdown": True,
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
    snap_warned = False


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

1) cmd: chạy lệnh shell trên máy tui. NỘI DUNG là lệnh (nhiều dòng được). Thư mục làm việc được giữ giữa các lần chạy (cd có tác dụng). Lệnh bị dừng sau 120 giây và không có bàn phím nên đừng chạy lệnh chờ nhập. Output dài sẽ bị cắt ở giữa. Đọc file: cat, sed -n, head. Tạo/sửa/xóa file: cat <<'EOF' > file, sed -i, python, rm. Sửa xong nên kiểm tra lại.
2) skill: xem kỹ năng tui đã lưu. NỘI DUNG là "list" hoặc tên skill để đọc hướng dẫn đầy đủ. Gặp việc hợp với skill nào thì đọc skill đó trước khi làm.
3) memory: bộ nhớ lâu dài giữa các cuộc trò chuyện. NỘI DUNG là JSON: {"action":"save","name":"...","content":"..."} hoặc {"action":"delete","name":"..."} hoặc {"action":"list"}. Chỉ lưu khi tui nhờ nhớ hoặc thông tin thật sự có ích lâu dài. Không lưu mật khẩu/key.
4) mcp: gọi công cụ của MCP server. NỘI DUNG là JSON: {"server":"tên","tool":"tên_tool","args":{...}}. Muốn xem đầy đủ tham số của server: {"server":"tên"}.
"""

NATIVE_DOC = """
---
CÔNG CỤ
MshLite dùng function calling để gọi công cụ: cmd, skill, memory, mcp (xem mô tả từng công cụ). Kết quả trả về nằm trong <result>. Có thể gọi công cụ nhiều lần; khi xong việc thì trả lời tui bình thường, không gọi công cụ nữa. Tuyệt đối không tự viết <result>.
"""

TOOLS = [
    {"type": "function", "function": {
        "name": "cmd",
        "description": "Chạy lệnh shell trên máy tui. Thư mục làm việc được giữ giữa các lần chạy (cd có tác dụng). "
                       "Lệnh bị dừng sau 120 giây và không có bàn phím nên đừng chạy lệnh chờ nhập. Output dài bị cắt ở giữa. "
                       "Đọc file: cat, sed -n, head. Tạo/sửa/xóa file: cat <<'EOF' > file, sed -i, python, rm. Sửa xong nên kiểm tra lại.",
        "parameters": {"type": "object", "properties": {
            "command": {"type": "string", "description": "Lệnh shell cần chạy (nhiều dòng được)."}},
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
]

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
    out = BASE_PROMPT.format(today(), STATE.cwd) + "\n" + (NATIVE_DOC if mode == "native" else TOOL_DOC)
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
            try:
                line = self.q.get(timeout=left)
            except queue.Empty:
                raise TimeoutError("quá thời gian chờ " + method)
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


def run_cmd(cmd):
    cmd = cmd.strip()
    cmd = re.sub(r"^```\w*\n|\n```$", "", cmd).strip()
    if not cmd:
        return "lệnh rỗng"
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
    timed_out = False
    try:
        out, _ = proc.communicate(timeout=CMD_TIMEOUT)
    except subprocess.TimeoutExpired:
        timed_out = True
        _kill(proc)
        out, _ = proc.communicate()
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
    if timed_out:
        out += "\n[bị dừng sau %d giây]" % CMD_TIMEOUT
    elif proc.returncode:
        out += "\n[mã thoát: %s]" % proc.returncode
    return out or "(không có output)"


def _kill(proc):
    try:
        if os.name == "nt":
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
        return str(args.get("command", ""))
    if name == "skill":
        return str(args.get("name", ""))
    return json.dumps(args, ensure_ascii=False)


def body_to_args(name, body):
    if name == "cmd":
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
            return run_cmd(str(args.get("command", "")))
        if name == "skill":
            return tool_skill(str(args.get("name", "")))
        if name == "memory":
            return tool_memory(args)
        if name == "mcp":
            return tool_mcp(args)
        return "không có công cụ '%s'. Chỉ có: cmd, skill, memory, mcp" % name
    except KeyboardInterrupt:
        raise
    except Exception as e:
        return "lỗi: %s" % e


# ---------------------------------------------------------------- gọi model (stream)
class ApiError(Exception):
    pass


class NativeUnsupported(ApiError):
    """Server/model không nhận function calling."""


def normalize(msgs):
    """Gộp các tin liền nhau cùng vai (user/user, assistant/assistant), không đụng tool_calls."""
    out = []
    for m in msgs:
        if (out and m["role"] in ("user", "assistant") and out[-1]["role"] == m["role"]
                and not m.get("tool_calls") and not out[-1].get("tool_calls")):
            out[-1] = dict(out[-1], content=out[-1]["content"] + "\n" + m["content"])
        else:
            out.append(dict(m))
    return out


def native_msgs(msgs):
    out = []
    for m in msgs:
        d = {"role": m["role"], "content": m.get("content") or ""}
        if m.get("tool_calls"):
            d["tool_calls"] = m["tool_calls"]
        if m.get("tool_call_id"):
            d["tool_call_id"] = m["tool_call_id"]
        out.append(d)
    return normalize(out)


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
            out.append({"role": r, "content": m.get("content") or ""})
    return normalize(out)


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


def md_inline(s, base=C_TEXT):
    """In đậm, nghiêng, gạch ngang, code, link. Code và ký tự thoát được giữ nguyên bằng placeholder."""
    stash = {}

    def keep(val):
        k = "\ue000%d\ue001" % len(stash)
        stash[k] = val
        return k

    s = re.sub(r"(`+)(.+?)\1", lambda m: keep(C_CODE + m.group(2).strip() + base), s)
    s = re.sub(r"\\([\\`*_{}\[\]()#+\-.!|~>])", lambda m: keep(m.group(1)), s)
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
        w(bar.join(B_ON + cell(grid[0][j], j) + B_OFF for j in range(n)) + "\n")
        w(C_DIM + "-+-".join("-" * wid[j] for j in range(n)) + RESET + "\n")
        for g in grid[1:]:
            w(bar.join(cell(g[j], j) for j in range(n)) + "\n")


class Printer:
    """Hiện chữ model đang gõ, ẩn khối <tool>, hiện phần suy nghĩ bằng màu mờ."""
    def __init__(self, filter_tools=True):
        self.buf, self.intool, self.thinking, self.any = "", False, False, False
        self.filter_tools = filter_tools
        self.md = MdStream() if CFG.get("markdown", True) else None

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


def chat_stream(messages, system, printer=None, mode="native"):
    """Trả về (text, calls). calls = [{"id","name","arguments"(chuỗi JSON),"error"?}]."""
    m = CFG["model"]
    if not m.get("model"):
        raise ApiError("chưa đặt model. Dùng /model")
    url = (m.get("base_url") or "").rstrip("/")
    if not url.endswith("/chat/completions"):
        url += "/chat/completions"
    hist = native_msgs(messages) if mode == "native" else text_msgs(messages)
    body = {"model": m["model"], "stream": True,
            "messages": [{"role": "system", "content": system}] + hist}
    if mode == "native":
        body["tools"] = TOOLS
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

    full, rawbuf, tcs = "", [], {}
    try:
        for raw in resp:
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
    finally:
        resp.close()
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


# ---------------------------------------------------------------- vòng lặp agent
def show_tool_call(name, args):
    if name == "cmd":
        shown = str(args.get("command", "")).strip()
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


def run_turn(chat, text):
    cp = {"len": len(chat["messages"]), "user": text, "cwd": STATE.cwd,
          "commit": snapshot(STATE.cwd),
          "memory": dict(CFG["memory"]), "skills": dict(CFG["skills"])}
    chat["checkpoints"].append(cp)
    chat["messages"].append({"role": "user", "content": "<user>%s</user>" % text})
    if chat["title"] == "(mới)":
        chat["title"] = text.strip().replace("\n", " ")[:50]

    for step in range(MAX_STEPS):
        mode = tool_mode()
        pr = Printer(filter_tools=(mode == "text"))
        try:
            reply, calls = chat_stream(chat["messages"], build_system(mode), pr, mode)
        except NativeUnsupported:
            pr.end()
            mark_text_fallback()
            p("model/server không nhận function calling, chuyển sang kiểu thẻ <tool>.", C_DIM)
            continue
        except ApiError as e:
            pr.end()
            p("lỗi: %s" % e, C_ERR)
            if step == 0:  # chưa làm gì thì hủy lượt này
                chat["messages"] = chat["messages"][:cp["len"]]
                chat["checkpoints"].pop()
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
            break
        answered = set()
        try:
            for c in calls:
                args = json.loads(c["arguments"])
                show_tool_call(c["name"], args)
                res = c["error"] if c.get("error") else exec_tool(c["name"], args)
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


def cmd_model(chat):
    m = CFG["model"]
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
    md = ask("markdown on/off", "on" if CFG.get("markdown", True) else "off", choices=["on", "off"])
    CFG["markdown"] = (md or "on") != "off"
    if m["tool_mode"] == "auto" and model_key() in CFG["text_models"]:
        CFG["text_models"].remove(model_key())  # thử lại function calling từ đầu
    save_cfg()
    p("đã lưu.", C_OK)


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
        p("đã lùi chat (file không có mốc nên không lùi).", C_OK)
    p("thay đổi ngoài thư mục làm việc và qua mcp không lùi được.", C_DIM)
    STATE.prefill = cp["user"]
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
    p("/model /skill /mcp /memory /compact /copy /conversation /clear /redo /exit", C_DIM)
    rule()


# ---------------------------------------------------------------- main
def read_input():
    if readline and STATE.prefill:
        pre = STATE.prefill
        readline.set_startup_hook(lambda: readline.insert_text(pre))
    try:
        line = inp("> ")
        while line.endswith("\\"):
            line = line[:-1] + "\n" + inp(". ")
        return line
    finally:
        STATE.prefill = ""
        if readline:
            readline.set_startup_hook()


def main():
    if readline:
        try:
            readline.read_history_file(HIST_PATH)
        except Exception:
            pass
        atexit.register(lambda: readline.write_history_file(HIST_PATH))
    atexit.register(lambda: (mcp_reset(), w("\033[0m\n")))

    chat = load_chat(CFG.get("current_chat") or "") or new_chat()
    if os.path.isdir(chat.get("cwd", "")) and chat["messages"]:
        STATE.cwd = chat["cwd"]
    clear_screen()
    banner(chat)

    while True:
        try:
            line = read_input()
        except EOFError:
            break
        except KeyboardInterrupt:
            p("\n(gõ /exit để thoát)", C_DIM)
            continue
        line = line.strip()
        if not line:
            continue
        try:
            if line.startswith("/"):
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
                else:
                    p("lệnh không có. Có: /model /skill /mcp /memory /compact /copy /conversation /clear /redo /exit", C_ERR)
            else:
                run_turn(chat, line)
        except KeyboardInterrupt:
            p("\nđã dừng.", C_DIM)
            save_chat(chat)
        except ApiError as e:
            p("lỗi: %s" % e, C_ERR)
        except Exception as e:
            p("lỗi không mong đợi: %s" % e, C_ERR)


if __name__ == "__main__":
    main()
