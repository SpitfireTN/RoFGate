#!/usr/bin/env python3
"""
BBS Telnet & SSH Gateway Server (bbs_gateway.py)
================================================
Listens on Telnet Port 23 (and optionally an inbound SSH port via `asyncssh`),
negotiates 8-bit binary CP437 character-mode options, displays `gateway.ans`
and/or an interactive CP437 ANSI lightbar menu, and bridges callers seamlessly
to:
  - Local or External Telnet BBS nodes (`LOCAL`, `EXTERNAL`)
  - Local or External SSH BBS nodes (`SSH-LOC`, `SSH-EXT`), using either
    `asyncssh` or a zero-dependency POSIX PTY + system `/usr/bin/ssh` bridge.

Designed for Mystic BBS / ANSI-BBS terminal codecs:
  - Transmits pure 8-bit IBM CP437 bytes (auto-converting UTF-8 .ans files)
  - Avoids unsupported VT220 private mode sequences (such as ESC[?25l)
  - Uses 79-column lines and explicit ESC[y;xH positioning to prevent 80-col wrap
  - Supports Mystic BBS pipe color codes (|00-|23) and screen MCI codes (|CL, |CR)
"""

from __future__ import annotations

from collections import defaultdict
import ipaddress
import argparse
import asyncio
from dataclasses import dataclass, field
import errno
import fcntl
import logging
import logging.handlers
import random
import os
import pty
import re
import shutil
import signal
import struct
import sys
import termios
import time
from typing import Dict, List, Optional, Tuple

try:
    import asyncssh  # Optional: enables native Python SSH client + Inbound SSH Server
    HAS_ASYNCSSH = True
except ImportError:
    HAS_ASYNCSSH = False

# Telnet Protocol Constants (RFC 854 / RFC 856 / RFC 857 / RFC 858)
IAC  = 255
DONT = 254
DO   = 253
WONT = 252
WILL = 251
SB   = 250
SE   = 240

OPT_BINARY   = 0
OPT_ECHO     = 1
OPT_SGA      = 3
OPT_TTYPE    = 24
OPT_NAWS     = 31
OPT_LINEMODE = 34

ESC = "\x1b"

DOS_FG_SGR = {
    0:  (0, 30),  # Black
    1:  (0, 34),  # Blue
    2:  (0, 32),  # Green
    3:  (0, 36),  # Cyan
    4:  (0, 31),  # Red
    5:  (0, 35),  # Magenta
    6:  (0, 33),  # Brown
    7:  (0, 37),  # Light Gray
    8:  (1, 30),  # Dark Gray
    9:  (1, 34),  # Light Blue
    10: (1, 32),  # Light Green
    11: (1, 36),  # Light Cyan
    12: (1, 31),  # Light Red
    13: (1, 35),  # Light Magenta
    14: (1, 33),  # Yellow
    15: (1, 37),  # White
}

DOS_BG_SGR = {
    0: 40,  # Black
    1: 44,  # Blue
    2: 42,  # Green
    3: 46,  # Cyan
    4: 41,  # Red
    5: 45,  # Magenta
    6: 43,  # Brown
    7: 47,  # Light Gray
}


def dos_color_to_ansi(fg: int, bg: int = 0) -> str:
    """Build a strict ANSI-BBS SGR escape sequence for DOS foreground (0-15) and background (0-7)."""
    bold, fg_code = DOS_FG_SGR.get(fg % 16, (0, 37))
    bg_code = DOS_BG_SGR.get(bg % 8, 40)
    if bold:
        return f"{ESC}[0;1;{fg_code};{bg_code}m"
    return f"{ESC}[0;{fg_code};{bg_code}m"


def mystic_pipe_to_ansi(text: str) -> str:
    """Convert Mystic BBS pipe color codes (|00 to |23) and MCI codes (|CL, |CR) into ANSI-BBS sequences."""
    text = text.replace("|CL", f"{ESC}[0m{ESC}[2J{ESC}[1;1H")
    text = text.replace("|CR", "\r\n")
    text = re.sub(r"\|\[X([0-9]{2})", lambda m: f"{ESC}[{int(m.group(1))}G", text)
    text = re.sub(r"\|\[Y([0-9]{2})", lambda m: f"{ESC}[{int(m.group(1))};1H", text)

    cur_fg = 7
    cur_bg = 0
    out: List[str] = []
    i = 0
    n = len(text)
    while i < n:
        if text[i] == "|" and i + 2 < n and text[i + 1:i + 3].isdigit():
            code = int(text[i + 1:i + 3])
            if 0 <= code <= 15:
                cur_fg = code
                out.append(dos_color_to_ansi(cur_fg, cur_bg))
                i += 3
                continue
            if 16 <= code <= 23:
                cur_bg = code - 16
                out.append(dos_color_to_ansi(cur_fg, cur_bg))
                i += 3
                continue
        out.append(text[i])
        i += 1
    return "".join(out)


# --- Box-drawing / decoration -> plain ASCII fallback (PLAIN mode / PETSCII 40-col terminals) ---
_PLAIN_CHAR_MAP = {
    "═": "=", "║": "|", "╔": "+", "╗": "+", "╚": "+", "╝": "+",
    "╠": "+", "╣": "+", "╦": "+", "╩": "+", "╬": "+", "╟": "+", "╢": "+",
    "─": "-", "│": "|", "┌": "+", "┐": "+", "└": "+", "┘": "+",
    "├": "+", "┤": "+", "»": ">", "«": "<", "•": "*", "·": ".",
}


def strip_to_plain(text: str) -> str:
    """Reduce Mystic pipe codes, ANSI/VT escape sequences, and CP437 box-drawing art to
    clean 7-bit ASCII for 40-column PETSCII / dumb terminals (used by DISPLAY_MODE=PLAIN).
    These are the bytes that render identically on both ANSI and Commodore terminals."""
    text = text.replace("|CL", "\r\n").replace("|CR", "\r\n")
    text = re.sub(r"\|\[[XY][0-9]{2}", "", text)          # Mystic cursor-position codes
    text = re.sub(r"\|(?:[01][0-9]|2[0-3])", "", text)    # Mystic pipe colour codes |00-|23
    text = re.sub(r"\x1b\[[0-9;?]*[ -/]*[@-~]", "", text) # ANSI/VT CSI sequences
    text = text.replace("\x1b", "")                       # stray ESC
    text = "".join(_PLAIN_CHAR_MAP.get(c, c) for c in text)
    return text


# PETSCII control bytes
PET_TEXT_MODE = 0x0E   # switch C64/128 to lowercase/uppercase (text) charset
PET_CLEAR     = 0x93   # clear screen / home


def ascii_to_petscii(text: str) -> bytes:
    """Translate plain 7-bit ASCII to PETSCII for Commodore terminals in text (lower/upper)
    charset. ASCII and PETSCII have swapped letter case: ASCII A-Z ($41-$5A) must become
    PETSCII $C1-$DA to show as UPPERCASE, and ASCII a-z ($61-$7A) -> $41-$5A to show as
    lowercase. Line endings: C64 uses CR ($0D) as newline, so LF is dropped."""
    out = bytearray()
    for ch in text:
        c = ord(ch)
        if ch == "\n":
            continue
        elif 0x41 <= c <= 0x5A:      # A-Z -> PETSCII uppercase
            out.append(c + 0x80)
        elif 0x61 <= c <= 0x7A:      # a-z -> PETSCII lowercase
            out.append(c - 0x20)
        elif c < 0x80:               # digits, space, punctuation, CR pass through
            out.append(c)
        else:
            out.append(ord("?"))
    return bytes(out)


# Terminal-type names that identify an ANSI/PC-style caller (vs a Commodore/PETSCII one).
_ANSI_TTYPE_HINTS = ("ANSI", "VT52", "VT100", "VT102", "VT220", "XTERM", "SYNCTERM",
                     "NETRUNNER", "MTEL", "QANSI", "PCANSI", "SCREEN", "LINUX", "PUTTY",
                     "RIP", "UTF-8", "CP437", "TERATERM", "SYNC")
_PETSCII_TTYPE_HINTS = ("COMMODORE", "PETSCII", "CBM", "C64", "C128", "C-64", "C-128", "VIC")


def classify_term(ttype: Optional[str], default: str) -> str:
    """Decide ANSI vs PETSCII from the negotiated telnet terminal-type.
    A client that negotiates a terminal type at all is almost certainly ANSI-capable;
    Commodore terminals typically do NOT negotiate, so a silent client falls back to
    `default` (normally PETSCII)."""
    if not ttype:
        return default.upper() if default.upper() in ("ANSI", "PETSCII") else "PETSCII"
    t = ttype.strip().upper()
    if any(h in t for h in _PETSCII_TTYPE_HINTS):
        return "PETSCII"
    if any(h in t for h in _ANSI_TTYPE_HINTS):
        return "ANSI"
    return "ANSI"  # named a terminal type => negotiating client => treat as ANSI-capable


# ===========================================================================
# PETSCII -> ANSI/CP437 live transcoder (ANSI caller viewing a PETSCII C64 board)
# ===========================================================================
try:
    from petscii_tables import UC as _PET_UC, LC as _PET_LC   # 256-char code->Unicode tables
except Exception:
    _PET_UC = _PET_LC = None

# C64 colour control code -> Pepto RGB (for 24-bit ANSI SGR, exact C64 palette)
_PET_RGB = {
    0x90: (0, 0, 0),       0x05: (255, 255, 255), 0x1c: (104, 55, 43),   0x9f: (112, 164, 178),
    0x9c: (111, 61, 134),  0x1e: (88, 141, 67),   0x1f: (53, 40, 121),   0x9e: (184, 199, 111),
    0x81: (111, 79, 37),   0x95: (67, 57, 0),     0x96: (154, 103, 89),  0x97: (68, 68, 68),
    0x98: (108, 108, 108), 0x99: (154, 210, 132), 0x9a: (108, 94, 181),  0x9b: (149, 149, 149),
}
_FORCE_CP437 = {"\xa0": 0xDB}   # PETSCII inverse-space -> solid block (cp437 would give nbsp)
_UNI_CP437_FALLBACK = {   # glyphs CP437 lacks -> closest CP437 byte
    "╭": 0xDA, "╮": 0xBF, "╰": 0xC0, "╯": 0xD9, "╳": ord("X"), "╲": ord("\\"), "╱": ord("/"),
    "▔": 0xDF, "▁": 0xDC, "▂": 0xDC, "▃": 0xDC, "▏": 0xB3, "▎": 0xB3, "▍": 0xDD, "▕": 0xDE,
    "▖": 0xDC, "▗": 0xDC, "▘": 0xDF, "▝": 0xDF, "▚": 0xB1, "◤": 0xDF, "◥": 0xDF,
    "●": 0x07, "✓": ord("v"), "π": 0xE3,
}
# C64 custom (private-use) graphics -> nearest CP437 line/block (one-eighth lines, shaded/quarter blocks)
_UNI_CP437_FALLBACK.update({chr(c): v for c, v in {
    0xf122:0xC4,0xf123:0xC4,0xf124:0xC4,0xf125:0xC4,0xf13b:0xC4,   # horizontals -> ─
    0xf126:0xB3,0xf127:0xB3,0xf128:0xB3,0xf129:0xB3,0xf13c:0xB3,   # verticals -> │
    0xf12a:0xC0,0xf12b:0xDA,0xf12c:0xBF,0xf12d:0xD9,               # eighth corners
    0xf12e:0xDD,0xf12f:0xDC,                                       # left/lower half shade -> ▌ ▄
    0xf130:0xDE,0xf131:0xDE,0xf132:0xDF,0xf133:0xDF,               # right/upper quarter blocks -> ▐ ▀
}.items()})



def _uni_to_cp437(ch: str) -> int:
    if ch in _FORCE_CP437:
        return _FORCE_CP437[ch]
    try:
        return ch.encode("cp437")[0]
    except Exception:
        return _UNI_CP437_FALLBACK.get(ch, 0x3F)   # '?'


class PetsciiToAnsi:
    """Stateful live transcoder: a C64 board's PETSCII byte stream -> ANSI/CP437 bytes for an
    ANSI (SyncTERM) caller. Handles C64 colour, reverse video, cursor/clear/home, and the
    uppercase-graphics / lowercase-text charset switch (which changes what each byte means)."""
    def __init__(self):
        self.mode = "uc"       # uc = uppercase/graphics (C64 power-on default); lc = lowercase/text
        self.reverse = False

    def feed(self, data: bytes) -> bytes:
        if _PET_UC is None:
            return data        # tables unavailable -> passthrough
        out = bytearray()
        table = _PET_UC if self.mode == "uc" else _PET_LC
        for b in data:
            if b == 0x0D:                         out += b"\r\n"; continue
            if b in (0x0A, 0x8D):                 continue
            if b == 0x93:                         out += b"\x1b[2J\x1b[H"; continue   # clear
            if b == 0x13:                         out += b"\x1b[H"; continue          # home
            if b == 0x11:                         out += b"\x1b[B"; continue          # cursor down
            if b == 0x91:                         out += b"\x1b[A"; continue          # up
            if b == 0x1D:                         out += b"\x1b[C"; continue          # right
            if b == 0x9D:                         out += b"\x1b[D"; continue          # left
            if b == 0x14:                         out += b"\b \b"; continue           # delete
            if b == 0x12:  self.reverse = True;   out += b"\x1b[7m"; continue         # reverse on
            if b == 0x92:  self.reverse = False;  out += b"\x1b[27m"; continue        # reverse off
            if b == 0x0E:  self.mode = "lc"; table = _PET_LC; continue                # text charset
            if b == 0x8E:  self.mode = "uc"; table = _PET_UC; continue                # graphics charset
            if b in _PET_RGB:
                r, g, bl = _PET_RGB[b]
                out += ("\x1b[38;2;%d;%d;%dm" % (r, g, bl)).encode("ascii"); continue
            if b < 0x20 or 0x80 <= b <= 0x9F:     continue   # other unhandled control -> drop
            ch = table[b]
            if ch == "�":               continue
            out.append(_uni_to_cp437(ch))
        return bytes(out)


def inst_del_input(data: bytes) -> bytes:
    """Map the caller's Backspace/Delete to PETSCII INST/DEL ($14) for a board that uses it
    (C-Net 128: pressing INST/DEL selects Commodore/PETSCII graphics, and $14 is the native
    delete). Handles ASCII BS ($08), ASCII DEL ($7F), and the ANSI Delete sequence ESC[3~.
    A bare ESC ($1B) is left untouched (that's the board's ANSI selection key). Everything
    else passes through unchanged, so ANSI output/typing is unaffected."""
    out = bytearray()
    i, n = 0, len(data)
    while i < n:
        b = data[i]
        if b == 0x1B and i + 3 < n and data[i + 1] == 0x5B and data[i + 2] == 0x33 and data[i + 3] == 0x7E:
            out.append(0x14); i += 4; continue        # ESC[3~  (Delete key)
        if b in (0x08, 0x7F):
            out.append(0x14); i += 1; continue        # Backspace / ASCII DEL
        out.append(b); i += 1
    return bytes(out)


class C128Session:
    """Stateful helper for a board that lets the caller choose ANSI or PETSCII (C-Net 128:
    [INST/DEL]=Commodore, [ESC]=ANSI). For an ANSI caller we watch which they pick from their
    keypress ($14=Commodore, $1B=ANSI): if Commodore, transcode the board's PETSCII output to
    ANSI/CP437 so an ANSI terminal can actually see it (colour + line breaks); if ANSI, pass the
    board's native ANSI straight through. A Commodore caller always gets raw. Backspace/Delete
    is mapped to PETSCII INST/DEL ($14) either way so the selection (and delete) works."""
    def __init__(self, caller_is_ansi: bool):
        self.ansi_caller = caller_is_ansi
        self.mode = None                 # None (undecided) | "petscii" | "ansi"
        self._pet = PetsciiToAnsi()

    def inp(self, data: bytes) -> bytes:  # caller -> board
        data = inst_del_input(data)
        if self.ansi_caller and self.mode is None:
            for b in data:
                if b == 0x14:
                    self.mode = "petscii"; break
                if b == 0x1B:
                    self.mode = "ansi"; break
        return data

    def out(self, data: bytes) -> bytes:  # board -> caller
        if self.ansi_caller and self.mode == "petscii":
            return self._pet.feed(data)   # transcode PETSCII -> ANSI for the ANSI terminal
        return data                       # native ANSI, or pre-selection ASCII, or Commodore caller


def ansi_input_to_petscii(data: bytes) -> bytes:
    """Translate an ANSI/SyncTERM caller's keystrokes to PETSCII for a C64 board."""
    out = bytearray()
    i, n = 0, len(data)
    while i < n:
        b = data[i]
        if b == 0x1B and i + 2 < n and data[i + 1] == 0x5B:    # ESC[ ... arrow -> CBM cursor
            out.append({0x41: 0x91, 0x42: 0x11, 0x43: 0x1D, 0x44: 0x9D}.get(data[i + 2], 0x20))
            i += 3; continue
        if b in (0x0A, 0x0D):    out.append(0x0D); i += 1; continue      # Enter
        if b in (0x08, 0x7F):    out.append(0x14); i += 1; continue      # Backspace -> PETSCII DEL
        if 0x61 <= b <= 0x7A:    out.append(b - 0x20); i += 1; continue  # a-z -> uppercase letters
        out.append(b); i += 1    # digits / punctuation / uppercase pass through
    return bytes(out)


@dataclass
class BBSEntry:
    """Represents a single target BBS (Telnet or SSH) in the gateway directory."""
    hotkey: str
    name: str
    host: str
    port: int
    scope: str = "EXTERNAL"  # LOCAL, EXTERNAL, SSH-LOC, or SSH-EXT
    description: str = ""
    charset: str = "ASCII"   # ASCII (default) or PETSCII — board's native output charset

    @property
    def is_ssh(self) -> bool:
        return "SSH" in self.scope.upper() or self.host.lower().startswith("ssh://")

    def parse_target(self) -> Tuple[Optional[str], Optional[str], str]:
        """
        Extract optional (ssh_user, ssh_password, clean_hostname) from `host`.
        Supports `host`, `user@host`, `user:pass@host`, or `ssh://user:pass@host`.
        """
        raw = self.host.strip()
        if raw.lower().startswith("ssh://"):
            raw = raw[6:]
        if "@" in raw:
            creds, clean_host = raw.rsplit("@", 1)
            if ":" in creds:
                user, pw = creds.split(":", 1)
                return user, pw, clean_host
            return creds, None, clean_host
        return None, None, raw


@dataclass
class GatewayConfig:
    """Holds all human-readable settings loaded from gateway.cfg."""
    gateway_title: str = "The Nexus BBS Telnet & SSH Gateway"
    sysop_name: str = "SysOp"
    listen_host: str = "0.0.0.0"
    listen_port: int = 23
    ansi_file: str = "gateway.ans"
    ssh_enabled: bool = False
    ssh_listen_port: int = 2222
    ssh_host_key: str = "gateway_ssh_host_key"
    display_mode: str = "BOTH"  # BOTH, LIGHTBAR, ANSI_HOTKEY, or PLAIN (40-col ASCII/PETSCII)
    terminal_gate: bool = True  # drop+ban non-terminal probes (HTTP/TLS/SSH/binary) on port 23
    bounce_detect: bool = True  # ban IPs that repeatedly reach a board then bounce without login
    bounce_min: int = 8         # board sessions shorter than this = instant/busy drop, not a bounce
    bounce_seconds: int = 120   # board sessions in [bounce_min, bounce_seconds] = a "login bounce"
    bounce_limit: int = 3       # this many bounces within bounce_window -> ban the IP
    bounce_window: int = 1800   # sliding window (seconds) for counting bounces
    botcheck: bool = False      # show a type-the-characters CAPTCHA before the menu (anti-bot)
    botcheck_exempt_allowlist: bool = True  # allowlisted IPs skip the CAPTCHA (set FALSE to test it yourself)
    botcheck_len: int = 5       # number of random characters in the challenge code
    botcheck_attempts: int = 2  # tries allowed before the caller is dropped + ban-logged
    botcheck_timeout: int = 60  # seconds the caller has to answer each try
    default_term: str = "PETSCII"  # assumed caller type when telnet TTYPE is not negotiated
    hotkey_prompt: bool = True     # ANSI_HOTKEY mode: append RoFGate's own hotkey prompt below the .ans
    public_host: str = ""  # public name shown to callers in place of real internal host:port
    terminal_prompt: bool = True  # ask the caller ANSI vs Commodore (auto-detect can't tell)
    menu_start_x: int = 3
    menu_start_y: int = 7
    menu_width: int = 75
    menu_rows: int = 10
    idle_timeout: int = 180
    connect_timeout: int = 15
    return_after_disconnect: bool = True
    color_header: int = 15
    color_border: int = 11
    color_item_fg: int = 7
    color_item_bg: int = 0
    color_hilite_fg: int = 15
    color_hilite_bg: int = 1
    security_enabled: bool = True
    max_connections_per_ip: int = 2
    max_total_nodes: int = 32
    rate_limit_connections: int = 5
    rate_limit_window: int = 60
    auto_ban_duration: int = 900
    denylist_file: str = "denylist.txt"
    allowlist_file: str = "allowlist.txt"
    mystic_data_path: str = ""
    bbs_list: List[BBSEntry] = field(default_factory=list)



class SecurityManager:
    """
    Built-in Application Firewall & Rate-Limiting Engine:
      - IP Allowlist & Denylist (Supports exact IPs, CIDR subnets, and wildcard 192.168.1.*)
      - Sliding-window connection rate limiting & temporary automatic bans
      - Max concurrent sessions per IP (anti-node-hogging / dupeip protection)
      - Total active node capacity enforcement (max total callers)
      - Anti-SSRF / re-entrancy loop detection
    """

    def __init__(self) -> None:
        self.connection_history: Dict[str, List[float]] = defaultdict(list)
        self.bounce_history: Dict[str, List[float]] = defaultdict(list)  # ip -> short-board-session times
        self.banned_ips: Dict[str, float] = {}  # ip -> unban_timestamp
        self.active_sessions: Dict[str, int] = defaultdict(int)  # ip -> count
        self.total_active: int = 0
        self.lock = asyncio.Lock()

    @staticmethod
    def _match_ip_in_entries(ip_str: str, entries: List[str]) -> bool:
        try:
            ip = ipaddress.ip_address(ip_str)
        except ValueError:
            return False
        for raw in entries:
            entry = raw.strip()
            if not entry or entry.startswith("#") or entry.startswith(";"):
                continue
            if "*" in entry:
                prefix = entry.split("*")[0]
                if ip_str.startswith(prefix):
                    return True
                continue
            try:
                net = ipaddress.ip_network(entry, strict=False)
                if ip in net:
                    return True
            except ValueError:
                pass
        return False

    def load_ip_list_file(self, filename: str, cfg: GatewayConfig, cfg_dir: str) -> List[str]:
        if not filename:
            return []
        paths = []
        if os.path.isabs(filename):
            paths.append(filename)
        else:
            paths.append(os.path.join(cfg_dir, filename))
            if cfg.mystic_data_path:
                paths.append(os.path.join(cfg.mystic_data_path, filename))

        entries: List[str] = []
        for p in paths:
            if os.path.exists(p):
                try:
                    with open(p, "r", encoding="utf-8", errors="replace") as f:
                        for line in f:
                            s = line.strip()
                            if s and not s.startswith("#") and not s.startswith(";"):
                                entries.append(s)
                except Exception as exc:
                    logging.warning("Error reading IP filter list %s: %s", p, exc)
        return entries

    async def check_connection(self, ip_str: str, cfg: GatewayConfig, cfg_dir: str) -> Tuple[bool, str]:
        """
        Evaluate incoming IP against allowlist, denylist, bans, concurrency, and rate limits.
        Returns (is_allowed, status_code).
        """
        if not cfg.security_enabled:
            return True, "OK"

        now = time.monotonic()
        async with self.lock:
            # 1. Allowlist check (bypasses all security throttles)
            allowlist_entries = self.load_ip_list_file(cfg.allowlist_file, cfg, cfg_dir)
            if self._match_ip_in_entries(ip_str, allowlist_entries):
                return True, "ALLOWLIST_BYPASS"

            # 2. Denylist check
            denylist_entries = self.load_ip_list_file(cfg.denylist_file, cfg, cfg_dir)
            if self._match_ip_in_entries(ip_str, denylist_entries):
                return False, "DENYLIST"

            # 3. Active Auto-Ban check
            if ip_str in self.banned_ips:
                if now < self.banned_ips[ip_str]:
                    rem = int(self.banned_ips[ip_str] - now)
                    return False, f"BANNED:{rem}"
                else:
                    del self.banned_ips[ip_str]

            # 4. Total Gateway Capacity (Max Nodes)
            if self.total_active >= cfg.max_total_nodes:
                return False, "BUSY"

            # 5. Concurrent Connections per IP
            if self.active_sessions[ip_str] >= cfg.max_connections_per_ip:
                return False, "DUPEIP"

            # 6. Rate Limiting (Sliding Window)
            history = [t for t in self.connection_history[ip_str] if now - t < cfg.rate_limit_window]
            history.append(now)
            self.connection_history[ip_str] = history
            if len(history) > cfg.rate_limit_connections:
                self.banned_ips[ip_str] = now + cfg.auto_ban_duration
                return False, f"RATE_LIMIT:{cfg.auto_ban_duration}"

            return True, "OK"

    async def add_runtime_ban(self, ip_str: str, duration: int) -> None:
        """Temporarily ban an IP in-memory (e.g. a non-terminal scanner caught by the gate)."""
        async with self.lock:
            self.banned_ips[ip_str] = time.monotonic() + max(1, duration)

    async def register_bounce(self, ip_str: str, cfg: "GatewayConfig", cfg_dir: str) -> bool:
        """Record a short 'board bounce' (an IP reached a board but left quickly, without logging
        in — the scanner signature). Returns True and temporarily bans the IP once it has bounced
        `bounce_limit` times within `bounce_window`. Allowlisted callers are never counted/banned."""
        async with self.lock:
            if self._match_ip_in_entries(ip_str, self.load_ip_list_file(cfg.allowlist_file, cfg, cfg_dir)):
                return False
            now = time.monotonic()
            hist = [t for t in self.bounce_history[ip_str] if now - t < cfg.bounce_window]
            hist.append(now)
            self.bounce_history[ip_str] = hist
            if len(hist) >= cfg.bounce_limit:
                self.banned_ips[ip_str] = now + cfg.auto_ban_duration
                self.bounce_history[ip_str] = []   # reset after banning
                return True
            return False

    async def register_connect(self, ip_str: str) -> None:
        async with self.lock:
            self.active_sessions[ip_str] += 1
            self.total_active += 1

    async def register_disconnect(self, ip_str: str) -> None:
        async with self.lock:
            if self.active_sessions[ip_str] > 0:
                self.active_sessions[ip_str] -= 1
            if self.total_active > 0:
                self.total_active -= 1


GLOBAL_SECURITY = SecurityManager()

def parse_bool(val: str) -> bool:
    return val.strip().upper() in ("TRUE", "YES", "1", "ON")


def load_gateway_config(cfg_path: str) -> GatewayConfig:
    """Load and parse the human-readable gateway.cfg file."""
    cfg = GatewayConfig()
    if not os.path.exists(cfg_path):
        logging.warning("Config file %s not found; using built-in defaults.", cfg_path)
        return cfg

    with open(cfg_path, "r", encoding="utf-8", errors="replace") as f:
        for raw_line in f:
            line = raw_line.strip()
            if not line or line.startswith("#") or line.startswith(";"):
                continue
            if "=" not in line:
                continue

            key, val = line.split("=", 1)
            key = key.strip().upper()
            val = val.strip()

            if key == "BBS":
                parts = [p.strip() for p in val.split("|")]
                if len(parts) >= 4:
                    hotkey = parts[0][:1].upper() if parts[0] else str(len(cfg.bbs_list) + 1)
                    name = parts[1]
                    host = parts[2]
                    try:
                        port = int(parts[3])
                    except ValueError:
                        port = 23
                    scope = parts[4].upper() if len(parts) >= 5 and parts[4] else (
                        "LOCAL" if host in ("127.0.0.1", "localhost") or host.startswith("192.168.") or host.startswith("10.") else "EXTERNAL"
                    )
                    desc = parts[5] if len(parts) >= 6 else ""
                    charset = parts[6].upper() if len(parts) >= 7 and parts[6] else "ASCII"
                    if charset not in ("ASCII", "PETSCII", "CHOICE"):
                        charset = "ASCII"
                    if hotkey in ("L", "P", "Q"):
                        logging.warning(
                            "BBS entry '%s' is assigned reserved hotkey '%s' (clashes with gateway controls L=Lightbar, P=Ping, Q=Quit)",
                            name, hotkey
                        )
                    cfg.bbs_list.append(
                        BBSEntry(
                            hotkey=hotkey,
                            name=name,
                            host=host,
                            port=port,
                            scope=scope,
                            description=desc,
                            charset=charset,
                        )
                    )
            elif key == "GATEWAY_TITLE":
                cfg.gateway_title = val
            elif key == "SYSOP_NAME":
                cfg.sysop_name = val
            elif key == "LISTEN_HOST":
                cfg.listen_host = val
            elif key == "LISTEN_PORT":
                try:
                    cfg.listen_port = int(val)
                except ValueError:
                    pass
            elif key == "ANSI_FILE":
                cfg.ansi_file = val
            elif key == "SSH_ENABLED":
                cfg.ssh_enabled = parse_bool(val)
            elif key == "SSH_LISTEN_PORT":
                try:
                    cfg.ssh_listen_port = int(val)
                except ValueError:
                    pass
            elif key == "SSH_HOST_KEY":
                cfg.ssh_host_key = val
            elif key == "DISPLAY_MODE":
                mode = val.upper()
                if mode in ("BOTH", "LIGHTBAR", "ANSI_HOTKEY", "PLAIN"):
                    cfg.display_mode = mode
            elif key == "TERMINAL_GATE":
                cfg.terminal_gate = parse_bool(val)
            elif key == "BOUNCE_DETECT":
                cfg.bounce_detect = parse_bool(val)
            elif key == "BOUNCE_MIN":
                cfg.bounce_min = max(0, int(val))
            elif key == "BOUNCE_SECONDS":
                cfg.bounce_seconds = max(10, int(val))
            elif key == "BOUNCE_LIMIT":
                cfg.bounce_limit = max(1, int(val))
            elif key == "BOUNCE_WINDOW":
                cfg.bounce_window = max(60, int(val))
            elif key == "BOTCHECK":
                cfg.botcheck = parse_bool(val)
            elif key == "BOTCHECK_EXEMPT_ALLOWLIST":
                cfg.botcheck_exempt_allowlist = parse_bool(val)
            elif key == "BOTCHECK_LEN":
                cfg.botcheck_len = max(3, min(10, int(val)))
            elif key == "BOTCHECK_ATTEMPTS":
                cfg.botcheck_attempts = max(1, int(val))
            elif key == "BOTCHECK_TIMEOUT":
                cfg.botcheck_timeout = max(10, int(val))
            elif key == "DEFAULT_TERM":
                v = val.upper()
                if v in ("ANSI", "PETSCII"):
                    cfg.default_term = v
            elif key == "HOTKEY_PROMPT":
                cfg.hotkey_prompt = parse_bool(val)
            elif key == "PUBLIC_HOST":
                cfg.public_host = val
            elif key == "TERMINAL_PROMPT":
                cfg.terminal_prompt = parse_bool(val)
            elif key == "MENU_START_X":
                cfg.menu_start_x = max(1, int(val))
            elif key == "MENU_START_Y":
                cfg.menu_start_y = max(1, int(val))
            elif key == "MENU_WIDTH":
                cfg.menu_width = max(40, min(77, int(val)))
            elif key == "MENU_ROWS":
                cfg.menu_rows = max(3, min(18, int(val)))
            elif key == "IDLE_TIMEOUT":
                cfg.idle_timeout = max(10, int(val))
            elif key == "CONNECT_TIMEOUT":
                cfg.connect_timeout = max(3, int(val))
            elif key == "RETURN_AFTER_DISCONNECT":
                cfg.return_after_disconnect = parse_bool(val)
            elif key == "COLOR_HEADER":
                cfg.color_header = int(val)
            elif key == "COLOR_BORDER":
                cfg.color_border = int(val)
            elif key == "COLOR_ITEM_FG":
                cfg.color_item_fg = int(val)
            elif key == "COLOR_ITEM_BG":
                cfg.color_item_bg = int(val)
            elif key == "COLOR_HILITE_FG":
                cfg.color_hilite_fg = int(val)
            elif key == "COLOR_HILITE_BG":
                cfg.color_hilite_bg = int(val)
            elif key == "SECURITY_ENABLED":
                cfg.security_enabled = parse_bool(val)
            elif key == "MAX_CONNECTIONS_PER_IP":
                cfg.max_connections_per_ip = max(1, int(val))
            elif key == "MAX_TOTAL_NODES":
                cfg.max_total_nodes = max(1, int(val))
            elif key == "RATE_LIMIT_CONNECTIONS":
                cfg.rate_limit_connections = max(1, int(val))
            elif key == "RATE_LIMIT_WINDOW":
                cfg.rate_limit_window = max(5, int(val))
            elif key == "AUTO_BAN_DURATION":
                cfg.auto_ban_duration = max(10, int(val))
            elif key == "DENYLIST_FILE":
                cfg.denylist_file = val
            elif key == "ALLOWLIST_FILE":
                cfg.allowlist_file = val
            elif key == "MYSTIC_DATA_PATH":
                cfg.mystic_data_path = val

    return cfg


def _normalize_ansi_frame(data: bytes) -> bytes:
    """Strip leading/trailing blank lines and any trailing newline from a CP437 .ans frame.
    A leading blank line prints as a black bar at the top of the screen; trailing blank lines
    (or a final newline) push the cursor off the bottom and scroll the whole screen up a row —
    which, in BOTH mode, de-aligns the absolutely-positioned lightbar overlay from the static
    art and can double the first board row. Normalizing here makes the gateway tolerant of
    hand-edited .ans files: the sysop can add/remove blank padding without breaking the layout."""
    def _blankish(ln: bytes) -> bool:
        return re.sub(rb"\x1b\[[0-9;?]*[A-Za-z]", b"", ln).strip(b" \x00") == b""
    lines = data.replace(b"\r\n", b"\n").split(b"\n")
    while lines and _blankish(lines[0]):
        lines.pop(0)
    while lines and _blankish(lines[-1]):
        lines.pop()
    return b"\r\n".join(lines)


def read_ansi_file_cp437(ansi_path: str) -> bytes:
    """
    Read an ANSI art file (.ans), strip SAUCE metadata and 0x1A EOF markers,
    and ensure output is pure 8-bit CP437 bytes for ANSI-BBS terminals.
    """
    if not os.path.exists(ansi_path):
        return b""

    with open(ansi_path, "rb") as f:
        data = f.read()

    if len(data) >= 128 and data[-128:-123] == b"SAUCE":
        sauce_comments = data[-128 + 104]
        data = data[:-128]
        if sauce_comments > 0:
            comnt_len = 5 + (sauce_comments * 64)
            if len(data) >= comnt_len and data[-comnt_len:-comnt_len + 5] == b"COMNT":
                data = data[:-comnt_len]

    eof_idx = data.find(b"\x1a")
    if eof_idx != -1:
        data = data[:eof_idx]

    if b"\xe2\x94" in data or b"\xe2\x95" in data or b"\xe2\x96" in data:
        try:
            text = data.decode("utf-8")
            text = mystic_pipe_to_ansi(text)
            return _normalize_ansi_frame(text.encode("cp437", errors="replace"))
        except UnicodeDecodeError:
            pass

    text = data.decode("cp437")
    if "|" in text:
        text = mystic_pipe_to_ansi(text)
    return _normalize_ansi_frame(text.encode("cp437", errors="replace"))


class TelnetSession:
    """Manages an incoming Telnet (or SSH) caller, CP437 lightbar UI, and Telnet/SSH outbound proxy."""

    def __init__(
        self,
        reader: asyncio.StreamReader,
        writer: asyncio.StreamWriter,
        cfg_path: str,
        is_inbound_ssh: bool = False,
    ) -> None:
        self.reader = reader
        self.writer = writer
        self.cfg_path = cfg_path
        self.is_inbound_ssh = is_inbound_ssh
        self.cfg = load_gateway_config(cfg_path)
        peer = writer.get_extra_info("peername") if writer else None
        self.client_ip = peer[0] if peer else "unknown"
        self.client_port = peer[1] if peer else 0
        self.selected_idx = 0
        self.scroll_offset = 0
        self.ping_status: Dict[int, str] = {}
        # Caller terminal class: "ANSI" (80-col colour lightbar) or "PETSCII" (40-col CBM).
        # Final value is decided from telnet TTYPE negotiation in run(); this is the fallback.
        self.term = self.cfg.default_term.upper() if self.cfg.default_term.upper() in ("ANSI", "PETSCII") else "PETSCII"

    async def send_raw(self, data: bytes) -> None:
        """Write raw bytes to the caller stream."""
        self.writer.write(data)
        await self.writer.drain()

    async def send_ansi(self, text: str) -> None:
        """Send gateway text to the caller, encoded for the detected terminal class.
        ANSI callers get full Mystic-pipe->CP437 ANSI colour. PETSCII (Commodore) callers get
        the colour/positioning stripped and the letters translated to PETSCII (case-correct)."""
        if self.term == "PETSCII":
            await self.send_raw(ascii_to_petscii(strip_to_plain(text)))
            return
        parsed = mystic_pipe_to_ansi(text)
        await self.send_raw(parsed.encode("cp437", errors="replace"))

    def _parse_iac_stream(self, data: bytes):
        """Parse a chunk of caller input during negotiation. Returns
        (non_iac_payload, [(verb,opt),...], ttype_or_None, naws_width_or_None). Handles the
        TERMINAL-TYPE (IAC SB TTYPE IS <name> IAC SE) and NAWS/window-size subnegotiations."""
        payload = bytearray()
        events = []
        ttype = None
        naws = None
        i, n = 0, len(data)
        while i < n:
            b = data[i]
            if b == IAC:
                if i + 1 >= n:
                    break
                cmd = data[i + 1]
                if cmd == IAC:
                    payload.append(IAC); i += 2
                elif cmd in (WILL, WONT, DO, DONT):
                    if i + 2 < n:
                        events.append((cmd, data[i + 2])); i += 3
                    else:
                        i += 2
                elif cmd == SB:
                    j = i + 2
                    sub = bytearray()
                    while j < n:
                        if data[j] == IAC:
                            if j + 1 < n and data[j + 1] == IAC:
                                sub.append(IAC); j += 2; continue
                            break            # IAC SE (or other) terminates the subnegotiation
                        sub.append(data[j]); j += 1
                    # sub = <option> <IS=0> <name...>
                    if len(sub) >= 2 and sub[0] == OPT_TTYPE and sub[1] == 0:
                        ttype = bytes(sub[2:]).decode("ascii", "replace").strip()
                    elif sub and sub[0] == OPT_NAWS and len(sub) >= 5:
                        naws = sub[1] * 256 + sub[2]   # reported terminal width (columns)
                    # advance past the terminator (IAC SE = 2 bytes, bare SE = 1)
                    if j < n and data[j] == IAC and j + 1 < n and data[j + 1] == SE:
                        i = j + 2
                    elif j < n and data[j] == SE:
                        i = j + 1
                    else:
                        i = j + 1
                else:
                    i += 2
            else:
                payload.append(b); i += 1
        return bytes(payload), events, ttype, naws

    async def negotiate_telnet_char_mode(self):
        """Negotiate 8-bit binary + char-at-a-time mode, AND probe the caller's TERMINAL-TYPE
        so we can auto-select the ANSI vs PETSCII front-end. Returns (early_payload, ttype, naws):
        early_payload = non-IAC bytes the caller sent (fed to the terminal gate), ttype = the
        negotiated terminal-type string or None, naws = the caller's reported terminal width in
        columns or None. Width is the reliable ANSI-vs-Commodore discriminator (40 vs 80 cols),
        because Commodore terminals like RGTerm report a PC-style terminal type ("ANSI-BBS")."""
        if self.is_inbound_ssh:
            return b"", None, None
        negotiation = bytes([
            IAC, WILL, OPT_BINARY,
            IAC, DO,   OPT_BINARY,
            IAC, WILL, OPT_ECHO,
            IAC, WILL, OPT_SGA,
            IAC, DO,   OPT_SGA,
            IAC, WONT, OPT_LINEMODE,
            IAC, DO,   OPT_TTYPE,      # ask the caller what terminal it is
            IAC, DO,   OPT_NAWS,       # ask the caller its window size (columns)
        ])
        await self.send_raw(negotiation)
        await asyncio.sleep(0.15)
        early = bytearray()
        ttype = None
        naws = None
        asked = False
        idle = 0
        # End negotiation after ~0.5s of silence (silent = non-negotiating Commodore term).
        while idle < 5:
            try:
                chunk = await asyncio.wait_for(self.reader.read(256), timeout=0.1)
            except asyncio.TimeoutError:
                idle += 1
                continue
            if not chunk:
                break
            idle = 0
            payload, events, sub_ttype, sub_naws = self._parse_iac_stream(chunk)
            early += payload
            for verb, opt in events:
                if verb == WILL and opt == OPT_TTYPE and not asked:
                    await self.send_raw(bytes([IAC, SB, OPT_TTYPE, 1, IAC, SE]))  # 1 = SEND
                    asked = True
            if sub_ttype:
                ttype = sub_ttype
            if sub_naws:
                naws = sub_naws
        return bytes(early), ttype, naws

    @staticmethod
    def _strip_telnet_iac(data: bytes) -> bytes:
        """Filter out Telnet IAC (0xFF) command sequences from user keyboard input."""
        out = bytearray()
        i = 0
        n = len(data)
        while i < n:
            b = data[i]
            if b == IAC:
                if i + 1 < n and data[i + 1] == IAC:
                    out.append(IAC)
                    i += 2
                elif i + 1 < n and data[i + 1] in (WILL, WONT, DO, DONT):
                    i += 3
                elif i + 1 < n and data[i + 1] == SB:
                    i += 2
                    while i < n and data[i] != SE:
                        i += 1
                    i += 1
                else:
                    i += 2
            else:
                out.append(b)
                i += 1
        return bytes(out)

    async def read_key(self, timeout: Optional[float] = None) -> Optional[str]:
        """Read a single keypress or ANSI-BBS / VT100 / Doorway arrow key from the caller."""
        wait_timeout = timeout or self.cfg.idle_timeout
        while True:
            try:
                raw = await asyncio.wait_for(self.reader.read(64), timeout=wait_timeout)
            except asyncio.TimeoutError:
                return "TIMEOUT"

            if not raw:
                return None

            clean = raw if self.is_inbound_ssh else self._strip_telnet_iac(raw)
            if not clean:
                continue

            if clean.startswith(b"\x1b"):
                if clean in (b"\x1b[A", b"\x1bOA"):
                    return "UP"
                if clean in (b"\x1b[B", b"\x1bOB"):
                    return "DOWN"
                if clean in (b"\x1b[C", b"\x1bOC"):
                    return "RIGHT"
                if clean in (b"\x1b[D", b"\x1bOD"):
                    return "LEFT"
                if clean in (b"\x1b[H", b"\x1b[1~", b"\x1bOH"):
                    return "HOME"
                if clean in (b"\x1b[F", b"\x1b[4~", b"\x1bOF", b"\x1b[K"):
                    return "END"
                if clean in (b"\x1b[5~", b"\x1b[V"):
                    return "PGUP"
                if clean in (b"\x1b[6~", b"\x1b[U"):
                    return "PGDN"
                if clean == b"\x1b":
                    return "ESC"
                continue

            if clean[0] in (0x00, 0xE0) and len(clean) >= 2:
                scan = clean[1]
                if scan == 72:
                    return "UP"
                if scan == 80:
                    return "DOWN"
                if scan == 71:
                    return "HOME"
                if scan == 79:
                    return "END"
                if scan == 73:
                    return "PGUP"
                if scan == 81:
                    return "PGDN"

            ch = clean[0]
            if ch in (13, 10):
                return "ENTER"
            if ch in (8, 127):
                return "BACKSPACE"
            if ch == 27:
                return "ESC"
            if 32 <= ch <= 126:
                return chr(ch)

    async def prompt_line(self, prompt_text: str, default: str = "", mask: bool = False, max_len: int = 32, timeout: float = 60, upper: bool = False) -> Optional[str]:
        """Interactive single-line input prompt (SSH username/password, botcheck answer, ...).
        upper=True echoes + stores each letter uppercased (so the answer matches the all-caps
        CAPTCHA code shown above it)."""
        await self.send_ansi(prompt_text)
        buf: List[str] = []
        while True:
            k = await self.read_key(timeout=timeout)
            if k is None or k == "TIMEOUT" or k == "ESC":
                return None
            if k == "ENTER":
                await self.send_ansi("\r\n")
                res = "".join(buf).strip()
                return res if res else default
            if k == "BACKSPACE":
                if buf:
                    buf.pop()
                    await self.send_raw(b"\x08 \x08")
                continue
            if len(k) == 1 and len(buf) < max_len:
                if upper:
                    k = k.upper()
                buf.append(k)
                echo_ch = "*" if mask else k
                await self.send_raw(echo_ch.encode("cp437"))

    def _resolve_ansi_path(self) -> str:
        if os.path.isabs(self.cfg.ansi_file):
            return self.cfg.ansi_file
        base_dir = os.path.dirname(os.path.abspath(self.cfg_path))
        return os.path.join(base_dir, self.cfg.ansi_file)

    async def render_generated_frame(self) -> None:
        """Render a standalone 79-column CP437 box-drawing frame using explicit ESC[y;1H positioning."""
        # Reign of Fire flame palette: red border, white title on red, yellow/orange accents.
        border_c = dos_color_to_ansi(self.cfg.color_border, 0)   # red
        head_c = dos_color_to_ansi(self.cfg.color_header, 4)     # white on red
        sub_c = dos_color_to_ansi(14, 0)                         # yellow
        col_c = dos_color_to_ansi(14, 0)                         # yellow
        norm_c = dos_color_to_ansi(12, 0)                        # orange (light red)
        dim_c = dos_color_to_ansi(6, 0)                          # dark orange (brown)
        hi_c = dos_color_to_ansi(15, 0)                          # white

        title = f" {self.cfg.gateway_title}  -  www.rofbbs.com "
        title_padded = title[:77].center(77)
        # Column header (built to EXACTLY 77 chars so the right border lands correctly)
        header_txt = ("  KEY   " + f"{'BBS SYSTEM NAME':<30}  " + f"{'ADDRESS':<24}  " + "PORT")[:77].ljust(77)

        rows = [
            f"{ESC}[0m{ESC}[2J{ESC}[1;1H{border_c}╔{'═' * 77}╗",
            f"{ESC}[2;1H{border_c}║{head_c}{title_padded}{border_c}║",
            f"{ESC}[3;1H{border_c}║{sub_c}  Use {hi_c}UP/DOWN{sub_c} Arrows + {hi_c}ENTER{sub_c} or press a {hi_c}Hotkey{sub_c} to connect (Telnet or SSH):   {border_c}║",
            f"{ESC}[4;1H{border_c}╠{'═' * 77}╣",
            f"{ESC}[5;1H{border_c}║{col_c}{header_txt}{border_c}║",
            f"{ESC}[6;1H{border_c}╟{'─' * 77}╢",
        ]
        for r in range(7, 17):
            rows.append(f"{ESC}[{r};1H{border_c}║{norm_c}{' ' * 77}{border_c}║")

        rows.extend([
            f"{ESC}[17;1H{border_c}╟{'─' * 77}╢",
            f"{ESC}[18;1H{border_c}║{dim_c}  INFO: {norm_c}{' ' * 69}{border_c}║",
            f"{ESC}[19;1H{border_c}╠{'═' * 77}╣",
            f"{ESC}[20;1H{border_c}║{norm_c}  [{hi_c}UP/DN{norm_c}] Move   [{hi_c}ENTER{norm_c}] Connect   [{hi_c}1-9/A-Z{norm_c}] Hotkey   [{hi_c}Q{norm_c}] Quit               {border_c}║",
            f"{ESC}[21;1H{border_c}╚{'═' * 77}╝{ESC}[0m",
        ])
        await self.send_ansi("".join(rows))

    async def render_lightbar_items(self) -> None:
        """Draw the visible rows of the lightbar selector and the active BBS description."""
        entries = self.cfg.bbs_list
        rows = self.cfg.menu_rows
        start_x = self.cfg.menu_start_x
        start_y = self.cfg.menu_start_y
        width = max(self.cfg.menu_width, 76)
        width = min(width, 79 - start_x)

        if self.selected_idx < self.scroll_offset:
            self.scroll_offset = self.selected_idx
        elif self.selected_idx >= self.scroll_offset + rows:
            self.scroll_offset = self.selected_idx - rows + 1

        normal_c = dos_color_to_ansi(self.cfg.color_item_fg, self.cfg.color_item_bg)
        hilite_c = dos_color_to_ansi(self.cfg.color_hilite_fg, self.cfg.color_hilite_bg)
        desc_c = dos_color_to_ansi(14, 0)   # yellow (flame palette)
        reset = f"{ESC}[0m"

        out: List[str] = []
        for r in range(rows):
            idx = self.scroll_offset + r
            y = start_y + r
            out.append(f"{ESC}[{y};{start_x}H")
            if idx < len(entries):
                item = entries[idx]
                is_sel = idx == self.selected_idx
                color = hilite_c if is_sel else normal_c
                marker = "»" if is_sel else " "
                disp_host = self.cfg.public_host or ""
                row_text = (
                    f" {marker}[{item.hotkey}]   "
                    f"{item.name[:33]:<33}  "
                    f"{disp_host[:24]:<24}  "
                    f"{item.port:<8}"
                )
                row_text = row_text[:width].ljust(width)
                out.append(f"{color}{row_text}{reset}")
            else:
                out.append(f"{normal_c}{' ' * width}{reset}")

        desc_y = start_y + rows + 1
        out.append(f"{ESC}[{desc_y};10H")
        if entries and 0 <= self.selected_idx < len(entries):
            cur = entries[self.selected_idx]
            disp_host = self.cfg.public_host or ""
            desc = f"{cur.description} ({disp_host})" if disp_host else cur.description
        else:
            desc = "No BBS entries configured in gateway.cfg."
        out.append(f"{desc_c}{desc[:68]:<68}{reset}")
        out.append(f"{ESC}[{desc_y + 2};78H")
        await self.send_ansi("".join(out))

    async def check_bbs_online(self) -> None:
        """Concurrently TCP-probe every listed board and record ONLINE/OFFLINE for the
        lightbar STATUS column. Internal host/port stays server-side; callers see only
        the word ONLINE or OFFLINE."""
        async def _probe_entry(idx: int, entry: BBSEntry) -> None:
            _, _, clean_host = entry.parse_target()
            # Skip self-referential / metadata targets (never proxy to our own port)
            if ((clean_host in ("127.0.0.1", "localhost", "0.0.0.0")
                 and entry.port in (self.cfg.listen_port, self.cfg.ssh_listen_port))
                    or clean_host == "169.254.169.254"):
                self.ping_status[idx] = ""
                return
            try:
                _, w = await asyncio.wait_for(
                    asyncio.open_connection(clean_host, entry.port), timeout=1.5
                )
                w.close()
                try:
                    await w.wait_closed()
                except Exception:
                    pass
                self.ping_status[idx] = "ONLINE"
            except Exception:
                self.ping_status[idx] = "OFFLINE"

        await asyncio.gather(
            *[_probe_entry(idx, entry) for idx, entry in enumerate(self.cfg.bbs_list)]
        )

    async def render_petscii_menu(self) -> None:
        """Render a 40-column PETSCII menu with Commodore colour for C64/C128 callers.
        Letters are translated to PETSCII (case-correct) and coloured with CBM control
        codes; the screen opens in text charset ($0E) + clear ($93), lines end in CR."""
        # 39 (not 40): a line exactly 40 chars wide auto-wraps on a 40-column Commodore
        # screen, and the following CR then adds a blank line. Keeping lines <=39 avoids that.
        W = 39
        # Reign of Fire flame palette (CBM colour control bytes)
        RED = b"\x1c"; ORANGE = b"\x81"; YELLOW = b"\x9e"; WHITE = b"\x05"
        def ln(s: str) -> bytes:
            return ascii_to_petscii(s[:W]) + b"\r"
        buf = bytearray([PET_TEXT_MODE, PET_CLEAR])
        bar = "=" * W
        buf += RED + ln(bar)
        buf += WHITE + ln(self.cfg.gateway_title.upper().center(W).rstrip())
        buf += YELLOW + ln("www.rofbbs.com".center(W).rstrip())
        buf += RED + ln(bar)
        buf += ln("")
        buf += YELLOW + ln(" SELECT A BOARD:")
        buf += ln("")
        for item in self.cfg.bbs_list:
            buf += ORANGE + ln(f" [{item.hotkey}] {item.name.upper()}")
        buf += ln("")
        buf += RED + ln(" [Q] QUIT")
        buf += RED + ln("-" * W)
        buf += WHITE + ascii_to_petscii(" YOUR CHOICE? ")
        await self.send_raw(bytes(buf))

    async def render_full_screen(self, force_lightbar: bool = False) -> None:
        """Render the menu for the detected terminal: a colour PETSCII 40-col screen for
        Commodore callers, or the 80-col ANSI colour lightbar for ANSI callers."""
        self.cfg = load_gateway_config(self.cfg_path)

        if self.term == "PETSCII":
            await self.render_petscii_menu()
            return

        ansi_bytes = read_ansi_file_cp437(self._resolve_ansi_path())
        mode = "LIGHTBAR" if force_lightbar else self.cfg.display_mode
        if mode == "PLAIN":
            mode = "LIGHTBAR"   # ANSI callers always get the colourful lightbar

        if mode == "ANSI_HOTKEY" and ansi_bytes:
            await self.send_raw(b"\x1b[0m\x1b[2J\x1b[1;1H" + ansi_bytes)
            if self.cfg.hotkey_prompt:
                prompt = (
                    f"{ESC}[22;1H{ESC}[0;1;36;40mSelect BBS Hotkey [{ESC}[1;37m1-{len(self.cfg.bbs_list)}{ESC}[1;36m], "
                    f"[{ESC}[1;37mL{ESC}[1;36m]ightbar Menu, or [{ESC}[1;37mQ{ESC}[1;36m]uit: {ESC}[0m"
                )
                await self.send_ansi(prompt)
        elif mode == "BOTH" and ansi_bytes:
            await self.send_raw(b"\x1b[0m\x1b[2J\x1b[1;1H" + ansi_bytes)
            await self.render_lightbar_items()
        else:
            await self.render_generated_frame()
            await self.render_lightbar_items()

    async def connect_to_ssh_bbs(self, entry: BBSEntry) -> None:
        """
        Connect the caller to a Local or External SSH BBS node.
        Uses `asyncssh` if installed, or falls back automatically to a POSIX PTY
        wrapping the system `/usr/bin/ssh` binary so no external pip packages are required.
        """
        ssh_user, ssh_pass, clean_host = entry.parse_target()

        await self.send_ansi(
            f"{ESC}[0m{ESC}[2J{ESC}[1;1H"
            f"|11╔═════════════════════════════════════════════════════════════════════════════╗\r\n"
            f"|11║ |15SSH Target    : |14{entry.name:<59} |11║\r\n"
            f"|11║ |15SSH Endpoint  : |10{f'{clean_host}:{entry.port} ({entry.scope})':<59} |11║\r\n"
            f"|11╚═════════════════════════════════════════════════════════════════════════════╝|07\r\n"
        )

        # Prompt caller for SSH login if not embedded in gateway.cfg as user:pass@host
        if not ssh_user:
            ssh_user = await self.prompt_line(
                "|11Enter SSH Username |08(Press ENTER for 'bbs', or ESC to cancel)|11: |15",
                default="bbs",
            )
            if not ssh_user:
                return

        if ssh_pass is None and HAS_ASYNCSSH:
            ssh_pass = await self.prompt_line(
                f"|11Enter SSH Password for |14{ssh_user}@{clean_host}|11 |08(Enter if none/prompted by BBS)|11: |15",
                default="",
                mask=True,
            )
            if ssh_pass is None:
                return

        await self.send_ansi(
            f"\r\n|10Establishing SSH tunnel to {ssh_user}@{clean_host}:{entry.port}...|07\r\n"
        )
        logging.info(
            "Caller %s:%s opening SSH connection to %s (%s@%s:%d)",
            self.client_ip,
            self.client_port,
            entry.name,
            ssh_user,
            clean_host,
            entry.port,
        )

        # Route 1: Native asyncssh client if available
        if HAS_ASYNCSSH:
            try:
                conn = await asyncio.wait_for(
                    asyncssh.connect(
                        clean_host,
                        port=entry.port,
                        username=ssh_user,
                        password=ssh_pass if ssh_pass else None,
                        known_hosts=None,
                        preferred_auth=("password", "keyboard-interactive", "none"),
                    ),
                    timeout=self.cfg.connect_timeout,
                )
                async with conn:
                    chan, _ = await conn.create_session(
                        asyncssh.SSHClientProcess,
                        term_type="ansi-bbs",
                        term_size=(80, 25),
                        encoding=None,
                    )
                    await self._bridge_streams(
                        chan.stdout,
                        chan.stdin,
                        strip_iac=not self.is_inbound_ssh,
                    )
                return
            except Exception as exc:
                await self.send_ansi(
                    f"\r\n|12[!] SSH connection failed ({clean_host}:{entry.port}): {exc}\r\n"
                    f"|07Press any key to return to the Gateway menu..."
                )
                await self.read_key(timeout=30)
                return

        # Route 2: Zero-dependency POSIX PTY + system `ssh` binary fallback
        ssh_bin = shutil.which("ssh")
        if not ssh_bin:
            await self.send_ansi(
                "\r\n|12[!] Neither Python 'asyncssh' nor system 'ssh' client found on host.\r\n"
                "|07Press any key to return to the Gateway menu..."
            )
            await self.read_key(timeout=30)
            return

        master_fd, slave_fd = pty.openpty()
        # Set 80x25 terminal window size on the PTY
        winsize = struct.pack("HHHH", 25, 80, 0, 0)
        fcntl.ioctl(slave_fd, termios.TIOCSWINSZ, winsize)

        cmd = [
            ssh_bin,
            "-tt",
            "-p", str(entry.port),
            "-o", "StrictHostKeyChecking=no",
            "-o", "UserKnownHostsFile=/dev/null",
            "-o", f"ConnectTimeout={self.cfg.connect_timeout}",
            f"{ssh_user}@{clean_host}",
        ]

        env = os.environ.copy()
        env["TERM"] = "ansi"

        proc = await asyncio.create_subprocess_exec(
            *cmd,
            stdin=slave_fd,
            stdout=slave_fd,
            stderr=slave_fd,
            env=env,
            start_new_session=True,
        )
        os.close(slave_fd)

        loop = asyncio.get_running_loop()
        pty_out_queue: asyncio.Queue[bytes] = asyncio.Queue()

        def _on_pty_readable() -> None:
            try:
                data = os.read(master_fd, 4096)
                if data:
                    pty_out_queue.put_nowait(data)
                else:
                    loop.remove_reader(master_fd)
                    pty_out_queue.put_nowait(b"")
            except OSError:
                loop.remove_reader(master_fd)
                pty_out_queue.put_nowait(b"")

        loop.add_reader(master_fd, _on_pty_readable)
        pw_sent = False

        async def _pty_to_caller() -> None:
            nonlocal pw_sent
            while True:
                chunk = await pty_out_queue.get()
                if not chunk:
                    break
                # If password was pre-configured in gateway.cfg, auto-answer SSH's password prompt
                if ssh_pass and not pw_sent and b"password:" in chunk.lower():
                    pw_sent = True
                    os.write(master_fd, (ssh_pass + "\n").encode("utf-8"))
                    continue
                await self.send_raw(chunk)

        async def _caller_to_pty() -> None:
            while True:
                data = await self.reader.read(4096)
                if not data:
                    break
                clean = data if self.is_inbound_ssh else self._strip_telnet_iac(data)
                if clean:
                    os.write(master_fd, clean)

        t1 = asyncio.create_task(_pty_to_caller())
        t2 = asyncio.create_task(_caller_to_pty())
        done, pending = await asyncio.wait([t1, t2], return_when=asyncio.FIRST_COMPLETED)
        for t in pending:
            t.cancel()

        try:
            loop.remove_reader(master_fd)
        except Exception:
            pass
        try:
            os.close(master_fd)
        except OSError:
            pass
        if proc.returncode is None:
            try:
                proc.terminate()
                await asyncio.wait_for(proc.wait(), timeout=2.0)
            except Exception:
                pass

    async def _bridge_streams(self, remote_reader, remote_writer, strip_iac: bool = False,
                              transform_out=None, transform_in=None) -> None:
        """Bidirectionally pipe bytes between caller and downstream BBS.
        transform_out(board->caller) and transform_in(caller->board) optionally rewrite the
        stream (e.g. live PETSCII<->ANSI transcoding for a mismatched caller/board charset)."""
        async def _c2s() -> None:
            try:
                while True:
                    data = await self.reader.read(4096)
                    if not data:
                        break
                    out = self._strip_telnet_iac(data) if strip_iac else data
                    if transform_in and out:
                        out = transform_in(out)
                    if out:
                        remote_writer.write(out)
                        await remote_writer.drain()
            except Exception:
                pass

        async def _s2c() -> None:
            try:
                while True:
                    data = await remote_reader.read(4096)
                    if not data:
                        break
                    out = transform_out(data) if transform_out else data
                    if out:
                        self.writer.write(out)
                        await self.writer.drain()
            except Exception:
                pass

        t1 = asyncio.create_task(_c2s())
        t2 = asyncio.create_task(_s2c())
        done, pending = await asyncio.wait([t1, t2], return_when=asyncio.FIRST_COMPLETED)
        for t in pending:
            t.cancel()

    async def _graphics_choice_handshake(self, rreader, rwriter) -> None:
        """Auto-answer a board that offers its own ANSI/PETSCII graphics selection (C-Net 128:
        'SELECT YOUR GRAPHICS -- [INST/DEL]=C64/128, [ESC]=ANSI'). Send ESC ($1B) for an ANSI
        caller, INST/DEL ($14) for a Commodore caller. The board then outputs natively in that
        format, so the stream is passed through with no transcoding. The intro is consumed."""
        seen = bytearray()
        prompt = False
        try:
            while True:
                chunk = await asyncio.wait_for(rreader.read(1024), timeout=(2.0 if prompt else 12.0))
                if not chunk:
                    break
                seen += self._strip_telnet_iac(chunk)
                up = seen.upper()
                if b"GRAPHICS" in up or b"SELECT" in up:
                    prompt = True
        except asyncio.TimeoutError:
            pass
        code = b"\x1b" if self.term == "ANSI" else b"\x14"   # ESC vs INST/DEL
        try:
            rwriter.write(code)
            await rwriter.drain()
            logging.info("C128 graphics-choice: sent %s for %s caller",
                         "ESC(ANSI)" if self.term == "ANSI" else "INST/DEL(Commodore)", self.term)
        except Exception:
            pass

    async def _petscii_detect_handshake(self, rreader, rwriter) -> None:
        """Answer the C64 board's 'PRESS BACKSPACE/DELETE' terminal-detect prompt as a
        Commodore terminal by sending PETSCII DEL ($14), so the board switches to PETSCII
        colour/graphics output. The board's ASCII intro is consumed (not shown to the caller);
        the board re-draws its banner in PETSCII after the switch."""
        seen = bytearray()
        prompt_seen = False
        try:
            while True:
                # Before the prompt: wait up to 12s per read (board boot/LOADING is slow).
                # After the prompt appears: wait only for a short idle gap so we send $14
                # once the board has FINISHED printing and is actually ready to read input
                # (sending it mid-print gets dropped and the board never switches).
                chunk = await asyncio.wait_for(rreader.read(1024), timeout=(2.0 if prompt_seen else 12.0))
                if not chunk:
                    break
                seen += self._strip_telnet_iac(chunk)
                if b"DELETE" in seen.upper() or b"BACKSPACE" in seen.upper():
                    prompt_seen = True
        except asyncio.TimeoutError:
            pass
        try:
            rwriter.write(b"\x14")   # PETSCII DEL = "I am a Commodore terminal" -> board sends PETSCII
            await rwriter.drain()
            logging.info("PETSCII handshake: sent $14 (prompt_seen=%s, consumed %d bytes)",
                         prompt_seen, len(seen))
        except Exception:
            pass

    async def connect_to_bbs(self, entry: BBSEntry) -> None:
        """Route caller to either an SSH BBS or a Telnet BBS based on the entry's mode."""
        if entry.is_ssh:
            await self.connect_to_ssh_bbs(entry)
            return

        _, _, clean_host = entry.parse_target()
        # Anti-SSRF and Loopback Protection
        if clean_host in ("127.0.0.1", "localhost", "0.0.0.0") and entry.port in (self.cfg.listen_port, self.cfg.ssh_listen_port):
            await self.send_ansi("\r\n|12[!] Loopback loop blocked: Gateway cannot proxy to its own listening port.|07\r\n")
            await self.read_key(timeout=10)
            return
        if clean_host == "169.254.169.254":
            await self.send_ansi("\r\n|12[!] Security policy blocked: Link-local metadata endpoint prohibited.|07\r\n")
            await self.read_key(timeout=10)
            return
        if self.term == "PETSCII":
            await self.send_raw(
                bytes([PET_CLEAR]) + ascii_to_petscii(f"CONNECTING TO {entry.name.upper()}...\r")
            )
        else:
            disp_host = self.cfg.public_host or entry.name
            await self.send_ansi(
                f"{ESC}[0m{ESC}[2J{ESC}[1;1H"
                f"|04╔═════════════════════════════════════════════════════════════════════════════╗\r\n"
                f"|04║ |15Connecting to : |14{entry.name:<59} |04║\r\n"
                f"|04║ |15Address       : |14{disp_host:<59} |04║\r\n"
                f"|04╚═════════════════════════════════════════════════════════════════════════════╝|07\r\n"
            )
        logging.info(
            "Caller %s:%s connecting via Telnet to %s (%s:%d [%s])",
            self.client_ip,
            self.client_port,
            entry.name,
            clean_host,
            entry.port,
            entry.scope,
        )

        try:
            remote_reader, remote_writer = await asyncio.wait_for(
                asyncio.open_connection(clean_host, entry.port),
                timeout=self.cfg.connect_timeout,
            )
        except Exception as exc:
            logging.warning("Connect to %s (%s:%d) failed: %s", entry.name, clean_host, entry.port, exc)
            await self.send_ansi(
                f"\r\n|12[!] {entry.name} is not answering right now.\r\n"
                f"|07Press any key to return to the Gateway menu..."
            )
            await self.read_key(timeout=30)
            return

        await self.send_ansi(f"|10Connected! Handing off session to {entry.name}...|07\r\n\r\n")

        transform_out = transform_in = None
        if entry.charset == "PETSCII":
            # Drive the C64 board into PETSCII (answer its terminal-detect as a Commodore term)
            await self._petscii_detect_handshake(remote_reader, remote_writer)
            if self.term == "ANSI":
                # ANSI caller: live-transcode the board's PETSCII to ANSI/CP437, and translate
                # the caller's keystrokes back to PETSCII. (A PETSCII caller gets it raw.)
                transform_out = PetsciiToAnsi().feed
                transform_in = ansi_input_to_petscii
        elif entry.charset == "CHOICE":
            # Board drives its own ANSI/PETSCII selection (C-Net 128: [INST/DEL]=Commodore,
            # [ESC]=ANSI). Watch the caller's choice: an ANSI caller who picks ANSI (ESC) gets
            # the board's native ANSI raw; one who picks Commodore ($14) gets the board's PETSCII
            # transcoded to ANSI so it actually renders. Backspace/Delete -> $14 (selection+delete).
            c128 = C128Session(self.term == "ANSI")
            transform_out = c128.out
            transform_in = c128.inp
        board_t0 = time.monotonic()
        await self._bridge_streams(remote_reader, remote_writer, strip_iac=False,
                                   transform_out=transform_out, transform_in=transform_in)
        board_dur = time.monotonic() - board_t0

        try:
            remote_writer.close()
            await remote_writer.wait_closed()
        except Exception:
            pass

        logging.info(
            "Caller %s:%s disconnected from %s (%.0fs)",
            self.client_ip,
            self.client_port,
            entry.name,
            board_dur,
        )

        # Bounce detector: an IP that reaches a board but leaves in [bounce_min, bounce_seconds]
        # — long enough to hit the login, too short to have logged in — is the scanner signature.
        # Enough such bounces in the window gets it banned (allowlisted callers are exempt).
        if (self.cfg.bounce_detect and not self.is_inbound_ssh
                and self.cfg.bounce_min <= board_dur <= self.cfg.bounce_seconds):
            cfg_dir = os.path.dirname(os.path.abspath(self.cfg_path))
            if await GLOBAL_SECURITY.register_bounce(self.client_ip, self.cfg, cfg_dir):
                logging.warning(
                    "[BOUNCE GATE] Banned login-bouncing scanner from %s "
                    "(%d bounces in <%ds; last %.0fs on %s)",
                    self.client_ip, self.cfg.bounce_limit, self.cfg.bounce_window, board_dur, entry.name,
                )

    # Signatures of automated non-terminal probes that hammer port 23 (bots/scanners).
    _PROBE_SIGNATURES = (
        b"GET ", b"POST ", b"HEAD ", b"PUT ", b"DELETE ", b"OPTIONS ", b"CONNECT ",
        b"HTTP/", b"SSH-", b"\x16\x03", b"\x80", b"\x04\x01", b"\x05\x01",
        b"<?XML", b"<NTP", b"\x00\x00\x00", b"\x1b\x1b",
    )

    def _is_allowlisted(self) -> bool:
        """True if this caller's IP is on the allowlist (sysop / LAN / loopback)."""
        try:
            cfg_dir = os.path.dirname(os.path.abspath(self.cfg_path))
            return GLOBAL_SECURITY._match_ip_in_entries(
                self.client_ip,
                GLOBAL_SECURITY.load_ip_list_file(self.cfg.allowlist_file, self.cfg, cfg_dir),
            )
        except Exception:
            return False

    async def _render_botcheck(self, code: str, attempt: int, attempts: int) -> None:
        """Draw the 'type these characters' CAPTCHA box. Mirrors DH3:CNet/SysText/sys.botcheck,
        kept <=39 columns so it renders on 40-column Commodore terminals too. Colour via Mystic
        pipe codes (|NN); NO literal '|' is used (that is the pipe-code prefix). send_ansi strips
        the colour + converts to PETSCII for Commodore callers automatically."""
        # Per-terminal clear/home (send_ansi strips raw ESC for PETSCII, so clear explicitly).
        if self.term == "PETSCII":
            await self.send_raw(b"\x93")                       # PETSCII clear
        else:
            await self.send_raw(b"\x1b[0m\x1b[2J\x1b[1;1H")    # ANSI clear+home
        W = 40

        def cen(colored: str) -> str:
            # centre within W columns on the VISIBLE text (strip |NN pipe-colour codes to measure)
            vis = re.sub(r"\|\d\d", "", colored)
            return " " * max(0, (W - len(vis)) // 2) + colored

        bpad = " " * max(0, (W - 32) // 2)   # the box is 32 columns wide, centred
        lines = []
        if attempt:
            lines.append(cen("|12(wrong - try again)"))
        lines += [
            bpad + "|04.------------------------------.",
            bpad + "|04: |15Reign of Fire BBS's  CAPTCHA|04 :",
            bpad + "|04:------------------------------'",
            bpad + "|04`----------------------> |15" + code,
            bpad + "|07 Enter those characters: ",
        ]
        await self.send_ansi("\r\n".join(lines))

    async def _botcheck_welcome(self) -> None:
        """Shown AFTER a correct answer: the Reign of Fire branding, held ~3s (the old
        sys.botcheck \\w3 pause) before run() clears to the menu. Rendered BELOW the challenge
        (no clear) so it reads as a continuation, like the C-Net original."""
        W = 40

        def cen(colored: str) -> str:
            vis = re.sub(r"\|\d\d", "", colored)
            return " " * max(0, (W - len(vis)) // 2) + colored

        lines = [
            "",
            cen("|08Reign of Fire BBS Group (C)1990-2026"),
            "",
            cen("|08Telnet: call.rofbbs.com"),
            cen("|08WEB: https://www.rofbbs.com"),
        ]
        await self.send_ansi("\r\n".join(lines))

    async def _botcheck(self) -> bool:
        """Human CAPTCHA shown BEFORE the menu: the caller must type a short random code.
        Stops menu-scraping bots that pass the terminal gate but never interact. Allowlisted
        IPs (sysop/LAN) are exempt. On failure the caller is dropped and ban-logged so the
        `rofgate` fail2ban jail escalates it to a firewall ban."""
        if self.cfg.botcheck_exempt_allowlist and self._is_allowlisted():
            return True
        alphabet = "ABCDEFGHJKMNPQRSTUVWXYZ23456789"   # no 0/O/1/I/L ambiguity
        n = max(3, min(self.cfg.botcheck_len, 10))
        attempts = max(1, self.cfg.botcheck_attempts)
        for attempt in range(attempts):
            code = "".join(random.choice(alphabet) for _ in range(n))
            await self._render_botcheck(code, attempt, attempts)
            answer = await self.prompt_line("", max_len=n + 4, timeout=self.cfg.botcheck_timeout, upper=True)
            if answer is None:
                break                                  # timeout / ESC / disconnect
            if answer.strip().upper() == code:
                await self._botcheck_welcome()
                await asyncio.sleep(3)              # old sys.botcheck \w3 pause before the menu
                return True
        logging.warning("[BOTCHECK] Failed challenge from %s", self.client_ip)
        try:
            await GLOBAL_SECURITY.add_runtime_ban(self.client_ip, self.cfg.auto_ban_duration)
        except Exception:
            pass
        try:
            await self.send_ansi("\r\n|12Verification failed. Disconnecting.|07\r\n")
        except Exception:
            pass
        return False

    async def _terminal_gate(self, early: bytes = b"") -> bool:
        """Sniff the caller's first payload. A real human terminal stays SILENT here (it is
        waiting to read the menu, which has not been sent yet), so a timeout or an
        empty/CR-only read passes. Anything that sends an actual payload before seeing the
        menu — HTTP/TLS/SSH/SOCKS probes, binary junk, or a burst of bytes — is a bot:
        it is temporarily banned and dropped. `early` is any non-IAC payload captured during
        telnet negotiation. Returns True if the connection was rejected."""
        # Allowlisted callers (sysop, localhost, LAN) are exempt from the probe gate so an
        # early keypress or a terminal's ESC auto-reply can never drop/ban a trusted caller.
        try:
            cfg_dir = os.path.dirname(os.path.abspath(self.cfg_path))
            if GLOBAL_SECURITY._match_ip_in_entries(
                self.client_ip,
                GLOBAL_SECURITY.load_ip_list_file(self.cfg.allowlist_file, self.cfg, cfg_dir),
            ):
                return False
        except Exception:
            pass
        clean = early
        if not clean:
            try:
                raw = await asyncio.wait_for(self.reader.read(256), timeout=2.0)
            except asyncio.TimeoutError:
                return False                  # silent = human reading the menu -> allow
            if not raw:
                return True                   # instant EOF (connect-scan) -> drop
            clean = self._strip_telnet_iac(raw)
        if not clean:
            return False                      # pure telnet negotiation = real terminal
        stripped = clean.strip(b"\r\n\x00 ")
        if not stripped:
            return False                      # bare CR/LF/space from a terminal -> allow
        up = stripped.upper()
        looks_bad = (
            any(up.startswith(sig) for sig in self._PROBE_SIGNATURES)
            or len(stripped) > 4                               # pre-menu burst = not a keypress
            or not all(32 <= b <= 126 for b in stripped)       # non-printable = binary probe
        )
        if looks_bad:
            await GLOBAL_SECURITY.add_runtime_ban(self.client_ip, self.cfg.auto_ban_duration)
            logging.warning(
                "[TERMINAL GATE] Banned non-terminal probe from %s: %r",
                self.client_ip, bytes(clean[:32]),
            )
            return True
        return False

    async def _choose_terminal(self, default: str) -> str:
        """Ask the caller ANSI vs Commodore and return the chosen term class. Needed because
        no telnet signal reliably distinguishes a Commodore terminal (RGTerm reports an 80-col
        'ANSI-BBS' type) from a PC ANSI terminal. Single-line plain-ASCII prompt so it's
        readable on both. Falls back to `default` on ENTER / timeout / unknown key."""
        dletter = "A" if default == "ANSI" else "C"
        prompt = f"\r\n\r\nSELECT DISPLAY -- [A]NSI (PC/80-col) or [C]OMMODORE/PETSCII (C64)? [default {dletter}] "
        await self.send_raw(prompt.encode("ascii", "replace"))
        k = await self.read_key(timeout=15)
        if k and k.upper() in ("A", "1"):
            chosen = "ANSI"
        elif k and k.upper() in ("C", "2", "P"):
            chosen = "PETSCII"
        else:
            chosen = default
        await self.send_raw((chosen + "\r\n").encode("ascii", "replace"))
        return chosen

    async def run(self) -> None:
        """Main session loop for an incoming Telnet or SSH caller."""
        proto_label = "SSH" if self.is_inbound_ssh else "Telnet"
        logging.info("Incoming %s connection from %s:%s", proto_label, self.client_ip, self.client_port)
        try:
            early, ttype, naws = await self.negotiate_telnet_char_mode()
            if (not self.is_inbound_ssh and self.cfg.security_enabled
                    and self.cfg.terminal_gate and await self._terminal_gate(early)):
                return  # non-terminal scanner/bot probe -> dropped & banned
            # Auto-detect a DEFAULT from width/TTYPE, but a Commodore terminal (RGTerm) reports
            # an 80-col "ANSI-BBS" type indistinguishable from a PC ANSI terminal, so we also
            # let the caller choose (TERMINAL_PROMPT). Width <=40 is still a useful default.
            if naws and naws <= 44:
                auto = "PETSCII"
            elif naws and naws >= 72:
                auto = "ANSI"
            else:
                auto = classify_term(ttype, self.cfg.default_term)
            if self.cfg.terminal_prompt and not self.is_inbound_ssh:
                self.term = await self._choose_terminal(auto)
            else:
                self.term = auto
            logging.info(
                "Caller %s:%s terminal=%s (auto=%s TTYPE=%s NAWS=%s)",
                self.client_ip, self.client_port, self.term, auto, ttype or "none", naws or "none",
            )
            # Human CAPTCHA before the menu (anti-bot). Renders for ANSI and 40-col PETSCII;
            # allowlisted callers are exempt; a failure drops + ban-logs the caller.
            if (not self.is_inbound_ssh and self.cfg.security_enabled
                    and self.cfg.botcheck and not await self._botcheck()):
                return
            force_lightbar = False
            await self.render_full_screen(force_lightbar=force_lightbar)

            while True:
                key = await self.read_key()
                if key is None or key == "TIMEOUT":
                    if key == "TIMEOUT":
                        await self.send_ansi(
                            "\r\n|14Idle timeout reached. Disconnecting...|07\r\n"
                        )
                    break

                entries = self.cfg.bbs_list
                upper_key = key.upper()

                if upper_key in ("Q", "ESC"):
                    await self.send_ansi(
                        f"|CL|11Thank you for visiting {self.cfg.gateway_title}! Disconnecting...|07\r\n"
                    )
                    break

                if upper_key == "L" and self.cfg.display_mode == "ANSI_HOTKEY":
                    force_lightbar = not force_lightbar
                    await self.render_full_screen(force_lightbar=force_lightbar)
                    continue

                # Lightbar navigation is ANSI-only, and only when the lightbar is the active
                # view — in ANSI_HOTKEY (custom .ans) mode, arrows must not overlay the art.
                if self.term != "PETSCII" and (force_lightbar or self.cfg.display_mode != "ANSI_HOTKEY"):
                    if key in ("UP", "LEFT") and entries:
                        self.selected_idx = (self.selected_idx - 1) % len(entries)
                        await self.render_lightbar_items()
                        continue

                    if key in ("DOWN", "RIGHT") and entries:
                        self.selected_idx = (self.selected_idx + 1) % len(entries)
                        await self.render_lightbar_items()
                        continue

                    if key == "HOME" and entries:
                        self.selected_idx = 0
                        await self.render_lightbar_items()
                        continue

                    if key == "END" and entries:
                        self.selected_idx = len(entries) - 1
                        await self.render_lightbar_items()
                        continue

                    if key == "PGUP" and entries:
                        self.selected_idx = max(0, self.selected_idx - self.cfg.menu_rows)
                        await self.render_lightbar_items()
                        continue

                    if key == "PGDN" and entries:
                        self.selected_idx = min(len(entries) - 1, self.selected_idx + self.cfg.menu_rows)
                        await self.render_lightbar_items()
                        continue

                target_entry: Optional[BBSEntry] = None
                if key == "ENTER" and entries:
                    target_entry = entries[self.selected_idx]
                else:
                    for idx, item in enumerate(entries):
                        if item.hotkey.upper() == upper_key:
                            self.selected_idx = idx
                            target_entry = item
                            break

                if target_entry is not None:
                    await self.connect_to_bbs(target_entry)
                    if not self.cfg.return_after_disconnect:
                        break
                    # Pause so the caller can read the board's logoff screen before the menu
                    # redraw clears it. (No clear here — just a prompt under the logoff.)
                    await self.send_ansi(f"{ESC}[0m\r\n|14Hit any key to return to the menu...|07")
                    if await self.read_key(timeout=self.cfg.idle_timeout) is None:
                        break   # caller disconnected
                    await self.negotiate_telnet_char_mode()
                    await self.render_full_screen(force_lightbar=force_lightbar)

        except Exception as exc:
            logging.error("Session error for %s: %s", self.client_ip, exc)
        finally:
            try:
                if self.term != "PETSCII":
                    await self.send_raw(f"{ESC}[0m".encode("ascii"))
                self.writer.close()
                await self.writer.wait_closed()
            except Exception:
                pass
            logging.info("Closed %s connection from %s:%s", proto_label, self.client_ip, self.client_port)

    async def CheckStatusAndRedraw(self, force_lightbar: bool) -> None:
        """Ping all configured BBS targets and update lightbar status column."""
        desc_y = self.cfg.menu_start_y + self.cfg.menu_rows + 1
        await self.send_ansi(
            f"{ESC}[{desc_y};10H|14Checking live status of all listed BBS nodes, please wait...        |07"
        )
        await self.check_bbs_online()
        await self.render_full_screen(force_lightbar=force_lightbar)


async def start_inbound_ssh_server(cfg: GatewayConfig, cfg_path: str, bind_host: str, ssh_port: int):
    """
    Start an optional inbound SSH listener using `asyncssh` so callers can also
    SSH directly into the gateway on `SSH_LISTEN_PORT` (default 2222).
    """
    if not HAS_ASYNCSSH:
        logging.warning(
            "SSH_ENABLED is TRUE in gateway.cfg, but 'asyncssh' is not installed. "
            "Install with 'pip install asyncssh' to enable the inbound SSH server. "
            "(Outbound SSH to BBS targets still works via the system 'ssh' client!)"
        )
        return None

    key_path = cfg.ssh_host_key
    if not os.path.isabs(key_path):
        key_path = os.path.join(os.path.dirname(os.path.abspath(cfg_path)), key_path)
    if not os.path.exists(key_path):
        logging.info("Generating new SSH host key at %s", key_path)
        priv_key = asyncssh.generate_private_key("ssh-ed25519")
        priv_key.write_private_key(key_path)

    class GatewaySSHServer(asyncssh.SSHServer):
        def begin_auth(self, username: str) -> bool:
            # Allow passwordless entry into the public BBS gateway menu
            return False

    async def _ssh_process_handler(process: "asyncssh.SSHServerProcess") -> None:
        session = TelnetSession(
            process.stdin,
            process.stdout,
            cfg_path,
            is_inbound_ssh=True,
        )
        await session.run()

    ssh_server = await asyncssh.create_server(
        GatewaySSHServer,
        bind_host,
        ssh_port,
        server_host_keys=[key_path],
        process_factory=_ssh_process_handler,
        encoding=None,
    )
    logging.info("Inbound SSH Gateway server listening on %s:%d", bind_host, ssh_port)
    return ssh_server


async def run_gateway_server(
    cfg_path: str,
    host_override: Optional[str],
    port_override: Optional[int],
    ssh_port_override: Optional[int] = None,
) -> None:
    """Start the asyncio TCP Telnet listener (and optional Inbound SSH listener)."""
    cfg = load_gateway_config(cfg_path)
    bind_host = host_override or cfg.listen_host
    bind_port = port_override or cfg.listen_port

    async def _client_connected(reader: asyncio.StreamReader, writer: asyncio.StreamWriter) -> None:
        peer = writer.get_extra_info("peername") if writer else None
        client_ip = peer[0] if peer else "unknown"
        cfg_dir = os.path.dirname(os.path.abspath(cfg_path))
        is_ok, reason = await GLOBAL_SECURITY.check_connection(client_ip, cfg, cfg_dir)
        if not is_ok:
            logging.warning("[FIREWALL REJECT] Caller %s rejected: %s", client_ip, reason)
            try:
                if reason == "DENYLIST":
                    writer.write(b"\r\n\x1b[0;1;31;40mAccess Denied: Your IP address is blocked by the gateway firewall.\x1b[0m\r\n")
                elif reason.startswith("BANNED") or reason.startswith("RATE_LIMIT"):
                    writer.write(b"\r\n\x1b[0;1;31;40mAccess Denied: Rate limit exceeded. Your IP has been temporarily banned.\x1b[0m\r\n")
                elif reason == "DUPEIP":
                    writer.write(f"\r\n\x1b[0;1;31;40mConnection Refused: Only {cfg.max_connections_per_ip} concurrent connection(s) allowed per IP.\x1b[0m\r\n".encode("ascii"))
                elif reason == "BUSY":
                    writer.write(f"\r\n\x1b[0;1;31;40mGateway Busy: Maximum caller capacity ({cfg.max_total_nodes} nodes) reached. Please try again later.\x1b[0m\r\n".encode("ascii"))
                await writer.drain()
            except Exception:
                pass
            writer.close()
            try:
                await writer.wait_closed()
            except Exception:
                pass
            return

        await GLOBAL_SECURITY.register_connect(client_ip)
        try:
            session = TelnetSession(reader, writer, cfg_path, is_inbound_ssh=False)
            await session.run()
        finally:
            await GLOBAL_SECURITY.register_disconnect(client_ip)

    try:
        server = await asyncio.start_server(_client_connected, bind_host, bind_port)
    except PermissionError:
        logging.error(
            "Permission denied binding to port %d. On Linux, run with sudo or grant "
            "capability: sudo setcap 'cap_net_bind_service=+ep' $(readlink -f $(which python3)) "
            "or test on an unprivileged port with: python3 bbs_gateway.py --port 2323",
            bind_port,
        )
        sys.exit(1)

    if cfg.ssh_enabled or ssh_port_override is not None:
        await start_inbound_ssh_server(
            cfg,
            cfg_path,
            bind_host,
            ssh_port_override or cfg.ssh_listen_port,
        )

    addrs = ", ".join(str(sock.getsockname()) for sock in (server.sockets or []))
    logging.info("%s listening on Telnet %s (config: %s)", cfg.gateway_title, addrs, cfg_path)
    async with server:
        await server.serve_forever()


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Telnet & SSH BBS Gateway Server with CP437 ANSI display and Lightbar menu."
    )
    parser.add_argument(
        "-c", "--config",
        default="gateway.cfg",
        help="Path to human-readable gateway.cfg (default: gateway.cfg)",
    )
    parser.add_argument(
        "--host",
        default=None,
        help="Override listen address from gateway.cfg (e.g., 0.0.0.0 or 127.0.0.1)",
    )
    parser.add_argument(
        "-p", "--port",
        type=int,
        default=None,
        help="Override Telnet listen port from gateway.cfg (default in config is 23)",
    )
    parser.add_argument(
        "--ssh-port",
        type=int,
        default=None,
        help="Enable and override Inbound SSH listen port (e.g. 2222, requires asyncssh)",
    )
    parser.add_argument(
        "--check-config",
        action="store_true",
        help="Validate gateway.cfg and print parsed settings and BBS listings, then exit.",
    )
    args = parser.parse_args()

    # Log to stdout (journald) AND a rotating file. fail2ban tails the file: its systemd
    # backend proved unable to read this unit's journal (0 lines delivered), so the file is
    # the reliable source for the rofgate / rofgate-flood jails.
    _log_handlers = [logging.StreamHandler()]
    try:
        _log_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "rofgate.log")
        _log_handlers.append(
            logging.handlers.RotatingFileHandler(_log_path, maxBytes=2_000_000, backupCount=3)
        )
    except Exception as _e:  # never let logging setup kill the server
        print(f"[WARN] could not open rofgate.log: {_e}")
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s [%(levelname)s] %(message)s",
        handlers=_log_handlers,
    )

    if args.check_config:
        cfg = load_gateway_config(args.config)
        print(f"Gateway Title : {cfg.gateway_title}")
        print(f"SysOp Name    : {cfg.sysop_name}")
        print(f"Telnet Socket : {cfg.listen_host}:{cfg.listen_port}")
        print(f"Inbound SSH   : {'ENABLED' if cfg.ssh_enabled else 'DISABLED'} (Port {cfg.ssh_listen_port})")
        print(f"ANSI File     : {cfg.ansi_file} (Mode: {cfg.display_mode})")
        print(f"BBS Listings  : {len(cfg.bbs_list)} configured")
        for idx, bbs in enumerate(cfg.bbs_list, 1):
            proto = "SSH" if bbs.is_ssh else "TELNET"
            print(f"  {idx}. [{bbs.hotkey}] {bbs.name:<22} -> {bbs.host}:{bbs.port} [{bbs.scope} / {proto}] - {bbs.description}")
        return

    try:
        asyncio.run(run_gateway_server(args.config, args.host, args.port, args.ssh_port))
    except KeyboardInterrupt:
        logging.info("Gateway server stopped by operator.")


if __name__ == "__main__":
    main()
