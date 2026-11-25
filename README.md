# RoFGate

**RoFGate** is a telnet front door for a group of C-Net BBSes. One listener
(e.g. `call.rofbbs.com:23`) menus callers into several boards and renders the
menu correctly for whatever terminal calls in — PC/ANSI or Commodore/PETSCII.

It began as a fork of [serverhand/BBS-Gateway](https://github.com/serverhand/BBS-Gateway)
(Python/asyncio) and adds Commodore-terminal auto-detection, a live PETSCII↔ANSI
transcoder, and a port-23 anti-scanner layer.

## Features

- **Terminal auto-detect** (telnet `TTYPE`): ANSI terminals get an **80-column
  CP437 colour lightbar** with arrow-key navigation; silent/Commodore terminals
  get a **40-column PETSCII (CBM-colour) menu**.
- **Live PETSCII→ANSI transcode** for PETSCII-only boards: the gateway answers the
  board's terminal-detect as a Commodore terminal and converts its PETSCII
  colour/graphics stream to ANSI/CP437 for ANSI callers. Native Commodore terminals
  (e.g. RGTerm) get the raw PETSCII passthrough.
- **CHOICE boards** (e.g. C-Net 128) that drive their own ANSI/PETSCII selection are
  passed through untouched, with the caller's Backspace/Delete mapped to PETSCII
  INST/DEL (`$14`) so the Commodore path is selectable.
- **Three display modes** for the ANSI menu: `LIGHTBAR` (self-contained colour
  frame), `BOTH` (your own `gateway.ans` art + a live navigable overlay), or
  `ANSI_HOTKEY` (your art + a hotkey prompt).
- **Anti-scanner defence on port 23**: a terminal gate that drops non-terminal
  probes (HTTP/TLS/SSH/binary), per-IP rate limiting, a login-bounce detector, and
  allow/deny lists. Designed to pair with fail2ban (tail `rofgate.log`).
- **Optional human CAPTCHA before the menu** (`BOTCHECK`): the caller must type a
  short random code to proceed, which stops low-and-slow menu-scraper bots that pass
  the terminal gate but never interact. Centred to 40 columns (ANSI + PETSCII), with
  allowlisted IPs exempt and failures ban-logged for fail2ban.

## Quick start

```bash
# 1. Copy the example configs to their live names (these are .gitignored)
cp gateway.cfg.example  gateway.cfg
cp allowlist.txt.example allowlist.txt
cp denylist.txt.example  denylist.txt

# 2. Edit gateway.cfg: set your title, PUBLIC_HOST, and the BBS = ... board lines
#    (hotkey | name | host | port | mode | description | [charset])

# 3. Run it (binding port 23 needs privilege or CAP_NET_BIND_SERVICE)
python3 bbs_gateway.py --config gateway.cfg
python3 bbs_gateway.py --config gateway.cfg --check-config   # validate + print parsed settings
```

Requires Python 3.9+. `asyncssh` is optional (only for SSH board targets; telnet
boards need no dependencies).

`gateway.ans` is an optional 80-column CP437 banner used by the `BOTH` /
`ANSI_HOTKEY` modes. Leading/trailing blank lines are stripped automatically, so
you can edit it freely without breaking the lightbar overlay alignment.

## Where the PETSCII translation lives — help wanted

The Commodore rendering is the most interesting part and the area most open to
improvement. If you want to help, start here:

- **`petscii_tables.py`** — the PETSCII→Unicode/CP437 glyph tables (uppercase/graphics
  and lowercase/text sets) plus the C64 colour palette used by the transcoder.
- **`PetsciiToAnsi`** (class in `bbs_gateway.py`) — the live byte-stream transcoder:
  handles charset switches (`$0E`/`$8E`), colour control codes, reverse video,
  cursor moves, and glyph fallbacks to CP437. This is the **80-column** ANSI side.
- **`render_petscii_menu()`** (in `bbs_gateway.py`) — the **40-column** CBM-colour
  menu drawn for native Commodore callers (ASCII→PETSCII case translation, CR line
  ends, CBM colour bytes).

Known rough edges / good first contributions:
- PETSCII→ANSI glyph fidelity for graphics-charset characters that have no exact
  CP437 equivalent (current behaviour falls back to the nearest glyph).
- 40-column PETSCII layout polish and colour accuracy across terminals
  (SyncTERM's C64 mode, RGTerm, CGTerm, etc.).
- Round-tripping colour/reverse-video state cleanly between the two column widths.

Issues and pull requests welcome.

## Credits & licence

- Upstream: [serverhand/BBS-Gateway](https://github.com/serverhand/BBS-Gateway).
- RoFGate additions by SpitfireTN (Reign of Fire BBS).
- MIT licence — see [LICENSE](LICENSE).
