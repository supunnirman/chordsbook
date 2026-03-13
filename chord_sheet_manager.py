"""
Chord Sheet Manager v4
======================
NEW in v4:
  - Closing "Host" window NO LONGER stops the server (server lives until Stop is clicked or app exits)
  - Web-app GUI completely redesigned: rich dark theme, live SSE push updates when song changes
  - Web-app auto-updates the moment you select a different song in the Python app (Server-Sent Events)
  - SetList songs: double-click opens SetListViewer with Prev/Next navigation + arrow key support
  - ViewerDialog: fullscreen button (⛶) — shows only chords+lyrics, Esc exits, ←→ for setlist nav
  - Font sizes, transpose, all existing features preserved

Requirements:
    pip install customtkinter flask qrcode[pil] pillow
"""

import customtkinter as ctk
import json, os, re, sys, socket, threading, subprocess, platform, time, queue, zipfile, shutil, tempfile
from datetime import datetime
from tkinter import messagebox, filedialog
import tkinter as tk
import tkinter.ttk as ttk
import html as _html

try:
    from PIL import Image, ImageTk
    PIL_OK = True
except ImportError:
    PIL_OK = False

try:
    from reportlab.lib.pagesizes import A4, letter
    from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
    from reportlab.lib.units import cm
    from reportlab.lib import colors as rl_colors
    from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, HRFlowable
    REPORTLAB_OK = True
except ImportError:
    REPORTLAB_OK = False

# ── App root ──────────────────────────────────────────────────────────────────
APP_DIR      = os.path.dirname(os.path.abspath(__file__))
CHORDS_DIR   = os.path.join(APP_DIR, "chords")
SETLISTS_DIR = os.path.join(APP_DIR, "setlists")
RECYCLE_DIR  = os.path.join(APP_DIR, "recycle_bin")
SETTINGS_JSON    = os.path.join(APP_DIR, "settings.json")
CATEGORIES_JSON  = os.path.join(APP_DIR, "categories.json")
ARTISTS_JSON     = os.path.join(APP_DIR, "artists.json")
for _d in (CHORDS_DIR, SETLISTS_DIR, RECYCLE_DIR):
    os.makedirs(_d, exist_ok=True)

CREATOR_NAME = "Supun Nirman Karunarathne"
APP_VERSION  = "v9"

ctk.set_appearance_mode("dark")
ctk.set_default_color_theme("blue")

# ── Settings (JSON) ───────────────────────────────────────────────────────────
DEFAULT_SETTINGS = {
    "chord_font_size":       "13",
    "lyric_font_size":       "13",
    "flask_port":            "5055",
    "show_clock":            "0",
    "show_timer":            "0",
    "chord_color":           "#e0f2ff",
    "section_color":         "#38bdf8",
    "lyric_color":           "#94a3b8",
    "chord_highlight_color": "#1e3a5f",   # bg highlight on individual chords
    "appearance":            "dark",
}

def load_settings():
    s = dict(DEFAULT_SETTINGS)
    if os.path.exists(SETTINGS_JSON):
        try:
            with open(SETTINGS_JSON,"r",encoding="utf-8") as f:
                data = json.load(f)
            s.update({k:str(v) for k,v in data.items()})
        except Exception: pass
    return s

def save_settings(s):
    with open(SETTINGS_JSON,"w",encoding="utf-8") as f:
        json.dump(s, f, indent=2, ensure_ascii=False)

# Apply saved appearance mode on startup (must be after load_settings is defined)
ctk.set_appearance_mode(load_settings().get("appearance", "dark"))

# ── Artists (JSON) ────────────────────────────────────────────────────────────
UNKNOWN_ARTIST = "UNKNOWN ARTIST"

def load_artists():
    if os.path.exists(ARTISTS_JSON):
        try:
            with open(ARTISTS_JSON,"r",encoding="utf-8") as f: return json.load(f)
        except Exception: pass
    return []

def save_artists(lst):
    with open(ARTISTS_JSON,"w",encoding="utf-8") as f: json.dump(lst,f,indent=2,ensure_ascii=False)

# ── Window centering helper ───────────────────────────────────────────────────
def center_window(win, w, h):
    """Center a Toplevel or Tk window on screen."""
    win.update_idletasks()
    sw = win.winfo_screenwidth()
    sh = win.winfo_screenheight()
    x  = max(0, (sw - w) // 2)
    y  = max(0, (sh - h) // 2)
    win.geometry(f"{w}x{h}+{x}+{y}")

# ── Music constants ───────────────────────────────────────────────────────────
CHROMATIC_SHARP=["C","C#","D","Eb","E","F","F#","G","Ab","A","Bb","B"]
CHROMATIC_FLAT =["C","Db","D","Eb","E","F","Gb","G","Ab","A","Bb","B"]
KEYS   =["C","C#","Db","D","Eb","E","F","F#","Gb","G","Ab","A","Bb","B"]
TUNINGS=["Standard (EADGBe)","Drop D","Open G","Open D","DADGAD","Half Step Down","Full Step Down","Other"]
FONT_SIZES=["10","11","12","13","14","15","16","17","18","19","20","22","24","26","28","30","32","35"]
CHORD_TOKEN=re.compile(r'([A-G][#b]?(?:maj7?|min7?|m7?|M7?|dim7?|aug|sus[24]?|add\d+|6|7|9|11|13)?(?:/[A-G][#b]?)?)\b')

# ── Transpose ─────────────────────────────────────────────────────────────────
def _note_index(note):
    if note in CHROMATIC_SHARP: return CHROMATIC_SHARP.index(note)
    if note in CHROMATIC_FLAT:  return CHROMATIC_FLAT.index(note)
    return -1

def transpose_chord(chord,semitones,use_flats=False):
    m=re.match(r'^([A-G][#b]?)(.*)',chord)
    if not m: return chord
    root,suffix=m.group(1),m.group(2); idx=_note_index(root)
    if idx==-1: return chord
    scale=CHROMATIC_FLAT if use_flats else CHROMATIC_SHARP
    slash_suffix=""
    if "/" in suffix:
        parts=suffix.split("/",1); suffix=parts[0]; bi=_note_index(parts[1])
        slash_suffix="/"+(scale[(bi+semitones)%12] if bi!=-1 else parts[1])
    return scale[(idx+semitones)%12]+suffix+slash_suffix

def transpose_chord_line(line,semitones,use_flats=False):
    rest,result,pos=line[1:],"#",0
    for m in CHORD_TOKEN.finditer(rest):
        result+=rest[pos:m.start()]+transpose_chord(m.group(1),semitones,use_flats); pos=m.end()
    return result+rest[pos:]

def transpose_body(body,semitones,use_flats=False):
    return "\n".join(transpose_chord_line(ln,semitones,use_flats) if ln.startswith("#") else ln for ln in body.split("\n"))

# ── File I/O ──────────────────────────────────────────────────────────────────
def _sheet_path(sid): return os.path.join(CHORDS_DIR,  f"{sid}.json")
def _sl_path(sid):    return os.path.join(SETLISTS_DIR,f"{sid}.json")

def load_all_sheets():
    out=[]
    for fn in os.listdir(CHORDS_DIR):
        if fn.endswith(".json"):
            try:
                with open(os.path.join(CHORDS_DIR,fn),encoding="utf-8") as f: out.append(json.load(f))
            except Exception: pass
    return out

def save_sheet(s):
    with open(_sheet_path(s["id"]),"w",encoding="utf-8") as f: json.dump(s,f,indent=2,ensure_ascii=False)

def delete_sheet_file(sid):
    """Move sheet JSON to recycle bin instead of permanent delete."""
    p = _sheet_path(sid)
    if not os.path.exists(p): return
    # Load to get title for naming in recycle bin
    try:
        with open(p, "r", encoding="utf-8") as f: data = json.load(f)
        title = data.get("title","untitled")[:40].replace("/","_").replace("\\","_")
    except Exception: title = sid
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    dest = os.path.join(RECYCLE_DIR, f"{stamp}__{sid}__{title}.json")
    shutil.move(p, dest)

def load_recycle_bin():
    """Return list of dicts {path, deleted_at, data} from recycle bin."""
    items = []
    for fn in sorted(os.listdir(RECYCLE_DIR), reverse=True):
        if not fn.endswith(".json"): continue
        fp = os.path.join(RECYCLE_DIR, fn)
        try:
            with open(fp,"r",encoding="utf-8") as f: data = json.load(f)
            # parse stamp from filename
            parts = fn.split("__", 2)
            stamp = parts[0] if len(parts)>0 else ""
            try:
                dt = datetime.strptime(stamp, "%Y%m%d_%H%M%S").strftime("%Y-%m-%d %H:%M")
            except: dt = stamp
            items.append({"path": fp, "deleted_at": dt, "data": data})
        except Exception: pass
    return items

def restore_sheet_from_recycle(item, dest_dir=None):
    """Restore a recycled sheet to CHORDS_DIR (or dest_dir) and return the restored path."""
    if dest_dir is None: dest_dir = CHORDS_DIR
    sid = item["data"].get("id","restored")
    dest = os.path.join(dest_dir, f"{sid}.json")
    shutil.copy2(item["path"], dest)
    os.remove(item["path"])
    return dest

def load_all_setlists():
    out=[]
    for fn in os.listdir(SETLISTS_DIR):
        if fn.endswith(".json"):
            try:
                with open(os.path.join(SETLISTS_DIR,fn),encoding="utf-8") as f: out.append(json.load(f))
            except Exception: pass
    return out

def save_setlist(sl):
    with open(_sl_path(sl["id"]),"w",encoding="utf-8") as f: json.dump(sl,f,indent=2,ensure_ascii=False)

def delete_setlist_file(sid):
    p=_sl_path(sid)
    if os.path.exists(p): os.remove(p)

def new_id(): return datetime.now().strftime("%Y%m%d%H%M%S%f")

# ── Library ZIP export / import ───────────────────────────────────────────────
def export_library_zip(path):
    """Pack chords/, setlists/, categories.json, artists.json into a zip."""
    with zipfile.ZipFile(path,"w",zipfile.ZIP_DEFLATED) as z:
        for fn in os.listdir(CHORDS_DIR):
            if fn.endswith(".json"):
                z.write(os.path.join(CHORDS_DIR,fn), f"chords/{fn}")
        for fn in os.listdir(SETLISTS_DIR):
            if fn.endswith(".json"):
                z.write(os.path.join(SETLISTS_DIR,fn), f"setlists/{fn}")
        for jf,name in [(CATEGORIES_JSON,"categories.json"),(ARTISTS_JSON,"artists.json"),
                        (SETTINGS_JSON,"settings.json")]:
            if os.path.exists(jf): z.write(jf, name)
    return True

def import_library_zip(path):
    """Extract a library zip over current data (overwrite). Returns (sheets, setlists, cats, artists)."""
    with zipfile.ZipFile(path,"r") as z:
        for member in z.namelist():
            if member.startswith("chords/") and member.endswith(".json"):
                z.extract(member, APP_DIR)
            elif member.startswith("setlists/") and member.endswith(".json"):
                z.extract(member, APP_DIR)
            elif member == "categories.json":
                z.extract(member, APP_DIR)
            elif member == "artists.json":
                z.extract(member, APP_DIR)
    return (load_all_sheets(), load_all_setlists(), load_categories(), load_artists())

# ── Categories ────────────────────────────────────────────────────────────────
# Structure: list of {"id":..., "name":..., "sheet_ids":[...], "children":[{sub-cat...}]}
# "Uncategorized" is virtual — sheets with no category anywhere go there.

def load_categories():
    if os.path.exists(CATEGORIES_JSON):
        try:
            with open(CATEGORIES_JSON,"r",encoding="utf-8") as f: return json.load(f)
        except Exception: pass
    return []

def save_categories(cats):
    with open(CATEGORIES_JSON,"w",encoding="utf-8") as f: json.dump(cats,f,indent=2,ensure_ascii=False)

def _all_cat_sheet_ids(cats):
    """Return set of all sheet IDs assigned anywhere in category tree."""
    ids = set()
    def _walk(lst):
        for c in lst:
            ids.update(c.get("sheet_ids",[]))
            _walk(c.get("children",[]))
    _walk(cats)
    return ids

def _find_cat_by_id(cats, cid):
    """Recursively find a category dict by id."""
    for c in cats:
        if c["id"] == cid: return c
        found = _find_cat_by_id(c.get("children",[]), cid)
        if found: return found
    return None

def _remove_cat_by_id(cats, cid):
    """Recursively remove a category by id, returning (removed_cat_or_None, modified_list)."""
    for i,c in enumerate(cats):
        if c["id"] == cid: return cats.pop(i)
        removed = _remove_cat_by_id(c.get("children",[]), cid)
        if removed: return removed
    return None

def _remove_sheet_from_all_cats(cats, sid):
    """Remove a sheet id from every category in the tree."""
    changed = False
    for c in cats:
        if sid in c.get("sheet_ids",[]):
            c["sheet_ids"].remove(sid); changed = True
        if _remove_sheet_from_all_cats(c.get("children",[]), sid): changed = True
    return changed

def open_folder(path):
    try:
        if platform.system()=="Windows":  subprocess.Popen(["explorer",path])
        elif platform.system()=="Darwin": subprocess.Popen(["open",path])
        else:                             subprocess.Popen(["xdg-open",path])
    except Exception as e: messagebox.showerror("Error",f"Cannot open folder:\n{e}")

# ── Chord suggestions / autocomplete ─────────────────────────────────────────
# All common chords for autocomplete dropdown in ChordGridPanel edit mode
COMMON_CHORDS = [
    "C","Cm","C7","Cmaj7","Cm7","Cdim","Caug","Csus2","Csus4","C9","C6","Cadd9",
    "C#","C#m","C#7","C#maj7","C#m7",
    "Db","Dbm","Db7","Dbmaj7",
    "D","Dm","D7","Dmaj7","Dm7","Ddim","Daug","Dsus2","Dsus4","D9","D6","Dadd9",
    "Eb","Ebm","Eb7",
    "Eb","Ebm","Eb7","Ebmaj7","Ebm7",
    "E","Em","E7","Emaj7","Em7","Edim","Eaug","Esus2","Esus4","E9","Eadd9",
    "F","Fm","F7","Fmaj7","Fm7","Fdim","Faug","Fsus2","Fsus4","F9","Fadd9",
    "F#","F#m","F#7","F#maj7","F#m7","F#dim",
    "Gb","Gbm","Gb7","Gbmaj7",
    "G","Gm","G7","Gmaj7","Gm7","Gdim","Gaug","Gsus2","Gsus4","G9","G6","Gadd9",
    "Ab","Abm","Ab7",
    "Ab","Abm","Ab7","Abmaj7","Abm7",
    "A","Am","A7","Amaj7","Am7","Adim","Aaug","Asus2","Asus4","A9","A6","Aadd9",
    "Bb","Bbm","Bb7",
    "Bb","Bbm","Bb7","Bbmaj7","Bbm7","Bbsus4",
    "B","Bm","B7","Bmaj7","Bm7","Bdim","Baug","Bsus4",
    # Slash chords
    "G/B","C/E","D/F#","A/C#","E/G#","F/A","Am/G","Dm/F","G/D","C/G",
]

# ── Chord family colour-coding by function ────────────────────────────────────
# Default colours — overridden by Settings → Chord Cell Colors
CHORD_ROLE_COLORS_DEFAULT = {
    "tonic":      "#1e4d2b",
    "subdominant":"#2a2a10",
    "dominant":   "#3a1a0a",
    "other":      "#0f1a2e",
}
CHORD_ROLE_FG_DEFAULT = {
    "tonic":      "#4ade80",
    "subdominant":"#fbbf24",
    "dominant":   "#f87171",
    "other":      "#e0f2ff",
}

# Keep module-level dicts that ChordGridPanel reads —
# updated by apply_chord_cell_colors() whenever settings change
CHORD_ROLE_COLORS = dict(CHORD_ROLE_COLORS_DEFAULT)
CHORD_ROLE_FG     = dict(CHORD_ROLE_FG_DEFAULT)

def apply_chord_cell_colors(settings):
    """Push saved cell colors from settings into the global dicts."""
    cc = settings.get("chord_cell_colors", {})
    fg = settings.get("chord_cell_fg", {})
    if not isinstance(cc, dict): cc = {}
    if not isinstance(fg, dict): fg = {}
    for role in CHORD_ROLE_COLORS_DEFAULT:
        CHORD_ROLE_COLORS[role] = cc.get(role, CHORD_ROLE_COLORS_DEFAULT[role])
        CHORD_ROLE_FG[role]     = fg.get(role, CHORD_ROLE_FG_DEFAULT[role])

# Scale degrees for major key: [I, II, III, IV, V, VI, VII]
MAJOR_SCALE_STEPS = [0, 2, 4, 5, 7, 9, 11]

def get_chord_role(chord_str, key_str):
    """Return 'tonic'|'subdominant'|'dominant'|'other' for chord in key."""
    if not chord_str or not key_str: return "other"
    m = re.match(r'^([A-G][#b]?)', chord_str)
    if not m: return "other"
    root = m.group(1)
    ki = _note_index(key_str); ri = _note_index(root)
    if ki == -1 or ri == -1: return "other"
    interval = (ri - ki) % 12
    quality = chord_str[len(root):].lower()
    is_minor = quality.startswith("m") and not quality.startswith("maj")
    steps = MAJOR_SCALE_STEPS
    if interval == steps[0]:   return "tonic"        # I
    if interval == steps[2]:   return "tonic"        # iii (relative)
    if interval == steps[5]:   return "tonic"        # vi
    if interval == steps[3]:   return "subdominant"  # IV
    if interval == steps[1]:   return "subdominant"  # ii
    if interval == steps[4]:   return "dominant"     # V
    if interval == steps[6]:   return "dominant"     # vii°
    return "other"

# ── Setlist PDF export ────────────────────────────────────────────────────────
def export_setlist_pdf(sl, sheet_map, path):
    """Export a setlist as a printable PDF. Requires reportlab."""
    if not REPORTLAB_OK:
        raise RuntimeError("reportlab not installed.\nRun: pip install reportlab")

    doc = SimpleDocTemplate(path, pagesize=A4,
          leftMargin=2*cm, rightMargin=2*cm, topMargin=2*cm, bottomMargin=2*cm)
    styles = getSampleStyleSheet()

    # Custom styles
    title_style = ParagraphStyle("sl_title", parent=styles["Title"],
        fontSize=22, spaceAfter=4, textColor=rl_colors.HexColor("#1a1a3e"))
    sub_style = ParagraphStyle("sl_sub", parent=styles["Normal"],
        fontSize=10, textColor=rl_colors.HexColor("#555555"), spaceAfter=12)
    song_title_style = ParagraphStyle("song_title", parent=styles["Normal"],
        fontSize=13, fontName="Helvetica-Bold", textColor=rl_colors.HexColor("#1a1a5f"),
        spaceBefore=2, spaceAfter=1)
    song_meta_style = ParagraphStyle("song_meta", parent=styles["Normal"],
        fontSize=9, textColor=rl_colors.HexColor("#666666"), spaceAfter=2)
    break_style = ParagraphStyle("break_row", parent=styles["Normal"],
        fontSize=10, textColor=rl_colors.HexColor("#888888"),
        fontName="Helvetica-Oblique", spaceBefore=4, spaceAfter=4)

    story = []
    story.append(Paragraph(sl.get("name","Setlist"), title_style))
    meta_parts = []
    if sl.get("date"):   meta_parts.append(sl["date"])
    if sl.get("venue"):  meta_parts.append(sl["venue"])
    if sl.get("notes"):  meta_parts.append(sl["notes"])
    if meta_parts:
        story.append(Paragraph("  ·  ".join(meta_parts), sub_style))
    story.append(HRFlowable(width="100%", thickness=1, color=rl_colors.HexColor("#ccccdd"),
                             spaceAfter=10))

    sheet_ids = sl.get("sheet_ids", [])
    for pos, sid in enumerate(sheet_ids, 1):
        if sid == "__break__":
            break_label = sl.get("break_labels", {}).get(str(pos), "Break")
            story.append(Paragraph(f"— {break_label} —", break_style))
            story.append(HRFlowable(width="60%", thickness=0.5,
                color=rl_colors.HexColor("#cccccc"), spaceAfter=4))
            continue
        s = sheet_map.get(sid)
        if not s:
            story.append(Paragraph(f"{pos:02d}.  [Missing song]", song_meta_style))
            continue
        num_txt = f"{pos:02d}."
        story.append(Paragraph(f"{num_txt}  {s['title']}", song_title_style))
        meta = []
        if s.get("artist"): meta.append(s["artist"])
        if s.get("key"):    meta.append(f"Key: {s['key']}")
        if s.get("bpm"):    meta.append(f"BPM: {s['bpm']}")
        if s.get("capo") and int(s.get("capo",0)) > 0:
            meta.append(f"Capo {s['capo']}")
        if meta:
            story.append(Paragraph("  ·  ".join(meta), song_meta_style))
        story.append(HRFlowable(width="100%", thickness=0.3,
            color=rl_colors.HexColor("#e0e0ee"), spaceAfter=4))

    doc.build(story)



# ── Song PDF export ───────────────────────────────────────────────────────────
def export_song_pdf(s, path, chord_grid=None):
    """
    Export a song as a printer-friendly PDF.
    When chord_grid provided, renders as right-side column using a simple Table.
    """
    if not REPORTLAB_OK:
        raise RuntimeError("reportlab not installed.\nRun: pip install reportlab")

    from reportlab.lib.enums import TA_CENTER, TA_LEFT

    if chord_grid is None:
        chord_grid = []

    PAGE_W, PAGE_H = A4
    MARGIN    = 1.8 * cm
    CONTENT_W = PAGE_W - 2 * MARGIN
    HAS_GRID  = bool(chord_grid)

    BODY_W = CONTENT_W * 0.62 if HAS_GRID else CONTENT_W
    GAP_W  = 0.3 * cm          if HAS_GRID else 0
    GRID_W = CONTENT_W - BODY_W - GAP_W if HAS_GRID else 0

    doc = SimpleDocTemplate(
        path, pagesize=A4,
        leftMargin=MARGIN, rightMargin=MARGIN,
        topMargin=2.6*cm, bottomMargin=2.2*cm,
        allowSplitting=1,
    )

    title_s   = ParagraphStyle("p_title",   fontSize=20, fontName="Helvetica-Bold",
        textColor=rl_colors.HexColor("#1a2a6c"), spaceAfter=1, leading=24)
    artist_s  = ParagraphStyle("p_artist",  fontSize=10, fontName="Helvetica-Oblique",
        textColor=rl_colors.HexColor("#3a3a66"), spaceAfter=2)
    meta_s    = ParagraphStyle("p_meta",    fontSize=9,  fontName="Helvetica",
        textColor=rl_colors.HexColor("#445"))
    section_s = ParagraphStyle("p_sec",     fontSize=10, fontName="Helvetica-Bold",
        textColor=rl_colors.HexColor("#1a5a9a"), spaceBefore=6, spaceAfter=1, leading=13)
    chord_s   = ParagraphStyle("p_chord",   fontSize=9,  fontName="Courier-Bold",
        textColor=rl_colors.HexColor("#1a4a8a"), backColor=rl_colors.HexColor("#e8f2ff"),
        spaceBefore=1, spaceAfter=0, leading=13, leftIndent=2, rightIndent=2)
    lyric_s   = ParagraphStyle("p_lyric",   fontSize=9,  fontName="Courier",
        textColor=rl_colors.HexColor("#222244"), spaceBefore=0, spaceAfter=2, leading=13)
    notes_s   = ParagraphStyle("p_notes",   fontSize=8,  fontName="Helvetica-Oblique",
        textColor=rl_colors.HexColor("#555"), spaceBefore=3, spaceAfter=2, leading=11)
    g_hdr_s   = ParagraphStyle("g_hdr",     fontSize=8,  fontName="Helvetica-Bold",
        textColor=rl_colors.HexColor("#ffffff"), alignment=TA_CENTER, leading=10)
    g_sec_s   = ParagraphStyle("g_sec",     fontSize=7,  fontName="Helvetica-Bold",
        textColor=rl_colors.HexColor("#60a5fa"), alignment=TA_LEFT, leading=10)

    key = s.get("key","")

    def make_body_items(width):
        items = []
        items.append(Paragraph(s.get("title","Untitled"), title_s))
        artist = (s.get("artist","") or "").strip()
        if artist and artist != "UNKNOWN ARTIST":
            items.append(Paragraph(artist, artist_s))
        items.append(HRFlowable(width="100%", thickness=1.5,
            color=rl_colors.HexColor("#1a2a6c"), spaceAfter=3, spaceBefore=1))
        # Metadata: Key, BPM, Capo
        meta_parts = []
        if s.get("key"):  meta_parts.append(f"<b>Key:</b> {s['key']}")
        if s.get("bpm"):  meta_parts.append(f"<b>BPM:</b> {s['bpm']}")
        if s.get("capo") and int(s.get("capo",0)) > 0:
            meta_parts.append(f"<b>Capo:</b> {s['capo']}")
        if meta_parts:
            n  = len(meta_parts)
            cw = width / n
            t  = Table([[Paragraph(m, meta_s) for m in meta_parts]], colWidths=[cw]*n)
            t.setStyle(TableStyle([
                ("BACKGROUND",(0,0),(-1,-1), rl_colors.HexColor("#eef2ff")),
                ("BOX",(0,0),(-1,-1), 0.4, rl_colors.HexColor("#b0b8e0")),
                ("INNERGRID",(0,0),(-1,-1), 0.2, rl_colors.HexColor("#c8d0f0")),
                ("TOPPADDING",(0,0),(-1,-1), 4),("BOTTOMPADDING",(0,0),(-1,-1), 4),
                ("LEFTPADDING",(0,0),(-1,-1), 6),
            ]))
            items.append(t)
        if s.get("notes","").strip():
            items.append(Paragraph(f"<b>Remarks:</b> {s['notes'].strip()}", notes_s))
        items.append(HRFlowable(width="100%", thickness=0.4,
            color=rl_colors.HexColor("#c0c8e8"), spaceAfter=4, spaceBefore=3))
        for line in s.get("body","").split("\n"):
            stripped = line.lstrip()
            if re.match(r"^\s*\[.+\]", line):
                items.append(Paragraph(line.strip(), section_s))
            elif stripped.startswith("#"):
                cl = stripped[1:].strip()
                if cl: items.append(Paragraph(cl, chord_s))
            elif stripped == "":
                items.append(Spacer(1, 3))
            else:
                items.append(Paragraph(line.strip() or "&nbsp;", lyric_s))
        return items

    # ── PDF chord grid — light-theme colors (readable on white paper) ─────────
    PDF_ROLE_BG = {
        "tonic":       rl_colors.HexColor("#d4f5e2"),   # light green
        "subdominant": rl_colors.HexColor("#fef9c3"),   # light amber
        "dominant":    rl_colors.HexColor("#fee2e2"),   # light red
        "other":       rl_colors.HexColor("#e8f0ff"),   # light blue
    }
    PDF_ROLE_FG = {
        "tonic":       "#166534",
        "subdominant": "#854d0e",
        "dominant":    "#991b1b",
        "other":       "#1e3a8a",
    }
    PDF_ROLE_BORDER = {
        "tonic":       rl_colors.HexColor("#86efac"),
        "subdominant": rl_colors.HexColor("#fde047"),
        "dominant":    rl_colors.HexColor("#fca5a5"),
        "other":       rl_colors.HexColor("#93c5fd"),
    }

    from reportlab.platypus.flowables import Flowable as RLFlowable

    class DiagonalSplitCell(RLFlowable):
        """Draws two chords in a diagonally split cell for the PDF grid."""
        def __init__(self, chord1, chord2, role1, role2, width, height):
            RLFlowable.__init__(self)
            self.chord1 = chord1
            self.chord2 = chord2
            self.role1  = role1
            self.role2  = role2
            self.width  = width
            self.height = height

        def wrap(self, availW, availH):
            return self.width, self.height

        def draw(self):
            c  = self.canv
            w, h = self.width, self.height
            bg1 = PDF_ROLE_BG.get(self.role1, PDF_ROLE_BG["other"])
            bg2 = PDF_ROLE_BG.get(self.role2, PDF_ROLE_BG["other"])
            fg1 = PDF_ROLE_FG.get(self.role1, PDF_ROLE_FG["other"])
            fg2 = PDF_ROLE_FG.get(self.role2, PDF_ROLE_FG["other"])

            c.saveState()
            # ReportLab: Y=0 = bottom, Y=h = top
            # Diagonal bottom-left(0,0) → top-right(w,h)
            # Bottom-right triangle → chord1
            p = c.beginPath()
            p.moveTo(0,0); p.lineTo(w,0); p.lineTo(w,h); p.close()
            c.setFillColor(bg1); c.drawPath(p, fill=1, stroke=0)
            # Top-left triangle → chord2
            p = c.beginPath()
            p.moveTo(0,0); p.lineTo(0,h); p.lineTo(w,h); p.close()
            c.setFillColor(bg2); c.drawPath(p, fill=1, stroke=0)
            # Diagonal line
            c.setStrokeColorRGB(0.5,0.55,0.7); c.setLineWidth(0.8)
            c.line(0,0, w,h)
            # Outer border
            c.setStrokeColorRGB(0.4,0.5,0.7); c.setLineWidth(0.6)
            c.rect(0,0, w,h, fill=0, stroke=1)
            # chord1 text — bottom-right
            c.setFont("Courier-Bold", 7)
            c.setFillColor(rl_colors.HexColor(fg1))
            c.drawCentredString(w*0.70, h*0.22, self.chord1)
            # chord2 text — top-left
            c.setFillColor(rl_colors.HexColor(fg2))
            c.drawCentredString(w*0.30, h*0.72, self.chord2)
            # asterisk
            c.setFont("Helvetica",5); c.setFillColorRGB(0.5,0.5,0.65)
            c.drawString(w-6, h-7, "*")
            c.restoreState()

    def make_grid_table():
        cw4 = GRID_W / 4
        CELL_H   = 22   # fixed height for chord rows
        HDR_H    = 20   # header row height
        SEC_H    = 16   # section label row height

        tbl_rows    = []
        tbl_styles  = [
            ("LEFTPADDING",  (0,0),(-1,-1), 0),
            ("RIGHTPADDING", (0,0),(-1,-1), 0),
            ("TOPPADDING",   (0,0),(-1,-1), 0),
            ("BOTTOMPADDING",(0,0),(-1,-1), 0),
            ("BOX", (0,0),(-1,-1), 1.0, rl_colors.HexColor("#3a4a7a")),
        ]
        row_heights = []   # one entry per tbl_row

        # Header row
        tbl_rows.append([Paragraph("CHORD GRID", g_hdr_s), "", "", ""])
        row_heights.append(HDR_H)
        tbl_styles += [
            ("SPAN",          (0,0),(3,0)),
            ("BACKGROUND",    (0,0),(3,0), rl_colors.HexColor("#1a2a6c")),
            ("TOPPADDING",    (0,0),(3,0), 5),
            ("BOTTOMPADDING", (0,0),(3,0), 5),
        ]

        for row in chord_grid:
            ri = len(tbl_rows)
            if row.get("type") == "section":
                lbl = row.get("label","")
                tbl_rows.append([Paragraph(f"[ {lbl} ]", g_sec_s), "", "", ""])
                row_heights.append(SEC_H)
                tbl_styles += [
                    ("SPAN",          (0,ri),(3,ri)),
                    ("BACKGROUND",    (0,ri),(3,ri), rl_colors.HexColor("#dde8ff")),
                    ("TOPPADDING",    (0,ri),(3,ri), 3),
                    ("BOTTOMPADDING", (0,ri),(3,ri), 3),
                    ("LEFTPADDING",   (0,ri),(3,ri), 5),
                    ("BOX",           (0,ri),(3,ri), 0.5, rl_colors.HexColor("#93c5fd")),
                ]

            elif row.get("type") == "chords":
                cells = (row.get("cells") or ["","","",""])[:4]
                while len(cells) < 4: cells.append("")
                cell_items = []
                has_dual = any("*" in (ch or "") for ch in cells)
                # Zero padding for rows with dual cells so flowable fills exactly
                row_pad = 0 if has_dual else 4

                for ci, chord in enumerate(cells):
                    is_dual = chord and "*" in chord
                    if is_dual:
                        parts  = chord.split("*", 1)
                        c1, c2 = parts[0].strip(), parts[1].strip()
                        role1  = get_chord_role(c1, key) if c1 else "other"
                        role2  = get_chord_role(c2, key) if c2 else "other"
                        # Use full CELL_H since padding is 0
                        cell_items.append(
                            DiagonalSplitCell(c1, c2, role1, role2, cw4, CELL_H))
                    else:
                        role = get_chord_role(chord, key) if chord else "other"
                        fg   = PDF_ROLE_FG.get(role, "#1e3a8a")
                        cp   = ParagraphStyle(f"gc{ri}_{ci}",
                            fontSize=8, fontName="Courier-Bold",
                            textColor=rl_colors.HexColor(fg),
                            alignment=TA_CENTER, leading=11)
                        cell_items.append(
                            Paragraph(chord if chord else u"\u2014", cp))
                        tbl_styles.append(
                            ("BACKGROUND", (ci,ri),(ci,ri),
                             PDF_ROLE_BG.get(role, PDF_ROLE_BG["other"])))
                        tbl_styles.append(
                            ("BOX", (ci,ri),(ci,ri), 0.5,
                             PDF_ROLE_BORDER.get(role, rl_colors.HexColor("#93c5fd"))))

                tbl_rows.append(cell_items)
                row_heights.append(CELL_H)
                tbl_styles += [
                    ("TOPPADDING",    (0,ri),(3,ri), row_pad),
                    ("BOTTOMPADDING", (0,ri),(3,ri), row_pad),
                    ("LEFTPADDING",   (0,ri),(3,ri), 0),
                    ("RIGHTPADDING",  (0,ri),(3,ri), 0),
                    ("INNERGRID",     (0,ri),(3,ri), 0.4, rl_colors.HexColor("#aab8d8")),
                    ("VALIGN",        (0,ri),(3,ri), "MIDDLE"),
                ]

        t = Table(tbl_rows, colWidths=[cw4, cw4, cw4, cw4],
                  rowHeights=row_heights)
        t.setStyle(TableStyle(tbl_styles))
        return t

    story = []

    if HAS_GRID:
        body_items = make_body_items(BODY_W)
        g_tbl      = make_grid_table()
        # Body items each wrapped in single-cell Table rows so platypus can split them
        body_rows  = [[item] for item in body_items]
        body_tbl   = Table(body_rows, colWidths=[BODY_W], splitByRow=True)
        body_tbl.setStyle(TableStyle([
            ("LEFTPADDING",  (0,0),(-1,-1), 0),("RIGHTPADDING",(0,0),(-1,-1), 0),
            ("TOPPADDING",   (0,0),(-1,-1), 0),("BOTTOMPADDING",(0,0),(-1,-1), 1),
            ("VALIGN",       (0,0),(-1,-1), "TOP"),
        ]))
        outer = Table([[body_tbl, Spacer(GAP_W,1), g_tbl]],
                      colWidths=[BODY_W, GAP_W, GRID_W], splitByRow=True)
        outer.setStyle(TableStyle([
            ("VALIGN",       (0,0),(-1,-1), "TOP"),
            ("LEFTPADDING",  (0,0),(-1,-1), 0),("RIGHTPADDING",(0,0),(-1,-1), 0),
            ("TOPPADDING",   (0,0),(-1,-1), 0),("BOTTOMPADDING",(0,0),(-1,-1), 0),
        ]))
        story.append(outer)
    else:
        story.extend(make_body_items(CONTENT_W))

    created  = (s.get("created","")  or "")[:10]
    modified = (s.get("modified","") or "")[:10]

    def draw_page(canvas, doc):
        canvas.saveState()
        canvas.setFont("Helvetica", 50)
        canvas.setFillColorRGB(0.88, 0.90, 0.98)
        canvas.setFillAlpha(0.10)
        canvas.translate(PAGE_W/2, PAGE_H/2)
        canvas.rotate(35)
        canvas.drawCentredString(0, 0, "Chord Sheet Manager")
        canvas.restoreState()
        canvas.saveState()
        canvas.setFillColorRGB(0.92, 0.94, 1.0)
        canvas.rect(0, 0, PAGE_W, 1.3*cm, fill=1, stroke=0)
        canvas.setFont("Helvetica", 7)
        canvas.setFillColorRGB(0.4, 0.4, 0.55)
        canvas.drawString(MARGIN, 0.46*cm,
            f"Created by {CREATOR_NAME}  \u00b7  Chord Sheet Manager {APP_VERSION}")
        canvas.setFont("Helvetica-Bold", 8)
        canvas.setFillColorRGB(0.3, 0.3, 0.5)
        canvas.drawCentredString(PAGE_W/2, 0.46*cm, f"Page {doc.page}")
        canvas.setFont("Helvetica", 7)
        canvas.setFillColorRGB(0.5, 0.5, 0.6)
        dt = f"Modified: {modified}" if modified else (f"Created: {created}" if created else "")
        canvas.drawRightString(PAGE_W - MARGIN, 0.46*cm, dt)
        canvas.setFillColorRGB(0.1, 0.16, 0.42)
        canvas.rect(0, PAGE_H - 1.1*cm, PAGE_W, 1.1*cm, fill=1, stroke=0)
        canvas.setFont("Helvetica-Bold", 9)
        canvas.setFillColorRGB(1, 1, 1)
        canvas.drawString(MARGIN, PAGE_H - 0.70*cm, s.get("title",""))
        canvas.setFont("Helvetica", 8)
        canvas.setFillColorRGB(0.7, 0.8, 1.0)
        canvas.drawRightString(PAGE_W - MARGIN, PAGE_H - 0.70*cm,
            f"Chord Sheet Manager  \u00b7  {CREATOR_NAME}")
        canvas.restoreState()

    doc.build(story, onFirstPage=draw_page, onLaterPages=draw_page)


# ── Network ───────────────────────────────────────────────────────────────────
def get_private_ips():
    ips,seen=[],set()
    try:
        for item in socket.getaddrinfo(socket.gethostname(),None):
            ip=item[4][0]
            if ip not in seen and not ip.startswith("127.") and ":" not in ip:
                seen.add(ip); ips.append(ip)
    except Exception: pass
    if not ips:
        try:
            s=socket.socket(socket.AF_INET,socket.SOCK_DGRAM); s.connect(("8.8.8.8",80))
            ips=[s.getsockname()[0]]; s.close()
        except Exception: ips=["127.0.0.1"]
    return ips

# ── QR ────────────────────────────────────────────────────────────────────────
def make_qr_image(data,size=180):
    try:
        import qrcode
        qr=qrcode.QRCode(box_size=4,border=2); qr.add_data(data); qr.make(fit=True)
        img=qr.make_image(fill_color="black",back_color="white")
        if PIL_OK: img=img.resize((size,size),Image.LANCZOS)
        return img
    except Exception: return None

# ── Flask web-app ─────────────────────────────────────────────────────────────
# song_ref is a mutable dict: {"sheet": <sheet_dict_or_None>}
# SSE clients subscribe to /stream and get "data: <json>\n\n" on every change.

FLASK_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title id="page-title">Chord Sheet Manager</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Playfair+Display:wght@700;900&family=Source+Code+Pro:wght@400;600;700&family=DM+Sans:ital,wght@0,300;0,400;0,500;0,600;1,400&display=swap" rel="stylesheet">
<style>
:root{
  --bg:#07090f;--surface:#0d1117;--card:#111827;
  --border:#1e2a3e;--accent:#3b82f6;--accent2:#60a5fa;
  --chord-bg:#0a1929;--chord-fg:#e0f2ff;--chord-bdr:#1d4ed8;
  --section-fg:#38bdf8;--lyric-fg:#94a3b8;--meta:#475569;
  --white:#f1f5f9;--green:#22c55e;--amber:#f59e0b;
  --radius:10px;
  --grid-bg:#0a0d14;--grid-row:#0f1520;--grid-row-alt:#111827;--grid-sec:#1a1a2e;
  --grid-chord:#e0f2ff;--grid-sec-fg:#38bdf8;--grid-div:#1e2a4e;
}
*{box-sizing:border-box;margin:0;padding:0}
html,body{height:100%}
body{background:var(--bg);color:var(--white);font-family:'DM Sans',sans-serif;min-height:100vh;overflow-x:hidden}

body::before{content:'';position:fixed;top:-30%;left:-20%;width:70vw;height:70vw;
  background:radial-gradient(circle,rgba(29,78,216,.07) 0%,transparent 65%);pointer-events:none;z-index:0}
body::after{content:'';position:fixed;bottom:-20%;right:-15%;width:55vw;height:55vw;
  background:radial-gradient(circle,rgba(56,189,248,.05) 0%,transparent 65%);pointer-events:none;z-index:0}

/* ── Sticky header ── */
.hdr{position:sticky;top:0;z-index:200;
  background:rgba(7,9,15,.92);backdrop-filter:blur(24px);-webkit-backdrop-filter:blur(24px);
  border-bottom:1px solid var(--border)}
.hdr-inner{width:100%;margin:auto;display:flex;align-items:center;gap:10px;
  height:52px;padding:0 clamp(12px,3vw,32px)}
.hdr-icon{font-size:1.2rem;animation:hpulse 3s ease-in-out infinite;flex-shrink:0}
@keyframes hpulse{0%,100%{opacity:1}50%{opacity:.55}}
.hdr-title{font-family:'Playfair Display',serif;font-size:clamp(.9rem,2vw,1.1rem);
  font-weight:700;color:var(--white);flex:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.live-pill{display:flex;align-items:center;gap:5px;
  background:rgba(34,197,94,.1);border:1px solid rgba(34,197,94,.28);
  color:#4ade80;font-size:.63rem;font-weight:700;letter-spacing:.1em;text-transform:uppercase;
  padding:3px 9px;border-radius:99px;flex-shrink:0}
.live-dot{width:6px;height:6px;border-radius:50%;background:#4ade80;animation:blink 1.3s ease-in-out infinite}
@keyframes blink{0%,100%{opacity:1}50%{opacity:.15}}

/* Width selector + grid toggle in header */
.hdr-sel{background:var(--card);border:1px solid var(--border);color:var(--white);
  font-size:.72rem;padding:3px 8px;border-radius:7px;cursor:pointer;outline:none;
  font-family:'DM Sans',sans-serif}
.hdr-sel:hover{border-color:var(--accent)}
.grid-tog-btn{background:rgba(59,130,246,.15);border:1px solid rgba(59,130,246,.35);
  color:var(--accent2);font-size:.7rem;font-weight:700;padding:4px 11px;
  border-radius:7px;cursor:pointer;white-space:nowrap;transition:background .15s,border-color .15s}
.grid-tog-btn:hover{background:rgba(59,130,246,.28);border-color:var(--accent)}
.grid-tog-btn.on{background:rgba(59,130,246,.28);border-color:var(--accent);color:#fff}

/* transition overlay */
#transition-overlay{
  position:fixed;inset:0;z-index:500;pointer-events:none;
  background:var(--bg);opacity:0;transition:opacity .25s ease}
#transition-overlay.flash{opacity:1}

/* ── Page layout ── */
.page-wrap{
  position:relative;z-index:1;
  width:100%;
  padding:0 clamp(10px,2vw,24px) 90px;
  margin:0 auto;
}
/* two-column layout */
.cols{display:flex;gap:0;align-items:flex-start;width:100%}
.col-sheet{flex:1;min-width:0;padding:clamp(14px,2vw,30px) 16px clamp(14px,2vw,30px) 0}
.col-grid{flex-shrink:0;border-left:1px solid var(--border);
  padding:clamp(14px,2vw,30px) 0 clamp(14px,2vw,30px) 16px;
  display:none;min-width:260px}
.col-grid.visible{display:block}

/* ── Hero ── */
.hero{margin-bottom:20px;padding-bottom:20px;border-bottom:1px solid var(--border);animation:fadeUp .5s ease both}
.hero-artist{font-size:.72rem;font-weight:600;letter-spacing:.14em;text-transform:uppercase;color:var(--accent2);margin-bottom:6px}
.hero-title{font-family:'Playfair Display',serif;font-size:clamp(1.6rem,4.5vw,2.8rem);
  font-weight:900;line-height:1.05;letter-spacing:-.02em;margin-bottom:14px}
.meta-row{display:flex;flex-wrap:wrap;gap:6px}
.chip{display:inline-flex;align-items:center;gap:5px;
  background:var(--card);border:1px solid var(--border);border-radius:8px;
  padding:4px 10px;font-size:.74rem;font-weight:500;color:var(--lyric-fg);cursor:default}
.chip:hover{border-color:var(--accent);color:var(--accent2)}
.chip-v{color:var(--white);font-weight:700}

/* ── Controls bar ── */
.ctrl-bar{display:flex;align-items:center;gap:9px;flex-wrap:wrap;
  background:var(--surface);border:1px solid var(--border);border-radius:10px;
  padding:7px 12px;margin-bottom:18px;font-size:.77rem;color:var(--meta);animation:fadeUp .5s .1s ease both}
.ctrl-lbl{font-weight:600;white-space:nowrap}
.ctrl-grp{display:flex;align-items:center;gap:6px}
.cbtn{width:24px;height:24px;background:var(--card);border:1px solid var(--border);
  border-radius:5px;color:var(--white);font-size:.8rem;font-weight:700;cursor:pointer;
  display:flex;align-items:center;justify-content:center;transition:background .15s}
.cbtn:hover{background:var(--accent);border-color:var(--accent)}
.csz{min-width:24px;text-align:center;font-family:'Source Code Pro',monospace;
  font-weight:700;color:var(--white);font-size:.8rem}
.csep{width:1px;height:16px;background:var(--border);flex-shrink:0}
.print-btn{margin-left:auto;background:var(--card);border:1px solid var(--border);
  border-radius:6px;color:var(--lyric-fg);padding:3px 10px;font-size:.74rem;
  font-weight:600;cursor:pointer;transition:background .15s}
.print-btn:hover{background:var(--accent);color:#fff}
.tog-wrap{display:flex;align-items:center;gap:6px}
.tog-lbl{white-space:nowrap}
.tog{position:relative;width:36px;height:19px;cursor:pointer}
.tog input{display:none}
.tog-track{position:absolute;inset:0;background:var(--card);border:1px solid var(--border);border-radius:99px;transition:background .2s}
.tog input:checked+.tog-track{background:var(--accent);border-color:var(--accent)}
.tog-thumb{position:absolute;top:3px;left:3px;width:11px;height:11px;
  background:#fff;border-radius:50%;transition:transform .2s;box-shadow:0 1px 3px rgba(0,0,0,.3)}
.tog input:checked~.tog-thumb{transform:translateX(17px)}

/* ── Sheet body ── */
.sheet{display:flex;flex-direction:column;gap:0;animation:fadeUp .5s .2s ease both}
.line-section{font-size:.67rem;font-weight:700;letter-spacing:.18em;text-transform:uppercase;
  color:var(--section-fg);margin-top:22px;margin-bottom:3px;padding:0 3px;
  display:flex;align-items:center;gap:6px}
.line-section::before{content:'';flex:none;width:10px;height:2px;background:var(--section-fg);border-radius:2px}
.line-chord{font-family:'Source Code Pro',monospace;font-weight:700;
  background:var(--chord-bg);border-left:3px solid var(--chord-bdr);
  border-radius:0 7px 7px 0;color:var(--chord-fg);
  padding:5px 12px 5px 10px;margin:2px 0;letter-spacing:.04em;line-height:1.5;
  white-space:pre;overflow-x:auto;display:block}
.line-chord:hover{background:rgba(10,25,41,.95);border-left-color:var(--accent2)}
.ct{display:inline-block;background:rgba(59,130,246,.16);border:1px solid rgba(96,165,250,.28);
  border-radius:4px;padding:0 4px;margin:0 1px;color:#a8d4ff;font-weight:700}
.ct:hover{background:rgba(59,130,246,.32);color:#fff}
.line-lyric{font-family:'DM Sans',sans-serif;color:var(--lyric-fg);
  padding:2px 4px;line-height:1.75;white-space:pre-wrap;display:block}
.line-lyric:hover{color:var(--white)}
.line-gap{height:12px;display:block}

/* ── Notes ── */
.notes-card{margin-top:24px;background:var(--surface);border:1px solid var(--border);
  border-left:3px solid var(--amber);border-radius:0 10px 10px 0;
  padding:12px 16px;font-size:.86rem;color:#d4a017;line-height:1.6}
.notes-card strong{display:block;font-size:.64rem;letter-spacing:.12em;text-transform:uppercase;
  color:var(--amber);margin-bottom:4px}

/* ── No song placeholder ── */
.no-song{display:flex;flex-direction:column;align-items:center;justify-content:center;
  min-height:55vh;gap:14px;text-align:center}
.no-song-icon{font-size:3.5rem;opacity:.18}
.no-song-text{color:var(--meta);font-size:.95rem;font-weight:500}

/* ── Chord Grid ── */
.cg-wrap{width:100%}
.cg-title{font-size:.72rem;font-weight:700;letter-spacing:.14em;text-transform:uppercase;
  color:var(--accent2);margin-bottom:12px;display:flex;align-items:center;gap:8px}
.cg-title::before{content:'';flex:none;width:3px;height:14px;background:var(--accent2);border-radius:2px}
.cg-empty{color:var(--meta);font-size:.83rem;padding:24px 0;text-align:center;opacity:.5}
.cg-section{background:var(--grid-sec);border-radius:6px;padding:6px 12px;
  margin:10px 0 4px;font-size:.67rem;font-weight:700;letter-spacing:.15em;
  text-transform:uppercase;color:var(--grid-sec-fg);display:flex;align-items:center;gap:6px}
.cg-section::before{content:'';flex:none;width:8px;height:2px;background:var(--grid-sec-fg);border-radius:2px}
.cg-row{display:grid;grid-template-columns:repeat(4,1fr);gap:2px;margin-bottom:2px}
.cg-cell{background:var(--grid-row);border:1px solid var(--grid-div);border-radius:5px;
  padding:6px 4px;text-align:center;min-height:40px;display:flex;flex-direction:column;
  align-items:center;justify-content:center;gap:2px}
.cg-cell:hover{border-color:var(--accent);background:rgba(14,25,55,.9)}
.cg-beat{font-size:.58rem;color:var(--grid-div);font-family:'Source Code Pro',monospace;line-height:1}
.cg-chord{font-family:'Source Code Pro',monospace;font-size:clamp(.85rem,1.4vw,1.1rem);
  font-weight:700;color:var(--grid-chord);line-height:1.2}
.cg-empty-cell .cg-chord{color:var(--grid-div);font-size:.8rem}
.cg-row-idx{font-size:.6rem;color:#2a3a5e;font-family:'Source Code Pro',monospace;
  padding-right:6px;align-self:center;flex-shrink:0;display:none}

/* ── Sticky footer ── */
.ftr{position:fixed;bottom:0;left:0;right:0;z-index:200;
  background:rgba(7,9,15,.92);backdrop-filter:blur(20px);border-top:1px solid var(--border)}
.ftr-inner{width:100%;margin:auto;height:40px;
  display:flex;align-items:center;justify-content:space-between;gap:12px;
  padding:0 clamp(12px,3vw,32px)}
.ftr-brand{font-size:.66rem;color:var(--meta);font-weight:600;letter-spacing:.06em}
.ftr-key{display:flex;align-items:center;gap:6px;font-size:.67rem;color:var(--meta)}
.key-badge{background:var(--chord-bg);border:1px solid var(--chord-bdr);
  color:var(--chord-fg);font-family:'Source Code Pro',monospace;
  font-size:.7rem;font-weight:700;padding:2px 8px;border-radius:5px}

/* ── Scrollbar ── */
::-webkit-scrollbar{width:4px;height:4px}
::-webkit-scrollbar-track{background:var(--bg)}
::-webkit-scrollbar-thumb{background:var(--border);border-radius:3px}
::-webkit-scrollbar-thumb:hover{background:var(--accent)}

/* ── Animations ── */
@keyframes fadeUp{from{opacity:0;transform:translateY(12px)}to{opacity:1;transform:translateY(0)}}
.sheet>*{animation:lineIn .32s both}
.sheet>*:nth-child(1){animation-delay:.22s}.sheet>*:nth-child(2){animation-delay:.25s}
.sheet>*:nth-child(3){animation-delay:.28s}.sheet>*:nth-child(4){animation-delay:.31s}
.sheet>*:nth-child(5){animation-delay:.34s}.sheet>*:nth-child(6){animation-delay:.37s}
.sheet>*:nth-child(7){animation-delay:.40s}.sheet>*:nth-child(8){animation-delay:.43s}
.sheet>*:nth-child(9){animation-delay:.46s}.sheet>*:nth-child(10){animation-delay:.49s}
@keyframes lineIn{from{opacity:0;transform:translateX(-6px)}to{opacity:1;transform:translateX(0)}}

@media print{
  .hdr,.ftr,.ctrl-bar{display:none}
  .col-grid{break-inside:avoid}
  .page-wrap{padding:0}
}
</style>
</head>
<body>
<div id="transition-overlay"></div>

<header class="hdr">
  <div class="hdr-inner">
    <span class="hdr-icon">&#127928;</span>
    <span class="hdr-title" id="hdr-title">Chord Sheet Manager</span>
    <span class="live-pill"><span class="live-dot"></span>LIVE</span>
    <!-- Width selector -->
    <select class="hdr-sel" id="width-sel" onchange="applyWidth(this.value)" title="Page width">
      <option value="100%">Full width</option>
      <option value="1400px">1400px</option>
      <option value="1200px">1200px</option>
      <option value="1000px">1000px</option>
      <option value="800px">800px</option>
      <option value="700px">700px</option>
      <option value="600px">600px</option>
    </select>
    <!-- Grid toggle button -->
    <button class="grid-tog-btn on" id="grid-tog-btn" onclick="toggleGrid()" title="Toggle chord grid">&#9638; Grid</button>
  </div>
</header>

<div class="page-wrap" id="page-wrap">
  <div id="no-song" class="no-song">
    <div class="no-song-icon">&#127928;</div>
    <div class="no-song-text">No song selected<br>Pick a chord sheet in the app</div>
  </div>
  <div id="song-content" style="display:none">
    <div class="hero">
      <div class="hero-artist" id="hero-artist"></div>
      <h1 class="hero-title" id="hero-title"></h1>
      <div class="meta-row" id="meta-row"></div>
    </div>
    <div class="ctrl-bar">
      <span class="ctrl-lbl">Chord</span>
      <div class="ctrl-grp">
        <button class="cbtn" onclick="chSz('chord',-1)">&#8722;</button>
        <span class="csz" id="c-sz">16</span>
        <button class="cbtn" onclick="chSz('chord',1)">+</button>
      </div>
      <div class="csep"></div>
      <span class="ctrl-lbl">Lyric</span>
      <div class="ctrl-grp">
        <button class="cbtn" onclick="chSz('lyric',-1)">&#8722;</button>
        <span class="csz" id="l-sz">14</span>
        <button class="cbtn" onclick="chSz('lyric',1)">+</button>
      </div>
      <div class="csep"></div>
      <button class="print-btn" onclick="window.print()">&#128424; Print</button>
      <div class="csep"></div>
      <div class="tog-wrap">
        <span class="tog-lbl">Highlight</span>
        <label class="tog">
          <input type="checkbox" id="hl-tog" checked onchange="toggleHL(this.checked)">
          <span class="tog-track"></span><span class="tog-thumb"></span>
        </label>
      </div>
    </div>
    <!-- two-column content area -->
    <div class="cols" id="cols">
      <div class="col-sheet">
        <div class="sheet" id="sheet"></div>
        <div id="notes-area"></div>
      </div>
      <div class="col-grid visible" id="col-grid">
        <div class="cg-wrap" id="cg-wrap"></div>
      </div>
    </div>
  </div>
</div>

<footer class="ftr">
  <div class="ftr-inner">
    <span class="ftr-brand">&#127928; Chord Sheet Manager</span>
    <div class="ftr-key" id="ftr-key"></div>
  </div>
</footer>

<script>
var cSz=16, lSz=14, gridVisible=true;

/* ── Width ── */
function applyWidth(w){
  document.getElementById("page-wrap").style.maxWidth = w==="100%" ? "none" : w;
}

/* ── Grid toggle ── */
function toggleGrid(){
  gridVisible = !gridVisible;
  var col = document.getElementById("col-grid");
  var btn = document.getElementById("grid-tog-btn");
  if(gridVisible){
    col.classList.add("visible");
    btn.classList.add("on");
    btn.innerHTML = "&#9638; Grid";
  } else {
    col.classList.remove("visible");
    btn.classList.remove("on");
    btn.innerHTML = "&#9638; Grid";
  }
}

/* ── Font sizes ── */
function applyCSz(){
  document.querySelectorAll(".line-chord").forEach(function(e){e.style.fontSize=cSz+"px"});
  document.getElementById("c-sz").textContent=cSz;
}
function applyLSz(){
  document.querySelectorAll(".line-lyric").forEach(function(e){e.style.fontSize=lSz+"px"});
  document.getElementById("l-sz").textContent=lSz;
}
function chSz(t,d){
  if(t==="chord"){cSz=Math.max(8,Math.min(40,cSz+d));applyCSz()}
  else{lSz=Math.max(8,Math.min(40,lSz+d));applyLSz()}
}

/* ── Chord highlight ── */
function toggleHL(on){
  document.querySelectorAll(".ct").forEach(function(e){
    e.style.background=on?"":"transparent";
    e.style.border=on?"":"none";
    e.style.color=on?"":"inherit"
  });
  document.querySelectorAll(".line-chord").forEach(function(e){
    e.style.background=on?"":"transparent";
    e.style.borderLeft=on?"":"3px solid transparent"
  })
}

/* ── Render chord grid ── */
function renderGrid(rows){
  var wrap = document.getElementById("cg-wrap");
  wrap.innerHTML = "";
  if(!rows || rows.length===0){
    wrap.innerHTML = "<div class=\\"cg-empty\\">No chord grid data for this song</div>";
    return;
  }
  var title = document.createElement("div");
  title.className = "cg-title";
  title.textContent = "Chord Grid";
  wrap.appendChild(title);
  var rowIdx = 0;
  rows.forEach(function(r){
    if(r.type==="section"){
      var sec = document.createElement("div");
      sec.className = "cg-section";
      sec.textContent = r.label || "Section";
      wrap.appendChild(sec);
      rowIdx = 0;
    } else {
      rowIdx++;
      var row = document.createElement("div");
      row.className = "cg-row";
      var cells = r.cells || ["","","",""];
      while(cells.length < 4) cells.push("");
      cells.slice(0,4).forEach(function(ch, ci){
        var cell = document.createElement("div");
        cell.className = "cg-cell" + (ch ? "" : " cg-empty-cell");
        var beat = document.createElement("div");
        beat.className = "cg-beat";
        beat.textContent = (ci+1);
        var chord = document.createElement("div");
        chord.className = "cg-chord";
        chord.textContent = ch || "—";
        cell.appendChild(beat);
        cell.appendChild(chord);
        row.appendChild(cell);
      });
      wrap.appendChild(row);
    }
  });
}

/* ── Render sheet ── */
function renderSheet(d){
  var ov=document.getElementById("transition-overlay");
  ov.classList.add("flash");
  setTimeout(function(){
    document.getElementById("no-song").style.display="none";
    document.getElementById("song-content").style.display="block";
    document.getElementById("page-title").textContent="\u266b "+d.title;
    document.getElementById("hdr-title").textContent=d.title;
    document.getElementById("hero-artist").textContent=d.artist||"";
    document.getElementById("hero-title").textContent=d.title;
    // meta chips
    var chips=[
      {i:"&#127932;",l:"Key",v:d.key},
      {i:"&#9201;",l:"BPM",v:d.bpm},
      {i:"&#127767;",l:"Capo",v:d.capo},
      {i:"&#127928;",l:"",v:d.tuning}
    ];
    var mr=document.getElementById("meta-row"); mr.innerHTML="";
    chips.forEach(function(c){
      if(!c.v && !c.l) return;
      var s=document.createElement("span"); s.className="chip";
      s.innerHTML=(c.l ? c.i+" "+c.l+" <span class='chip-v'>"+c.v+"</span>"
                       : c.i+" <span class='chip-v'>"+c.v+"</span>");
      mr.appendChild(s);
    });
    // sheet body
    document.getElementById("sheet").innerHTML=d.body_html;
    applyCSz(); applyLSz();
    // notes
    var na=document.getElementById("notes-area");
    na.innerHTML=d.notes?"<div class='notes-card'><strong>Notes</strong>"+escH(d.notes)+"</div>":"";
    // footer
    document.getElementById("ftr-key").innerHTML=
      "Key <span class='key-badge'>"+escH(d.key)+"</span>&nbsp;"+escH(d.difficulty||"");
    // chord grid
    renderGrid(d.chord_grid||[]);
    ov.classList.remove("flash");
  },220);
}

function noSong(){
  document.getElementById("no-song").style.display="flex";
  document.getElementById("song-content").style.display="none";
  document.getElementById("page-title").textContent="Chord Sheet Manager";
  document.getElementById("hdr-title").textContent="Chord Sheet Manager";
  document.getElementById("cg-wrap").innerHTML="";
}

function escH(s){var d=document.createElement("div");d.textContent=s||"";return d.innerHTML}

// SSE live updates
var evtSrc=null;
function connect(){
  evtSrc=new EventSource("/stream");
  evtSrc.onmessage=function(e){
    var data=JSON.parse(e.data);
    if(data.type==="sheet") renderSheet(data);
    else if(data.type==="no_song") noSong();
  };
  evtSrc.onerror=function(){evtSrc.close();setTimeout(connect,3000)};
}
connect();

// Initial load
fetch("/current").then(function(r){return r.json()}).then(function(d){
  if(d.type==="sheet") renderSheet(d); else noSong();
}).catch(function(){noSong()});

// Keyboard shortcuts
document.addEventListener("keydown",function(e){
  if(e.key==="+"||e.key==="="){chSz("chord",1);chSz("lyric",1)}
  if(e.key==="-"){chSz("chord",-1);chSz("lyric",-1)}
  if(e.ctrlKey&&e.key==="p"){e.preventDefault();window.print()}
  if(e.key==="g"&&!e.ctrlKey&&!e.altKey){toggleGrid()}
});
</script>
</body>
</html>"""

CHORD_TOKEN_WEB = re.compile(
    r'\b([A-G][#b]?(?:maj7?|min7?|m7?|M7?|dim7?|aug|sus[24]?|add\d+|6|7|9|11|13)?(?:/[A-G][#b]?)?)\b'
)

def _tokenize_chord_line(raw):
    display = raw.lstrip("#").lstrip(" ") if raw.startswith("#") else raw
    result,pos="",0
    for m in CHORD_TOKEN_WEB.finditer(display):
        result += _html.escape(display[pos:m.start()])
        result += f'<span class="ct">{_html.escape(m.group(1))}</span>'
        pos = m.end()
    return result + _html.escape(display[pos:])

def _build_body_html(sheet):
    parts=[]
    for line in sheet.get("body","").split("\n"):
        stripped=line.lstrip()
        if stripped.startswith("#"):
            parts.append(f'<span class="line-chord">{_tokenize_chord_line(line)}</span>')
        elif re.match(r"^\s*\[.+\]",line):
            label=re.sub(r"^\s*\[(.+)\]\s*$",r"\1",line)
            parts.append(f'<span class="line-section">{_html.escape(label)}</span>')
        elif stripped=="":
            parts.append('<span class="line-gap"></span>')
        else:
            parts.append(f'<span class="line-lyric">{_html.escape(line)}</span>')
    return "\n".join(parts)

def _sheet_payload(sheet):
    return {
        "type":       "sheet",
        "title":      sheet.get("title",""),
        "artist":     sheet.get("artist",""),
        "key":        sheet.get("key",""),
        "bpm":        str(sheet.get("bpm","")),
        "capo":       str(sheet.get("capo",0)),
        "tuning":     sheet.get("tuning",""),
        "genre":      sheet.get("genre",""),
        "difficulty": sheet.get("difficulty",""),
        "notes":      sheet.get("notes",""),
        "body_html":  _build_body_html(sheet),
        "chord_grid": sheet.get("chord_grid",[]),
    }

# Global server state — persists across HostDialog open/close
_SERVER_STATE = {
    "thread":     None,
    "stop_event": None,
    "running":    False,
    "port":       5055,
    "song_ref":   {},      # {"sheet": <dict>}
    "sse_queues": [],      # list of queue.Queue, one per SSE client
}

def _push_sse(payload_dict):
    """Push JSON payload to all connected SSE clients."""
    msg = "data: " + json.dumps(payload_dict) + "\n\n"
    dead = []
    for q in _SERVER_STATE["sse_queues"]:
        try: q.put_nowait(msg)
        except Exception: dead.append(q)
    for q in dead:
        try: _SERVER_STATE["sse_queues"].remove(q)
        except ValueError: pass

def update_hosted_song(sheet_or_none):
    """Called from the main app whenever the selected song changes."""
    if sheet_or_none is None:
        _SERVER_STATE["song_ref"].pop("sheet", None)
        _push_sse({"type":"no_song"})
    else:
        _SERVER_STATE["song_ref"]["sheet"] = sheet_or_none
        _push_sse(_sheet_payload(sheet_or_none))

def start_flask_server(port):
    """Start Flask if not already running. Safe to call multiple times."""
    if _SERVER_STATE["running"]: return True
    try: from flask import Flask, Response, stream_with_context, jsonify
    except ImportError: return False

    stop_event = threading.Event()
    flask_app   = Flask(__name__)
    flask_app.config["PROPAGATE_EXCEPTIONS"] = False

    @flask_app.route("/")
    def index():
        from flask import Response
        return Response(FLASK_HTML.encode("utf-8","replace"),
                        200, {"Content-Type":"text/html; charset=utf-8"})

    @flask_app.route("/current")
    def current():
        sheet = _SERVER_STATE["song_ref"].get("sheet")
        if sheet: return jsonify(_sheet_payload(sheet))
        return jsonify({"type":"no_song"})

    @flask_app.route("/stream")
    def stream():
        q = queue.Queue(maxsize=30)
        _SERVER_STATE["sse_queues"].append(q)
        def gen():
            try:
                yield ": connected\n\n"
                # send current song immediately on connect
                sheet = _SERVER_STATE["song_ref"].get("sheet")
                if sheet:
                    yield "data: " + json.dumps(_sheet_payload(sheet)) + "\n\n"
                else:
                    yield "data: " + json.dumps({"type":"no_song"}) + "\n\n"
                while not stop_event.is_set():
                    try:
                        msg = q.get(timeout=15)
                        yield msg
                    except Exception:
                        yield ": keepalive\n\n"
            finally:
                try: _SERVER_STATE["sse_queues"].remove(q)
                except ValueError: pass
        return Response(stream_with_context(gen()),
                        mimetype="text/event-stream",
                        headers={"Cache-Control":"no-cache","X-Accel-Buffering":"no",
                                 "Connection":"keep-alive"})

    import logging
    logging.getLogger("werkzeug").setLevel(logging.ERROR)

    def run():
        try:
            flask_app.run(host="0.0.0.0", port=port, threaded=True,
                          use_reloader=False, debug=False)
        except Exception:
            pass

    t = threading.Thread(target=run, daemon=True); t.start()
    _SERVER_STATE.update(thread=t, stop_event=stop_event, running=True, port=port)
    return True

def stop_flask_server():
    if _SERVER_STATE["stop_event"]: _SERVER_STATE["stop_event"].set()
    _SERVER_STATE.update(thread=None, stop_event=None, running=False)

# ── Desktop renderer ──────────────────────────────────────────────────────────
def render_body(tb, body, chord_size=13, lyric_size=13,
                chord_color="#e0f2ff", section_color="#38bdf8", lyric_color="#94a3b8",
                chord_highlight="#1e3a5f"):
    tb.configure(state="normal"); tb.delete("0.0","end"); inner=tb._textbox

    # Theme-aware colors
    mode = ctk.get_appearance_mode().lower()
    if mode == "light":
        if chord_color      == "#e0f2ff": chord_color      = "#1a5a9a"
        if section_color    == "#38bdf8": section_color    = "#0070c0"
        if lyric_color      == "#94a3b8": lyric_color      = "#334155"
        if chord_highlight  == "#1e3a5f": chord_highlight  = "#cce4ff"
    line_bg = "transparent"   # no whole-line background any more

    inner.tag_configure("section",    foreground=section_color,
                        font=("Courier New", chord_size, "bold"))
    inner.tag_configure("lyric",      foreground=lyric_color,
                        font=("Courier New", lyric_size))
    inner.tag_configure("chord_text", foreground=chord_color,
                        font=("Courier New", chord_size, "bold"))
    inner.tag_configure("chord_hl",   background=chord_highlight,
                        foreground=chord_color,
                        font=("Courier New", chord_size, "bold"))
    inner.tag_configure("chord_space",foreground=lyric_color,
                        font=("Courier New", chord_size))
    # invisible tag for the leading # — same bg/fg as widget bg, zero-width illusion
    inner.tag_configure("hash_hidden", elide=True)   # elide hides the char completely

    # Regex to match individual chord tokens on a chord line
    CHORD_RE = re.compile(
        r'([A-G][#b]?(?:maj|min|m|M|dim|aug|sus|add)?(?:2|4|5|6|7|9|11|13)?'
        r'(?:maj7|maj9|m7|m9|7sus4|7sus2)?(?:/[A-G][#b]?)?'
        r'(?:\*[A-G][#b]?(?:maj|min|m|M|dim|aug|sus|add)?(?:2|4|5|6|7|9|11|13)?(?:/[A-G][#b]?)?)?)'
    )

    lines = body.split("\n")
    for i, line in enumerate(lines):
        nl = "\n" if i < len(lines)-1 else ""
        stripped = line.lstrip()
        is_chord = stripped.startswith("#")
        is_section = bool(re.match(r"^\s*\[.+\]", line))

        if is_chord:
            # Hide the leading # character (elide it)
            start = inner.index("end-1c")
            inner.insert("end", "#")
            end_hash = inner.index("end-1c")
            inner.tag_add("hash_hidden", start, end_hash)

            # Rest of line after the #
            rest = stripped[1:]   # everything after the leading #
            # Preserve leading spaces that came before # in original
            prefix_spaces = line[: len(line)-len(stripped)]
            if prefix_spaces:
                ps = inner.index("end-1c")
                inner.insert("end", prefix_spaces)
                inner.tag_add("chord_space", ps, inner.index("end-1c"))

            # Tokenise: highlight chord tokens, spaces between as plain
            pos = 0
            while pos < len(rest):
                m = CHORD_RE.match(rest, pos)
                if m and m.group(0):
                    cs = inner.index("end-1c")
                    inner.insert("end", m.group(0))
                    ce = inner.index("end-1c")
                    inner.tag_add("chord_hl",   cs, ce)
                    inner.tag_add("chord_text", cs, ce)
                    pos = m.end()
                else:
                    # Space / punctuation — plain text, lyric colour
                    cs = inner.index("end-1c")
                    inner.insert("end", rest[pos])
                    ce = inner.index("end-1c")
                    inner.tag_add("chord_space", cs, ce)
                    pos += 1

            if nl:
                inner.insert("end", nl)
        else:
            start = inner.index("end-1c")
            inner.insert("end", line + nl)
            n = len(line) + (1 if nl else 0)
            end = f"{start}+{n}c"
            if is_section:
                inner.tag_add("section", start, end)
            else:
                inner.tag_add("lyric", start, end)

    tb.configure(state="disabled")

# ── HostDialog ────────────────────────────────────────────────────────────────
class HostDialog(ctk.CTkToplevel):
    """
    Closing this window does NOT stop the server.
    Server stops only via "Stop Server" button or app exit.
    Always floats above the main window.
    """
    def __init__(self, parent):
        super().__init__(parent)
        self._qr_photos=[]
        self.title("Host Song on Network")
        self.resizable(True,True)
        self.attributes("-topmost", True)   # always float above main window
        self.protocol("WM_DELETE_WINDOW", self.destroy)
        self._build()
        self._sync_ui()
        center_window(self, 600, 680)
        self.lift(); self.focus_force()

    def _build(self):
        hdr=ctk.CTkFrame(self,fg_color="#0d1117",corner_radius=0); hdr.pack(fill="x")
        self._song_lbl=ctk.CTkLabel(hdr,text="No song selected",
            font=("Segoe UI",13,"bold"),text_color="#4A90D9")
        self._song_lbl.pack(side="left",padx=14,pady=10)

        self._status_var=ctk.StringVar(value="Server stopped")
        self._status_lbl=ctk.CTkLabel(self,textvariable=self._status_var,
            font=("Segoe UI",12),text_color="#888")
        self._status_lbl.pack(pady=(12,2))

        prow=ctk.CTkFrame(self,fg_color="transparent"); prow.pack(pady=4)
        ctk.CTkLabel(prow,text="Port:").pack(side="left",padx=(0,6))
        self._port_var=ctk.StringVar(value=str(_SERVER_STATE["port"]))
        ctk.CTkEntry(prow,textvariable=self._port_var,width=80).pack(side="left")

        self._toggle_btn=ctk.CTkButton(self,text="Start Server",width=190,height=42,
            font=("Segoe UI",13,"bold"),fg_color="#2E7D32",hover_color="#388E3C",
            command=self._toggle)
        self._toggle_btn.pack(pady=10)

        ctk.CTkLabel(self,text="Scan QR or open URL on any device on this network:",
            text_color="#aaa",font=("Segoe UI",11)).pack()
        self._qr_scroll=ctk.CTkScrollableFrame(self,label_text="")
        self._qr_scroll.pack(fill="both",expand=True,padx=14,pady=(6,8))
        ctk.CTkLabel(self._qr_scroll,text="Start the server to see QR codes.",
            text_color="#555",font=("Segoe UI",12)).pack(pady=40)

        ctk.CTkButton(self,text="Close Window  (server keeps running)",
            command=self.destroy,fg_color="#333",hover_color="#444",width=260,
            font=("Segoe UI",11)).pack(pady=8)

    def _sync_ui(self):
        """Sync toggle button / status / QR to actual global server state."""
        sheet=_SERVER_STATE["song_ref"].get("sheet")
        self._song_lbl.configure(text=sheet["title"] if sheet else "No song selected")
        if _SERVER_STATE["running"]:
            port=_SERVER_STATE["port"]
            self._toggle_btn.configure(text="Stop Server",fg_color="#B71C1C",hover_color="#C62828")
            self._status_var.set(f"Running on port {port}")
            self._status_lbl.configure(text_color="#5DBE8A")
            self._port_var.set(str(port))
            self._render_qr(port)
        else:
            self._toggle_btn.configure(text="Start Server",fg_color="#2E7D32",hover_color="#388E3C")
            self._status_var.set("Server stopped")
            self._status_lbl.configure(text_color="#888")

    def _toggle(self):
        if _SERVER_STATE["running"]: self._do_stop()
        else: self._do_start()

    def _do_start(self):
        try: port=int(self._port_var.get())
        except: port=5055
        if not _SERVER_STATE["song_ref"].get("sheet"):
            messagebox.showwarning("No Song","Please select a chord sheet first.",parent=self); return
        ok=start_flask_server(port)
        if not ok:
            messagebox.showerror("Flask Missing","Flask not installed.\nRun: pip install flask",parent=self); return
        self._sync_ui()

    def _do_stop(self):
        stop_flask_server()
        self._sync_ui()
        for w in self._qr_scroll.winfo_children(): w.destroy()
        ctk.CTkLabel(self._qr_scroll,text="Start the server to see QR codes.",
            text_color="#555",font=("Segoe UI",12)).pack(pady=40)

    def _render_qr(self,port):
        for w in self._qr_scroll.winfo_children(): w.destroy()
        self._qr_photos.clear()
        ips=get_private_ips()
        if not ips:
            ctk.CTkLabel(self._qr_scroll,text="No network interfaces found.",text_color="#888").pack(pady=20); return
        for ip in ips:
            url=f"http://{ip}:{port}/"
            card=ctk.CTkFrame(self._qr_scroll,corner_radius=10,fg_color="#161625")
            card.pack(fill="x",pady=6,padx=4)
            ctk.CTkLabel(card,text=url,font=("Courier New",12,"bold"),text_color="#4A90D9").pack(pady=(10,4))
            qr_img=make_qr_image(url,180)
            if qr_img and PIL_OK:
                try:
                    photo=ImageTk.PhotoImage(qr_img); self._qr_photos.append(photo)
                    lbl=tk.Label(card,image=photo,bg="#161625",bd=0); lbl.pack(pady=(0,4))
                except Exception:
                    ctk.CTkLabel(card,text="[QR render error]",text_color="#666").pack(pady=4)
            else:
                ctk.CTkLabel(card,text="Install: pip install qrcode[pil] pillow",
                    text_color="#666",font=("Courier New",10)).pack(pady=(0,8))
            ctk.CTkButton(card,text="Copy URL",width=140,fg_color="#1565C0",hover_color="#1976D2",
                command=lambda u=url: self._copy(u)).pack(pady=(0,10))

    def _copy(self,url):
        self.clipboard_clear(); self.clipboard_append(url)
        messagebox.showinfo("Copied",f"URL copied:\n{url}",parent=self)

# ── SetList Viewer (double-click opens this) ──────────────────────────────────
class SetListViewer(ctk.CTkToplevel):
    """
    Shows songs in a setlist one at a time.
    Prev/Next buttons + left/right arrow keys navigate.
    Fullscreen button shows chords+lyrics only; Esc exits fullscreen.
    """
    def __init__(self, parent, setlist, sheets, start_index=0, settings=None):
        super().__init__(parent)
        self._sl        = setlist
        self._all_sheets= {s["id"]:s for s in sheets}
        self._settings  = settings or load_settings()
        self._ids       = setlist.get("sheet_ids",[])
        self._idx       = start_index
        self._fullscreen= False

        self.title(f"Set List: {setlist['name']}")
        self.minsize(600,400)
        self.transient(parent)
        self._build()
        center_window(self, 900, 720)
        self.lift()
        self.after(100, lambda: (self.lift(), self.focus_force(), self.attributes("-topmost", True), self.after(200, lambda: self.attributes("-topmost", False))))
        self._load_song(self._idx)

        self.bind("<Left>",  lambda e: self._nav(-1))
        self.bind("<Right>", lambda e: self._nav(1))
        self.bind("<Escape>",lambda e: self._exit_fs() if self._fullscreen else None)

    # ── layout ───────────────────────────────────────────────────────────────
    def _build(self):
        # Top bar
        self._topbar=ctk.CTkFrame(self,fg_color="#0d1117",corner_radius=0)
        self._topbar.pack(fill="x")
        self._title_lbl=ctk.CTkLabel(self._topbar,text="",font=("Segoe UI",17,"bold"))
        self._title_lbl.pack(side="left",padx=14,pady=10)
        ctk.CTkButton(self._topbar,text="⛶ Fullscreen",width=120,
            fg_color="#1a1a2e",hover_color="#252540",
            command=self._enter_fs).pack(side="right",padx=6,pady=8)
        ctk.CTkButton(self._topbar,text="Transpose",width=96,
            fg_color="#5A189A",hover_color="#6A1FAC",
            command=self._transpose).pack(side="right",padx=3,pady=8)
        # Quick transpose buttons
        ctk.CTkButton(self._topbar,text="▲ Key",width=64,height=30,
            fg_color="#1a2a3a",hover_color="#243040",
            command=lambda: self._quick_transpose(1)).pack(side="right",padx=(0,2),pady=8)
        ctk.CTkButton(self._topbar,text="▼ Key",width=64,height=30,
            fg_color="#1a2a3a",hover_color="#243040",
            command=lambda: self._quick_transpose(-1)).pack(side="right",padx=(0,2),pady=8)

        # Auto-scroll + font controls bar
        self._ctrl_bar=ctk.CTkFrame(self,fg_color="#111120"); self._ctrl_bar.pack(fill="x",padx=10,pady=(4,0))
        ctk.CTkLabel(self._ctrl_bar,text="Chord:",font=("Segoe UI",11),text_color="#888").pack(side="left",padx=(8,4))
        self._chord_var=ctk.StringVar(value=self._settings.get("chord_font_size","13"))
        ctk.CTkOptionMenu(self._ctrl_bar,variable=self._chord_var,values=FONT_SIZES,width=66,height=24,
            command=lambda _: self._rerender()).pack(side="left")
        ctk.CTkLabel(self._ctrl_bar,text="  Lyric:",font=("Segoe UI",11),text_color="#888").pack(side="left",padx=(10,4))
        self._lyric_var=ctk.StringVar(value=self._settings.get("lyric_font_size","13"))
        ctk.CTkOptionMenu(self._ctrl_bar,variable=self._lyric_var,values=FONT_SIZES,width=66,height=24,
            command=lambda _: self._rerender()).pack(side="left")
        # Font size hotkeys indicator
        ctk.CTkLabel(self._ctrl_bar,text="  (+/- keys)",font=("Segoe UI",9),text_color="#444").pack(side="left")
        ctk.CTkLabel(self._ctrl_bar,text="auto-saved",font=("Segoe UI",9),text_color="#444").pack(side="left",padx=(6,0))
        # Auto-scroll controls
        self._scroll_running = False
        self._scroll_after   = None
        self._scroll_speed   = ctk.IntVar(value=3)   # lines per tick
        ctk.CTkLabel(self._ctrl_bar,text="   Auto-scroll:",font=("Segoe UI",11),text_color="#888").pack(side="left",padx=(14,4))
        self._scroll_btn = ctk.CTkButton(self._ctrl_bar,text="▶ Start",width=72,height=24,
            fg_color="#1a3a1a",hover_color="#254525",text_color="#4ade80",
            font=("Segoe UI",10,"bold"),command=self._toggle_scroll)
        self._scroll_btn.pack(side="left",padx=(0,4))
        ctk.CTkLabel(self._ctrl_bar,text="Speed:",font=("Segoe UI",10),text_color="#666").pack(side="left")
        ctk.CTkSlider(self._ctrl_bar,from_=1,to=10,number_of_steps=9,
            variable=self._scroll_speed,width=80,height=14).pack(side="left",padx=4)

        # Meta row
        self._meta=ctk.CTkFrame(self,fg_color="#161625",corner_radius=8)
        self._meta.pack(fill="x",padx=10,pady=(6,2))

        # Section jump bar (rebuilt per song)
        self._secbar=ctk.CTkFrame(self,fg_color="#0d1117",corner_radius=0)
        self._secbar.pack(fill="x",padx=10,pady=(0,2))

        # Textbox
        self._tb=ctk.CTkTextbox(self,wrap="word",font=("Courier New",13))
        self._tb.pack(fill="both",expand=True,padx=10,pady=4)

        # Next-song preview panel
        self._next_panel=ctk.CTkFrame(self,fg_color="#0d1a10",corner_radius=0,height=36)
        self._next_panel.pack(fill="x"); self._next_panel.pack_propagate(False)
        ctk.CTkLabel(self._next_panel,text="NEXT:",font=("Segoe UI",10,"bold"),
            text_color="#555",width=46).pack(side="left",padx=(8,0))
        self._next_lbl=ctk.CTkLabel(self._next_panel,text="",font=("Segoe UI",11),
            text_color="#4ade80")
        self._next_lbl.pack(side="left",padx=4)
        # Set progress bar
        self._prog_frame=ctk.CTkFrame(self,fg_color="#080c14",corner_radius=0,height=6)
        self._prog_frame.pack(fill="x"); self._prog_frame.pack_propagate(False)
        self._prog_bar=ctk.CTkProgressBar(self._prog_frame,height=6,corner_radius=0,
            fg_color="#111120",progress_color="#1E3A5F")
        self._prog_bar.pack(fill="x"); self._prog_bar.set(0)

        # Bottom nav bar
        self._navbar=ctk.CTkFrame(self,fg_color="#0d1117",corner_radius=0)
        self._navbar.pack(fill="x")
        self._prev_btn=ctk.CTkButton(self._navbar,text="◀  Previous",width=160,height=40,
            font=("Segoe UI",13,"bold"),fg_color="#1E3A5F",hover_color="#243f6e",
            command=lambda: self._nav(-1))
        self._prev_btn.pack(side="left",padx=12,pady=8)
        self._pos_lbl=ctk.CTkLabel(self._navbar,text="",font=("Segoe UI",12),text_color="#666")
        self._pos_lbl.pack(side="left",expand=True)
        self._next_btn=ctk.CTkButton(self._navbar,text="Next  ▶",width=160,height=40,
            font=("Segoe UI",13,"bold"),fg_color="#1E3A5F",hover_color="#243f6e",
            command=lambda: self._nav(1))
        self._next_btn.pack(side="right",padx=12,pady=8)

    # ── navigation ───────────────────────────────────────────────────────────
    def _nav(self, delta):
        new = self._idx + delta
        if 0 <= new < len(self._ids):
            self._stop_scroll()
            self._load_song(new)

    def _load_song(self, idx):
        self._idx = idx
        # Skip break rows automatically
        while idx < len(self._ids) and self._ids[idx] == "__break__":
            idx += 1
            self._idx = idx
        sid = self._ids[idx] if idx < len(self._ids) else None
        s   = self._all_sheets.get(sid) if sid else None
        if not s:
            self._title_lbl.configure(text="[Missing song]")
            for w in self._secbar.winfo_children(): w.destroy()
            self._tb.configure(state="normal"); self._tb.delete("0.0","end")
            self._tb.configure(state="disabled")
            self._next_lbl.configure(text="")
        else:
            self._cur_sheet = s
            self._title_lbl.configure(text=s["title"])
            self.title(f"Set List: {self._sl['name']}  —  {s['title']}")
            update_hosted_song(s)

            # ── Meta row ─────────────────────────────────────────────────────
            for w in self._meta.winfo_children(): w.destroy()
            meta_fields = [
                ("Key",    s.get("key","—")),
                ("BPM",    str(s.get("bpm","—"))),
                ("Artist", s.get("artist","—")),
            ]
            if s.get("sx_style"):   meta_fields.append(("🎹 Style",  s["sx_style"]))
            if s.get("sx_ots"):     meta_fields.append(("OTS",       f"#{s['sx_ots']}"))
            if s.get("sx_intro"):   meta_fields.append(("Intro",     s["sx_intro"]))
            if s.get("sx_ending"):  meta_fields.append(("Ending",    s["sx_ending"]))
            if s.get("sx_voice_r"): meta_fields.append(("R.Hand",    s["sx_voice_r"]))
            if s.get("sx_voice_l"): meta_fields.append(("L.Hand",    s["sx_voice_l"]))
            for c,(lbl,val) in enumerate(meta_fields):
                ctk.CTkLabel(self._meta, text=lbl, font=("Segoe UI",10), text_color="#555"
                    ).grid(row=0,column=c,padx=10,pady=(5,0),sticky="w")
                ctk.CTkLabel(self._meta, text=val, font=("Segoe UI",12,"bold"), text_color="#ccc"
                    ).grid(row=1,column=c,padx=10,pady=(0,5),sticky="w")
            if s.get("sx_variation"):
                ctk.CTkLabel(self._meta, text="Variation plan:", font=("Segoe UI",9), text_color="#4A90D9"
                    ).grid(row=2,column=0,padx=10,pady=(0,4),sticky="w")
                ctk.CTkLabel(self._meta, text=s["sx_variation"],
                    font=("Segoe UI",10,"bold"), text_color="#93c5fd"
                    ).grid(row=2,column=1,columnspan=max(1,len(meta_fields)-1),
                           padx=10,pady=(0,4),sticky="w")
            # Between-song notes / announcement hints
            if s.get("notes"):
                ctk.CTkLabel(self._meta,
                    text=f"📝  {s['notes']}",
                    font=("Segoe UI",10), text_color="#f59e0b",
                    wraplength=800, justify="left"
                ).grid(row=3, column=0, columnspan=max(len(meta_fields),1)+1,
                       padx=10, pady=(0,6), sticky="w")

            # ── Section jump buttons ──────────────────────────────────────────
            self._build_section_jumps(s)

            # ── Next-song preview ─────────────────────────────────────────────
            self._update_next_preview()

            # ── Render body ───────────────────────────────────────────────────
            self._countdown_start(s)

        # Position label, button states, progress bar
        total = len(self._ids)
        real_total = sum(1 for sid in self._ids if sid != "__break__")
        real_pos   = sum(1 for sid in self._ids[:self._idx+1] if sid != "__break__")
        self._pos_lbl.configure(
            text=f"{real_pos} / {real_total}  —  {self._sl['name']}")
        self._prev_btn.configure(state="normal" if self._idx > 0 else "disabled")
        self._next_btn.configure(state="normal" if self._idx < total-1 else "disabled")
        # Progress bar
        prog = (real_pos / real_total) if real_total > 1 else 1.0
        self._prog_bar.set(prog)
        if self._fullscreen: self._fs_render()

    # ── Section jump buttons ──────────────────────────────────────────────────
    def _build_section_jumps(self, s):
        for w in self._secbar.winfo_children(): w.destroy()
        body = s.get("body","")
        sections = []
        line_no  = 0
        for line in body.split("\n"):
            if re.match(r"^\s*\[.+\]", line):
                label = line.strip().strip("[]")
                sections.append((label, line_no))
            line_no += 1
        if not sections:
            return
        ctk.CTkLabel(self._secbar, text="Jump:", font=("Segoe UI",10),
            text_color="#555").pack(side="left", padx=(8,4), pady=4)
        for label, lno in sections:
            ctk.CTkButton(self._secbar, text=label, width=0,
                height=26, font=("Segoe UI",10,"bold"),
                fg_color="#1a2a3a", hover_color="#243040",
                text_color="#38bdf8",
                command=lambda n=lno: self._jump_to_line(n)
            ).pack(side="left", padx=3, pady=4)

    def _jump_to_line(self, line_no):
        """Scroll textbox to a given line number."""
        try:
            self._tb.configure(state="normal")
            self._tb.see(f"{line_no + 1}.0")
            self._tb.configure(state="disabled")
        except: pass

    # ── Next-song preview ─────────────────────────────────────────────────────
    def _update_next_preview(self):
        # Find next real song (skip breaks)
        next_s = None
        for i in range(self._idx + 1, len(self._ids)):
            sid = self._ids[i]
            if sid != "__break__":
                next_s = self._all_sheets.get(sid)
                if next_s: break
        if not next_s:
            self._next_lbl.configure(text="— end of setlist —", text_color="#333")
            return
        # First chord in body
        first_chord = ""
        for line in next_s.get("body","").split("\n"):
            if line.strip().startswith("#"):
                chords = line.strip().lstrip("#").split()
                if chords: first_chord = "  ·  First: " + "  ".join(chords[:4])
                break
        style_txt = f"  ·  🎹 {next_s['sx_style']}" if next_s.get("sx_style") else ""
        ots_txt   = f"  OTS#{next_s['sx_ots']}"      if next_s.get("sx_ots")   else ""
        preview   = (f"{next_s['title']}"
                     f"  ·  Key: {next_s.get('key','?')}"
                     f"  ·  BPM: {next_s.get('bpm','?')}"
                     f"{style_txt}{ots_txt}{first_chord}")
        self._next_lbl.configure(text=preview, text_color="#4ade80")

    # ── Countdown flash ───────────────────────────────────────────────────────
    def _countdown_start(self, s):
        """Show 4-3-2-1 flash overlay then render the body."""
        overlay = ctk.CTkFrame(self, fg_color="#050810", corner_radius=0)
        overlay.place(relx=0, rely=0, relwidth=1, relheight=1)
        lbl = ctk.CTkLabel(overlay, text="", font=("Segoe UI",96,"bold"),
                           text_color="#4A90D9")
        lbl.place(relx=0.5, rely=0.4, anchor="center")
        song_lbl = ctk.CTkLabel(overlay, text=s["title"],
            font=("Segoe UI",22,"bold"), text_color="#38bdf8")
        song_lbl.place(relx=0.5, rely=0.6, anchor="center")
        key_lbl = ctk.CTkLabel(overlay,
            text=f"Key: {s.get('key','?')}   BPM: {s.get('bpm','?')}",
            font=("Segoe UI",14), text_color="#666")
        key_lbl.place(relx=0.5, rely=0.68, anchor="center")

        counts = ["4", "3", "2", "1", "▶"]
        colors = ["#e0f2ff","#93c5fd","#60a5fa","#4ade80","#22c55e"]

        def _tick(i=0):
            if i < len(counts):
                lbl.configure(text=counts[i], text_color=colors[i])
                self.after(600, lambda: _tick(i+1))
            else:
                overlay.destroy()
                self._rerender()
        _tick()

    # ── Auto-scroll ───────────────────────────────────────────────────────────
    def _toggle_scroll(self):
        if self._scroll_running:
            self._stop_scroll()
        else:
            self._scroll_running = True
            self._scroll_btn.configure(text="⏹ Stop", fg_color="#3a1a1a",
                                       text_color="#f87171")
            self._scroll_tick()

    def _stop_scroll(self):
        self._scroll_running = False
        if self._scroll_after:
            try: self.after_cancel(self._scroll_after)
            except: pass
            self._scroll_after = None
        self._scroll_btn.configure(text="▶ Start", fg_color="#1a3a1a",
                                   text_color="#4ade80")

    def _scroll_tick(self):
        if not self._scroll_running: return
        try:
            self._tb.configure(state="normal")
            self._tb._textbox.yview_scroll(1, "units")
            self._tb.configure(state="disabled")
        except: pass
        # Speed 1-10 → delay 1200ms-120ms
        spd   = max(1, min(10, self._scroll_speed.get()))
        delay = int(1200 - (spd - 1) * 120)
        self._scroll_after = self.after(delay, self._scroll_tick)

    # ── Font size hotkeys ─────────────────────────────────────────────────────
    def _font_bump(self, delta):
        for var in (self._chord_var, self._lyric_var):
            try:
                cur = int(var.get())
                nv  = max(8, min(48, cur + delta))
                var.set(str(nv))
            except: pass
        self._rerender()

    # ── Quick transpose ───────────────────────────────────────────────────────
    def _quick_transpose(self, semitones):
        if not hasattr(self,"_cur_sheet"): return
        from_key = self._cur_sheet.get("key","C")
        key_list = KEYS
        try:   idx_k = key_list.index(from_key)
        except ValueError: idx_k = 0
        to_key   = key_list[(idx_k + semitones) % len(key_list)]
        new_body = transpose_body(self._cur_sheet.get("body",""), semitones)
        if new_body:
            if not self._cur_sheet.get("original_body"):
                self._cur_sheet["original_body"] = self._cur_sheet["body"]
                self._cur_sheet["original_key"]  = from_key
            self._cur_sheet["body"] = new_body
            self._cur_sheet["key"]  = to_key
            self._rerender()
            self._title_lbl.configure(
                text=f"{self._cur_sheet['title']}  [{to_key}]")

    # ── Render ────────────────────────────────────────────────────────────────
    def _rerender(self):
        if not hasattr(self,"_cur_sheet"): return
        try: cs=int(self._chord_var.get())
        except: cs=13
        try: ls=int(self._lyric_var.get())
        except: ls=13
        cc=self._settings.get("chord_color","#e0f2ff")
        sc=self._settings.get("section_color","#38bdf8")
        lc=self._settings.get("lyric_color","#94a3b8")
        hc=self._settings.get("chord_highlight_color","#1e3a5f")
        render_body(self._tb,self._cur_sheet.get("body",""),cs,ls,cc,sc,lc,hc)
        self._settings["chord_font_size"]=str(cs)
        self._settings["lyric_font_size"]=str(ls)
        save_settings(self._settings)

    def _transpose(self):
        if not hasattr(self,"_cur_sheet"): return
        dlg=TransposeDialog(self,self._cur_sheet); self.wait_window(dlg)
        if dlg.result_body:
            self._cur_sheet["body"]=dlg.result_body
            self._cur_sheet["key"]=dlg.result_key or self._cur_sheet["key"]
            self._rerender()

    # ── Fullscreen ────────────────────────────────────────────────────────────
    def _enter_fs(self):
        if self._fullscreen: return
        self._fullscreen=True
        self._topbar.pack_forget()
        self._ctrl_bar.pack_forget()
        self._meta.pack_forget()
        self._secbar.pack_forget()
        self._tb.pack_forget()
        self._next_panel.pack_forget()
        self._prog_frame.pack_forget()
        self._navbar.pack_forget()

        self._fs_frame=ctk.CTkFrame(self,fg_color="#050810",corner_radius=0)
        self._fs_frame.pack(fill="both",expand=True)

        fs_top=ctk.CTkFrame(self._fs_frame,fg_color="#0a0e18",corner_radius=0)
        fs_top.pack(fill="x")
        self._fs_title=ctk.CTkLabel(fs_top,text="",font=("Segoe UI",14,"bold"),text_color="#4A90D9")
        self._fs_title.pack(side="left",padx=16,pady=6)
        ctk.CTkLabel(fs_top,text="Esc=exit  ←→=navigate  +/-=font  ▲▼=key",
            font=("Segoe UI",10),text_color="#333").pack(side="left",padx=8)
        ctk.CTkButton(fs_top,text="✕",width=44,height=26,
            fg_color="#333",hover_color="#B71C1C",command=self._exit_fs
            ).pack(side="right",padx=8,pady=5)
        ctk.CTkButton(fs_top,text="▲ Key",width=64,height=24,
            fg_color="#1a2a3a",hover_color="#243040",
            command=lambda: self._quick_transpose(1)).pack(side="right",padx=2,pady=5)
        ctk.CTkButton(fs_top,text="▼ Key",width=64,height=24,
            fg_color="#1a2a3a",hover_color="#243040",
            command=lambda: self._quick_transpose(-1)).pack(side="right",padx=2,pady=5)
        self._fs_prev=ctk.CTkButton(fs_top,text="◀",width=40,height=28,
            fg_color="#1E3A5F",hover_color="#243f6e",command=lambda: self._nav(-1))
        self._fs_prev.pack(side="right",padx=2,pady=4)
        self._fs_next=ctk.CTkButton(fs_top,text="▶",width=40,height=28,
            fg_color="#1E3A5F",hover_color="#243f6e",command=lambda: self._nav(1))
        self._fs_next.pack(side="right",padx=2,pady=4)
        self._fs_pos=ctk.CTkLabel(fs_top,text="",font=("Segoe UI",11),text_color="#555")
        self._fs_pos.pack(side="right",padx=6)

        # Section jump bar inside fullscreen
        self._fs_secbar=ctk.CTkFrame(self._fs_frame,fg_color="#080c14",corner_radius=0)
        self._fs_secbar.pack(fill="x")
        if hasattr(self,"_cur_sheet"):
            self._build_fs_section_jumps()

        self._fs_tb=ctk.CTkTextbox(self._fs_frame,wrap="word",
            font=("Courier New",int(self._chord_var.get())),fg_color="#050810")
        self._fs_tb.pack(fill="both",expand=True,padx=16,pady=8)

        # Next-song strip at bottom of fullscreen
        fs_bot=ctk.CTkFrame(self._fs_frame,fg_color="#0d1a10",corner_radius=0,height=30)
        fs_bot.pack(fill="x"); fs_bot.pack_propagate(False)
        ctk.CTkLabel(fs_bot,text="NEXT:",font=("Segoe UI",9,"bold"),
            text_color="#555").pack(side="left",padx=(10,4))
        self._fs_next_lbl=ctk.CTkLabel(fs_bot,text="",font=("Segoe UI",10),text_color="#4ade80")
        self._fs_next_lbl.pack(side="left")

        self.after(50,lambda: self.attributes("-fullscreen",True))
        self.bind("<Escape>",lambda e: self._exit_fs())
        self.bind("<equal>",  lambda e: self._font_bump(2))
        self.bind("<plus>",   lambda e: self._font_bump(2))
        self.bind("<minus>",  lambda e: self._font_bump(-2))
        self._fs_render()

    def _build_fs_section_jumps(self):
        for w in self._fs_secbar.winfo_children(): w.destroy()
        body = self._cur_sheet.get("body","")
        sections = []
        for i, line in enumerate(body.split("\n")):
            if re.match(r"^\s*\[.+\]", line):
                sections.append((line.strip().strip("[]"), i))
        if not sections: return
        ctk.CTkLabel(self._fs_secbar,text="Jump:",font=("Segoe UI",10),
            text_color="#444").pack(side="left",padx=(10,4),pady=3)
        for label, lno in sections:
            ctk.CTkButton(self._fs_secbar,text=label,width=0,height=22,
                font=("Segoe UI",9,"bold"),fg_color="#0d1a2e",hover_color="#1a2a3a",
                text_color="#38bdf8",
                command=lambda n=lno: self._jump_fs_line(n)
            ).pack(side="left",padx=2,pady=3)

    def _jump_fs_line(self, line_no):
        try:
            self._fs_tb.configure(state="normal")
            self._fs_tb._textbox.yview_scroll(0,"units")
            self._fs_tb._textbox.see(f"{line_no+1}.0")
            self._fs_tb.configure(state="disabled")
        except: pass

    def _exit_fs(self):
        if not self._fullscreen: return
        self.attributes("-fullscreen",False)
        self._fullscreen=False
        self._fs_frame.destroy()
        self._fs_frame=None; self._fs_tb=None
        self.unbind("<equal>"); self.unbind("<plus>"); self.unbind("<minus>")
        self._topbar.pack(fill="x")
        self._ctrl_bar.pack(fill="x",padx=10,pady=(4,0))
        self._meta.pack(fill="x",padx=10,pady=(6,2))
        self._secbar.pack(fill="x",padx=10,pady=(0,2))
        self._tb.pack(fill="both",expand=True,padx=10,pady=4)
        self._next_panel.pack(fill="x")
        self._prog_frame.pack(fill="x")
        self._navbar.pack(fill="x")
        self.bind("<Escape>",lambda e: None)

    def _fs_render(self):
        if not hasattr(self,"_cur_sheet") or not self._fs_tb: return
        try: cs=int(self._chord_var.get())
        except: cs=13
        try: ls=int(self._lyric_var.get())
        except: ls=13
        cc=self._settings.get("chord_color","#e0f2ff")
        sc=self._settings.get("section_color","#38bdf8")
        lc=self._settings.get("lyric_color","#94a3b8")
        hc=self._settings.get("chord_highlight_color","#1e3a5f")
        render_body(self._fs_tb,self._cur_sheet.get("body",""),cs,ls,cc,sc,lc,hc)
        self._fs_title.configure(text=self._cur_sheet["title"])
        total=len(self._ids)
        real_pos = sum(1 for sid in self._ids[:self._idx+1] if sid!="__break__")
        real_tot = sum(1 for sid in self._ids if sid!="__break__")
        self._fs_pos.configure(text=f"{real_pos}/{real_tot}")
        self._fs_prev.configure(state="normal" if self._idx>0 else "disabled")
        self._fs_next.configure(state="normal" if self._idx<total-1 else "disabled")
        # Next label in fullscreen
        if hasattr(self,"_fs_next_lbl"):
            self._fs_next_lbl.configure(text=self._next_lbl.cget("text"))
        if hasattr(self,"_fs_secbar"):
            self._build_fs_section_jumps()

# ── ViewerDialog ──────────────────────────────────────────────────────────────
class ViewerDialog(ctk.CTkToplevel):
    """Single-song viewer. Fullscreen support. Optional setlist context for navigation."""
    def __init__(self, parent, sheet, settings=None, setlist_sheets=None, setlist_idx=0):
        super().__init__(parent)
        self._sheet       = dict(sheet)
        self._settings    = settings or load_settings()
        self._sl_sheets   = setlist_sheets   # list of sheet dicts (setlist context) or None
        self._sl_idx      = setlist_idx
        self._fullscreen  = False
        self._fs_frame    = None
        self._fs_tb       = None

        self.title(f"  {sheet['title']}")
        self.resizable(True,True)
        self.transient(parent)
        self._build()
        center_window(self, 840, 700)
        self.lift()
        self.after(100, lambda: (self.lift(), self.focus_force(), self.attributes("-topmost", True), self.after(200, lambda: self.attributes("-topmost", False))))

        self.bind("<Left>",  lambda e: self._nav(-1) if self._sl_sheets else None)
        self.bind("<Right>", lambda e: self._nav(1)  if self._sl_sheets else None)
        self.bind("<Escape>",lambda e: self._exit_fs() if self._fullscreen else None)

    def _csz(self):
        try: return int(self._chord_var.get())
        except: return 13
    def _lsz(self):
        try: return int(self._lyric_var.get())
        except: return 13
    def _toggle_maximize(self):
        cur = self.wm_state()
        if cur == "zoomed": self.wm_state("normal")
        else: self.wm_state("zoomed")

    def _build(self):
        s=self._sheet
        self._topbar=ctk.CTkFrame(self,fg_color="#0d1117",corner_radius=0)
        self._topbar.pack(fill="x")
        self._meta_lbl=ctk.CTkLabel(self._topbar,
            text=f"  {s.get('artist','---')}   Key: {s.get('key','---')}   BPM: {s.get('bpm','---')}",
            font=("Segoe UI",12),text_color="#aaa")
        self._meta_lbl.pack(side="left",pady=8)
        ctk.CTkButton(self._topbar,text="⛶ Fullscreen",width=110,
            fg_color="#1a1a2e",hover_color="#252540",
            command=self._enter_fs).pack(side="right",padx=6,pady=6)
        ctk.CTkButton(self._topbar,text="⬜ Maximize",width=100,
            fg_color="#1a2a1a",hover_color="#253525",
            command=self._toggle_maximize).pack(side="right",padx=2,pady=6)
        ctk.CTkButton(self._topbar,text="Transpose",width=96,
            fg_color="#5A189A",hover_color="#6A1FAC",
            command=self._transpose).pack(side="right",padx=3,pady=6)
        self._reset_btn=ctk.CTkButton(self._topbar,text="↺ Reset",width=78,height=30,
            fg_color="#1a3a2a",hover_color="#1e5c36",text_color="#4ade80",
            command=self._reset_transpose)
        if self._sheet.get("original_body"):
            self._reset_btn.pack(side="right",padx=(0,2),pady=6)

        self._fsz=ctk.CTkFrame(self,fg_color="#111120"); self._fsz.pack(fill="x",padx=12,pady=(6,2))
        ctk.CTkLabel(self._fsz,text="Chord font:",font=("Segoe UI",11),text_color="#888").pack(side="left",padx=(8,4))
        self._chord_var=ctk.StringVar(value=self._settings.get("chord_font_size","13"))
        ctk.CTkOptionMenu(self._fsz,variable=self._chord_var,values=FONT_SIZES,width=70,height=26,
            command=self._rerender).pack(side="left")
        ctk.CTkLabel(self._fsz,text="   Lyric font:",font=("Segoe UI",11),text_color="#888").pack(side="left",padx=(12,4))
        self._lyric_var=ctk.StringVar(value=self._settings.get("lyric_font_size","13"))
        ctk.CTkOptionMenu(self._fsz,variable=self._lyric_var,values=FONT_SIZES,width=70,height=26,
            command=self._rerender).pack(side="left")
        ctk.CTkLabel(self._fsz,text="auto-saved",font=("Segoe UI",9),text_color="#444").pack(side="left",padx=(10,0))

        self._tb=ctk.CTkTextbox(self,wrap="word",font=("Courier New",self._csz()))
        self._tb.pack(fill="both",expand=True,padx=12,pady=4)
        render_body(self._tb,self._sheet.get("body",""),self._csz(),self._lsz(),
                    self._settings.get("chord_color","#e0f2ff"),
                    self._settings.get("section_color","#38bdf8"),
                    self._settings.get("lyric_color","#94a3b8"),
                    self._settings.get("chord_highlight_color","#1e3a5f"))

        self._leg=ctk.CTkFrame(self,fg_color="transparent"); self._leg.pack(fill="x",padx=12,pady=2)
        for txt,col in [("chord","#4A90D9"),("   [Section]","#38bdf8"),("   Lyrics","#888")]:
            ctk.CTkLabel(self._leg,text=txt,text_color=col,font=("Segoe UI",11)).pack(side="left")

        self._notes_lbl=None
        if self._sheet.get("notes"):
            self._notes_lbl=ctk.CTkLabel(self,text=f"Notes: {self._sheet['notes']}",
                text_color="#888",font=("Segoe UI",12),wraplength=780)
            self._notes_lbl.pack(padx=12,pady=(2,4),anchor="w")

        # Nav bar (only if setlist context)
        if self._sl_sheets:
            self._navbar=ctk.CTkFrame(self,fg_color="#0d1117",corner_radius=0)
            self._navbar.pack(fill="x")
            self._prev_btn=ctk.CTkButton(self._navbar,text="◀  Previous",width=140,height=36,
                font=("Segoe UI",12,"bold"),fg_color="#1E3A5F",hover_color="#243f6e",
                command=lambda: self._nav(-1))
            self._prev_btn.pack(side="left",padx=10,pady=6)
            self._pos_lbl=ctk.CTkLabel(self._navbar,text="",font=("Segoe UI",11),text_color="#555")
            self._pos_lbl.pack(side="left",expand=True)
            self._next_btn=ctk.CTkButton(self._navbar,text="Next  ▶",width=140,height=36,
                font=("Segoe UI",12,"bold"),fg_color="#1E3A5F",hover_color="#243f6e",
                command=lambda: self._nav(1))
            self._next_btn.pack(side="right",padx=10,pady=6)
            self._update_nav_state()
        else:
            ctk.CTkButton(self,text="Close",command=self.destroy,width=100).pack(pady=8)

    def _update_nav_state(self):
        if not self._sl_sheets: return
        n=len(self._sl_sheets); i=self._sl_idx
        self._pos_lbl.configure(text=f"{i+1} / {n}")
        self._prev_btn.configure(state="normal" if i>0 else "disabled")
        self._next_btn.configure(state="normal" if i<n-1 else "disabled")

    def _nav(self,delta):
        if not self._sl_sheets: return
        new=self._sl_idx+delta
        if 0<=new<len(self._sl_sheets):
            self._sl_idx=new
            self._sheet=dict(self._sl_sheets[new])
            s=self._sheet
            cc=self._settings.get("chord_color","#e0f2ff")
            sc=self._settings.get("section_color","#38bdf8")
            lc=self._settings.get("lyric_color","#94a3b8")
            hc=self._settings.get("chord_highlight_color","#1e3a5f")
            self.title(f"  {s['title']}")
            self._meta_lbl.configure(text=f"  {s.get('artist','---')}   Key: {s.get('key','---')}   BPM: {s.get('bpm','---')}")
            render_body(self._tb,s.get("body",""),self._csz(),self._lsz(),cc,sc,lc,hc)
            if self._fullscreen and self._fs_tb:
                render_body(self._fs_tb,s.get("body",""),self._csz(),self._lsz(),cc,sc,lc,hc)
                self._fs_title.configure(text=s["title"])
                n=len(self._sl_sheets); i=self._sl_idx
                self._fs_pos.configure(text=f"{i+1}/{n}")
                self._fs_prev.configure(state="normal" if i>0 else "disabled")
                self._fs_next.configure(state="normal" if i<n-1 else "disabled")
            self._update_nav_state()

    def _rerender(self,_=None):
        cs=self._csz(); ls=self._lsz()
        cc=self._settings.get("chord_color","#e0f2ff")
        sc=self._settings.get("section_color","#38bdf8")
        lc=self._settings.get("lyric_color","#94a3b8")
        hc=self._settings.get("chord_highlight_color","#1e3a5f")
        render_body(self._tb,self._sheet.get("body",""),cs,ls,cc,sc,lc,hc)
        if self._fullscreen and self._fs_tb:
            render_body(self._fs_tb,self._sheet.get("body",""),cs,ls,cc,sc,lc,hc)
        self._settings["chord_font_size"]=str(cs)
        self._settings["lyric_font_size"]=str(ls)
        save_settings(self._settings)

    def _transpose(self):
        dlg=TransposeDialog(self,self._sheet); self.wait_window(dlg)
        if dlg.result_body:
            if getattr(dlg,"result_reset",False):
                # Reset — restore original and hide reset button
                self._sheet["body"] = dlg.result_body
                self._sheet["key"]  = dlg.result_key or self._sheet["key"]
                self._sheet.pop("original_body",None); self._sheet.pop("original_key",None)
                self._reset_btn.pack_forget()
            else:
                # Normal transpose — save original on first transpose only
                if not self._sheet.get("original_body"):
                    self._sheet["original_body"] = self._sheet["body"]
                    self._sheet["original_key"]  = self._sheet.get("key","")
                self._sheet["body"] = dlg.result_body
                self._sheet["key"]  = dlg.result_key or self._sheet["key"]
                self._reset_btn.pack(side="right",padx=(0,2),pady=6)
            self._meta_lbl.configure(text=f"  {self._sheet.get('artist','---')}   Key: {self._sheet.get('key','---')}   BPM: {self._sheet.get('bpm','---')}")
            self._rerender()

    def _reset_transpose(self):
        if not self._sheet.get("original_body"): return
        self._sheet["body"] = self._sheet.pop("original_body")
        self._sheet["key"]  = self._sheet.pop("original_key","")
        self._reset_btn.pack_forget()
        self._meta_lbl.configure(text=f"  {self._sheet.get('artist','---')}   Key: {self._sheet.get('key','---')}   BPM: {self._sheet.get('bpm','---')}")
        self._rerender()

    def _enter_fs(self):
        if self._fullscreen: return
        self._fullscreen=True
        self._topbar.pack_forget(); self._fsz.pack_forget()
        self._tb.pack_forget()
        self._leg.pack_forget()
        if self._notes_lbl: self._notes_lbl.pack_forget()
        if hasattr(self,"_navbar"): self._navbar.pack_forget()

        self._fs_frame=ctk.CTkFrame(self,fg_color="#050810",corner_radius=0)
        self._fs_frame.pack(fill="both",expand=True)

        fs_top=ctk.CTkFrame(self._fs_frame,fg_color="#0a0e18",corner_radius=0); fs_top.pack(fill="x")
        self._fs_title=ctk.CTkLabel(fs_top,text=self._sheet["title"],
            font=("Segoe UI",14,"bold"),text_color="#4A90D9")
        self._fs_title.pack(side="left",padx=16,pady=6)
        ctk.CTkLabel(fs_top,text="Esc = exit fullscreen" + ("  |  ← → = navigate" if self._sl_sheets else ""),
            font=("Segoe UI",10),text_color="#444").pack(side="left",padx=8)
        ctk.CTkButton(fs_top,text="✕ Exit",width=70,height=26,
            fg_color="#333",hover_color="#B71C1C",command=self._exit_fs
            ).pack(side="right",padx=8,pady=5)

        if self._sl_sheets:
            self._fs_prev=ctk.CTkButton(fs_top,text="◀",width=36,height=26,
                fg_color="#1E3A5F",hover_color="#243f6e",command=lambda: self._nav(-1))
            self._fs_prev.pack(side="right",padx=2,pady=5)
            self._fs_next=ctk.CTkButton(fs_top,text="▶",width=36,height=26,
                fg_color="#1E3A5F",hover_color="#243f6e",command=lambda: self._nav(1))
            self._fs_next.pack(side="right",padx=2,pady=5)
            self._fs_pos=ctk.CTkLabel(fs_top,text="",font=("Segoe UI",11),text_color="#555")
            self._fs_pos.pack(side="right",padx=8)
            n=len(self._sl_sheets); i=self._sl_idx
            self._fs_pos.configure(text=f"{i+1}/{n}")
            self._fs_prev.configure(state="normal" if i>0 else "disabled")
            self._fs_next.configure(state="normal" if i<n-1 else "disabled")

        self._fs_tb=ctk.CTkTextbox(self._fs_frame,wrap="word",
            font=("Courier New",self._csz()),fg_color="#050810")
        self._fs_tb.pack(fill="both",expand=True,padx=16,pady=8)
        render_body(self._fs_tb,self._sheet.get("body",""),self._csz(),self._lsz(),
                    self._settings.get("chord_color","#e0f2ff"),
                    self._settings.get("section_color","#38bdf8"),
                    self._settings.get("lyric_color","#94a3b8"),
                    self._settings.get("chord_highlight_color","#1e3a5f"))

        self.after(50,lambda: self.attributes("-fullscreen",True))
        self.bind("<Escape>",lambda e: self._exit_fs())

    def _exit_fs(self):
        if not self._fullscreen: return
        self.attributes("-fullscreen",False); self._fullscreen=False
        self._fs_frame.destroy(); self._fs_frame=None; self._fs_tb=None
        # Restore all widgets in correct order
        self._topbar.pack(fill="x")
        self._fsz.pack(fill="x",padx=12,pady=(6,2))
        self._tb.pack(fill="both",expand=True,padx=12,pady=4)
        self._leg.pack(fill="x",padx=12,pady=2)
        if self._notes_lbl: self._notes_lbl.pack(padx=12,pady=(2,4),anchor="w")
        if hasattr(self,"_navbar"): self._navbar.pack(fill="x")
        self.bind("<Escape>",lambda e: None)

# ── SheetFormDialog ───────────────────────────────────────────────────────────
class SheetFormDialog(ctk.CTkToplevel):
    def __init__(self, parent, sheet=None, categories=None, current_cat_id=None, artists=None):
        super().__init__(parent)
        self.result = None
        self.result_category_id = current_cat_id
        self.sheet = sheet
        self._categories = categories or []
        self._current_cat_id = current_cat_id
        self._artists = [UNKNOWN_ARTIST] + [a for a in (artists or []) if a != UNKNOWN_ARTIST]
        self.title("Edit Chord Sheet" if sheet else "New Chord Sheet")
        self.resizable(True, True)
        # grab removed — allows Chord Writer to stay interactive
        self._build()
        if sheet: self._populate(sheet)
        center_window(self, 840, 820)
        self.lift(); self.focus_force()

    def _build(self):
        pad = {"padx":16,"pady":5}
        main = ctk.CTkFrame(self, fg_color="transparent"); main.pack(fill="both",expand=True)
        main.columnconfigure(0, weight=1)
        main.rowconfigure(0, weight=1)

        # ── Single-column scrollable form ──
        sc = ctk.CTkScrollableFrame(main); sc.grid(row=0, column=0, sticky="nsew", padx=4)
        ctk.CTkLabel(sc,text="Song Title *",anchor="w").pack(fill="x",**pad)
        self.title_var = ctk.StringVar()
        ctk.CTkEntry(sc,textvariable=self.title_var,placeholder_text="e.g. Wonderwall").pack(fill="x",**pad)

        # Artist picker
        ctk.CTkLabel(sc,text="Artist",anchor="w").pack(fill="x",**pad)
        self.artist_var = ctk.StringVar(value=UNKNOWN_ARTIST)
        artist_row = ctk.CTkFrame(sc, fg_color="transparent"); artist_row.pack(fill="x", **pad)
        self._artist_display = ctk.CTkLabel(artist_row, textvariable=self.artist_var,
            font=("Segoe UI",12), anchor="w", fg_color="#1e1e2e", corner_radius=6,
            width=320, text_color="#ccc")
        self._artist_display.pack(side="left", ipady=5, ipadx=8)
        ctk.CTkButton(artist_row, text="Change...", width=90, height=30,
            fg_color="#2a2a3a", hover_color="#3a3a4a",
            command=lambda: self._pick_artist(sc)).pack(side="left", padx=(6,0))

        # Category picker (popup)
        ctk.CTkLabel(sc,text="Category",anchor="w").pack(fill="x",**pad)
        self._cat_display_var = ctk.StringVar(value="📂 Uncategorized")
        cat_row = ctk.CTkFrame(sc, fg_color="transparent"); cat_row.pack(fill="x", **pad)
        self._cat_display = ctk.CTkLabel(cat_row, textvariable=self._cat_display_var,
            font=("Segoe UI",12), anchor="w", fg_color="#1e1e2e", corner_radius=6,
            width=320, text_color="#60a5fa")
        self._cat_display.pack(side="left", ipady=5, ipadx=8)
        ctk.CTkButton(cat_row, text="Change...", width=90, height=30,
            fg_color="#2a2a3a", hover_color="#3a3a4a",
            command=self._pick_category).pack(side="left", padx=(6,0))
        # Pre-fill display if category already set
        if self._current_cat_id:
            c = _find_cat_by_id(self._categories, self._current_cat_id)
            if c: self._cat_display_var.set(f"📁 {c['name']}")

        r1 = ctk.CTkFrame(sc,fg_color="transparent"); r1.pack(fill="x",**pad)
        ctk.CTkLabel(r1,text="Key").grid(row=0,column=0,sticky="w",padx=(0,4))
        self.key_var = ctk.StringVar(value=KEYS[0])
        ctk.CTkOptionMenu(r1,variable=self.key_var,values=KEYS,width=180).grid(row=1,column=0,padx=(0,14))
        ctk.CTkLabel(r1,text="BPM").grid(row=0,column=1,sticky="w")
        self.bpm_var = ctk.StringVar(value="120")
        ctk.CTkEntry(r1,textvariable=self.bpm_var,width=90).grid(row=1,column=1)

        # ── Yamaha SX720 Arranger Fields ──────────────────────────────────────
        ysec = ctk.CTkFrame(sc, fg_color="#0d1117", corner_radius=8)
        ysec.pack(fill="x", **pad)
        ctk.CTkLabel(ysec, text="🎹  Yamaha SX720 Settings",
            font=("Segoe UI",12,"bold"), text_color="#4A90D9").pack(anchor="w", padx=12, pady=(8,4))

        yr1 = ctk.CTkFrame(ysec, fg_color="transparent"); yr1.pack(fill="x", padx=12, pady=(0,4))
        ctk.CTkLabel(yr1, text="Style Name", anchor="w", font=("Segoe UI",11), text_color="#aaa").grid(row=0,column=0,sticky="w")
        ctk.CTkLabel(yr1, text="   Variation Plan (A/B/C/D per section)", anchor="w", font=("Segoe UI",11), text_color="#aaa").grid(row=0,column=1,sticky="w")
        self.style_var = ctk.StringVar()
        ctk.CTkEntry(yr1, textvariable=self.style_var, placeholder_text="e.g. 8Beat Pop 2", width=190).grid(row=1,column=0,sticky="w",padx=(0,8))
        self.variation_var = ctk.StringVar()
        ctk.CTkEntry(yr1, textvariable=self.variation_var, placeholder_text="e.g. Intro1→A  Verse→B  Chorus→C  End2", width=270).grid(row=1,column=1,sticky="w")

        yr2 = ctk.CTkFrame(ysec, fg_color="transparent"); yr2.pack(fill="x", padx=12, pady=(4,4))
        ctk.CTkLabel(yr2, text="OTS #", anchor="w", font=("Segoe UI",11), text_color="#aaa").grid(row=0,column=0,sticky="w")
        ctk.CTkLabel(yr2, text="   Intro", anchor="w", font=("Segoe UI",11), text_color="#aaa").grid(row=0,column=1,sticky="w")
        ctk.CTkLabel(yr2, text="   Ending", anchor="w", font=("Segoe UI",11), text_color="#aaa").grid(row=0,column=2,sticky="w")
        ctk.CTkLabel(yr2, text="   Multi Pad Bank", anchor="w", font=("Segoe UI",11), text_color="#aaa").grid(row=0,column=3,sticky="w")
        self.ots_var    = ctk.StringVar()
        self.intro_var  = ctk.StringVar()
        self.ending_var = ctk.StringVar()
        self.mpad_var   = ctk.StringVar()
        ctk.CTkOptionMenu(yr2, variable=self.ots_var,    values=["","1","2","3","4"],       width=70).grid(row=1,column=0,sticky="w",padx=(0,6))
        ctk.CTkOptionMenu(yr2, variable=self.intro_var,  values=["","1","2","3"],           width=70).grid(row=1,column=1,sticky="w",padx=(6,6))
        ctk.CTkOptionMenu(yr2, variable=self.ending_var, values=["","1","2","3"],           width=70).grid(row=1,column=2,sticky="w",padx=(6,6))
        ctk.CTkEntry(yr2, textvariable=self.mpad_var, placeholder_text="e.g. Bank 3", width=120).grid(row=1,column=3,sticky="w",padx=(6,0))

        yr3 = ctk.CTkFrame(ysec, fg_color="transparent"); yr3.pack(fill="x", padx=12, pady=(4,8))
        ctk.CTkLabel(yr3, text="Right Hand Voice", anchor="w", font=("Segoe UI",11), text_color="#aaa").grid(row=0,column=0,sticky="w")
        ctk.CTkLabel(yr3, text="   Left Hand Voice", anchor="w", font=("Segoe UI",11), text_color="#aaa").grid(row=0,column=1,sticky="w")
        ctk.CTkLabel(yr3, text="   Split Point", anchor="w", font=("Segoe UI",11), text_color="#aaa").grid(row=0,column=2,sticky="w")
        self.voice_r_var = ctk.StringVar()
        self.voice_l_var = ctk.StringVar()
        self.split_var   = ctk.StringVar()
        ctk.CTkEntry(yr3, textvariable=self.voice_r_var, placeholder_text="e.g. Grand Piano", width=160).grid(row=1,column=0,sticky="w",padx=(0,8))
        ctk.CTkEntry(yr3, textvariable=self.voice_l_var, placeholder_text="e.g. Strings Pad", width=160).grid(row=1,column=1,sticky="w",padx=(0,8))
        ctk.CTkEntry(yr3, textvariable=self.split_var,   placeholder_text="e.g. F3",          width=90).grid(row=1,column=2,sticky="w")

        hint=("Format hint:\n  # C  G  Am  F  ← chord line\n  [Verse 1]       ← section\n  Lyric words     ← lyric")
        ctk.CTkLabel(sc,text=hint,font=("Courier New",10),text_color="#555",justify="left").pack(anchor="w",**pad)
        ctk.CTkLabel(sc,text="Chord Sheet Body *",anchor="w").pack(fill="x",**pad)
        self.body_text = ctk.CTkTextbox(sc,height=280,wrap="word",font=("Courier New",13))
        self.body_text.pack(fill="both",expand=True,**pad)
        self.body_text.insert("0.0","[Intro]\n# C  G  Am  F\n\n[Verse 1]\n# C         G\nToday is a wonderful day\n# Am        F\nEverything feels okay\n\n[Chorus]\n# F  C  G  Am\nSing it out loud\n\n[Bridge]\n# Dm  Am  Bb  F\nWhen the night falls down\n")
        ctk.CTkLabel(sc,text="Notes  (supports unicode, emoji ✨, markdown hints)",
                     font=("Segoe UI",11),text_color="#556",anchor="w").pack(fill="x",**pad)
        # Notes toolbar for quick formatting
        ntb = ctk.CTkFrame(sc, fg_color="#0d1117", corner_radius=6)
        ntb.pack(fill="x", padx=16, pady=(0,2))
        for sym, tip in [("★","Star"),("✓","Check"),("→","Arrow"),("♩","Note"),
                         ("🎸","Guitar"),("🎹","Piano"),("🎵","Music"),("⚡","Energy")]:
            b = ctk.CTkButton(ntb, text=sym, width=32, height=24,
                fg_color="transparent", hover_color="#1e2a3e",
                font=("Segoe UI",13), command=lambda s=sym: self._insert_note_sym(s))
            b.pack(side="left", padx=1, pady=2)
        self.notes_text = ctk.CTkTextbox(sc, height=80, wrap="word",
                                          font=("Segoe UI",13))
        self.notes_text.pack(fill="x", **pad)
        br = ctk.CTkFrame(sc,fg_color="transparent"); br.pack(fill="x",padx=16,pady=12)
        ctk.CTkButton(br,text="Save",command=self._save,fg_color="#2E7D32",hover_color="#388E3C").pack(side="left",padx=(0,10))
        ctk.CTkButton(br,text="Cancel",command=self.destroy,fg_color="#555",hover_color="#666").pack(side="left")

    def _insert_note_sym(self, sym):
        """Insert a symbol/emoji at cursor position in notes_text."""
        try: self.notes_text.insert("insert", sym)
        except: self.notes_text.insert("end", sym)

    def _pick_category(self):
        """Popup search/tree picker for category assignment."""
        dlg = ctk.CTkToplevel(self); dlg.title("Select Category")
        dlg.resizable(False, False); dlg.grab_set(); dlg.transient(self)
        dlg.attributes("-topmost", True)

        ctk.CTkLabel(dlg, text="Select a category:", font=("Segoe UI",11)).pack(padx=16,pady=(12,4),anchor="w")

        # Flat searchable list built from tree
        lf = ctk.CTkScrollableFrame(dlg, height=220, fg_color="#0d1117")
        lf.pack(fill="x", padx=16, pady=(0,6))

        sel_id   = [self._current_cat_id]   # mutable container
        sel_name = [self._cat_display_var.get()]

        def build_flat(cats, depth=0):
            items = [("__none__", "📂 Uncategorized", 0)]
            def _walk(lst, d):
                for c in lst:
                    icon = "📁" if d==0 else "📂"
                    items.append((c["id"], "  "*d + icon + " " + c["name"], d))
                    _walk(c.get("children",[]), d+1)
            _walk(cats, depth)
            return items

        flat = build_flat(self._categories)

        def refresh():
            for w in lf.winfo_children(): w.destroy()
            for (cid, label, depth) in flat:
                is_sel = (cid == "__none__" and sel_id[0] is None) or (cid == sel_id[0])
                row = ctk.CTkFrame(lf, fg_color="#1e3a5f" if is_sel else "transparent",
                                   cursor="hand2"); row.pack(fill="x", pady=1)
                fg = "#fff" if is_sel else ("#60a5fa" if depth==0 else "#a0c4ff")
                lbl = ctk.CTkLabel(row, text=label, font=("Segoe UI",11), anchor="w", text_color=fg)
                lbl.pack(fill="x", padx=6, pady=2)
                def _pick(c=cid, n=label):
                    sel_id[0] = None if c=="__none__" else c
                    sel_name[0] = n
                    refresh()
                for w in (row, lbl):
                    w.bind("<Button-1>",    lambda e,c=cid,n=label: _pick(c,n))
                    w.bind("<Double-Button-1>", lambda e,c=cid,n=label: (_pick(c,n), ok()))

        refresh()

        def ok():
            self._current_cat_id    = sel_id[0]
            self.result_category_id = sel_id[0]
            name = sel_name[0].strip()
            self._cat_display_var.set(name)
            dlg.destroy()

        br = ctk.CTkFrame(dlg, fg_color="transparent"); br.pack(pady=(0,12))
        ctk.CTkButton(br, text="Select", width=100, fg_color="#2E7D32",
                      hover_color="#388E3C", command=ok).pack(side="left", padx=6)
        ctk.CTkButton(br, text="Cancel", width=100, fg_color="#555",
                      hover_color="#666", command=dlg.destroy).pack(side="left")
        dlg.bind("<Return>", lambda e: ok()); dlg.bind("<Escape>", lambda e: dlg.destroy())
        center_window(dlg, 360, 360); dlg.lift()

    def _pick_artist(self, parent_widget):
        """Popup search dialog for selecting an artist."""
        dlg = ctk.CTkToplevel(self); dlg.title("Select Artist")
        dlg.resizable(False, False); dlg.grab_set(); dlg.transient(self)
        dlg.attributes("-topmost", True)

        ctk.CTkLabel(dlg, text="Search artist:", font=("Segoe UI",11)).pack(padx=16,pady=(12,4),anchor="w")
        search_var = ctk.StringVar()
        ent = ctk.CTkEntry(dlg, textvariable=search_var, width=300, placeholder_text="Type to filter…")
        ent.pack(padx=16, pady=(0,6)); ent.focus_set()

        # List frame
        lf = ctk.CTkScrollableFrame(dlg, height=200, fg_color="#0d1117")
        lf.pack(fill="x", padx=16, pady=(0,6))

        sel_var = ctk.StringVar(value=self.artist_var.get())

        all_artists = sorted([UNKNOWN_ARTIST] + [a for a in self._artists if a != UNKNOWN_ARTIST])

        def refresh(q=""):
            for w in lf.winfo_children(): w.destroy()
            q = q.strip().lower()
            matches = [a for a in all_artists if not q or q in a.lower()]
            for name in matches:
                is_sel = sel_var.get() == name
                row = ctk.CTkFrame(lf, fg_color="#1e3a5f" if is_sel else "transparent",
                                   cursor="hand2"); row.pack(fill="x", pady=1)
                lbl = ctk.CTkLabel(row, text=f"  {name}", font=("Segoe UI",11),
                                   anchor="w", text_color="#fff" if is_sel else "#ccc")
                lbl.pack(fill="x", padx=4, pady=2)
                def _pick(n=name):
                    sel_var.set(n); refresh(search_var.get())
                for w in (row, lbl): w.bind("<Button-1>", lambda e,n=name: _pick(n))
                if is_sel:
                    # Double-click confirms
                    for w in (row, lbl): w.bind("<Double-Button-1>", lambda e,n=name: (sel_var.set(n), ok()))

        refresh()
        search_var.trace_add("write", lambda *_: refresh(search_var.get()))

        def ok():
            self.artist_var.set(sel_var.get())
            dlg.destroy()

        br = ctk.CTkFrame(dlg, fg_color="transparent"); br.pack(pady=(0,12))
        ctk.CTkButton(br, text="Select", width=100, fg_color="#2E7D32",
                      hover_color="#388E3C", command=ok).pack(side="left", padx=6)
        ctk.CTkButton(br, text="Cancel", width=100, fg_color="#555",
                      hover_color="#666", command=dlg.destroy).pack(side="left")
        dlg.bind("<Return>", lambda e: ok()); dlg.bind("<Escape>", lambda e: dlg.destroy())
        center_window(dlg, 340, 340); dlg.lift()

    def _populate(self, s):
        self.title_var.set(s.get("title",""))
        artist = s.get("artist","") or UNKNOWN_ARTIST
        if artist in self._artists: self.artist_var.set(artist)
        else: self.artist_var.set(UNKNOWN_ARTIST)
        if s.get("key") in KEYS: self.key_var.set(s["key"])
        self.bpm_var.set(str(s.get("bpm",120)))
        self.body_text.delete("0.0","end"); self.body_text.insert("0.0",s.get("body",""))
        self.notes_text.delete("0.0","end"); self.notes_text.insert("0.0",s.get("notes",""))
        # Yamaha fields
        self.style_var.set(s.get("sx_style",""))
        self.variation_var.set(s.get("sx_variation",""))
        self.ots_var.set(s.get("sx_ots",""))
        self.intro_var.set(s.get("sx_intro",""))
        self.ending_var.set(s.get("sx_ending",""))
        self.mpad_var.set(s.get("sx_mpad",""))
        self.voice_r_var.set(s.get("sx_voice_r",""))
        self.voice_l_var.set(s.get("sx_voice_l",""))
        self.split_var.set(s.get("sx_split",""))
        # Refresh category label
        if self._current_cat_id:
            c = _find_cat_by_id(self._categories, self._current_cat_id)
            if c: self._cat_display_var.set(f"📁 {c['name']}")
        else:
            self._cat_display_var.set("📂 Uncategorized")

    def _save(self):
        title=self.title_var.get().strip(); body=self.body_text.get("0.0","end").strip()
        if not title: messagebox.showwarning("Missing Title","Please enter a song title.",parent=self); return
        if not body: messagebox.showwarning("Missing Content","Please enter the chord sheet.",parent=self); return
        try: bpm=int(self.bpm_var.get())
        except: bpm=120
        now=datetime.now().strftime("%Y-%m-%d %H:%M")
        capo       = self.sheet.get("capo",0)                      if self.sheet else 0
        tuning     = self.sheet.get("tuning","Standard (EADGBe)")  if self.sheet else "Standard (EADGBe)"
        difficulty = self.sheet.get("difficulty","Intermediate")   if self.sheet else "Intermediate"
        orig_body  = self.sheet.get("original_body")               if self.sheet else None
        orig_key   = self.sheet.get("original_key")                if self.sheet else None
        chord_grid = self.sheet.get("chord_grid", [])              if self.sheet else []
        favorite   = self.sheet.get("favorite", False)             if self.sheet else False
        artist = self.artist_var.get()
        if artist == UNKNOWN_ARTIST: artist = ""
        self.result={"id":self.sheet["id"] if self.sheet else new_id(),"title":title,
            "artist":artist,"key":self.key_var.get(),"tuning":tuning,"bpm":bpm,
            "capo":capo,"difficulty":difficulty,"body":body,
            "notes":self.notes_text.get("0.0","end").strip(),
            "created":self.sheet.get("created",now) if self.sheet else now,
            "modified":now,"original_body":orig_body,"original_key":orig_key,
            "chord_grid":chord_grid,"favorite":favorite,
            # Yamaha SX720 fields
            "sx_style":    self.style_var.get().strip(),
            "sx_variation":self.variation_var.get().strip(),
            "sx_ots":      self.ots_var.get(),
            "sx_intro":    self.intro_var.get(),
            "sx_ending":   self.ending_var.get(),
            "sx_mpad":     self.mpad_var.get().strip(),
            "sx_voice_r":  self.voice_r_var.get().strip(),
            "sx_voice_l":  self.voice_l_var.get().strip(),
            "sx_split":    self.split_var.get().strip(),
        }
        self.destroy()

# ── SetListFormDialog ─────────────────────────────────────────────────────────
class SetListFormDialog(ctk.CTkToplevel):
    def __init__(self,parent,all_sheets,setlist=None):
        super().__init__(parent); self.result=None; self.setlist=setlist
        self.all_sheets=sorted(all_sheets,key=lambda s:s["title"].lower())
        self._sel_ids=list(setlist.get("sheet_ids",[]) if setlist else [])
        self.title("Edit Set List" if setlist else "New Set List")
        self.resizable(True,True)
        self.grab_set()
        self._build()
        if setlist: self._populate()
        center_window(self, 700, 640)
        self.lift(); self.focus_force()

    def _build(self):
        pad={"padx":14,"pady":5}
        ctk.CTkLabel(self,text="Set List Name *",anchor="w").pack(fill="x",**pad)
        self.name_var=ctk.StringVar()
        ctk.CTkEntry(self,textvariable=self.name_var,placeholder_text="e.g. Friday Night Gig").pack(fill="x",**pad)
        r=ctk.CTkFrame(self,fg_color="transparent"); r.pack(fill="x",**pad)
        ctk.CTkLabel(r,text="Venue").grid(row=0,column=0,sticky="w")
        self.venue_var=ctk.StringVar()
        ctk.CTkEntry(r,textvariable=self.venue_var,placeholder_text="Venue name",width=220).grid(row=1,column=0)
        ctk.CTkLabel(r,text="  Date").grid(row=0,column=1,sticky="w",padx=(18,0))
        self.date_var=ctk.StringVar(value=datetime.now().strftime("%Y-%m-%d"))
        ctk.CTkEntry(r,textvariable=self.date_var,width=130).grid(row=1,column=1,padx=(18,0))
        ctk.CTkLabel(self,text="Notes",anchor="w").pack(fill="x",**pad)
        self.notes_text=ctk.CTkTextbox(self,height=48,wrap="word"); self.notes_text.pack(fill="x",**pad)
        picker=ctk.CTkFrame(self,fg_color="transparent"); picker.pack(fill="both",expand=True,**pad)
        picker.columnconfigure(0,weight=1); picker.columnconfigure(2,weight=1)
        ctk.CTkLabel(picker,text="Available Songs",font=("Segoe UI",12,"bold")).grid(row=0,column=0,pady=(0,4))
        ctk.CTkLabel(picker,text="Set List Order",font=("Segoe UI",12,"bold")).grid(row=0,column=2,pady=(0,4))
        self._avail=tk.Listbox(picker,bg="#1e1e2e",fg="#ccc",selectbackground="#1E3A5F",font=("Segoe UI",11),height=13,selectmode=tk.EXTENDED,bd=0)
        self._avail.grid(row=1,column=0,sticky="nsew")
        mid=ctk.CTkFrame(picker,fg_color="transparent",width=82); mid.grid(row=1,column=1,padx=6)
        for t,cmd in [("Add ->",self._add),("<- Remove",self._rem),("Up",self._up),("Down",self._dn)]:
            ctk.CTkButton(mid,text=t,width=80,command=cmd).pack(pady=4)
        self._order=tk.Listbox(picker,bg="#1e1e2e",fg="#ccc",selectbackground="#1E3A5F",font=("Segoe UI",11),height=13,selectmode=tk.EXTENDED,bd=0)
        self._order.grid(row=1,column=2,sticky="nsew"); self._refresh_pickers()
        br=ctk.CTkFrame(self,fg_color="transparent"); br.pack(fill="x",padx=14,pady=10)
        ctk.CTkButton(br,text="Save",command=self._save,fg_color="#2E7D32",hover_color="#388E3C").pack(side="left",padx=(0,10))
        ctk.CTkButton(br,text="Cancel",command=self.destroy,fg_color="#555",hover_color="#666").pack(side="left")

    def _populate(self):
        self.name_var.set(self.setlist.get("name","")); self.venue_var.set(self.setlist.get("venue",""))
        self.date_var.set(self.setlist.get("date","")); self.notes_text.insert("0.0",self.setlist.get("notes",""))

    def _lbl(self,sid):
        s=next((x for x in self.all_sheets if x["id"]==sid),None)
        return f"{s['title']}  -  {s.get('artist','')}" if s else f"[{sid}]"

    def _refresh_pickers(self):
        self._avail.delete(0,"end"); self._order.delete(0,"end")
        for s in self.all_sheets:
            if s["id"] not in self._sel_ids: self._avail.insert("end",f"{s['title']}  -  {s.get('artist','')}")
        for sid in self._sel_ids: self._order.insert("end",self._lbl(sid))

    def _add(self):
        avail=[s for s in self.all_sheets if s["id"] not in self._sel_ids]
        for i in self._avail.curselection():
            if i<len(avail): self._sel_ids.append(avail[i]["id"])
        self._refresh_pickers()

    def _rem(self):
        for i in reversed(self._order.curselection()):
            if i<len(self._sel_ids): self._sel_ids.pop(i)
        self._refresh_pickers()

    def _up(self):
        sel=self._order.curselection()
        if not sel or sel[0]==0: return
        for i in sel: self._sel_ids[i-1],self._sel_ids[i]=self._sel_ids[i],self._sel_ids[i-1]
        self._refresh_pickers()
        for i in sel: self._order.selection_set(i-1)

    def _dn(self):
        sel=self._order.curselection()
        if not sel or sel[-1]>=len(self._sel_ids)-1: return
        for i in reversed(sel): self._sel_ids[i],self._sel_ids[i+1]=self._sel_ids[i+1],self._sel_ids[i]
        self._refresh_pickers()
        for i in sel: self._order.selection_set(i+1)

    def _save(self):
        name=self.name_var.get().strip()
        if not name: messagebox.showwarning("Missing Name","Please enter a name.",parent=self); return
        now=datetime.now().strftime("%Y-%m-%d %H:%M")
        self.result={"id":self.setlist["id"] if self.setlist else new_id(),"name":name,"venue":self.venue_var.get().strip(),"date":self.date_var.get().strip(),"notes":self.notes_text.get("0.0","end").strip(),"sheet_ids":self._sel_ids,"created":self.setlist.get("created",now) if self.setlist else now,"modified":now}
        self.destroy()

# ── TransposeDialog ───────────────────────────────────────────────────────────
class TransposeDialog(ctk.CTkToplevel):
    def __init__(self,parent,sheet):
        super().__init__(parent)
        self.sheet=sheet; self.result_body=None; self.result_key=None
        self.title("Transpose"); self.resizable(False,False)
        self.grab_set()

        ctk.CTkLabel(self,text=f"Transpose: {sheet['title']}",
            font=("Segoe UI",14,"bold")).pack(pady=(18,4))
        ctk.CTkLabel(self,text=f"Current key: {sheet.get('key','?')}",
            text_color="#aaa").pack()

        row=ctk.CTkFrame(self,fg_color="transparent"); row.pack(pady=14)
        ctk.CTkLabel(row,text="Semitones:").pack(side="left",padx=(0,8))
        self.semi_var=ctk.IntVar(value=0)
        self._semi_lbl=ctk.CTkLabel(row,text=" 0",width=34)
        ctk.CTkSlider(row,from_=-12,to=12,number_of_steps=24,
            variable=self.semi_var,width=200,command=self._upd).pack(side="left")
        self._semi_lbl.pack(side="left")

        self.flat_var=ctk.BooleanVar(value=False)
        ctk.CTkCheckBox(self,text="Use flats",variable=self.flat_var,
            command=self._upd).pack(pady=4)

        krow=ctk.CTkFrame(self,fg_color="transparent"); krow.pack()
        ctk.CTkLabel(krow,text="New key: ",text_color="#aaa").pack(side="left")
        self._key_lbl=ctk.CTkLabel(krow,text="C",
            font=("Segoe UI",18,"bold"),text_color="#4A90D9")
        self._key_lbl.pack(side="left")
        self._upd()

        # Buttons row: Apply | Reset (if transposed) | Cancel
        br=ctk.CTkFrame(self,fg_color="transparent"); br.pack(pady=16)
        ctk.CTkButton(br,text="Apply",command=self._apply,
            fg_color="#2E7D32",hover_color="#388E3C",width=100).pack(side="left",padx=5)
        if sheet.get("original_body"):
            ctk.CTkButton(br,text="↺ Reset to Original",command=self._reset,
                fg_color="#1a3a2a",hover_color="#1e5c36",text_color="#4ade80",
                width=140).pack(side="left",padx=5)
        ctk.CTkButton(br,text="Cancel",command=self.destroy,
            fg_color="#555",hover_color="#666",width=100).pack(side="left",padx=5)

        # Height depends on whether Reset button is shown
        h = 310 if sheet.get("original_body") else 280
        center_window(self, 480, h)
        self.lift(); self.focus_force()

    def _upd(self,_=None):
        s=int(self.semi_var.get())
        self._semi_lbl.configure(text=f"{s:+d}" if s else " 0")
        cur=self.sheet.get("key","C"); idx=_note_index(cur)
        if idx!=-1:
            scale=CHROMATIC_FLAT if self.flat_var.get() else CHROMATIC_SHARP
            self._key_lbl.configure(text=scale[(idx+s)%12])

    def _apply(self):
        s=int(self.semi_var.get()); uf=self.flat_var.get()
        self.result_body=transpose_body(self.sheet.get("body",""),s,uf)
        cur=self.sheet.get("key","C"); idx=_note_index(cur)
        scale=CHROMATIC_FLAT if uf else CHROMATIC_SHARP
        self.result_key=scale[(idx+s)%12] if idx!=-1 else cur
        self.destroy()

    def _reset(self):
        """Return to original scale — sets result to original_body/original_key."""
        self.result_body = self.sheet["original_body"]
        self.result_key  = self.sheet.get("original_key","")
        self.result_reset = True   # flag so caller knows it was a reset
        self.destroy()

# ── SettingsDialog ────────────────────────────────────────────────────────────
class SettingsDialog(ctk.CTkToplevel):
    """Settings popup: artists, clock/timer toggles, font colors, port. OK / Cancel."""

    # Common named colors for font color pickers
    FONT_COLORS = [
        ("Default Blue",    "#e0f2ff"),
        ("Sky Blue",        "#60a5fa"),
        ("Cyan",            "#38bdf8"),
        ("Teal",            "#2dd4bf"),
        ("Green",           "#4ade80"),
        ("Lime",            "#a3e635"),
        ("Yellow",          "#facc15"),
        ("Amber",           "#f59e0b"),
        ("Orange",          "#fb923c"),
        ("Red",             "#f87171"),
        ("Pink",            "#f472b6"),
        ("Purple",          "#c084fc"),
        ("Slate",           "#94a3b8"),
        ("White",           "#f1f5f9"),
        ("Light Gray",      "#cbd5e1"),
        ("Gray",            "#64748b"),
    ]

    def __init__(self, parent, settings, artists, on_save):
        super().__init__(parent)
        self.title("Settings")
        self.resizable(True, True)
        self.grab_set()
        self.transient(parent)
        self._settings = dict(settings)
        self._artists  = sorted(list(artists))
        self._on_save  = on_save
        self._build()
        center_window(self, 520, 720)
        self.lift(); self.focus_force()

    def _build(self):
        # Outer scrollable so nothing gets cut off
        scroll = ctk.CTkScrollableFrame(self, fg_color="transparent")
        scroll.pack(fill="both", expand=True, padx=0, pady=0)

        def section(txt):
            ctk.CTkLabel(scroll, text=txt, font=("Segoe UI",14,"bold"),
                         text_color="#4A90D9").pack(anchor="w", padx=20, pady=(14,4))

        # ── Artists ──────────────────────────────────────────────────────────
        section("Artists")
        af = ctk.CTkFrame(scroll, fg_color="#111120", corner_radius=8)
        af.pack(fill="x", padx=20, pady=(0,6))
        self._artist_list_frame = ctk.CTkScrollableFrame(af, height=130, fg_color="#0d1117")
        self._artist_list_frame.pack(fill="x", padx=8, pady=(8,4))
        self._artist_selected = ctk.StringVar(value="")
        self._refresh_artist_list()
        btn_row = ctk.CTkFrame(af, fg_color="transparent"); btn_row.pack(fill="x", padx=8, pady=(0,8))
        ctk.CTkButton(btn_row, text="+ Add Artist", width=120, height=28,
                      fg_color="#2E7D32", hover_color="#388E3C",
                      command=self._add_artist).pack(side="left", padx=(0,6))
        ctk.CTkButton(btn_row, text="Remove Selected", width=130, height=28,
                      fg_color="#6a1a1a", hover_color="#8a2a2a",
                      command=self._remove_artist).pack(side="left")

        # ── Display Widgets ───────────────────────────────────────────────────
        section("Display Widgets")
        wf = ctk.CTkFrame(scroll, fg_color="#111120", corner_radius=8)
        wf.pack(fill="x", padx=20, pady=(0,6))

        # Clock toggle switch
        cr = ctk.CTkFrame(wf, fg_color="transparent"); cr.pack(fill="x", padx=16, pady=(12,6))
        self._clock_var = ctk.BooleanVar(value=self._settings.get("show_clock","0")=="1")
        ctk.CTkSwitch(cr, text="Clock  —  show current time (12-hr HH:MM:SS) in main window",
                      variable=self._clock_var, font=("Segoe UI",12),
                      onvalue=True, offvalue=False).pack(side="left")

        # Timer toggle switch
        tr = ctk.CTkFrame(wf, fg_color="transparent"); tr.pack(fill="x", padx=16, pady=(0,12))
        self._timer_var = ctk.BooleanVar(value=self._settings.get("show_timer","0")=="1")
        ctk.CTkSwitch(tr, text="Timer  —  show stopwatch with Start/Pause and Reset",
                      variable=self._timer_var, font=("Segoe UI",12),
                      onvalue=True, offvalue=False).pack(side="left")

        # ── Font Colors ───────────────────────────────────────────────────────
        section("Chord Sheet Font Colors")
        cf = ctk.CTkFrame(scroll, fg_color="#111120", corner_radius=8)
        cf.pack(fill="x", padx=20, pady=(0,6))

        color_names = [c[0] for c in self.FONT_COLORS]
        color_map   = {c[0]: c[1] for c in self.FONT_COLORS}
        hex_map     = {c[1]: c[0] for c in self.FONT_COLORS}

        def hex_to_name(h): return hex_map.get(h, color_names[0])
        def make_color_row(parent, label, setting_key, default_hex):
            row = ctk.CTkFrame(parent, fg_color="transparent"); row.pack(fill="x", padx=16, pady=6)
            ctk.CTkLabel(row, text=label, font=("Segoe UI",12), width=140, anchor="w").pack(side="left")
            var = ctk.StringVar(value=hex_to_name(self._settings.get(setting_key, default_hex)))
            om = ctk.CTkOptionMenu(row, variable=var, values=color_names, width=160)
            om.pack(side="left", padx=(8,8))
            # Color swatch
            swatch = ctk.CTkLabel(row, text="  ", width=28, height=22, corner_radius=4,
                                  fg_color=color_map.get(var.get(), default_hex))
            swatch.pack(side="left")
            def _upd(choice, _sw=swatch, _map=color_map):
                _sw.configure(fg_color=_map.get(choice, default_hex))
            om.configure(command=_upd)
            return var, color_map

        self._chord_color_var, self._chord_cmap = make_color_row(
            cf, "Chord text",      "chord_color",           "#e0f2ff")
        self._section_color_var, self._section_cmap = make_color_row(
            cf, "Section labels",  "section_color",         "#38bdf8")
        self._lyric_color_var, self._lyric_cmap = make_color_row(
            cf, "Lyrics",          "lyric_color",           "#94a3b8")
        self._hl_color_var, self._hl_cmap = make_color_row(
            cf, "Chord highlight", "chord_highlight_color", "#1e3a5f")
        ctk.CTkLabel(cf, text="  ↑ background highlight applied to individual chord tokens only",
                     font=("Segoe UI",10), text_color="#555").pack(anchor="w", padx=16, pady=(0,6))

        # ── Chord Grid Cell Colors ────────────────────────────────────────────
        section("Chord Grid Cell Colors")
        cgc_f = ctk.CTkFrame(scroll, fg_color="#111120", corner_radius=8)
        cgc_f.pack(fill="x", padx=20, pady=(0,6))
        cgc_inner = ctk.CTkFrame(cgc_f, fg_color="transparent")
        cgc_inner.pack(fill="x", padx=16, pady=10)
        ctk.CTkLabel(cgc_inner,
            text="Pre-define background and text colours for each chord function role\n"
                 "(Tonic, Subdominant, Dominant, Other). Applied to all chord grids.",
            font=("Segoe UI",11), text_color="#888", justify="left").pack(anchor="w")
        ctk.CTkButton(cgc_inner, text="🎨  Edit Cell Colors…", width=180, height=32,
            fg_color="#2a1a3a", hover_color="#3b2a4e",
            command=lambda: ChordCellColorDialog(self, self._settings)).pack(anchor="w", pady=(8,0))

        # ── Appearance / Theme ────────────────────────────────────────────────
        section("Appearance")
        af2 = ctk.CTkFrame(scroll, fg_color="#111120", corner_radius=8)
        af2.pack(fill="x", padx=20, pady=(0,6))
        tr2 = ctk.CTkFrame(af2, fg_color="transparent"); tr2.pack(fill="x", padx=16, pady=10)
        ctk.CTkLabel(tr2, text="Theme:", font=("Segoe UI",12), width=80, anchor="w").pack(side="left")
        self._theme_var = ctk.StringVar(value=self._settings.get("appearance","dark").capitalize())
        ctk.CTkSegmentedButton(tr2, values=["Dark","Light","System"],
            variable=self._theme_var, font=("Segoe UI",12)).pack(side="left", padx=(8,0))

        # ── Web Server Port ────────────────────────────────────────────────────
        section("Web Server Port")
        pf = ctk.CTkFrame(scroll, fg_color="#111120", corner_radius=8)
        pf.pack(fill="x", padx=20, pady=(0,6))
        self._port_var = ctk.StringVar(value=self._settings.get("flask_port","5055"))
        pr = ctk.CTkFrame(pf, fg_color="transparent"); pr.pack(fill="x", padx=12, pady=10)
        ctk.CTkEntry(pr, textvariable=self._port_var, width=100).pack(side="left")
        ctk.CTkLabel(pr, text="  (restart app to apply)",
                     font=("Segoe UI",10), text_color="#555").pack(side="left")

        # ── OK / Cancel ────────────────────────────────────────────────────────
        ctk.CTkFrame(scroll, height=1, fg_color="#222233").pack(fill="x", padx=20, pady=(8,0))
        br = ctk.CTkFrame(scroll, fg_color="transparent")
        br.pack(pady=14)
        ctk.CTkButton(br, text="OK",     width=120, fg_color="#2E7D32",
                      hover_color="#388E3C", command=self._ok).pack(side="left", padx=10)
        ctk.CTkButton(br, text="Cancel", width=120, fg_color="#444",
                      hover_color="#555",   command=self.destroy).pack(side="left", padx=10)
        self.bind("<Return>", lambda e: self._ok())
        self.bind("<Escape>", lambda e: self.destroy())

    def _refresh_artist_list(self):
        for w in self._artist_list_frame.winfo_children(): w.destroy()
        if not self._artists:
            ctk.CTkLabel(self._artist_list_frame, text="No artists added yet.",
                         text_color="#555", font=("Segoe UI",11)).pack(pady=8)
            return
        for name in sorted(self._artists):          # always alphabetical
            row = ctk.CTkFrame(self._artist_list_frame,
                               fg_color="#1e3a5f" if self._artist_selected.get()==name else "transparent",
                               cursor="hand2")
            row.pack(fill="x", pady=1)
            lbl = ctk.CTkLabel(row, text=f"  {name}",
                               font=("Segoe UI",11), anchor="w",
                               text_color="#fff" if self._artist_selected.get()==name else "#ccc")
            lbl.pack(fill="x", padx=4, pady=2)
            for w in (row, lbl):
                w.bind("<Button-1>", lambda e, n=name: (
                    self._artist_selected.set(n), self._refresh_artist_list()))

    def _add_artist(self):
        dlg = ctk.CTkToplevel(self); dlg.title("Add Artist"); dlg.resizable(False,False)
        dlg.grab_set(); dlg.transient(self)
        ctk.CTkLabel(dlg, text="Artist name:", font=("Segoe UI",12)).pack(padx=20,pady=(16,6))
        var = ctk.StringVar()
        ent = ctk.CTkEntry(dlg, textvariable=var, width=280)
        ent.pack(padx=20,pady=(0,10)); ent.focus_set()
        def ok():
            name = var.get().strip()
            if name and name != UNKNOWN_ARTIST and name not in self._artists:
                self._artists.append(name)
                self._artists.sort()            # keep alphabetical
                self._refresh_artist_list()
            dlg.destroy()
        br2 = ctk.CTkFrame(dlg,fg_color="transparent"); br2.pack(pady=(0,14))
        ctk.CTkButton(br2,text="Add",   width=80,command=ok,           fg_color="#2E7D32",hover_color="#388E3C").pack(side="left",padx=6)
        ctk.CTkButton(br2,text="Cancel",width=80,command=dlg.destroy,  fg_color="#555",   hover_color="#666").pack(side="left")
        dlg.bind("<Return>",lambda e:ok()); dlg.bind("<Escape>",lambda e:dlg.destroy())
        center_window(dlg,340,155); dlg.lift(); dlg.focus_force()

    def _remove_artist(self):
        name = self._artist_selected.get()
        if not name or name not in self._artists:
            messagebox.showinfo("Select Artist","Click an artist in the list first.",parent=self); return
        self._artists.remove(name)
        self._artist_selected.set("")
        self._refresh_artist_list()

    def _ok(self):
        try: port = str(int(self._port_var.get()))
        except: port = "5055"
        color_map = {c[0]:c[1] for c in self.FONT_COLORS}
        self._settings["show_clock"]     = "1" if self._clock_var.get()  else "0"
        self._settings["show_timer"]     = "1" if self._timer_var.get()  else "0"
        self._settings["flask_port"]     = port
        self._settings["chord_color"]    = color_map.get(self._chord_color_var.get(),   "#e0f2ff")
        self._settings["section_color"]  = color_map.get(self._section_color_var.get(), "#38bdf8")
        self._settings["lyric_color"]    = color_map.get(self._lyric_color_var.get(),   "#94a3b8")
        self._settings["chord_highlight_color"] = color_map.get(self._hl_color_var.get(), "#1e3a5f")
        theme = self._theme_var.get().lower()
        self._settings["appearance"] = theme
        ctk.set_appearance_mode(theme)
        apply_chord_cell_colors(self._settings)
        self._on_save(self._settings, self._artists)
        self.destroy()


# ── WriterDialog ──────────────────────────────────────────────────────────────
class WriterDialog(ctk.CTkToplevel):
    """Chord Writer — 3×12 pad grid.  Sound engine: numpy-accelerated synthesis
    on a dedicated synth thread; a separate playback thread handles ticks and
    chords so the metronome loop is never blocked."""

    ROOTS     = ["C","C#","D","Eb","E","F","F#","G","Ab","A","Bb","B"]
    SEMITONES = {"C":0,"C#":1,"Db":1,"D":2,"D#":3,"Eb":3,"E":4,"F":5,
                 "F#":6,"Gb":6,"G":7,"G#":8,"Ab":8,"A":9,"A#":10,"Bb":10,"B":11,
                 "Abm":8,"Ebm":3,"Bbm":10}

    DEFAULT_PADS = (
        [("C",0),("C#",1),("D",2),("Eb",3),("E",4),("F",5),
         ("F#",6),("G",7),("Ab",8),("A",9),("Bb",10),("B",11)],
        [("Cm",0),("C#m",1),("Dm",2),("Ebm",3),("Em",4),("Fm",5),
         ("F#m",6),("Gm",7),("Abm",8),("Am",9),("Bbm",10),("Bm",11)],
        [("",0)]*12,
    )
    SHORTCUTS = (
        ["q","w","e","r","t","y","u","i","o","p","[","]"],
        ["a","s","d","f","g","h","j","k","l",";","'","\\"],
        ["z","x","c","v","b","n","m",",",".","/","F1","F2"],
    )

    ALL_MAJOR = ["C","C#","D","Eb","E","F","F#","G","Ab","A","Bb","B","Db","Gb"]
    ALL_MINOR = ["Cm","C#m","Dm","Ebm","Em","Fm","F#m","Gm","Abm","Am","Bbm","Bm","Dbm","Gbm"]
    ALL_7TH   = ["C7","Cmaj7","D7","E7","F7","G7","A7","B7","Dm7","Em7","Am7","Bb7"]
    ALL_SUS   = ["Csus2","Csus4","Dsus2","Dsus4","Gsus2","Gsus4","Asus2","Asus4"]
    ALL_DIM   = ["Cdim","Ddim","Edim","Fdim","Gdim","Adim","Bdim","Cdim7","Ddim7","Adim7"]
    ALL_AUG   = ["Caug","Daug","Eaug","Faug","Gaug","Aaug","Baug"]

    INTERVALS = {
        "maj":[0,4,7],"min":[0,3,7],"7":[0,4,7,10],"maj7":[0,4,7,11],
        "m7":[0,3,7,10],"dim":[0,3,6],"dim7":[0,3,6,9],
        "aug":[0,4,8],"sus2":[0,2,7],"sus4":[0,5,7],
    }
    INSTRUMENTS = ["Piano","Electric Piano","Acoustic Guitar","Strings"]
    OCTAVES     = ["3","4","5"]
    TIME_SIGS   = ["4/4","3/4","6/8","2/4","5/4","7/8"]
    ROW_STYLE   = [
        ("#0c1f3a","#3b82f6","#93c5fd","#1a3a6a","MAJOR"),
        ("#180d2d","#a855f7","#c084fc","#271445","MINOR"),
        ("#111118","#475569","#94a3b8","#1e1e28","CUSTOM"),
    ]

    def __init__(self, parent):
        super().__init__(parent)
        self.title("🎹  Chord Writer")
        self.resizable(True, True)
        # Non-modal: no grab_set so other windows stay accessible
        self.attributes("-topmost", False)

        self._pads         = [[list(c) for c in row] for row in self.DEFAULT_PADS]
        self._instrument   = tk.StringVar(value="Piano")
        self._octave       = tk.StringVar(value="4")
        self._bpm_var      = tk.StringVar(value="120")
        self._timesig_var  = tk.StringVar(value="4/4")
        self._volume_var   = tk.DoubleVar(value=80.0)
        self._metro_running = False
        self._metro_stop    = threading.Event()
        self._tap_times     = []
        self._cvs           = [[None]*12 for _ in range(3)]
        self._bframes       = [[None]*12 for _ in range(3)]
        self._key_map       = {}
        self._notation_var  = tk.StringVar(value="")

        # ── Audio architecture ───────────────────────────────────────────────
        # _play_q  : playback thread reads WAV bytes and plays them (non-blocking)
        # _synth_q : synth thread reads chord requests, synthesises, pushes to _play_q
        # Metronome loop → _play_q directly (ticks are tiny, pre-built once)
        import queue
        self._play_q   = queue.Queue()   # items: bytes | None(stop)
        self._synth_q  = queue.Queue()   # items: dict | None(stop)
        self._stop_evt = threading.Event()
        # Pre-built tick WAV bytes (rebuilt on volume change via trace)
        self._tick_acc  = b""
        self._tick_reg  = b""
        self._rebuild_ticks()
        self._volume_var.trace_add("write", lambda *_: self._rebuild_ticks())

        self._build()
        center_window(self, 1200, 580)
        self.lift(); self.focus_force()
        self._bind_keys()
        self.protocol("WM_DELETE_WINDOW", self._on_close)

        threading.Thread(target=self._play_worker,  daemon=True).start()
        threading.Thread(target=self._synth_worker, daemon=True).start()

    # ── UI build ──────────────────────────────────────────────────────────────
    def _build(self):
        self.configure(fg_color="#07090f")

        tb = ctk.CTkFrame(self, fg_color="#0d1117", corner_radius=0, height=50)
        tb.pack(fill="x"); tb.pack_propagate(False)

        ctk.CTkLabel(tb, text="🎹  Chord Writer",
            font=("Segoe UI",15,"bold"), text_color="#60a5fa").pack(side="left", padx=14)

        def sep():
            ctk.CTkFrame(tb, width=1, fg_color="#2a3a5e").pack(
                side="left", fill="y", pady=10, padx=8)

        ctk.CTkLabel(tb, text="Instrument:", font=("Segoe UI",10),
            text_color="#64748b").pack(side="left", padx=(4,3))
        ctk.CTkOptionMenu(tb, variable=self._instrument,
            values=self.INSTRUMENTS, width=140,
            font=("Segoe UI",11)).pack(side="left")

        ctk.CTkLabel(tb, text="Octave:", font=("Segoe UI",10),
            text_color="#64748b").pack(side="left", padx=(10,3))
        ctk.CTkOptionMenu(tb, variable=self._octave,
            values=self.OCTAVES, width=65,
            font=("Segoe UI",11)).pack(side="left")

        sep()

        ctk.CTkLabel(tb, text="♩", font=("Segoe UI",16),
            text_color="#f59e0b").pack(side="left", padx=(0,4))
        ctk.CTkLabel(tb, text="BPM:", font=("Segoe UI",10),
            text_color="#64748b").pack(side="left", padx=(0,3))
        ctk.CTkEntry(tb, textvariable=self._bpm_var, width=52,
            font=("Courier New",12,"bold")).pack(side="left")

        ctk.CTkLabel(tb, text="Time:", font=("Segoe UI",10),
            text_color="#64748b").pack(side="left", padx=(8,3))
        ctk.CTkOptionMenu(tb, variable=self._timesig_var,
            values=self.TIME_SIGS, width=70,
            font=("Segoe UI",11)).pack(side="left")

        self._metro_btn = ctk.CTkButton(tb, text="▶ Start", width=88, height=30,
            fg_color="#1a3a1a", hover_color="#254525",
            text_color="#4ade80", font=("Segoe UI",10,"bold"),
            command=self._toggle_metro)
        self._metro_btn.pack(side="left", padx=8)

        self._beat_dot = ctk.CTkLabel(tb, text="●", font=("Segoe UI",18),
            text_color="#1a3a1a", width=22)
        self._beat_dot.pack(side="left")
        self._beat_num_lbl = ctk.CTkLabel(tb, text="1",
            font=("Courier New",12,"bold"), text_color="#f59e0b", width=20)
        self._beat_num_lbl.pack(side="left", padx=(0,4))

        ctk.CTkButton(tb, text="Tap", width=46, height=28,
            fg_color="#2a2a18", hover_color="#3a3a24",
            text_color="#fbbf24", font=("Segoe UI",10),
            command=self._tap_tempo).pack(side="left", padx=(0,8))

        ctk.CTkButton(tb, text="✕ Close", width=74, height=28,
            fg_color="#2a1414", hover_color="#4a2020",
            text_color="#f87171", font=("Segoe UI",10),
            command=self._on_close).pack(side="right", padx=10)

        ctk.CTkFrame(tb, width=1, fg_color="#2a3a5e").pack(
            side="right", fill="y", pady=10, padx=6)
        ctk.CTkLabel(tb, text="🔊", font=("Segoe UI",13),
            text_color="#64748b").pack(side="right", padx=(0,2))
        ctk.CTkSlider(tb, variable=self._volume_var,
            from_=0, to=100, width=110, height=16,
            button_color="#60a5fa", button_hover_color="#93c5fd",
            progress_color="#1e3a5f").pack(side="right", padx=(0,4))
        ctk.CTkLabel(tb, text="Vol:", font=("Segoe UI",10),
            text_color="#64748b").pack(side="right", padx=(8,2))

        # ── Pad grid ─────────────────────────────────────────────────────────
        main = tk.Frame(self, bg="#07090f")
        main.pack(fill="both", expand=True, padx=8, pady=(6,0))

        for r in range(3):
            bg, border, fg_text, hover, row_lbl = self.ROW_STYLE[r]
            main.rowconfigure(r, weight=1)
            lf = tk.Frame(main, bg="#07090f", width=54)
            lf.grid(row=r, column=0, sticky="nsew", padx=(0,4), pady=3)
            lf.pack_propagate(False)
            tk.Label(lf, text=row_lbl, bg="#07090f",
                fg=["#3b82f6","#a855f7","#475569"][r],
                font=("Segoe UI",8,"bold"), wraplength=46,
                justify="center").pack(expand=True)

            for c in range(12):
                label, semitone = self._pads[r][c]
                shortcut = self.SHORTCUTS[r][c] if c < 12 else ""
                main.columnconfigure(c+1, weight=1)

                active = bool(label)
                pad_bg = bg    if active else "#0e1018"
                pad_bd = border if active else "#1e2030"

                bf = tk.Frame(main, bg=pad_bd, padx=1, pady=1)
                bf.grid(row=r, column=c+1, padx=2, pady=3, sticky="nsew")
                self._bframes[r][c] = bf

                cv = tk.Canvas(bf, bg=pad_bg, highlightthickness=0, cursor="hand2")
                cv.pack(fill="both", expand=True)
                self._cvs[r][c] = cv

                nid = cv.create_text(0, 0,
                    text=label if label else "+",
                    fill=fg_text if active else "#2a3050",
                    font=("Segoe UI",12,"bold"), anchor="center",
                    tags="chord_name")
                kid = cv.create_text(0, 0,
                    text=(shortcut if len(shortcut)==1 else shortcut).upper(),
                    fill="#1e2a3a", font=("Courier New",7,"bold"),
                    anchor="ne", tags="shortcut_key")

                def _repos(e, cv=cv, nid=nid, kid=kid):
                    cv.coords(nid, e.width//2, e.height//2)
                    cv.coords(kid, e.width-3, 3)
                cv.bind("<Configure>", _repos)

                cv.bind("<Enter>",    lambda e, cv=cv, bf=bf, h=hover:
                                          (cv.configure(bg=h), bf.configure(bg="#ffffff")))
                cv.bind("<Leave>",    lambda e, cv=cv, bf=bf, pb=pad_bg, pb2=pad_bd:
                                          (cv.configure(bg=pb), bf.configure(bg=pb2)))
                cv.bind("<Button-1>", lambda e, rr=r, cc=c: self._pad_press(rr, cc))

                ctx = tk.Menu(self, tearoff=0, bg="#12182a", fg="#b0bcd0",
                    activebackground="#1e3a5f", activeforeground="#fff",
                    font=("Segoe UI",10))

                def _sub(title, chords, _ctx=ctx, _r=r, _c=c):
                    sub = tk.Menu(_ctx, tearoff=0, bg="#12182a", fg="#b0bcd0",
                        activebackground="#1e3a5f", activeforeground="#fff",
                        font=("Segoe UI",10))
                    for ch in chords:
                        sub.add_command(label=f"   {ch}",
                            command=lambda x=ch, a=_r, b=_c: self._set_pad(a,b,x))
                    _ctx.add_cascade(label=f"  {title} ▸", menu=sub)

                _sub("Major",   self.ALL_MAJOR)
                _sub("Minor",   self.ALL_MINOR)
                _sub("7th",     self.ALL_7TH)
                _sub("Sus",     self.ALL_SUS)
                _sub("Dim/Aug", self.ALL_DIM + self.ALL_AUG)
                ctx.add_separator()
                ctx.add_command(label="  ▶ Play",      command=lambda a=r,b=c: self._pad_press(a,b))
                ctx.add_command(label="  ✏ Type chord…", command=lambda a=r,b=c: self._type_chord(a,b))
                ctx.add_command(label="  ✕ Clear pad",  command=lambda a=r,b=c: self._clear_pad(a,b))
                if r < 2:
                    ctx.add_command(label="  ↺ Reset pad", command=lambda a=r,b=c: self._reset_pad(a,b))

                cv.bind("<Button-3>", lambda e, m=ctx:
                    (m.tk_popup(e.x_root, e.y_root), m.grab_release()))

                if shortcut:
                    self._key_map[shortcut.lower()] = (r, c)

        # ── Notation bar ──────────────────────────────────────────────────────
        nb = ctk.CTkFrame(self, fg_color="#090d1a", corner_radius=0, height=36)
        nb.pack(fill="x", side="bottom"); nb.pack_propagate(False)
        ctk.CTkLabel(nb, text="Notation:", font=("Segoe UI",9),
            text_color="#334155").pack(side="left", padx=(12,5))
        ctk.CTkLabel(nb, textvariable=self._notation_var,
            font=("Courier New",11,"bold"), text_color="#60a5fa",
            anchor="w").pack(side="left", fill="x", expand=True)
        ctk.CTkButton(nb, text="Copy", width=56, height=24,
            fg_color="#0e1a2e", hover_color="#162440",
            text_color="#60a5fa", font=("Segoe UI",9),
            command=self._copy_notation).pack(side="right", padx=(0,4))
        ctk.CTkButton(nb, text="Clear", width=56, height=24,
            fg_color="#131320", hover_color="#1e1e30",
            text_color="#475569", font=("Segoe UI",9),
            command=lambda: self._notation_var.set("")).pack(side="right", padx=4)

    def _bind_keys(self):
        for key, (r, c) in self._key_map.items():
            if key.startswith("f") and key[1:].isdigit():
                self.bind(f"<{key.upper()}>", lambda e,a=r,b=c: self._pad_press(a,b))
            else:
                self.bind(f"<KeyPress-{key}>",        lambda e,a=r,b=c: self._pad_press(a,b))
                self.bind(f"<KeyPress-{key.upper()}>", lambda e,a=r,b=c: self._pad_press(a,b))

    # ── Pad actions ───────────────────────────────────────────────────────────
    def _pad_press(self, r, c):
        label, semitone = self._pads[r][c]
        if not label: return
        cv = self._cvs[r][c]; bf = self._bframes[r][c]
        bg, border, _, hover, _ = self.ROW_STYLE[r]
        cv.configure(bg=hover); bf.configure(bg="#ffffff")
        self.after(170, lambda: cv.configure(bg=bg))
        self.after(170, lambda: bf.configure(bg=border))
        cur = self._notation_var.get()
        self._notation_var.set(cur + (" — " if cur else "") + label)
        self._synth_q.put({
            "semitone":   semitone,
            "intervals":  self._chord_intervals(label),
            "instrument": self._instrument.get(),
            "octave":     int(self._octave.get()),
        })

    def _set_pad(self, r, c, chord_name):
        semi = self._chord_to_semitone(chord_name)
        self._pads[r][c] = [chord_name, semi]
        bg, border, fg_text, _, _ = self.ROW_STYLE[r]
        self._cvs[r][c].itemconfigure("chord_name", text=chord_name, fill=fg_text)
        self._cvs[r][c].configure(bg=bg)
        self._bframes[r][c].configure(bg=border)

    def _clear_pad(self, r, c):
        self._pads[r][c] = ["", 0]
        self._cvs[r][c].itemconfigure("chord_name", text="+", fill="#2a3050")
        self._cvs[r][c].configure(bg="#0e1018")
        self._bframes[r][c].configure(bg="#1e2030")

    def _reset_pad(self, r, c):
        orig = self.DEFAULT_PADS[r][c]
        self._pads[r][c] = list(orig)
        bg, border, fg_text, _, _ = self.ROW_STYLE[r]
        lbl = orig[0]
        self._cvs[r][c].itemconfigure("chord_name",
            text=lbl if lbl else "+", fill=fg_text if lbl else "#2a3050")
        self._cvs[r][c].configure(bg=bg if lbl else "#0e1018")
        self._bframes[r][c].configure(bg=border if lbl else "#1e2030")

    def _type_chord(self, r, c):
        dlg = tk.Toplevel(self)
        dlg.title("Set Chord"); dlg.configure(bg="#12182a")
        dlg.resizable(False, False)
        dlg.transient(self); dlg.grab_set()
        W, H = 280, 112
        dlg.update_idletasks()
        px = self.winfo_rootx() + (self.winfo_width()  - W) // 2
        py = self.winfo_rooty() + (self.winfo_height() - H) // 2
        dlg.geometry(f"{W}x{H}+{px}+{py}")
        tk.Label(dlg, text="Enter chord name:", bg="#12182a", fg="#94a3b8",
            font=("Segoe UI",10)).pack(pady=(14,4))
        var = tk.StringVar(value=self._pads[r][c][0])
        ent = tk.Entry(dlg, textvariable=var, bg="#1e2a3a", fg="#e2e8f0",
            font=("Segoe UI",13,"bold"), insertbackground="#60a5fa",
            relief="flat", bd=6)
        ent.pack(padx=20, fill="x")
        ent.focus_set(); ent.select_range(0, "end")
        def _ok(e=None):
            v = var.get().strip()
            if v: self._set_pad(r, c, v)
            dlg.destroy()
        ent.bind("<Return>", _ok)
        tk.Button(dlg, text="  Set  ", command=_ok,
            bg="#1e3a5f", fg="#93c5fd", activebackground="#2a4a7f",
            relief="flat", font=("Segoe UI",10,"bold"),
            cursor="hand2").pack(pady=8)

    def _chord_to_semitone(self, chord_name):
        m = re.match(r'^([A-G][#b]?)', chord_name)
        return self.SEMITONES.get(m.group(1), 0) if m else 0

    def _copy_notation(self):
        txt = self._notation_var.get()
        if txt: self.clipboard_clear(); self.clipboard_append(txt)

    # ── Chord intervals ───────────────────────────────────────────────────────
    def _chord_intervals(self, chord_name):
        cn = chord_name
        if   "maj7" in cn:                       return self.INTERVALS["maj7"]
        elif "m7"   in cn:                       return self.INTERVALS["m7"]
        elif "dim7" in cn:                       return self.INTERVALS["dim7"]
        elif "dim"  in cn:                       return self.INTERVALS["dim"]
        elif "aug"  in cn:                       return self.INTERVALS["aug"]
        elif "sus4" in cn:                       return self.INTERVALS["sus4"]
        elif "sus2" in cn:                       return self.INTERVALS["sus2"]
        elif cn.endswith("7"):                   return self.INTERVALS["7"]
        elif cn.endswith("m") or (len(cn)>1 and cn[1]=="m"):
                                                 return self.INTERVALS["min"]
        else:                                    return self.INTERVALS["maj"]

    # ── Sound synthesis (numpy-accelerated) ───────────────────────────────────
    def _make_wav_bytes(self, pcm_int16, sr=44100):
        """Wrap a numpy int16 array as WAV bytes."""
        import wave, io
        out = io.BytesIO()
        with wave.open(out, "w") as wf:
            wf.setnchannels(1); wf.setsampwidth(2); wf.setframerate(sr)
            wf.writeframes(pcm_int16.tobytes())
        return out.getvalue()

    def _synth_chord(self, semitone, intervals, instrument, octave):
        """Synthesise a chord. Uses numpy; falls back to array if numpy absent."""
        vol = max(0.01, self._volume_var.get() / 100.0)
        sr  = 44100; dur = 0.9
        amp = 20000.0 * vol / max(len(intervals), 1)

        def f(s):
            return 440.0 * 2.0 ** ((s + (octave-4)*12 - 9) / 12.0)
        freqs = [f(semitone + iv) for iv in intervals]

        try:
            import numpy as np
            t   = np.linspace(0, dur, int(sr*dur), endpoint=False, dtype=np.float32)
            sig = np.zeros(len(t), dtype=np.float32)
            for freq in freqs:
                if instrument == "Piano":
                    s   = (np.sin(2*np.pi*freq*t)*0.55 +
                           np.sin(4*np.pi*freq*t)*0.25 +
                           np.sin(6*np.pi*freq*t)*0.13 +
                           np.sin(8*np.pi*freq*t)*0.07)
                    env = np.exp(-3.2*t)
                elif instrument == "Electric Piano":
                    s   = (np.sin(2*np.pi*freq*t)*0.65 +
                           np.sin(4*np.pi*freq*t)*0.22 +
                           np.sin(2*np.pi*freq*1.007*t)*0.13)
                    env = np.exp(-1.8*t)
                elif instrument == "Acoustic Guitar":
                    s   = sum(np.sin(2*np.pi*freq*k*t)/(k**1.4) for k in range(1,8))
                    env = np.exp(-5.0*t) * np.clip(t*80, 0, 1)
                else:  # Strings
                    vib = 1.0 + 0.003*np.sin(2*np.pi*5.5*t)
                    s   = (np.sin(2*np.pi*freq*vib*t)*0.70 +
                           np.sin(2*np.pi*freq*2.001*t)*0.17 +
                           np.sin(2*np.pi*freq*0.999*t)*0.13)
                    env = np.clip(t*6, 0, 1) * np.exp(-0.65*t)
                sig += s * env
            pcm = np.clip(sig * amp, -32767, 32767).astype(np.int16)
            return self._make_wav_bytes(pcm)
        except ImportError:
            # Fallback: pure stdlib (slower but works)
            import math, array
            n   = int(sr * dur)
            buf = array.array('h', [0]*n)
            for i in range(n):
                t  = i / sr
                sv = 0.0
                for freq in freqs:
                    sv += math.sin(2*math.pi*freq*t) * math.exp(-3.2*t)
                buf[i] = max(-32767, min(32767, int(sv * amp)))
            import io, wave
            out = io.BytesIO()
            with wave.open(out,"w") as wf:
                wf.setnchannels(1); wf.setsampwidth(2)
                wf.setframerate(sr); wf.writeframes(buf.tobytes())
            return out.getvalue()

    def _rebuild_ticks(self):
        """Pre-build metronome tick WAV bytes (called at init and on vol change)."""
        import math, array, io, wave
        vol = max(0.01, self._volume_var.get() / 100.0)
        def _tick(accent):
            sr = 44100; dur = 0.055
            freq = 1900 if accent else 1300
            amp  = int((28000 if accent else 18000) * vol)
            n    = int(sr * dur)
            buf  = array.array('h', [0]*n)
            for i in range(n):
                t = i/sr
                buf[i] = int(amp * math.exp(-65*t) * math.sin(2*math.pi*freq*t))
            out = io.BytesIO()
            with wave.open(out,"w") as wf:
                wf.setnchannels(1); wf.setsampwidth(2)
                wf.setframerate(sr); wf.writeframes(buf.tobytes())
            return out.getvalue()
        self._tick_acc = _tick(True)
        self._tick_reg = _tick(False)

    # ── Playback worker (plays WAV bytes — non-blocking per sound) ────────────
    def _play_worker(self):
        """Dedicated thread: receives WAV bytes, writes temp file, plays async."""
        import sys, os, tempfile
        fh = tempfile.NamedTemporaryFile(suffix=".wav", delete=False)
        tmp = fh.name; fh.close()

        def _play_file(path):
            if sys.platform == "win32":
                import winsound
                winsound.PlaySound(path,
                    winsound.SND_FILENAME | winsound.SND_ASYNC | winsound.SND_NODEFAULT)
            elif sys.platform == "darwin":
                import subprocess; subprocess.Popen(["afplay", path])
            else:
                import subprocess
                for p in ("aplay", "paplay", "ffplay"):
                    try:
                        if p == "ffplay":
                            subprocess.Popen(["ffplay","-nodisp","-autoexit",
                                              "-loglevel","quiet", path])
                        else:
                            subprocess.Popen([p, "-q", path])
                        break
                    except FileNotFoundError:
                        continue

        while not self._stop_evt.is_set():
            try:
                wav = self._play_q.get(timeout=0.05)
            except:
                continue
            if wav is None:
                break
            try:
                with open(tmp, "wb") as f: f.write(wav)
                _play_file(tmp)
            except Exception:
                pass
        try: os.unlink(tmp)
        except: pass

    # ── Synth worker (synthesises chords, drains stale requests) ─────────────
    def _synth_worker(self):
        """Dedicated thread: synthesises chords and forwards WAV to play queue.
        Drains the synth queue before synthesising so rapid presses only play
        the latest chord — no backlog, no stutter."""
        while not self._stop_evt.is_set():
            try:
                msg = self._synth_q.get(timeout=0.05)
            except:
                continue
            if msg is None:
                break
            # Drain: if more chord requests queued up while we waited, skip to last
            latest = msg
            while True:
                try:
                    latest = self._synth_q.get_nowait()
                except:
                    break
            if latest is None:
                break
            try:
                wav = self._synth_chord(
                    latest["semitone"], latest["intervals"],
                    latest["instrument"], latest["octave"])
                self._play_q.put(wav)
            except Exception:
                pass

    # ── Metronome ─────────────────────────────────────────────────────────────
    def _toggle_metro(self):
        if self._metro_running: self._stop_metro()
        else:                   self._start_metro()

    def _start_metro(self):
        try: bpm = max(20, min(300, int(self._bpm_var.get())))
        except: bpm = 120
        self._bpm_var.set(str(bpm))
        self._metro_running = True
        self._metro_stop.clear()
        self._metro_btn.configure(text="■ Stop",
            fg_color="#2d1010", text_color="#f87171")
        threading.Thread(target=self._metro_loop, args=(bpm,), daemon=True).start()

    def _stop_metro(self):
        self._metro_running = False
        self._metro_stop.set()
        self._metro_btn.configure(text="▶ Start",
            fg_color="#1a3a1a", text_color="#4ade80")
        try: self._beat_dot.configure(text_color="#1a3a1a")
        except: pass

    def _metro_loop(self, bpm):
        """Tight timing loop — only queues pre-built tick bytes, zero synthesis."""
        import time
        try:   num = int(self._timesig_var.get().split("/")[0])
        except: num = 4
        interval  = 60.0 / bpm
        beat_idx  = [0]
        nxt       = time.perf_counter()

        while not self._metro_stop.is_set():
            now = time.perf_counter()
            if now >= nxt:
                beat_idx[0] = (beat_idx[0] % num) + 1
                bn = beat_idx[0]
                self.after(0, lambda b=bn, mx=num: self._metro_flash(b, mx))
                # Tick goes straight to play queue — bypasses synth worker entirely
                self._play_q.put(self._tick_acc if bn == 1 else self._tick_reg)
                nxt += interval
            time.sleep(0.001)

    def _metro_flash(self, beat_num, beats_per_bar):
        try:
            self._beat_dot.configure(
                text_color="#f59e0b" if beat_num == 1 else "#4ade80")
            self._beat_num_lbl.configure(text=str(beat_num))
            self.after(130, lambda: self._beat_dot.configure(text_color="#1a3a1a"))
        except: pass

    def _tap_tempo(self):
        import time
        self._tap_times.append(time.time())
        self._tap_times = self._tap_times[-8:]
        if len(self._tap_times) >= 2:
            gaps = [self._tap_times[i+1]-self._tap_times[i]
                    for i in range(len(self._tap_times)-1)]
            bpm = max(20, min(300, int(round(60.0/(sum(gaps)/len(gaps))))))
            self._bpm_var.set(str(bpm))
            if self._metro_running:
                self._stop_metro(); self._start_metro()

    def _on_close(self):
        self._stop_metro()
        self._stop_evt.set()
        self._play_q.put(None)
        self._synth_q.put(None)
        self.destroy()

# ── RecycleBinDialog ──────────────────────────────────────────────────────────
class RecycleBinDialog(ctk.CTkToplevel):
    """
    Shows all songs in the Recycle Bin.
    Right-click a song for: Restore to Library, Restore to Folder, Delete Permanently.
    """
    def __init__(self, parent):
        super().__init__(parent)
        self._parent = parent
        self.title("🗑  Recycle Bin")
        self.resizable(True, True)
        self.grab_set()
        self.transient(parent)
        self._build()
        center_window(self, 640, 480)
        self.lift(); self.focus_force()

    def _build(self):
        ctk.CTkLabel(self, text="🗑  Recycle Bin",
            font=("Segoe UI",16,"bold"), text_color="#f87171").pack(pady=(14,2))
        ctk.CTkLabel(self,
            text="Right-click a song to Restore or Delete Permanently.",
            font=("Segoe UI",10), text_color="#666").pack()

        self._list_frame = ctk.CTkScrollableFrame(self, fg_color="#0d1117")
        self._list_frame.pack(fill="both", expand=True, padx=14, pady=(10,6))

        br = ctk.CTkFrame(self, fg_color="transparent"); br.pack(pady=(0,12))
        ctk.CTkButton(br, text="Empty Bin", width=120, fg_color="#6a1a1a",
            hover_color="#8a2a2a", command=self._empty_bin).pack(side="left", padx=8)
        ctk.CTkButton(br, text="Close", width=100, fg_color="#333",
            hover_color="#444", command=self.destroy).pack(side="left")

        self._refresh()

    def _refresh(self):
        for w in self._list_frame.winfo_children(): w.destroy()
        self._items = load_recycle_bin()
        if not self._items:
            ctk.CTkLabel(self._list_frame, text="Recycle Bin is empty.",
                text_color="#555", font=("Segoe UI",13)).pack(pady=30)
            return
        for item in self._items:
            d = item["data"]
            row = ctk.CTkFrame(self._list_frame, fg_color="#111827", corner_radius=6)
            row.pack(fill="x", pady=3, padx=2)
            info = ctk.CTkFrame(row, fg_color="transparent"); info.pack(fill="x", padx=10, pady=6)
            ctk.CTkLabel(info, text=d.get("title","?"),
                font=("Segoe UI",13,"bold"), anchor="w").pack(side="left")
            ctk.CTkLabel(info,
                text=f"  {d.get('artist','')}   ·   Deleted: {item['deleted_at']}",
                font=("Segoe UI",10), text_color="#666", anchor="w").pack(side="left")
            # Right-click menu
            ctx_menu = tk.Menu(self, tearoff=0, bg="#1e1e2e", fg="#ccc",
                activebackground="#1e3a5f", activeforeground="#fff",
                font=("Segoe UI",10))
            ctx_menu.add_command(label="  ♻  Restore to Library",
                command=lambda it=item: self._restore(it, CHORDS_DIR))
            ctx_menu.add_command(label="  📁  Restore to Folder…",
                command=lambda it=item: self._restore_to_folder(it))
            ctx_menu.add_separator()
            ctx_menu.add_command(label="  🗑  Delete Permanently",
                command=lambda it=item: self._delete_permanently(it))
            def _show_menu(e, m=ctx_menu):
                try: m.tk_popup(e.x_root, e.y_root)
                finally: m.grab_release()
            row.bind("<Button-3>", _show_menu)
            for child in row.winfo_children():
                child.bind("<Button-3>", _show_menu)
                for c2 in child.winfo_children():
                    c2.bind("<Button-3>", _show_menu)

    def _restore(self, item, dest_dir):
        try:
            restore_sheet_from_recycle(item, dest_dir)
            # Reload sheets in parent app
            if hasattr(self._parent, "sheets"):
                self._parent.sheets = load_all_sheets()
                self._parent._refresh_list()
            messagebox.showinfo("Restored",
                f"'{item['data'].get('title','')}' restored to library.", parent=self)
        except Exception as e:
            messagebox.showerror("Error", str(e), parent=self)
        self._refresh()

    def _restore_to_folder(self, item):
        dest = filedialog.askdirectory(title="Restore to Folder…", parent=self)
        if dest: self._restore(item, dest)

    def _delete_permanently(self, item):
        title = item["data"].get("title","?")
        if not messagebox.askyesno("Delete Permanently",
            f"Permanently delete '{title}'?\nThis CANNOT be undone.", parent=self): return
        try:
            os.remove(item["path"])
        except Exception as e:
            messagebox.showerror("Error", str(e), parent=self)
        self._refresh()

    def _empty_bin(self):
        items = load_recycle_bin()
        if not items:
            messagebox.showinfo("Empty", "Recycle Bin is already empty.", parent=self); return
        if not messagebox.askyesno("Empty Bin",
            f"Permanently delete all {len(items)} item(s)?\nThis CANNOT be undone.", parent=self): return
        for item in items:
            try: os.remove(item["path"])
            except Exception: pass
        self._refresh()


# ── ChordCellColorDialog ──────────────────────────────────────────────────────
class ChordCellColorDialog(ctk.CTkToplevel):
    """
    Sub-window for defining background + text colours for each chord role.
    Changes are saved directly into the passed settings dict and persisted.
    """
    ROLES = [
        ("tonic",       "Tonic  (I · iii · vi)",        "#1e4d2b", "#4ade80"),
        ("subdominant", "Subdominant  (IV · ii)",        "#2a2a10", "#fbbf24"),
        ("dominant",    "Dominant  (V · vii°)",          "#3a1a0a", "#f87171"),
        ("other",       "Other / Outside key",           "#0f1a2e", "#e0f2ff"),
    ]
    # A palette of quick-pick colours shown as swatches
    PALETTE_BG = [
        "#0f1a2e","#1e4d2b","#2a2a10","#3a1a0a","#1a1a3a","#2a0a2a",
        "#0a2a2a","#2a1a0a","#1e2a1e","#1a0a0a","#0a1a1a","#0a0a1a",
    ]
    PALETTE_FG = [
        "#e0f2ff","#4ade80","#fbbf24","#f87171","#60a5fa","#c084fc",
        "#38bdf8","#fb923c","#a3e635","#f472b6","#2dd4bf","#facc15",
    ]

    def __init__(self, parent, settings):
        super().__init__(parent)
        self._settings = settings
        self.title("Chord Grid Cell Colors")
        self.resizable(False, False)
        self.grab_set()
        self.transient(parent)
        self._build()
        center_window(self, 560, 520)
        self.lift(); self.focus_force()

    def _build(self):
        ctk.CTkLabel(self, text="Chord Grid Cell Colors",
            font=("Segoe UI",15,"bold"), text_color="#4A90D9").pack(pady=(16,4))
        ctk.CTkLabel(self,
            text="Click a swatch to pick that colour, or type a hex value directly.",
            font=("Segoe UI",10), text_color="#666").pack(pady=(0,8))

        sc = ctk.CTkScrollableFrame(self, fg_color="transparent")
        sc.pack(fill="both", expand=True, padx=16, pady=(0,8))

        self._bg_vars = {}
        self._fg_vars = {}
        self._bg_swatches = {}
        self._fg_swatches = {}

        for role, label, def_bg, def_fg in self.ROLES:
            saved_bg = self._settings.get("chord_cell_colors", {}).get(role, def_bg)
            saved_fg = self._settings.get("chord_cell_fg",     {}).get(role, def_fg)

            card = ctk.CTkFrame(sc, fg_color="#111120", corner_radius=8)
            card.pack(fill="x", pady=4)

            # Role label + live preview cell
            top_row = ctk.CTkFrame(card, fg_color="transparent"); top_row.pack(fill="x", padx=12, pady=(8,4))
            ctk.CTkLabel(top_row, text=label, font=("Segoe UI",12,"bold"),
                         text_color="#ccc", anchor="w").pack(side="left")
            # Live preview canvas (updates as user changes colours)
            prev_cv = tk.Canvas(top_row, width=80, height=28,
                                bg=saved_bg, highlightthickness=1,
                                highlightbackground="#3a3a5a", bd=0)
            prev_cv.pack(side="right", padx=(0,4))
            prev_lbl_id = prev_cv.create_text(40, 14, text="Am  G",
                font=("Courier New",11,"bold"), fill=saved_fg)

            # BG row
            bg_row = ctk.CTkFrame(card, fg_color="transparent"); bg_row.pack(fill="x", padx=12, pady=2)
            ctk.CTkLabel(bg_row, text="BG:", font=("Segoe UI",11), width=28, text_color="#888").pack(side="left")
            bg_var = tk.StringVar(value=saved_bg)
            bg_ent = ctk.CTkEntry(bg_row, textvariable=bg_var, width=90, font=("Courier New",11))
            bg_ent.pack(side="left", padx=(4,6))
            # BG palette swatches
            for hex_c in self.PALETTE_BG:
                sw = tk.Frame(bg_row, bg=hex_c, width=18, height=18, cursor="hand2",
                              highlightthickness=1, highlightbackground="#333")
                sw.pack(side="left", padx=1)
                sw.bind("<Button-1>", lambda e, h=hex_c, v=bg_var: v.set(h))
            # Current swatch
            cur_bg_sw = tk.Frame(bg_row, bg=saved_bg, width=22, height=22,
                                  highlightthickness=1, highlightbackground="#888")
            cur_bg_sw.pack(side="left", padx=(6,0))
            self._bg_swatches[role] = cur_bg_sw

            # FG row
            fg_row = ctk.CTkFrame(card, fg_color="transparent"); fg_row.pack(fill="x", padx=12, pady=(2,8))
            ctk.CTkLabel(fg_row, text="FG:", font=("Segoe UI",11), width=28, text_color="#888").pack(side="left")
            fg_var = tk.StringVar(value=saved_fg)
            fg_ent = ctk.CTkEntry(fg_row, textvariable=fg_var, width=90, font=("Courier New",11))
            fg_ent.pack(side="left", padx=(4,6))
            for hex_c in self.PALETTE_FG:
                sw = tk.Frame(fg_row, bg=hex_c, width=18, height=18, cursor="hand2",
                              highlightthickness=1, highlightbackground="#333")
                sw.pack(side="left", padx=1)
                sw.bind("<Button-1>", lambda e, h=hex_c, v=fg_var: v.set(h))
            cur_fg_sw = tk.Frame(fg_row, bg=saved_fg, width=22, height=22,
                                  highlightthickness=1, highlightbackground="#888")
            cur_fg_sw.pack(side="left", padx=(6,0))
            self._fg_swatches[role] = cur_fg_sw

            self._bg_vars[role] = bg_var
            self._fg_vars[role] = fg_var

            # Live update preview and swatch when entry changes
            def _upd_preview(_, _role=role, _cv=prev_cv, _lid=prev_lbl_id):
                try:
                    nb = self._bg_vars[_role].get().strip()
                    nf = self._fg_vars[_role].get().strip()
                    if nb.startswith("#") and len(nb) in (4,7):
                        _cv.configure(bg=nb)
                        self._bg_swatches[_role].configure(bg=nb)
                    if nf.startswith("#") and len(nf) in (4,7):
                        _cv.itemconfigure(_lid, fill=nf)
                        self._fg_swatches[_role].configure(bg=nf)
                except: pass

            bg_var.trace_add("write", _upd_preview)
            fg_var.trace_add("write", _upd_preview)

        # Buttons
        br = ctk.CTkFrame(self, fg_color="transparent"); br.pack(pady=(0,14))
        ctk.CTkButton(br, text="Save & Apply", width=140, fg_color="#2E7D32",
            hover_color="#388E3C", command=self._save).pack(side="left", padx=8)
        ctk.CTkButton(br, text="Reset Defaults", width=120, fg_color="#3a2a1a",
            hover_color="#4a3a2a", command=self._reset).pack(side="left", padx=4)
        ctk.CTkButton(br, text="Cancel", width=100, fg_color="#444",
            hover_color="#555", command=self.destroy).pack(side="left", padx=4)
        self.bind("<Escape>", lambda e: self.destroy())

    def _save(self):
        cc = {}; fg = {}
        for role in self._bg_vars:
            b = self._bg_vars[role].get().strip()
            f = self._fg_vars[role].get().strip()
            if b.startswith("#"): cc[role] = b
            if f.startswith("#"): fg[role] = f
        self._settings["chord_cell_colors"] = cc
        self._settings["chord_cell_fg"]     = fg
        apply_chord_cell_colors(self._settings)
        save_settings(self._settings)
        self.destroy()

    def _reset(self):
        for role, _, def_bg, def_fg in self.ROLES:
            self._bg_vars[role].set(def_bg)
            self._fg_vars[role].set(def_fg)


# ── ChordGridPanel ────────────────────────────────────────────────────────────
# Stores rows as list of dicts:
#   {"type":"section", "label":"Verse 1"}
#   {"type":"chords",  "cells":["C","G","Am","F"]}

class ChordGridPanel(ctk.CTkFrame):
    """
    3rd-column chord grid panel.
    Displays a 4-column chord grid (view mode) or full edit mode with
    drag-to-reorder, inline editing, add/delete rows.
    Data is stored in sheet["chord_grid"] and saved via save_callback.
    """
    ROW_H        = 44        # px per chord row
    SECTION_H    = 34        # px per section row
    CELL_W       = 80        # px per chord cell
    DRAG_COLOR   = "#2a2a4a"
    HANDLE_COLOR = "#333355"
    BG           = "#0d1117"
    ROW_BG       = "#111827"
    ROW_ALT      = "#0f1520"
    SEC_BG       = "#1a1a2e"
    CHORD_FG     = "#e0f2ff"
    SEC_FG       = "#38bdf8"
    ACCENT       = "#3b82f6"

    def __init__(self, master, sheet, save_callback, **kw):
        kw.setdefault("fg_color", "#0a0d14")
        kw.setdefault("corner_radius", 12)
        super().__init__(master, **kw)
        self._sheet        = sheet
        self._save_cb      = save_callback
        self._edit         = False
        self._colour_code  = True          # colour cells by chord function
        self._rows         = self._load_rows()
        self._drag         = None
        self._ac_popup     = None          # active autocomplete popup
        self._build()

    # ── data helpers ─────────────────────────────────────────────────────────

    def _load_rows(self):
        raw = self._sheet.get("chord_grid", [])
        rows = []
        for r in raw:
            if r.get("type") == "section":
                rows.append({"type":"section","label":r.get("label","")})
            else:
                cells = list(r.get("cells", ["","","",""]))
                while len(cells) < 4: cells.append("")
                rows.append({"type":"chords","cells":cells[:4]})
        return rows

    def reload(self, sheet):
        """Reload data from a (possibly updated) sheet dict."""
        self._sheet = sheet
        self._rows  = self._load_rows()
        self._render()

    def _save(self):
        import copy
        self._sheet["chord_grid"] = copy.deepcopy(self._rows)
        self._save_cb(self._sheet)

    def _duplicate_row(self, idx):
        """Insert a copy of row at idx+1."""
        import copy
        if idx < len(self._rows):
            self._rows.insert(idx + 1, copy.deepcopy(self._rows[idx]))
            self._save()
            self._render()

    # ── build ─────────────────────────────────────────────────────────────────

    def _build(self):
        # Header bar
        hdr = ctk.CTkFrame(self, fg_color="#0d1117", corner_radius=0, height=40)
        hdr.pack(fill="x"); hdr.pack_propagate(False)
        ctk.CTkLabel(hdr, text="Chord Grid",
                     font=("Segoe UI",13,"bold"), text_color="#4A90D9").pack(side="left",padx=12)
        self._mode_btn = ctk.CTkButton(hdr, text="✏ Edit", width=72, height=28,
            fg_color="#2a2a3a", hover_color="#3a3a4a",
            font=("Segoe UI",11), command=self._toggle_mode)
        self._mode_btn.pack(side="right", padx=6, pady=6)
        # Colour-code toggle
        self._cc_btn = ctk.CTkButton(hdr, text="🎨 Color", width=76, height=28,
            fg_color="#2a1a3a", hover_color="#3a2a4a",
            font=("Segoe UI",11), command=self._toggle_colour_code)
        self._cc_btn.pack(side="right", padx=(0,2), pady=6)
        self._add_chord_btn = ctk.CTkButton(hdr, text="+ Chord Row", width=96, height=28,
            fg_color="#1e3a1e", hover_color="#254525",
            font=("Segoe UI",11), command=self._add_chord_row)
        self._add_section_btn = ctk.CTkButton(hdr, text="+ Section", width=80, height=28,
            fg_color="#1a1a3a", hover_color="#252545",
            font=("Segoe UI",11), command=self._add_section_row)
        # Canvas + scrollbar
        self._canvas_frame = ctk.CTkFrame(self, fg_color="transparent")
        self._canvas_frame.pack(fill="both", expand=True)
        self._vsb = ttk.Scrollbar(self._canvas_frame, orient="vertical")
        self._canvas = tk.Canvas(self._canvas_frame,
            bg=self.BG, bd=0, highlightthickness=0,
            yscrollcommand=self._vsb.set)
        self._vsb.configure(command=self._canvas.yview)
        self._vsb.pack(side="right", fill="y")
        self._canvas.pack(side="left", fill="both", expand=True)
        self._canvas.bind("<Configure>",     lambda e: self._render())
        self._canvas.bind("<MouseWheel>",    self._on_scroll)
        self._canvas.bind("<Button-4>",      self._on_scroll)
        self._canvas.bind("<Button-5>",      self._on_scroll)
        # Inner frame inside canvas
        self._inner = tk.Frame(self._canvas, bg=self.BG)
        self._canvas_win = self._canvas.create_window((0,0), window=self._inner, anchor="nw")
        self._inner.bind("<Configure>", self._on_inner_configure)
        self._render()

    def _on_inner_configure(self, event=None):
        self._canvas.configure(scrollregion=self._canvas.bbox("all"))
        w = self._canvas.winfo_width()
        if w > 1:
            self._canvas.itemconfigure(self._canvas_win, width=w)

    def _on_scroll(self, event):
        if event.num == 4 or (hasattr(event,"delta") and event.delta > 0):
            self._canvas.yview_scroll(-2, "units")
        elif event.num == 5 or (hasattr(event,"delta") and event.delta < 0):
            self._canvas.yview_scroll(2, "units")

    # ── render ────────────────────────────────────────────────────────────────

    def _render(self):
        for w in self._inner.winfo_children(): w.destroy()
        self._row_frames = []
        for i, row in enumerate(self._rows):
            if row["type"] == "section":
                self._render_section(i, row)
            else:
                self._render_chord_row(i, row)
        if self._edit and not self._rows:
            ctk.CTkLabel(self._inner, text="No rows yet. Add a chord row or section above.",
                         text_color="#444", font=("Segoe UI",11), bg_color=self.BG
                         ).pack(pady=20)
        self._inner.update_idletasks()
        self._on_inner_configure()

    def _render_section(self, idx, row):
        """Render a section header row (full-width label)."""
        frm = tk.Frame(self._inner, bg=self.SEC_BG, height=self.SECTION_H)
        frm.pack(fill="x", pady=(2,0))
        frm.pack_propagate(False)
        self._row_frames.append(frm)

        if self._edit:
            # Drag handle
            handle = tk.Label(frm, text="⠿", bg=self.SEC_BG, fg="#4a5a8a",
                               font=("Courier New",16,"bold"), cursor="fleur", width=2)
            handle.pack(side="left", padx=(4,2))
            self._bind_drag(handle, idx)
            # Delete button packed RIGHT first
            tk.Button(frm, text="✕", bg="#2a1010", fg="#f87171",
                      relief="flat", bd=0, font=("Segoe UI",11,"bold"),
                      activebackground="#3a1a1a", activeforeground="#fca5a5",
                      cursor="hand2", padx=6,
                      command=lambda i=idx: self._delete_row(i)).pack(side="right", padx=(4,6), pady=4)
            # Editable label
            var = tk.StringVar(value=row["label"])
            ent = tk.Entry(frm, textvariable=var, bg="#1e2a3a", fg=self.SEC_FG,
                           insertbackground="#fff", relief="flat",
                           font=("Segoe UI",12,"bold"), bd=0)
            ent.pack(side="left", fill="x", expand=True, padx=4, ipady=6)
            def _on_change(name, idx=idx, var=var):
                if idx < len(self._rows):
                    self._rows[idx]["label"] = var.get()
                    self._save()
            var.trace_add("write", lambda *a, idx=idx, var=var: _on_change(None, idx, var))
        else:
            # View mode
            tk.Label(frm, text=f"[ {row['label']} ]" if row["label"] else "[ Section ]",
                     bg=self.SEC_BG, fg=self.SEC_FG,
                     font=("Segoe UI",12,"bold"), anchor="w").pack(fill="x", padx=12, pady=4)

    def _render_chord_row(self, idx, row):
        """Render a 4-cell chord row with colour-coding, duplicate, and autocomplete."""
        bg = self.ROW_BG if idx % 2 == 0 else self.ROW_ALT
        frm = tk.Frame(self._inner, bg=bg, height=self.ROW_H)
        frm.pack(fill="x", pady=(1,0))
        frm.pack_propagate(False)
        self._row_frames.append(frm)
        key = self._sheet.get("key", "")

        if self._edit:
            # Drag handle (leftmost)
            handle = tk.Label(frm, text="⠿", bg=bg, fg="#4a5a8a",
                               font=("Courier New",16,"bold"), cursor="fleur", width=2)
            handle.pack(side="left", padx=(4,0))
            self._bind_drag(handle, idx)
            # Beat counter
            beat_lbl = tk.Label(frm, text=f"{idx+1:02d}", bg=bg,
                                fg="#333d55", font=("Courier New",11), width=3)
            beat_lbl.pack(side="left", padx=(2,4))
            # Delete + Duplicate buttons packed RIGHT first
            del_btn = tk.Button(frm, text="✕", bg="#2a1010", fg="#f87171",
                      relief="flat", bd=0, font=("Segoe UI",11,"bold"),
                      activebackground="#3a1a1a", activeforeground="#fca5a5",
                      cursor="hand2", padx=5, pady=0,
                      command=lambda i=idx: self._delete_row(i))
            del_btn.pack(side="right", padx=(2,6), pady=4)
            dup_btn = tk.Button(frm, text="⧉", bg="#0e2a1e", fg="#4ade80",
                      relief="flat", bd=0, font=("Segoe UI",12),
                      activebackground="#163a28", activeforeground="#86efac",
                      cursor="hand2", padx=5, pady=0,
                      command=lambda i=idx: self._duplicate_row(i))
            dup_btn.pack(side="right", padx=(2,0), pady=4)
            # 4 chord cells with autocomplete
            cells = row["cells"]
            for ci in range(4):
                raw_val = cells[ci]
                is_dual = raw_val and "*" in raw_val
                # For colour role use first chord only
                chord_for_role = raw_val.split("*")[0].strip() if is_dual else raw_val
                role = get_chord_role(chord_for_role, key) if (self._colour_code and chord_for_role) else "other"
                cell_bg = CHORD_ROLE_COLORS.get(role, "#0f1a2e") if self._colour_code and chord_for_role else "#0f1a2e"
                cell_frm = tk.Frame(frm, bg=cell_bg, relief="flat",
                                    highlightbackground="#3b5a8a" if is_dual else "#1e2a4e",
                                    highlightthickness=1)
                cell_frm.pack(side="left", padx=3, pady=4)
                # Label row: cell number + dual indicator
                lbl_row = tk.Frame(cell_frm, bg=cell_bg)
                lbl_row.pack(anchor="nw", fill="x")
                tk.Label(lbl_row, text=f"{ci+1}", bg=cell_bg,
                         fg="#2a3a5e", font=("Segoe UI",8), anchor="w").pack(side="left", padx=2)
                if is_dual:
                    tk.Label(lbl_row, text="✦", bg=cell_bg,
                             fg="#60a5fa", font=("Segoe UI",7)).pack(side="right", padx=2)
                var = tk.StringVar(value=raw_val)
                cell_fg = CHORD_ROLE_FG.get(role, self.CHORD_FG) if (self._colour_code and chord_for_role) else self.CHORD_FG
                ent = tk.Entry(cell_frm, textvariable=var,
                               bg=cell_bg, fg=cell_fg,
                               insertbackground="#60a5fa",
                               relief="flat", bd=0, width=8,
                               font=("Courier New",12,"bold"),
                               justify="center")
                ent.pack(padx=3, pady=(0,4), ipady=2)

                def _on_cell(name, _idx=idx, _ci=ci, _var=var):
                    if _idx < len(self._rows):
                        self._rows[_idx]["cells"][_ci] = _var.get()
                        self._save()

                var.trace_add("write", lambda *a, _i=idx, _c=ci, _v=var: _on_cell(None,_i,_c,_v))

                # Autocomplete bindings
                ent.bind("<KeyRelease>", lambda e, _v=var, _e=ent: self._show_autocomplete(_v, _e))
                ent.bind("<Escape>",     lambda e: self._hide_autocomplete())
                ent.bind("<FocusOut>",   lambda e: self.after(200, self._hide_autocomplete))
                ent.bind("<Down>",       lambda e: self._ac_focus_next())
        else:
            # View mode — beat number
            beat_lbl = tk.Label(frm, text=f"{idx+1:02d}", bg=bg,
                                fg="#1e3a5f", font=("Courier New",11), width=3)
            beat_lbl.pack(side="left", padx=(8,4), pady=0)
            tk.Frame(frm, bg="#1e2a4e", width=1).pack(side="left", fill="y", pady=6)
            cells = row["cells"]
            for ci, chord in enumerate(cells):
                # Check for dual chord (Am*Dm syntax)
                dual = chord.split("*") if chord and "*" in chord else None
                chord1 = dual[0].strip() if dual else chord
                chord2 = dual[1].strip() if dual and len(dual) > 1 else None

                role1 = get_chord_role(chord1, key) if (self._colour_code and chord1) else "other"
                cell_bg1 = CHORD_ROLE_COLORS.get(role1, bg) if (self._colour_code and chord1) else bg
                cell_fg1 = CHORD_ROLE_FG.get(role1, self.CHORD_FG) if (self._colour_code and chord1) else self.CHORD_FG

                cw = self.CELL_W
                ch = self.ROW_H - 4

                if dual and chord2:
                    # ── Diagonal split cell (canvas) ─────────────────────────
                    role2   = get_chord_role(chord2, key) if self._colour_code else "other"
                    cell_bg2 = CHORD_ROLE_COLORS.get(role2, bg) if self._colour_code else bg
                    cell_fg2 = CHORD_ROLE_FG.get(role2, self.CHORD_FG) if self._colour_code else self.CHORD_FG

                    cv = tk.Canvas(frm, width=cw, height=ch,
                                   bg=bg, bd=0, highlightthickness=0)
                    cv.pack(side="left", padx=1, pady=2)

                    # Lower-left triangle  → chord1
                    cv.create_polygon(0,0, cw,ch, 0,ch,
                                      fill=cell_bg1, outline="")
                    # Upper-right triangle → chord2
                    cv.create_polygon(0,0, cw,0, cw,ch,
                                      fill=cell_bg2, outline="")
                    # Diagonal divider line
                    cv.create_line(0,0, cw,ch, fill="#2a3a5e", width=1)

                    # chord1 label — bottom-left quadrant
                    font_sz = max(8, min(11, int(cw * 0.13)))
                    cv.create_text(cw*0.28, ch*0.72, text=chord1,
                                   font=("Courier New",font_sz,"bold"),
                                   fill=cell_fg1, anchor="center")
                    # chord2 label — top-right quadrant
                    cv.create_text(cw*0.72, ch*0.28, text=chord2,
                                   font=("Courier New",font_sz,"bold"),
                                   fill=cell_fg2, anchor="center")
                    # Asterisk indicator — tiny, top-left corner
                    cv.create_text(6, 6, text="*", font=("Segoe UI",7),
                                   fill="#888", anchor="nw")
                elif chord:
                    cell_frm = tk.Frame(frm, bg=cell_bg1, width=cw)
                    cell_frm.pack(side="left", fill="y"); cell_frm.pack_propagate(False)
                    tk.Label(cell_frm, text=chord, bg=cell_bg1, fg=cell_fg1,
                             font=("Courier New",14,"bold"),
                             anchor="center").pack(expand=True, fill="both")
                else:
                    cell_frm = tk.Frame(frm, bg=bg, width=cw)
                    cell_frm.pack(side="left", fill="y"); cell_frm.pack_propagate(False)
                    tk.Label(cell_frm, text="—", bg=bg, fg="#1e2a4e",
                             font=("Courier New",12), anchor="center").pack(expand=True, fill="both")
                tk.Frame(frm, bg="#1e2a4e", width=1).pack(side="left", fill="y", pady=6)

    # ── autocomplete ─────────────────────────────────────────────────────────

    def _show_autocomplete(self, var, entry_widget):
        """Show a floating autocomplete listbox matching typed text."""
        self._hide_autocomplete()
        text = var.get().strip()
        if not text or len(text) < 1:
            return
        matches = [c for c in COMMON_CHORDS if c.lower().startswith(text.lower()) and c != text]
        if not matches:
            return
        matches = matches[:8]  # max 8 suggestions

        # Position popup below entry widget
        try:
            x = entry_widget.winfo_rootx()
            y = entry_widget.winfo_rooty() + entry_widget.winfo_height() + 2
        except Exception:
            return

        popup = tk.Toplevel(self)
        popup.wm_overrideredirect(True)
        popup.wm_geometry(f"+{x}+{y}")
        popup.configure(bg="#1e2a3e")
        popup.attributes("-topmost", True)
        self._ac_popup = popup

        lb = tk.Listbox(popup, bg="#1e2a3e", fg="#e0f2ff",
                        selectbackground="#3b82f6", selectforeground="#ffffff",
                        font=("Courier New",12,"bold"), bd=0, highlightthickness=1,
                        highlightbackground="#3b82f6", relief="flat",
                        width=12, height=len(matches))
        lb.pack()
        for m in matches:
            lb.insert("end", m)

        def _pick(event=None):
            sel = lb.curselection()
            if sel:
                var.set(lb.get(sel[0]))
                self._hide_autocomplete()

        lb.bind("<ButtonRelease-1>", _pick)
        lb.bind("<Return>", _pick)
        lb.bind("<Escape>", lambda e: self._hide_autocomplete())
        self._ac_listbox = lb

    def _hide_autocomplete(self):
        if self._ac_popup:
            try: self._ac_popup.destroy()
            except: pass
            self._ac_popup = None

    def _ac_focus_next(self):
        if self._ac_popup and self._ac_listbox:
            try:
                cur = self._ac_listbox.curselection()
                nxt = (cur[0] + 1) if cur else 0
                nxt = min(nxt, self._ac_listbox.size() - 1)
                self._ac_listbox.selection_clear(0, "end")
                self._ac_listbox.selection_set(nxt)
                self._ac_listbox.activate(nxt)
                self._ac_listbox.focus_set()
            except: pass

    def _toggle_colour_code(self):
        self._colour_code = not self._colour_code
        self._cc_btn.configure(
            fg_color="#2a1a3a" if not self._colour_code else "#3b1f5e",
            text="🎨 Color" if not self._colour_code else "🎨 Color ✓")
        self._render()

    # ── drag-to-reorder ───────────────────────────────────────────────────────

    def _bind_drag(self, widget, idx):
        widget.bind("<ButtonPress-1>",   lambda e, i=idx: self._drag_start(e, i))
        widget.bind("<B1-Motion>",       self._drag_motion)
        widget.bind("<ButtonRelease-1>", self._drag_end)

    def _drag_start(self, event, idx):
        self._drag = {"src": idx, "y_start": event.y_root, "last_idx": idx}
        # Highlight source row
        if idx < len(self._row_frames):
            self._row_frames[idx].configure(bg=self.DRAG_COLOR)

    def _drag_motion(self, event):
        if not self._drag: return
        dy    = event.y_root - self._drag["y_start"]
        steps = int(dy / 30)     # ~30px per row step
        new   = max(0, min(len(self._rows)-1, self._drag["src"] + steps))
        if new != self._drag["last_idx"]:
            # Swap rows up/down one step at a time
            cur = self._drag["last_idx"]
            direction = 1 if new > cur else -1
            while cur != new:
                nxt = cur + direction
                if 0 <= nxt < len(self._rows):
                    self._rows[cur], self._rows[nxt] = self._rows[nxt], self._rows[cur]
                    cur = nxt
            self._drag["last_idx"] = new
            self._save()
            self._render()

    def _drag_end(self, event):
        self._drag = None

    # ── edit actions ─────────────────────────────────────────────────────────

    def _toggle_mode(self):
        self._edit = not self._edit
        if self._edit:
            self._mode_btn.configure(text="👁 View", fg_color="#1e3a5f", hover_color="#243f6e")
            self._add_chord_btn.pack(side="right", padx=(0,4), pady=6)
            self._add_section_btn.pack(side="right", padx=(0,2), pady=6)
        else:
            self._mode_btn.configure(text="✏ Edit", fg_color="#2a2a3a", hover_color="#3a3a4a")
            self._add_chord_btn.pack_forget()
            self._add_section_btn.pack_forget()
        self._render()

    def _add_chord_row(self):
        self._rows.append({"type":"chords","cells":["","","",""]})
        self._save(); self._render()
        # Scroll to bottom
        self.after(50, lambda: self._canvas.yview_moveto(1.0))

    def _add_section_row(self):
        self._rows.append({"type":"section","label":""})
        self._save(); self._render()
        self.after(50, lambda: self._canvas.yview_moveto(1.0))

    def _delete_row(self, idx):
        if 0 <= idx < len(self._rows):
            del self._rows[idx]
            self._save(); self._render()


# ── Main App ──────────────────────────────────────────────────────────────────
class ChordSheetApp(ctk.CTk):
    def __init__(self):
        super().__init__()
        self.title("Chord Sheet Manager v5"); self.minsize(960,600)
        center_window(self, 1540, 860)
        self._settings    = load_settings()
        self.sheets       = load_all_sheets()
        self.setlists     = load_all_setlists()
        self.categories   = load_categories()
        self.artists      = load_artists()
        self._sel_sheet_id = None; self._sel_sl_id = None; self._mode = "chords"
        self._search_var  = ctk.StringVar()
        self._search_var.trace_add("write", lambda *_: self._refresh_list())
        self._det_tb = None; self._det_chord_var = None; self._det_lyric_var = None
        self._chord_grid_panel  = None   # ChordGridPanel instance
        self._chord_grid_visible = False  # show/hide state
        # Clock / Timer state
        self._clock_after = None
        self._timer_running = False
        self._timer_elapsed = 0
        self._timer_after = None
        self._clock_lbl = None
        self._timer_lbl = None
        self.protocol("WM_DELETE_WINDOW", self._on_quit)
        self._build_ui()
        self._refresh_list()
        self._start_clock_tick()
        self._bind_shortcuts()

    def _bind_shortcuts(self):
        """Bind global keyboard shortcuts for the main window."""
        self.bind("<Control-n>",      lambda e: self._new_item())
        self.bind("<Control-N>",      lambda e: self._new_item())
        self.bind("<Control-e>",      lambda e: self._edit_selected())
        self.bind("<Control-E>",      lambda e: self._edit_selected())
        self.bind("<Delete>",         lambda e: self._delete_selected())
        self.bind("<Control-d>",      lambda e: self._duplicate_selected())
        self.bind("<Control-D>",      lambda e: self._duplicate_selected())
        self.bind("<Control-f>",      lambda e: self._focus_search())
        self.bind("<Control-F>",      lambda e: self._focus_search())
        self.bind("<Control-comma>",  lambda e: self._open_settings())
        self.bind("<Control-h>",      lambda e: self._open_host())
        self.bind("<F5>",             lambda e: self._refresh_list())
        self.bind("<Control-t>",      lambda e: self._cycle_theme())

    def _edit_selected(self):
        if self._mode == "chords" and self._sel_sheet_id:
            s = next((x for x in self.sheets if x["id"]==self._sel_sheet_id), None)
            if s: self._edit_sheet(s)

    def _delete_selected(self):
        if self._mode == "chords" and self._sel_sheet_id:
            s = next((x for x in self.sheets if x["id"]==self._sel_sheet_id), None)
            if s: self._del_sheet(s)
        elif self._mode == "setlists" and self._sel_sl_id:
            sl = next((x for x in self.setlists if x["id"]==self._sel_sl_id), None)
            if sl: self._del_sl(sl)

    def _duplicate_selected(self):
        if self._mode == "chords" and self._sel_sheet_id:
            s = next((x for x in self.sheets if x["id"]==self._sel_sheet_id), None)
            if s: self._duplicate_sheet(s)

    def _focus_search(self):
        """Focus the search box."""
        try:
            for w in self._sb.winfo_children():
                if isinstance(w, ctk.CTkEntry):
                    w.focus_set(); return
        except: pass

    def _cycle_theme(self):
        """Cycle Dark → Light → System → Dark."""
        cur = self._settings.get("appearance","dark")
        nxt = {"dark":"light","light":"system","system":"dark"}.get(cur,"dark")
        self._settings["appearance"] = nxt
        ctk.set_appearance_mode(nxt)
        save_settings(self._settings)

    def _on_quit(self):
        stop_flask_server()
        self.destroy()

    def _build_ui(self):
        # ── Top bar ───────────────────────────────────────────────────────────
        top = ctk.CTkFrame(self, corner_radius=0, height=56, fg_color="#0d1117")
        top.pack(fill="x"); top.pack_propagate(False)
        ctk.CTkLabel(top, text="🎸 Chord Sheet Manager",
                     font=("Segoe UI",18,"bold"), text_color="#4A90D9").pack(side="left", padx=16)
        self._seg = ctk.CTkSegmentedButton(top, values=["Chord Sheets","Set Lists"],
                                           command=self._switch_mode, font=("Segoe UI",13))
        self._seg.set("Chord Sheets"); self._seg.pack(side="left", padx=20)
        self._new_btn = ctk.CTkButton(top, text="+ New Sheet", width=136,
                                      fg_color="#2E7D32", hover_color="#388E3C", command=self._new_item)
        self._new_btn.pack(side="right", padx=8, pady=8)
        ctk.CTkButton(top, text="Host", width=68, fg_color="#5A189A",
                      hover_color="#6A1FAC", command=self._open_host).pack(side="right", padx=(0,4), pady=8)
        ctk.CTkButton(top, text="🎹 Writer", width=92, fg_color="#0e3a4a",
                      hover_color="#154f66", text_color="#38bdf8",
                      command=self._open_writer).pack(side="right", padx=(0,4), pady=8)
        ctk.CTkButton(top, text="⚙ Settings", width=90, fg_color="#2a2a3a",
                      hover_color="#3a3a4a", command=self._open_settings).pack(side="right", padx=(0,4), pady=8)
        ctk.CTkButton(top, text="📂 Import", width=82, fg_color="#1a2a3a",
                      hover_color="#243040", command=self._import_library).pack(side="right", padx=(0,4), pady=8)
        ctk.CTkButton(top, text="📦 Export", width=82, fg_color="#1a2a3a",
                      hover_color="#243040", command=self._export_library).pack(side="right", padx=(0,4), pady=8)

        # ── Clock / Timer status row (hidden until enabled) ───────────────────
        self._status_row = ctk.CTkFrame(self, corner_radius=0, height=34, fg_color="#080c14")
        # Only pack if either is enabled — handled in _start_clock_tick
        self._clock_lbl = ctk.CTkLabel(self._status_row, text="",
                                       font=("Courier New",14,"bold"), text_color="#4ade80")
        self._clock_lbl.pack(side="left", padx=(16,32))
        # Timer widgets
        self._timer_lbl = ctk.CTkLabel(self._status_row, text="00:00:00",
                                       font=("Courier New",14,"bold"), text_color="#f59e0b")
        self._timer_lbl.pack(side="left", padx=(0,8))
        self._timer_start_btn = ctk.CTkButton(self._status_row, text="▶ Start", width=78, height=24,
            font=("Segoe UI",10,"bold"), fg_color="#1a3a1a", hover_color="#254525",
            text_color="#4ade80", command=self._timer_toggle)
        self._timer_start_btn.pack(side="left", padx=(0,4))
        self._timer_reset_btn = ctk.CTkButton(self._status_row, text="↺ Reset", width=66, height=24,
            font=("Segoe UI",10), fg_color="#2a2a3a", hover_color="#3a3a4a",
            command=self._timer_reset)
        self._timer_reset_btn.pack(side="left")

        # ── Creator credit footer ────────────────────────────────────────────
        foot = ctk.CTkFrame(self, corner_radius=0, height=22, fg_color="#07090f")
        foot.pack(fill="x", side="bottom"); foot.pack_propagate(False)
        ctk.CTkLabel(foot,
            text=f"✦  Developed by {CREATOR_NAME}   ·   Chord Sheet Manager {APP_VERSION}   ·   © 2025",
            font=("Segoe UI", 9), text_color="#2a3a5e").pack(side="left", padx=12)

        # Use a PanedWindow so the 3rd column is drag-resizable
        self._main_pane = ctk.CTkFrame(self, fg_color="transparent")
        self._main_pane.pack(fill="both", expand=True, padx=10, pady=8)
        self._sb = ctk.CTkFrame(self._main_pane, width=316, corner_radius=12)
        self._sb.pack(side="left", fill="y", padx=(0,8)); self._sb.pack_propagate(False)
        ctk.CTkEntry(self._sb, textvariable=self._search_var,
                     placeholder_text="Search…", height=34).pack(fill="x", padx=10, pady=(10,4))

        # Artist filter (replaces key filter)
        self._flt_frame = ctk.CTkFrame(self._sb, fg_color="transparent")
        self._flt_frame.pack(fill="x", padx=10, pady=(0,4))
        self._flt_artist = ctk.StringVar(value="All Artists")
        self._flt_artist.trace_add("write", lambda *_: self._refresh_list())
        self._flt_artist_menu = ctk.CTkOptionMenu(self._flt_frame, variable=self._flt_artist,
                          values=["All Artists"] + sorted(self.artists),
                          width=290, height=26,
                          font=("Segoe UI",11))
        self._flt_artist_menu.pack(side="left")

        # Category toolbar
        self._cat_toolbar = ctk.CTkFrame(self._sb, fg_color="transparent")
        self._cat_toolbar.pack(fill="x", padx=8, pady=(0,2))
        ctk.CTkButton(self._cat_toolbar, text="+ Category", width=290, height=26,
                      font=("Segoe UI",10), fg_color="#2a2a3a", hover_color="#3a3a4a",
                      command=self._cat_new_root).pack(fill="x")

        # Tree frame
        self._tree_frame = ctk.CTkFrame(self._sb, fg_color="#111120", corner_radius=8)
        self._tree_frame.pack(fill="both", expand=True, padx=6, pady=(2,2))

        # Flat list frame for setlists
        self._list_frame = ctk.CTkScrollableFrame(self._sb, label_text="")

        self._stats_var = ctk.StringVar()
        ctk.CTkLabel(self._sb, textvariable=self._stats_var,
                     font=("Segoe UI",11), text_color="#555").pack(pady=4)

        # Right area: detail + chord-grid in a horizontal PanedWindow (drag-resizable)
        self._right_pane = tk.PanedWindow(self._main_pane,
            orient=tk.HORIZONTAL, sashwidth=6, sashrelief="flat",
            bg="#1a1a2e", bd=0, handlepad=60, handlesize=8)
        self._right_pane.pack(side="left", fill="both", expand=True)

        # Column 2: detail
        self._detail = ctk.CTkFrame(self._right_pane, corner_radius=12)
        self._right_pane.add(self._detail, minsize=300, stretch="always")

        # Column 3: chord grid (not added to pane until toggled)
        self._cg_pane = ctk.CTkFrame(self._right_pane, corner_radius=12, fg_color="#0a0d14")
        # Added/removed from _right_pane dynamically via _show/_hide_chord_grid

        self._build_tree()
        self._update_status_row()
        self._show_welcome()

    # ── Clock / Timer ─────────────────────────────────────────────────────────
    def _update_status_row(self):
        show_c = self._settings.get("show_clock","0") == "1"
        show_t = self._settings.get("show_timer","0") == "1"
        if not show_c and not show_t:
            self._status_row.pack_forget()
            return
        # Ensure status row is packed between topbar and pane
        # Temporarily hide pane, pack status_row, re-show pane
        self._main_pane.pack_forget()
        self._status_row.pack(fill="x")
        self._main_pane.pack(fill="both", expand=True, padx=10, pady=8)
        # Show/hide individual widgets
        self._clock_lbl.pack_forget()
        self._timer_lbl.pack_forget()
        self._timer_start_btn.pack_forget()
        self._timer_reset_btn.pack_forget()
        if show_c:
            self._clock_lbl.pack(side="left", padx=(16,32))
        if show_t:
            self._timer_lbl.pack(side="left", padx=(0,8))
            self._timer_start_btn.pack(side="left", padx=(0,4))
            self._timer_reset_btn.pack(side="left")

    def _start_clock_tick(self):
        if self._clock_after:
            try: self.after_cancel(self._clock_after)
            except: pass
        self._tick_clock()

    def _tick_clock(self):
        if self._settings.get("show_clock","0") == "1":
            self._clock_lbl.configure(text=datetime.now().strftime("🕐  %I:%M:%S %p"))
        self._clock_after = self.after(1000, self._tick_clock)

    def _timer_toggle(self):
        if self._timer_running:
            self._timer_running = False
            if self._timer_after:
                try: self.after_cancel(self._timer_after)
                except: pass
                self._timer_after = None
            self._timer_start_btn.configure(text="▶ Resume")
        else:
            self._timer_running = True
            self._timer_start_btn.configure(text="⏸ Pause")
            self._tick_timer()

    def _tick_timer(self):
        if not self._timer_running: return
        self._timer_elapsed += 1
        h,rem = divmod(self._timer_elapsed,3600); m,s = divmod(rem,60)
        self._timer_lbl.configure(text=f"{h:02d}:{m:02d}:{s:02d}")
        self._timer_after = self.after(1000, self._tick_timer)

    def _timer_reset(self):
        self._timer_running = False
        if self._timer_after:
            try: self.after_cancel(self._timer_after)
            except: pass
            self._timer_after = None
        self._timer_elapsed = 0
        self._timer_lbl.configure(text="00:00:00")
        self._timer_start_btn.configure(text="▶ Start")

    # ── Settings dialog ───────────────────────────────────────────────────────
    def _open_settings(self):
        SettingsDialog(self, self._settings, self.artists, self._on_settings_saved)

    def _on_settings_saved(self, new_settings, new_artists):
        self._settings  = new_settings
        self.artists    = new_artists
        save_settings(new_settings)
        save_artists(new_artists)
        # Refresh artist filter dropdown
        self._flt_artist_menu.configure(values=["All Artists"] + sorted(self.artists))
        # Rebuild status row visibility
        self._update_status_row()
        self._start_clock_tick()
        if new_settings.get("show_timer","0") != "1":
            self._timer_reset()

    # ── File menu actions ─────────────────────────────────────────────────────
    def _export_library(self):
        path = filedialog.asksaveasfilename(
            defaultextension=".zip", filetypes=[("ZIP Archive","*.zip")],
            initialfile="chord_library.zip", title="Export Library")
        if not path: return
        try:
            export_library_zip(path)
            messagebox.showinfo("Exported",
                f"Library exported:\n  {len(self.sheets)} songs\n  {len(self.setlists)} set lists\n→ {path}", parent=self)
        except Exception as e:
            messagebox.showerror("Export Error", str(e), parent=self)

    def _import_library(self):
        path = filedialog.askopenfilename(
            filetypes=[("ZIP Archive","*.zip")], title="Import Library")
        if not path: return
        if not messagebox.askyesno("Import Library",
                "This will overwrite all current songs, set lists, categories and artists.\nContinue?",
                parent=self): return
        try:
            self.sheets, self.setlists, self.categories, self.artists = import_library_zip(path)
            self._refresh_list()
            messagebox.showinfo("Imported",
                f"Library imported:\n  {len(self.sheets)} songs\n  {len(self.setlists)} set lists", parent=self)
        except Exception as e:
            messagebox.showerror("Import Error", str(e), parent=self)

    # Keep old _export/_import for backward compat (now no-op aliases)
    def _export(self): self._export_library()
    def _import(self): self._import_library()
    def _build_tree(self):
        style = ttk.Style()
        style.theme_use("default")
        style.configure("CSM.Treeview",
            background="#111120", foreground="#cccccc",
            fieldbackground="#111120", rowheight=28,
            font=("Segoe UI",11), borderwidth=0)
        style.configure("CSM.Treeview.Heading",
            background="#0d1117", foreground="#4A90D9",
            font=("Segoe UI",10,"bold"), borderwidth=0)
        style.map("CSM.Treeview",
            background=[("selected","#1e3a5f")],
            foreground=[("selected","#ffffff")])
        vsb = ttk.Scrollbar(self._tree_frame, orient="vertical")
        self._tree = ttk.Treeview(self._tree_frame, style="CSM.Treeview",
            selectmode="browse", show="tree", yscrollcommand=vsb.set)
        vsb.configure(command=self._tree.yview)
        vsb.pack(side="right", fill="y")
        self._tree.pack(side="left", fill="both", expand=True)
        self._tree.column("#0", width=270, minwidth=160)
        self._tree.bind("<<TreeviewSelect>>", self._on_tree_select)
        self._tree.bind("<Button-3>", self._on_tree_right_click)

    def _collect_expanded(self, parent=""):
        out = set()
        children = self._tree.get_children(parent)
        for iid in children:
            if self._tree.item(iid, "open"): out.add(iid)
            out |= self._collect_expanded(iid)
        return out

    def _populate_tree(self):
        expanded = self._collect_expanded()
        for iid in self._tree.get_children(): self._tree.delete(iid)

        q   = self._search_var.get().strip().lower()
        fa  = self._flt_artist.get()

        def matches(s):
            artist = s.get("artist","") or UNKNOWN_ARTIST
            if q and q not in s["title"].lower() and q not in artist.lower(): return False
            if fa != "All Artists":
                # match by artist name or UNKNOWN_ARTIST
                if fa == UNKNOWN_ARTIST:
                    if s.get("artist","").strip(): return False
                else:
                    if artist != fa: return False
            return True

        self._tree.tag_configure("cat",     foreground="#4A90D9", font=("Segoe UI",11,"bold"))
        self._tree.tag_configure("subcat",  foreground="#60a5fa", font=("Segoe UI",10,"bold"))
        self._tree.tag_configure("song",    foreground="#cccccc", font=("Segoe UI",11))
        self._tree.tag_configure("sel",     foreground="#ffffff", background="#1e3a5f", font=("Segoe UI",11,"bold"))
        self._tree.tag_configure("fav",     foreground="#fbbf24", font=("Segoe UI",11))
        self._tree.tag_configure("fav_sel", foreground="#fde68a", background="#1e3a5f", font=("Segoe UI",11,"bold"))
        self._tree.tag_configure("cat_unc", foreground="#666",    font=("Segoe UI",11,"bold"))

        total_shown = [0]

        def song_label(s):
            artist = s.get("artist","") or UNKNOWN_ARTIST
            star = " ★" if s.get("favorite") else ""
            return f"   ♪  {s['title']}  —  {artist}{star}"

        def song_tag(s):
            fav = bool(s.get("favorite"))
            sel = s["id"] == self._sel_sheet_id
            if fav and sel: return ("fav_sel",)
            if fav:         return ("fav",)
            if sel:         return ("sel",)
            return ("song",)

        def insert_songs(parent_iid, cat):
            for sid in cat.get("sheet_ids",[]):
                s = next((x for x in self.sheets if x["id"]==sid), None)
                if s and matches(s):
                    self._tree.insert(parent_iid, "end", iid="song_"+s["id"],
                        text=song_label(s), tags=song_tag(s))
                    total_shown[0] += 1

        def insert_cat(parent_iid, cat, depth=0):
            icon = "📁" if depth == 0 else "📂"
            cid  = "cat_" + cat["id"]
            self._tree.insert(parent_iid, "end", iid=cid,
                text=f"{icon}  {cat['name']}",
                open=(cid in expanded or not expanded),
                tags=("cat" if depth==0 else "subcat",))
            insert_songs(cid, cat)
            for child in cat.get("children",[]):
                insert_cat(cid, child, depth+1)

        for cat in self.categories:
            insert_cat("", cat)

        # Uncategorized
        cat_ids = _all_cat_sheet_ids(self.categories)
        uncat = sorted([s for s in self.sheets if s["id"] not in cat_ids and matches(s)],
                       key=lambda s: s["title"].lower())
        if uncat:
            unc_iid = "cat_uncategorized"
            self._tree.insert("", "end", iid=unc_iid,
                text="📂  Uncategorized",
                open=(unc_iid in expanded or not expanded), tags=("cat_unc",))
            for s in uncat:
                self._tree.insert(unc_iid, "end", iid="song_"+s["id"],
                    text=song_label(s), tags=song_tag(s))
                total_shown[0] += 1

        if self._sel_sheet_id:
            try: self._tree.selection_set("song_"+self._sel_sheet_id)
            except Exception: pass

        self._stats_var.set(f"{total_shown[0]} / {len(self.sheets)} sheets")

    def _on_tree_select(self, event=None):
        sel = self._tree.selection()
        if not sel: return
        iid = sel[0]
        if not iid.startswith("song_"): return
        sid = iid[5:]
        if sid == self._sel_sheet_id: return
        self._sel_sheet_id = sid
        s = next((x for x in self.sheets if x["id"]==sid), None)
        if s:
            update_hosted_song(s)
            self._sheet_detail(s)

    def _on_tree_right_click(self, event):
        iid = self._tree.identify_row(event.y)
        if not iid: return
        self._tree.selection_set(iid)

        MN = lambda: tk.Menu(self, tearoff=0, bg="#1e1e2e", fg="#ccc",
                             activebackground="#1e3a5f", activeforeground="#fff",
                             font=("Segoe UI",10))
        menu = MN()

        if iid.startswith("song_"):
            # ── Song context menu ──
            sid = iid[5:]
            s = next((x for x in self.sheets if x["id"]==sid), None)
            if not s: return
            fav = bool(s.get("favorite"))
            menu.add_command(label=f"♪  {s['title']}", state="disabled")
            menu.add_separator()
            menu.add_command(label="  ★  Mark as Favourite" if not fav else "  ☆  Remove Favourite",
                command=lambda: self._toggle_favorite(s))
            menu.add_separator()
            menu.add_command(label="  ✏  Edit Song",   command=lambda: self._edit_sheet(s))
            menu.add_command(label="  🗑  Delete Song", command=lambda: self._del_sheet(s))
            menu.add_separator()
            menu.add_command(label="  Move to …", state="disabled")
            def _add_move_targets(submenu, cats, indent=0):
                for c in cats:
                    label = "  " * indent + f"📁 {c['name']}"
                    submenu.add_command(label=label,
                        command=lambda _c=c,_s=s: self._assign_to_cat(_s, _c))
                    _add_move_targets(submenu, c.get("children",[]), indent+1)
            _add_move_targets(menu, self.categories)
            menu.add_command(label="  📂 Uncategorized",
                command=lambda _s=s: self._assign_to_cat(_s, None))

        elif iid == "cat_uncategorized":
            menu.add_command(label="📂 Uncategorized", state="disabled")
            menu.add_separator()
            menu.add_command(label="  ＋ Add Top-Level Category",
                command=self._cat_new_root)

        elif iid.startswith("cat_"):
            cid = iid[4:]
            cat = _find_cat_by_id(self.categories, cid)
            if not cat: return
            menu.add_command(label=f"📁  {cat['name']}", state="disabled")
            menu.add_separator()
            menu.add_command(label="  ＋ Add Sub-Category",
                command=lambda: self._cat_new_sub(cid))
            menu.add_command(label="  ✎  Rename",
                command=lambda: self._cat_rename_by_id(cid))
            menu.add_separator()
            menu.add_command(label="  ＋ Add Top-Level Category",
                command=self._cat_new_root)
            menu.add_separator()
            menu.add_command(label="  🗑  Delete Category",
                command=lambda: self._cat_delete_by_id(cid))

        try: menu.tk_popup(event.x_root, event.y_root)
        finally: menu.grab_release()

    def _assign_to_cat(self, s, cat_or_none):
        _remove_sheet_from_all_cats(self.categories, s["id"])
        if cat_or_none:
            cat_or_none.setdefault("sheet_ids",[])
            if s["id"] not in cat_or_none["sheet_ids"]:
                cat_or_none["sheet_ids"].append(s["id"])
        save_categories(self.categories); self._populate_tree()

    def _toggle_favorite(self, s):
        idx = next((i for i,x in enumerate(self.sheets) if x["id"]==s["id"]), None)
        if idx is None: return
        self.sheets[idx]["favorite"] = not bool(self.sheets[idx].get("favorite"))
        save_sheet(self.sheets[idx])
        self._populate_tree()
        # Refresh detail header if this song is selected
        if self._sel_sheet_id == s["id"]:
            self._sheet_detail(self.sheets[idx])

    # ── Category CRUD ─────────────────────────────────────────────────────────
    def _cat_new_root(self):
        name = self._prompt("New Category", "Enter category name:")
        if not name: return
        self.categories.append({"id": new_id(), "name": name.strip(),
                                 "sheet_ids": [], "children": []})
        save_categories(self.categories); self._populate_tree()

    def _cat_new_sub(self, parent_cid):
        parent = _find_cat_by_id(self.categories, parent_cid)
        if not parent: return
        name = self._prompt("New Sub-Category",
                            f"Sub-category under '{parent['name']}':")
        if not name: return
        parent.setdefault("children",[]).append(
            {"id": new_id(), "name": name.strip(), "sheet_ids": [], "children": []})
        save_categories(self.categories); self._populate_tree()

    def _cat_rename_by_id(self, cid):
        cat = _find_cat_by_id(self.categories, cid)
        if not cat: return
        name = self._prompt("Rename", f"New name for '{cat['name']}':", default=cat["name"])
        if not name: return
        cat["name"] = name.strip(); save_categories(self.categories); self._populate_tree()

    def _cat_delete_by_id(self, cid):
        cat = _find_cat_by_id(self.categories, cid)
        if not cat: return
        if not messagebox.askyesno("Delete",
                f"Delete '{cat['name']}' and all its sub-categories?\nSongs move to Uncategorized.",
                parent=self): return
        _remove_cat_by_id(self.categories, cid)
        save_categories(self.categories); self._populate_tree()

    # Keep old toolbar hooks (now only root new is in toolbar)
    def _cat_new(self):   self._cat_new_root()
    def _cat_rename(self): pass
    def _cat_delete(self): pass

    def _prompt(self, title, prompt, default=""):
        dlg = ctk.CTkToplevel(self); dlg.title(title); dlg.resizable(False,False)
        dlg.grab_set()
        ctk.CTkLabel(dlg, text=prompt, font=("Segoe UI",12)).pack(padx=20, pady=(16,6))
        var = ctk.StringVar(value=default)
        ent = ctk.CTkEntry(dlg, textvariable=var, width=280)
        ent.pack(padx=20, pady=(0,10)); ent.focus_set(); ent.select_range(0,"end")
        result = [None]
        def ok():     result[0] = var.get().strip(); dlg.destroy()
        def cancel(): dlg.destroy()
        br = ctk.CTkFrame(dlg, fg_color="transparent"); br.pack(pady=(0,14))
        ctk.CTkButton(br,text="OK",    width=80,command=ok,    fg_color="#2E7D32",hover_color="#388E3C").pack(side="left",padx=6)
        ctk.CTkButton(br,text="Cancel",width=80,command=cancel,fg_color="#555",   hover_color="#666").pack(side="left")
        dlg.bind("<Return>",lambda e:ok()); dlg.bind("<Escape>",lambda e:cancel())
        center_window(dlg,340,160); dlg.lift(); dlg.focus_force()
        dlg.wait_window()
        return result[0]

    # ── Mode switching ────────────────────────────────────────────────────────
    def _switch_mode(self, val):
        self._mode = "setlists" if "Set" in val else "chords"
        self._sel_sheet_id = None; self._sel_sl_id = None
        self._new_btn.configure(text="+ New Set List" if self._mode=="setlists" else "+ New Sheet")
        # Hide chord grid when switching away from chord sheets
        self._hide_chord_grid()
        if self._mode == "setlists":
            self._flt_frame.pack_forget()
            self._cat_toolbar.pack_forget()
            self._tree_frame.pack_forget()
            self._list_frame.pack(fill="both", expand=True, padx=6, pady=2)
        else:
            self._list_frame.pack_forget()
            self._flt_frame.pack(fill="x", padx=10, pady=(0,4))
            self._cat_toolbar.pack(fill="x", padx=8, pady=(0,2))
            self._tree_frame.pack(fill="both", expand=True, padx=6, pady=(2,2))
        self._refresh_list(); self._show_welcome()

    def _refresh_list(self):
        if self._mode == "chords":
            self._populate_tree()
        else:
            for w in self._list_frame.winfo_children(): w.destroy()
            self._render_setlists()

    def _render_sheets(self):
        """Legacy — now delegates to tree."""
        self._populate_tree()

    def _render_setlists(self):
        q=self._search_var.get().strip().lower()
        filtered=sorted([sl for sl in self.setlists if not q or q in sl["name"].lower() or q in sl.get("venue","").lower()],key=lambda sl:sl["name"].lower())
        for sl in filtered: self._sl_card(sl)
        self._stats_var.set(f"{len(filtered)} / {len(self.setlists)} set lists")

    def _sheet_card(self,s):
        """Legacy flat card — kept for compatibility but not used in tree mode."""
        pass

    def _sl_card(self,sl):
        sel=sl["id"]==self._sel_sl_id; cnt=len(sl.get("sheet_ids",[]))
        c=ctk.CTkFrame(self._list_frame,corner_radius=8,cursor="hand2",fg_color="#2a1e3a" if sel else "#1e1e2e",border_width=2 if sel else 0,border_color="#7B68EE")
        c.pack(fill="x",padx=4,pady=3)
        t=ctk.CTkLabel(c,text=sl["name"],font=("Segoe UI",13,"bold"),anchor="w",text_color="#eee"); t.pack(fill="x",padx=10,pady=(7,0))
        a=ctk.CTkLabel(c,text=f"{sl.get('date','---')}  -  {sl.get('venue','---')}  -  {cnt} songs",font=("Segoe UI",11),text_color="#888",anchor="w"); a.pack(fill="x",padx=10,pady=(0,6))
        for w in (c,t,a):
            w.bind("<Button-1>",lambda e,slid=sl["id"]: self._sel_setlist(slid))

    def _sel_sheet(self,sid):
        self._sel_sheet_id=sid
        self._populate_tree()
        s=next((x for x in self.sheets if x["id"]==sid),None)
        if s: update_hosted_song(s); self._sheet_detail(s)

    def _sel_setlist(self,slid):
        self._sel_sl_id=slid; self._refresh_list()
        sl=next((x for x in self.setlists if x["id"]==slid),None)
        if sl: self._sl_detail(sl)

    def _show_welcome(self):
        self._hide_chord_grid()
        for w in self._detail.winfo_children(): w.destroy()
        ctk.CTkLabel(self._detail,text="SET LISTS" if self._mode=="setlists" else "CHORD SHEETS",font=("Segoe UI",14,"bold"),text_color="#333").pack(expand=True)
        ctk.CTkLabel(self._detail,text="Select an item or create a new one",font=("Segoe UI",13),text_color="#444").pack(pady=4)

    def _sheet_detail(self,s):
        for w in self._detail.winfo_children(): w.destroy()
        # If chord grid is open for a DIFFERENT song, reload it for this song
        if self._chord_grid_visible:
            if self._chord_grid_panel is None or self._chord_grid_panel._sheet.get("id") != s.get("id"):
                self._show_chord_grid(s)
        hdr=ctk.CTkFrame(self._detail,fg_color="#0d1117",corner_radius=0); hdr.pack(fill="x")
        # Favourite star in title area
        fav = bool(s.get("favorite"))
        star_lbl = "★" if fav else "☆"
        star_col  = "#fbbf24" if fav else "#555"
        ctk.CTkButton(hdr, text=star_lbl, width=36, height=36,
            font=("Segoe UI",18), fg_color="transparent", hover_color="#1e1e2e",
            text_color=star_col,
            command=lambda _s=s: self._toggle_favorite(_s)).pack(side="left",padx=(8,0),pady=8)
        ctk.CTkLabel(hdr,text=s["title"],font=("Segoe UI",20,"bold")).pack(side="left",padx=(4,14),pady=10)
        # Transposed indicator + reset button
        if s.get("original_body"):
            ctk.CTkLabel(hdr,text="⟳ transposed",font=("Segoe UI",10),
                text_color="#38bdf8").pack(side="left",padx=(0,6),pady=10)
        for txt,cmd,col in [
            ("View",      lambda _s=s: ViewerDialog(self,_s,self._settings), "#1565C0"),
            ("Edit",      lambda _s=s: self._edit_sheet(_s),                 "#E65100"),
            ("Transpose", lambda _s=s: self._transpose_sheet(_s),            "#5A189A"),
            ("Delete",    lambda _s=s: self._del_sheet(_s),                  "#B71C1C"),
            ("Duplicate", lambda _s=s: self._duplicate_sheet(_s),            "#0d3a4a"),
        ]:
            ctk.CTkButton(hdr,text=txt,width=90,fg_color=col,hover_color=col,command=cmd).pack(side="right",padx=3,pady=8)
        ctk.CTkButton(hdr,text="📄 PDF",width=78,height=30,fg_color="#1a3050",hover_color="#243a60",
            command=lambda _s=s: self._export_sheet_pdf(_s)).pack(side="right",padx=3,pady=8)
        ctk.CTkButton(hdr,text="🗑 Bin",width=72,height=30,fg_color="#2a1a2a",hover_color="#3a243a",
            command=lambda: RecycleBinDialog(self)).pack(side="right",padx=3,pady=8)
        if s.get("original_body"):
            ctk.CTkButton(hdr,text="↺ Reset",width=78,height=30,
                fg_color="#1a3a2a",hover_color="#1e5c36",text_color="#4ade80",
                command=lambda _s=s: self._reset_transpose(_s)
                ).pack(side="right",padx=(4,0),pady=10)
        ctk.CTkButton(hdr,text="Folder",width=60,height=30,fg_color="#2a2a3a",hover_color="#3a3a4a",command=lambda: open_folder(CHORDS_DIR)).pack(side="right",padx=(8,2),pady=10)
        ctk.CTkButton(hdr,text="📁 Copy To…",width=90,height=30,fg_color="#1a2a1a",hover_color="#253525",
            command=lambda _s=s: self._copy_sheet_to_folder(_s)).pack(side="right",padx=(2,2),pady=10)
        # Chord Grid toggle button
        cg_active = self._chord_grid_visible and (
            self._chord_grid_panel is not None and
            self._chord_grid_panel._sheet.get("id") == s.get("id"))
        self._cg_toggle_btn = ctk.CTkButton(
            hdr, text="⊞ Grid ▶" if not cg_active else "⊞ Grid ✕",
            width=84, height=30,
            fg_color="#1a2a3a" if not cg_active else "#0e2a3a",
            hover_color="#243040",
            text_color="#60a5fa",
            command=lambda _s=s: self._toggle_chord_grid(_s))
        self._cg_toggle_btn.pack(side="right", padx=(4,0), pady=10)

        meta=ctk.CTkFrame(self._detail,fg_color="#161625",corner_radius=8); meta.pack(fill="x",padx=12,pady=(8,2))
        for i,(lbl,val) in enumerate([("Artist",s.get("artist") or "---"),("Key",s.get("key","---")),("BPM",str(s.get("bpm","---"))),("Category",self._get_cat_name(s["id"]))]):
            ctk.CTkLabel(meta,text=lbl,font=("Segoe UI",11),text_color="#777").grid(row=0,column=i,padx=16,pady=(6,0),sticky="w")
            ctk.CTkLabel(meta,text=val,font=("Segoe UI",13,"bold"),text_color="#ccc").grid(row=1,column=i,padx=16,pady=(0,6),sticky="w")

        # Yamaha SX720 meta row (only shown if any field is set)
        sx_fields = [
            ("🎹 Style", s.get("sx_style","")),
            ("Variation", s.get("sx_variation","")),
            ("OTS", f"#{s['sx_ots']}" if s.get("sx_ots") else ""),
            ("Intro", s.get("sx_intro","")),
            ("Ending", s.get("sx_ending","")),
            ("Multi Pad", s.get("sx_mpad","")),
            ("R.Hand", s.get("sx_voice_r","")),
            ("L.Hand", s.get("sx_voice_l","")),
            ("Split", s.get("sx_split","")),
        ]
        sx_set = [(l,v) for l,v in sx_fields if v]
        if sx_set:
            sxmeta = ctk.CTkFrame(self._detail, fg_color="#0d1a2e", corner_radius=6)
            sxmeta.pack(fill="x", padx=12, pady=(0,4))
            for i,(lbl,val) in enumerate(sx_set):
                ctk.CTkLabel(sxmeta,text=lbl,font=("Segoe UI",9),text_color="#4A90D9").grid(row=0,column=i,padx=10,pady=(4,0),sticky="w")
                ctk.CTkLabel(sxmeta,text=val,font=("Segoe UI",11,"bold"),text_color="#93c5fd").grid(row=1,column=i,padx=10,pady=(0,5),sticky="w")

        fsz=ctk.CTkFrame(self._detail,fg_color="#111120"); fsz.pack(fill="x",padx=12,pady=(2,2))
        ctk.CTkLabel(fsz,text="Chord font:",font=("Segoe UI",11),text_color="#888").pack(side="left",padx=(8,4))
        self._det_chord_var=ctk.StringVar(value=self._settings.get("chord_font_size","13"))
        ctk.CTkOptionMenu(fsz,variable=self._det_chord_var,values=FONT_SIZES,width=68,height=24,command=lambda _: self._rerender_det(s)).pack(side="left")
        ctk.CTkLabel(fsz,text="   Lyric font:",font=("Segoe UI",11),text_color="#888").pack(side="left",padx=(10,4))
        self._det_lyric_var=ctk.StringVar(value=self._settings.get("lyric_font_size","13"))
        ctk.CTkOptionMenu(fsz,variable=self._det_lyric_var,values=FONT_SIZES,width=68,height=24,command=lambda _: self._rerender_det(s)).pack(side="left")
        ctk.CTkLabel(fsz,text="auto-saved",font=("Segoe UI",9),text_color="#444").pack(side="left",padx=(10,0))
        # Two-column toggle
        self._twocol = False
        self._twocol_btn = ctk.CTkButton(fsz, text="⊞ 2-Col", width=76, height=24,
            fg_color="#1a2a3a", hover_color="#243040", font=("Segoe UI",10),
            command=lambda _s=s: self._toggle_two_col(_s))
        self._twocol_btn.pack(side="right", padx=6)

        self._det_body_frame = ctk.CTkFrame(self._detail, fg_color="transparent")
        self._det_body_frame.pack(fill="both", expand=True, padx=12, pady=(0,4))
        self._det_body_frame.columnconfigure(0, weight=1)
        self._det_body_frame.rowconfigure(0, weight=0)
        self._det_body_frame.rowconfigure(1, weight=1)

        ctk.CTkLabel(self._det_body_frame,text="Chord Sheet",font=("Segoe UI",11,"bold"),
                     text_color="#aaa",anchor="w",width=1).grid(row=0,column=0,sticky="w",padx=2,pady=(2,0))
        self._det_tb=ctk.CTkTextbox(self._det_body_frame,wrap="word",font=("Courier New",int(self._settings.get("chord_font_size","13"))))
        self._det_tb.grid(row=1,column=0,sticky="nsew")
        self._det_tb2 = None  # second column textbox (two-col mode)
        render_body(self._det_tb,s.get("body",""),
                    int(self._settings.get("chord_font_size","13")),
                    int(self._settings.get("lyric_font_size","13")),
                    self._settings.get("chord_color","#e0f2ff"),
                    self._settings.get("section_color","#38bdf8"),
                    self._settings.get("lyric_color","#94a3b8"),
                    self._settings.get("chord_highlight_color","#1e3a5f"))

        leg=ctk.CTkFrame(self._detail,fg_color="transparent"); leg.pack(fill="x",padx=12,pady=(0,2))
        for txt,col in [("chord line","#4A90D9"),("   [Section]","#38bdf8"),("   Lyrics","#888")]:
            ctk.CTkLabel(leg,text=txt,text_color=col,font=("Segoe UI",11)).pack(side="left")
        if s.get("notes"):
            ctk.CTkLabel(self._detail,text=f"Notes: {s['notes']}",text_color="#777",font=("Segoe UI",12),wraplength=800).pack(padx=14,pady=(0,6),anchor="w")

    def _get_cat_name(self, sid):
        """Return the category path name for a sheet id."""
        def _walk(cats, sid, path=""):
            for c in cats:
                p = (path + " / " if path else "") + c["name"]
                if sid in c.get("sheet_ids",[]): return p
                found = _walk(c.get("children",[]), sid, p)
                if found: return found
            return None
        result = _walk(self.categories, sid)
        return result or "Uncategorized"

    def _rerender_det(self,s):
        if self._det_tb is None: return
        try: cs=int(self._det_chord_var.get())
        except: cs=13
        try: ls=int(self._det_lyric_var.get())
        except: ls=13
        cc=self._settings.get("chord_color","#e0f2ff")
        sc=self._settings.get("section_color","#38bdf8")
        lc=self._settings.get("lyric_color","#94a3b8")
        hc=self._settings.get("chord_highlight_color","#1e3a5f")
        body=s.get("body","")
        if self._twocol and self._det_tb2:
            # Split body at roughly mid-line count for two columns
            lines=body.split("\n"); mid=len(lines)//2
            # Advance to next section boundary if possible
            for i in range(mid, min(mid+8, len(lines))):
                if lines[i].startswith("[") or lines[i].strip()=="": mid=i; break
            half1="\n".join(lines[:mid]); half2="\n".join(lines[mid:])
            render_body(self._det_tb, half1, cs, ls, cc, sc, lc, hc)
            render_body(self._det_tb2, half2, cs, ls, cc, sc, lc, hc)
        else:
            render_body(self._det_tb, body, cs, ls, cc, sc, lc, hc)
        self._settings["chord_font_size"]=str(cs)
        self._settings["lyric_font_size"]=str(ls)
        save_settings(self._settings)

    def _toggle_two_col(self, s):
        """Toggle two-column lyrics layout."""
        self._twocol = not self._twocol
        if self._twocol:
            # Add second column
            self._det_body_frame.columnconfigure(1, weight=1)
            self._det_tb2 = ctk.CTkTextbox(self._det_body_frame, wrap="word",
                font=("Courier New", int(self._settings.get("chord_font_size","13"))))
            self._det_tb2.grid(row=1, column=1, sticky="nsew", padx=(4,0))
            self._twocol_btn.configure(text="⊞ 1-Col", fg_color="#0e2a1e")
        else:
            if self._det_tb2:
                self._det_tb2.destroy(); self._det_tb2 = None
            self._twocol_btn.configure(text="⊞ 2-Col", fg_color="#1a2a3a")
        self._rerender_det(s)

    # ── Chord Grid Panel ──────────────────────────────────────────────────────

    def _toggle_chord_grid(self, s):
        same_song = (self._chord_grid_panel is not None and
                     self._chord_grid_panel._sheet.get("id") == s.get("id"))
        if self._chord_grid_visible and same_song:
            self._hide_chord_grid()
        else:
            self._show_chord_grid(s)

    def _show_chord_grid(self, s):
        # Destroy old panel
        if self._chord_grid_panel is not None:
            try: self._chord_grid_panel.destroy()
            except: pass
            self._chord_grid_panel = None

        self._chord_grid_panel = ChordGridPanel(
            self._cg_pane, s,
            save_callback=self._grid_save_cb)
        self._chord_grid_panel.pack(fill="both", expand=True)

        if not self._chord_grid_visible:
            # Add pane with initial width 420px
            self._right_pane.add(self._cg_pane, minsize=260, width=420, stretch="never")
            self._chord_grid_visible = True

        try:
            self._cg_toggle_btn.configure(text="⊞ Grid ✕",
                fg_color="#0e2a3a", hover_color="#122838")
        except: pass

    def _hide_chord_grid(self):
        if self._chord_grid_panel is not None:
            try: self._chord_grid_panel.destroy()
            except: pass
            self._chord_grid_panel = None
        if self._chord_grid_visible:
            try: self._right_pane.remove(self._cg_pane)
            except: pass
            self._chord_grid_visible = False
        try:
            self._cg_toggle_btn.configure(text="⊞ Grid ▶",
                fg_color="#1a2a3a", hover_color="#243040")
        except: pass

    def _grid_save_cb(self, updated_sheet):
        """Called by ChordGridPanel when the user edits the grid."""
        idx = next((i for i,x in enumerate(self.sheets) if x["id"]==updated_sheet["id"]), None)
        if idx is not None:
            self.sheets[idx] = updated_sheet
        save_sheet(updated_sheet)

    def _sl_detail(self,sl):
        for w in self._detail.winfo_children(): w.destroy()
        hdr=ctk.CTkFrame(self._detail,fg_color="#0d1117",corner_radius=0); hdr.pack(fill="x")
        ctk.CTkLabel(hdr,text=sl["name"],font=("Segoe UI",20,"bold")).pack(side="left",padx=14,pady=10)
        ctk.CTkButton(hdr,text="Folder",width=60,height=30,fg_color="#2a2a3a",hover_color="#3a3a4a",command=lambda: open_folder(SETLISTS_DIR)).pack(side="right",padx=(8,4),pady=10)
        for txt,cmd,col in [
            ("Edit",   lambda _sl=sl: self._edit_sl(_sl),      "#E65100"),
            ("Delete", lambda _sl=sl: self._del_sl(_sl),        "#B71C1C"),
            ("📄 PDF", lambda _sl=sl: self._export_sl_pdf(_sl), "#1a3a5a"),
        ]:
            ctk.CTkButton(hdr,text=txt,width=88,fg_color=col,hover_color=col,command=cmd).pack(side="right",padx=3,pady=8)

        meta=ctk.CTkFrame(self._detail,fg_color="#161625",corner_radius=8); meta.pack(fill="x",padx=12,pady=(8,4))
        for c,(lbl,val) in enumerate([("Date",sl.get("date","---")),("Venue",sl.get("venue","---")),("Songs",str(len(sl.get("sheet_ids",[])))),("Modified",sl.get("modified","---"))]):
            ctk.CTkLabel(meta,text=lbl,font=("Segoe UI",11),text_color="#777").grid(row=0,column=c,padx=16,pady=(6,0),sticky="w")
            ctk.CTkLabel(meta,text=val,font=("Segoe UI",13,"bold"),text_color="#ccc").grid(row=1,column=c,padx=16,pady=(0,8),sticky="w")
        if sl.get("notes"):
            ctk.CTkLabel(self._detail,text=f"Notes: {sl['notes']}",text_color="#888",font=("Segoe UI",12),wraplength=800).pack(padx=14,pady=(0,6),anchor="w")

        ctk.CTkLabel(self._detail,text="Songs in Set  (click to send to web  |  double-click to open viewer)",
            font=("Segoe UI",12,"bold"),text_color="#aaa").pack(anchor="w",padx=14)

        # "Add Break" button
        def _add_break():
            label = self._prompt("Add Break", "Break label (e.g. 'Break 5 min'):", "Break")
            if label is None: return
            ids = list(sl.get("sheet_ids", []))
            ids.append("__break__")
            sl["sheet_ids"] = ids
            # Store break label keyed by position
            sl.setdefault("break_labels", {})[str(len(ids))] = label or "Break"
            save_setlist(sl); self._sl_detail(sl)
        ctk.CTkButton(self._detail, text="+ Add Break", width=110, height=26,
            fg_color="#2a2a1a", hover_color="#3a3a2a", font=("Segoe UI",11),
            command=_add_break).pack(anchor="w", padx=14, pady=(2,4))

        sf=ctk.CTkScrollableFrame(self._detail); sf.pack(fill="both",expand=True,padx=12,pady=(0,8))
        sheet_map={s["id"]:s for s in self.sheets}
        sl_sheets=[sheet_map[sid] for sid in sl.get("sheet_ids",[]) if sid in sheet_map and sid != "__break__"]

        # Send first song to web on open
        if sl_sheets:
            update_hosted_song(sl_sheets[0])

        self._sl_selected_idx = [0]
        row_widgets = []
        song_counter = 0

        def highlight_row(idx):
            for i,(rw,_) in enumerate(row_widgets):
                try: rw.configure(fg_color="#2a1e3a" if i==idx else "#1e1e2e")
                except: pass

        for pos, sid in enumerate(sl.get("sheet_ids",[]), 1):
            if sid == "__break__":
                break_label = sl.get("break_labels", {}).get(str(pos), "Break")
                brow = ctk.CTkFrame(sf, corner_radius=6, fg_color="#1e1e0a")
                brow.pack(fill="x", pady=3)
                ctk.CTkLabel(brow, text=f"— {break_label} —",
                    font=("Segoe UI",11,"italic"), text_color="#a0a050").pack(side="left",padx=14,pady=5)
                # Remove break button
                def _rm_break(p=pos):
                    ids = list(sl.get("sheet_ids", []))
                    if p-1 < len(ids): ids.pop(p-1)
                    sl["sheet_ids"] = ids; save_setlist(sl); self._sl_detail(sl)
                ctk.CTkButton(brow, text="✕", width=28, height=22,
                    fg_color="#2a1a1a", hover_color="#3a2a2a",
                    font=("Segoe UI",10), command=_rm_break).pack(side="right",padx=6,pady=4)
                continue

            s=sheet_map.get(sid)
            is_first = (song_counter == 0)
            row=ctk.CTkFrame(sf,corner_radius=8,fg_color="#2a1e3a" if is_first else "#1e1e2e")
            row.pack(fill="x",pady=3)
            song_counter += 1
            ctk.CTkLabel(row,text=f"{song_counter:02d}",font=("Courier New",14,"bold"),
                         text_color="#4A90D9",width=36).pack(side="left",padx=(10,6),pady=6)
            if s:
                ctk.CTkLabel(row,text=s["title"],font=("Segoe UI",13,"bold"),text_color="#eee").pack(side="left")
                ctk.CTkLabel(row,text=f"  {s.get('artist','---')}  -  Key: {s.get('key','---')}  -  BPM: {s.get('bpm','---')}",
                    font=("Segoe UI",11),text_color="#888").pack(side="left",padx=6)
                si = song_counter - 1
                view_btn=ctk.CTkButton(row,text="View",width=56,fg_color="#1565C0",hover_color="#1976D2",
                    command=lambda _s=s,_i=si: ViewerDialog(self,_s,self._settings,sl_sheets,_i))
                view_btn.pack(side="right",padx=8,pady=4)
                def _single(e, _s=s, _i=si):
                    update_hosted_song(_s); highlight_row(_i)
                _dbl_cmd = lambda e,_i=si: SetListViewer(self,sl,self.sheets,_i,self._settings)
                row.bind("<Button-1>", _single)
                row.bind("<Double-Button-1>", _dbl_cmd)
                for child in row.winfo_children():
                    if child is not view_btn:
                        child.bind("<Button-1>", _single)
                        child.bind("<Double-Button-1>", _dbl_cmd)
                row_widgets.append((row, s))
            else:
                ctk.CTkLabel(row,text=f"[Missing: {sid}]",text_color="#555").pack(side="left",padx=8,pady=6)
                row_widgets.append((row, None))

    def _export_sl_pdf(self, sl):
        """Export the setlist as a formatted PDF."""
        if not REPORTLAB_OK:
            messagebox.showerror("Missing Library",
                "reportlab is not installed.\nRun:  pip install reportlab", parent=self)
            return
        path = filedialog.asksaveasfilename(
            defaultextension=".pdf",
            filetypes=[("PDF File","*.pdf")],
            initialfile=f"{sl['name'].replace('/','_')}.pdf",
            title="Export Setlist as PDF")
        if not path: return
        sheet_map = {s["id"]:s for s in self.sheets}
        try:
            export_setlist_pdf(sl, sheet_map, path)
            messagebox.showinfo("Exported", f"Setlist PDF saved:\n{path}", parent=self)
        except Exception as e:
            messagebox.showerror("Export Failed", str(e), parent=self)

    def _export_sheet_pdf(self, s):
        """Export a single song as a beautiful printer-friendly PDF."""
        if not REPORTLAB_OK:
            messagebox.showerror("Missing Library",
                "reportlab is not installed.\nRun:  pip install reportlab", parent=self)
            return
        safe = s["title"].replace("/","_").replace("\\","_")
        path = filedialog.asksaveasfilename(
            defaultextension=".pdf",
            filetypes=[("PDF File","*.pdf")],
            initialfile=f"{safe}.pdf",
            title="Export Song as PDF")
        if not path: return
        # Include chord grid only if it is currently visible for this song
        include_grid = (
            self._chord_grid_visible and
            self._chord_grid_panel is not None and
            self._chord_grid_panel._sheet.get("id") == s.get("id")
        )
        chord_grid = s.get("chord_grid", []) if include_grid else []
        try:
            export_song_pdf(s, path, chord_grid=chord_grid)
            messagebox.showinfo("Exported", f"PDF saved:\n{path}", parent=self)
        except Exception as e:
            messagebox.showerror("Export Failed", str(e), parent=self)

    # ── CRUD ──────────────────────────────────────────────────────────────────
    def _new_item(self):
        if self._mode=="chords": self._new_sheet()
        else: self._new_sl()

    def _new_sheet(self):
        dlg=SheetFormDialog(self,categories=self.categories,artists=self.artists); self.wait_window(dlg)
        if dlg.result:
            self.sheets.append(dlg.result); save_sheet(dlg.result)
            self._sel_sheet_id=dlg.result["id"]
            if dlg.result_category_id:
                cat=_find_cat_by_id(self.categories, dlg.result_category_id)
                if cat:
                    cat.setdefault("sheet_ids",[]).append(dlg.result["id"])
                    save_categories(self.categories)
            update_hosted_song(dlg.result)
            self._refresh_list(); self._sheet_detail(dlg.result)

    def _edit_sheet(self,s):
        cur_cat_id = next((c["id"] for c in self.categories
                           if s["id"] in c.get("sheet_ids",[])), None)
        if cur_cat_id is None:
            def _find_sub(cats):
                for c in cats:
                    if s["id"] in c.get("sheet_ids",[]): return c["id"]
                    r = _find_sub(c.get("children",[]));
                    if r: return r
                return None
            cur_cat_id = _find_sub(self.categories)
        dlg=SheetFormDialog(self,s,categories=self.categories,current_cat_id=cur_cat_id,
                            artists=self.artists); self.wait_window(dlg)
        if dlg.result:
            idx=next(i for i,x in enumerate(self.sheets) if x["id"]==s["id"])
            self.sheets[idx]=dlg.result; save_sheet(dlg.result)
            new_cat_id = dlg.result_category_id
            if new_cat_id != cur_cat_id:
                _remove_sheet_from_all_cats(self.categories, s["id"])
                if new_cat_id:
                    cat=_find_cat_by_id(self.categories, new_cat_id)
                    if cat: cat.setdefault("sheet_ids",[]).append(s["id"])
                save_categories(self.categories)
            update_hosted_song(dlg.result)
            self._refresh_list(); self._sheet_detail(self.sheets[idx])

    def _del_sheet(self,s):
        if not messagebox.askyesno("Delete Sheet",f"Delete '{s['title']}'?\nIt will be moved to Recycle Bin.",parent=self): return
        self.sheets=[x for x in self.sheets if x["id"]!=s["id"]]
        delete_sheet_file(s["id"]); self._sel_sheet_id=None
        if _remove_sheet_from_all_cats(self.categories, s["id"]):
            save_categories(self.categories)
        if _SERVER_STATE["song_ref"].get("sheet",{}).get("id")==s["id"]: update_hosted_song(None)
        self._refresh_list(); self._show_welcome()

    def _transpose_sheet(self,s):
        dlg=TransposeDialog(self,s); self.wait_window(dlg)
        if dlg.result_body:
            idx=next(i for i,x in enumerate(self.sheets) if x["id"]==s["id"])
            sh=self.sheets[idx]
            if getattr(dlg,"result_reset",False):
                # Reset — restore original, clear stored originals
                sh["body"] = dlg.result_body
                sh["key"]  = dlg.result_key or sh["key"]
                sh.pop("original_body",None); sh.pop("original_key",None)
            else:
                # Normal transpose — save original on first transpose only
                if not sh.get("original_body"):
                    sh["original_body"] = sh["body"]
                    sh["original_key"]  = sh.get("key","")
                sh["body"] = dlg.result_body
                sh["key"]  = dlg.result_key or sh["key"]
            sh["modified"]= datetime.now().strftime("%Y-%m-%d %H:%M")
            save_sheet(sh); update_hosted_song(sh)
            self._refresh_list(); self._sheet_detail(sh)

    def _reset_transpose(self,s):
        idx=next((i for i,x in enumerate(self.sheets) if x["id"]==s["id"]),None)
        if idx is None: return
        sh=self.sheets[idx]
        if not sh.get("original_body"): return
        if not messagebox.askyesno("Reset Transpose",
                f"Restore '{sh['title']}' to its original key ({sh.get('original_key','?')})?\n"
                "This will discard the current transposition.",parent=self): return
        sh["body"]    = sh.pop("original_body")
        sh["key"]     = sh.pop("original_key","")
        sh["modified"]= datetime.now().strftime("%Y-%m-%d %H:%M")
        save_sheet(sh); update_hosted_song(sh)
        self._refresh_list(); self._sheet_detail(sh)

    def _new_sl(self):
        dlg=SetListFormDialog(self,self.sheets); self.wait_window(dlg)
        if dlg.result:
            self.setlists.append(dlg.result); save_setlist(dlg.result)
            self._sel_sl_id=dlg.result["id"]; self._refresh_list(); self._sl_detail(dlg.result)

    def _duplicate_sheet(self, s):
        """Create a copy of s with a new id and '(Copy)' suffix."""
        import copy
        new_s = copy.deepcopy(s)
        new_s["id"] = new_id()
        new_s["title"] = s["title"] + " (Copy)"
        now = datetime.now().strftime("%Y-%m-%d %H:%M")
        new_s["created"] = now; new_s["modified"] = now
        self.sheets.append(new_s); save_sheet(new_s)
        self._sel_sheet_id = new_s["id"]
        self._refresh_list(); self._sheet_detail(new_s)

    def _copy_sheet_to_folder(self, s):
        """Copy the sheet JSON file to a user-chosen folder."""
        dest_dir = filedialog.askdirectory(title="Choose destination folder")
        if not dest_dir: return
        src = _sheet_path(s["id"])
        if not os.path.exists(src):
            messagebox.showerror("Error", "Source file not found.", parent=self); return
        dest = os.path.join(dest_dir, f"{s['title'].replace('/','_')}.json")
        try:
            shutil.copy2(src, dest)
            messagebox.showinfo("Copied",
                f"'{s['title']}'\ncopied to:\n{dest}", parent=self)
        except Exception as e:
            messagebox.showerror("Copy Failed", str(e), parent=self)

    def _edit_sl(self,sl):
        dlg=SetListFormDialog(self,self.sheets,sl); self.wait_window(dlg)
        if dlg.result:
            idx=next(i for i,x in enumerate(self.setlists) if x["id"]==sl["id"])
            self.setlists[idx]=dlg.result; save_setlist(dlg.result); self._refresh_list(); self._sl_detail(self.setlists[idx])

    def _del_sl(self,sl):
        if not messagebox.askyesno("Delete Set List",f"Delete '{sl['name']}'?\nThis cannot be undone.",parent=self): return
        self.setlists=[x for x in self.setlists if x["id"]!=sl["id"]]
        delete_setlist_file(sl["id"]); self._sel_sl_id=None; self._refresh_list(); self._show_welcome()

    def _open_writer(self):
        """Open the Chord Writer pad dialog (singleton — only one instance)."""
        if hasattr(self, "_writer_win") and self._writer_win and                 self._writer_win.winfo_exists():
            self._writer_win.lift()
            self._writer_win.focus_force()
            return
        self._writer_win = WriterDialog(self)

    def _open_host(self):
        HostDialog(self)

if __name__=="__main__":
    apply_chord_cell_colors(load_settings())
    app=ChordSheetApp()
    app.mainloop()
