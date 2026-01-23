import os, re, time, threading, logging, xml.etree.ElementTree as ET, customtkinter as ctk, tkinter as tk
from tkinter import messagebox, filedialog, Menu
import mido, socket, webbrowser, zipfile, shutil, requests
from flask import Flask, render_template_string, jsonify, request, send_file
from threading import Thread
from io import BytesIO
import qrcode
from PIL import Image, ImageTk
import io

logging.basicConfig(filename='ablechord.log', level=logging.DEBUG, format='%(asctime)s - %(levelname)s - %(message)s')
ctk.set_appearance_mode("dark")

COLORS = {"background": "#121212", "secondary": "#1e1e1e", "panel": "#161616", "accent": "#f1c40f", "success": "#27ae60", "warning": "#f39c12", "danger": "#e74c3c", "info": "#3498db", "primary": "#2c3e50", "button": "#34495e"}
SECTION_COLORS = {"ADLIB": "#9b59b6", "INTRO": "#f1c40f", "CHORUS": "#3498db", "VERSE": "#2ecc71", "INTER": "#e67e22", "BRIDGE": "#e74c3c", "SOLO": "#1abc9c", "ENDING": "#95a5a6", "HOOK": "#f39c12", "OUTRO": "#34495e"}
FONTS = {"large": ("Arial", 32, "bold"), "medium": ("Arial", 16, "bold"), "normal": ("Arial", 12), "small": ("Arial", 10)}
DIMENSIONS = {"perf_bar_height": 90, "nav_width": 280, "chord_width": 380, "section_order_height": 120}
PROTECTED_SECTIONS = ["CHORUS", "VERSE", "INTRO", "OUTRO", "BRIDGE", "SOLO", "HOOK", "ENDING", "INTER"]
ALL_NOTES = ["C", "C#", "D", "Eb", "E", "F", "F#", "G", "Ab", "A", "Bb", "B"]
DEFAULT_SYSEX = {"A": "43 7E 00 00 7F", "B": "43 7E 00 01 7F", "C": "43 7E 00 02 7F", "D": "43 7E 00 03 7F", "I1": "43 7E 00 04 7F", "I2": "43 7E 00 05 7F", "I3": "43 7E 00 06 7F", "E1": "43 7E 00 08 7F", "E2": "43 7E 00 09 7F", "E3": "43 7E 00 0A 7F", "F1": "43 7E 00 10 7F", "F2": "43 7E 00 11 7F", "F3": "43 7E 00 12 7F", "F4": "43 7E 00 13 7F", "BREAK": "43 7E 00 13 7F", "ACMP_ON": "43 10 4C 08 00 01 7F", "ACMP_OFF": "43 10 4C 08 00 01 00", "SYNC_START_ON": "43 10 4C 08 00 02 7F", "SYNC_START_OFF": "43 10 4C 08 00 02 00", "START": "7B", "STOP": "7C", "CHORD_C": "43 7E 00 20 7F", "CHORD_CM": "43 7E 00 21 7F", "CHORD_G": "43 7E 00 22 7F", "CHORD_GM": "43 7E 00 23 7F"}
VAR_MAP = {"A": 0x00, "B": 0x01, "C": 0x02, "D": 0x03, "I1": 0x04, "I2": 0x05, "I3": 0x06, "E1": 0x08, "E2": 0x09, "E3": 0x0A, "F1": 0x10, "F2": 0x11, "F3": 0x12, "F4": 0x13}

def parse_voice_file(filepath):
    categories = {}
    if not os.path.exists(filepath):
        return {"General": []}
    try:
        current_cat = "General"
        with open(filepath, 'r', encoding='utf-8') as f:
            for line_num, line in enumerate(f, 1):
                if re.match(r'\[g\d+\](.*)', line):
                    current_cat = re.match(r'\[g\d+\](.*)', line).group(1).strip()
                    categories[current_cat] = []
                    continue
                voice_match = re.search(r'\[p[23],(\d+),(\d+),(\d+)\](.*)', line)
                if voice_match:
                    try:
                        categories[current_cat].append({
                            "name": voice_match.group(4).strip(),
                            "msb": int(voice_match.group(1)),
                            "lsb": int(voice_match.group(2)),
                            "pc": int(voice_match.group(3))
                        })
                    except ValueError as e:
                        logging.warning(f"Invalid voice data at line {line_num}: {line.strip()}")
    except Exception as e:
        logging.error(f"Error parsing voice file: {e}")
    return categories

class MIDIHandler:
    def __init__(self, app):
        self.app = app
        self.midi_out = None
        self.midi_in = None
        self.midi_out_ports = []
        self.midi_in_ports = []
        self.listener_thread = None
        self.running = False
        self.chord_octave = 4
    
    def scan_ports(self):
        try:
            all_out_ports = mido.get_output_names()
            all_in_ports = mido.get_input_names()
            logging.info(f"All MIDI outputs: {all_out_ports}")
            logging.info(f"All MIDI inputs: {all_in_ports}")
            
            yamaha_patterns = ['yamaha', 'sx', 'psr', 'sx720', 'sx-720', 'usb-midi', 'midi-usb', 'usb midi', 'midi usb', 'usb_midi', 'usbmidi', 'midiout', 'midiin']
            self.midi_out_ports = []
            self.midi_in_ports = []
            
            for port in all_out_ports:
                port_lower = port.lower()
                for pattern in yamaha_patterns:
                    if pattern in port_lower:
                        self.midi_out_ports.append(port)
                        logging.debug(f"Found Yamaha output: {port}")
                        break
            
            for port in all_in_ports:
                port_lower = port.lower()
                for pattern in yamaha_patterns:
                    if pattern in port_lower:
                        self.midi_in_ports.append(port)
                        logging.debug(f"Found Yamaha input: {port}")
                        break
            
            if not self.midi_out_ports:
                for port in all_out_ports:
                    port_lower = port.lower()
                    if 'usb' in port_lower and 'midi' in port_lower:
                        self.midi_out_ports.append(port)
                        logging.debug(f"Found USB MIDI output: {port}")
            
            if not self.midi_in_ports:
                for port in all_in_ports:
                    port_lower = port.lower()
                    if 'usb' in port_lower and 'midi' in port_lower:
                        self.midi_in_ports.append(port)
                        logging.debug(f"Found USB MIDI input: {port}")
            
            if not self.midi_out_ports:
                self.midi_out_ports = all_out_ports
                logging.warning("No Yamaha ports found, using all output ports")
            
            if not self.midi_in_ports:
                self.midi_in_ports = all_in_ports
                logging.warning("No Yamaha ports found, using all input ports")
            
            if self.midi_out_ports:
                logging.info(f"Filtered MIDI outputs: {self.midi_out_ports}")
            if self.midi_in_ports:
                logging.info(f"Filtered MIDI inputs: {self.midi_in_ports}")
            
            return self.midi_out_ports, self.midi_in_ports
        except Exception as e:
            logging.error(f"Error scanning MIDI ports: {e}")
            return [], []
    
    def connect(self, out_port=None, in_port=None):
        self.disconnect()
        
        if out_port and out_port in self.midi_out_ports:
            try:
                self.midi_out = mido.open_output(out_port)
                logging.info(f"Connected to MIDI output: {out_port}")
                self.send_test_sysex()
            except Exception as e:
                logging.error(f"Error connecting to output {out_port}: {e}")
                self.midi_out = None
        
        if in_port and in_port in self.midi_in_ports:
            try:
                self.midi_in = mido.open_input(in_port)
                logging.info(f"Connected to MIDI input: {in_port}")
                self.start_listener()
            except Exception as e:
                logging.error(f"Error connecting to input {in_port}: {e}")
                self.midi_in = None
        
        return self.midi_out is not None or self.midi_in is not None
    
    def disconnect(self):
        self.running = False
        
        if self.listener_thread:
            try:
                self.listener_thread.join(timeout=1)
            except:
                pass
        
        if self.midi_out:
            try:
                self.midi_out.close()
            except:
                pass
            self.midi_out = None
        
        if self.midi_in:
            try:
                self.midi_in.close()
            except:
                pass
            self.midi_in = None
    
    def start_listener(self):
        if not self.midi_in or self.running:
            return
        self.running = True
        self.listener_thread = threading.Thread(target=self._listen_loop, daemon=True)
        self.listener_thread.start()
    
    def _listen_loop(self):
        rev_map = {0x00: "A", 0x01: "B", 0x02: "C", 0x03: "D", 0x08: "E1", 0x09: "E2", 0x0A: "E3", 0x04: "I1", 0x05: "I2", 0x06: "I3", 0x10: "F1", 0x11: "F2", 0x12: "F3", 0x13: "F4"}
        
        while self.running and self.midi_in and not self.midi_in.closed:
            try:
                msg = self.midi_in.receive(timeout=0.1)
                if msg:
                    self.app.log_midi("IN", msg)
                    
                    if msg.type == 'start':
                        self.app.style_running = True
                        self.app.sync_start_on = False
                        self.app.after(0, self.app.update_style_ui_states)
                    elif msg.type == 'stop':
                        self.app.style_running = False
                        self.app.after(0, self.app.update_style_ui_states)
                    
                    if msg.type == 'sysex' and len(msg.data) >= 5:
                        if msg.data[0] == 0x43 and msg.data[1] == 0x7E:
                            cmd = msg.data[3]
                            if cmd in rev_map:
                                code = rev_map[cmd]
                                if code.startswith("F"):
                                    base = code
                                    self.app.after(0, lambda b=base: self.app.blink_button(b))
                                else:
                                    self.app.current_variation = code
                                    self.app.after(0, self.app.update_variation_indicators)
                        
                        if msg.data[0] == 0x43 and msg.data[1] == 0x10 and msg.data[2] == 0x4C:
                            if msg.data[3:6] == [0x08, 0x00, 0x01]:
                                self.app.acmp_on = (msg.data[6] > 0)
                                self.app.after(0, self.app.update_style_ui_states)
                            elif msg.data[3:6] == [0x08, 0x00, 0x02]:
                                self.app.sync_start_on = (msg.data[6] > 0)
                                self.app.after(0, self.app.update_style_ui_states)
            except Exception as e:
                if "port not open" not in str(e):
                    logging.error(f"MIDI listener error: {e}")
                break
    
    def send_test_sysex(self):
        try:
            msg = mido.Message('sysex', data=[0x43, 0x7E, 0x00, 0x7F])
            self.midi_out.send(msg)
            logging.info("Sent Yamaha device inquiry")
            return True
        except Exception as e:
            logging.error(f"Error sending test SysEx: {e}")
            return False
    
    def send_variation(self, var_name):
        if not self.midi_out:
            logging.warning("No MIDI output connected")
            return False
        
        try:
            if hasattr(self.app, 'sysex_commands') and var_name in self.app.sysex_commands:
                sysex_str = self.app.sysex_commands[var_name]
                if sysex_str:
                    hex_bytes = self._parse_sysex_string(sysex_str)
                    if hex_bytes:
                        msg = mido.Message('sysex', data=hex_bytes)
                        self.midi_out.send(msg)
                        self.app.log_midi("OUT", msg)
                        logging.info(f"Sent custom SysEx for {var_name}: {sysex_str}")
                        return True
            
            if var_name in VAR_MAP:
                cmd = VAR_MAP[var_name]
                msg = mido.Message('sysex', data=[0x43, 0x7E, 0x00, cmd, 0x7F])
                self.midi_out.send(msg)
                self.app.log_midi("OUT", msg)
                logging.info(f"Sent variation: {var_name} (cmd: 0x{cmd:02X})")
                return True
            else:
                logging.error(f"Unknown variation: {var_name}")
                return False
        except Exception as e:
            logging.error(f"Error sending variation {var_name}: {e}")
            return False
    
    def _parse_sysex_string(self, sysex_str):
        if not sysex_str:
            return None
        try:
            hex_values = [x.strip() for x in sysex_str.split() if x.strip()]
            if hex_values and hex_values[0].upper() == "F0":
                hex_values = hex_values[1:]
            if hex_values and hex_values[-1].upper() == "F7":
                hex_values = hex_values[:-1]
            if not hex_values:
                return None
            
            data_bytes = [int(x, 16) for x in hex_values]
            return data_bytes
        except Exception as e:
            logging.error(f"Error parsing SysEx string: {e}")
            return None
    
    def send_sysex(self, data):
        if not self.midi_out:
            return False
        try:
            msg = mido.Message('sysex', data=data)
            self.midi_out.send(msg)
            self.app.log_midi("OUT", msg)
            return True
        except Exception as e:
            logging.error(f"Error sending SysEx: {e}")
            return False
    
    def send_acmp(self, state):
        if hasattr(self.app, 'sysex_commands'):
            key = "ACMP_ON" if state else "ACMP_OFF"
            if key in self.app.sysex_commands and self.app.sysex_commands[key]:
                sysex_str = self.app.sysex_commands[key]
                try:
                    hex_bytes = self._parse_sysex_string(sysex_str)
                    if hex_bytes:
                        return self.send_sysex(hex_bytes)
                except Exception as e:
                    logging.error(f"Error parsing custom ACMP SysEx: {e}")
        
        val = 0x7F if state else 0x00
        return self.send_sysex([0x43, 0x10, 0x4C, 0x08, 0x00, 0x01, val])
    
    def send_sync_start(self, state):
        if hasattr(self.app, 'sysex_commands'):
            key = "SYNC_START_ON" if state else "SYNC_START_OFF"
            if key in self.app.sysex_commands and self.app.sysex_commands[key]:
                sysex_str = self.app.sysex_commands[key]
                try:
                    hex_bytes = self._parse_sysex_string(sysex_str)
                    if hex_bytes:
                        return self.send_sysex(hex_bytes)
                except Exception as e:
                    logging.error(f"Error parsing custom Sync Start SysEx: {e}")
        
        val = 0x7F if state else 0x00
        return self.send_sysex([0x43, 0x10, 0x4C, 0x08, 0x00, 0x02, val])
    
    def send_transport(self, start=True):
        if not self.midi_out:
            return False
        
        try:
            if hasattr(self.app, 'sysex_commands'):
                key = "START" if start else "STOP"
                if key in self.app.sysex_commands and self.app.sysex_commands[key]:
                    sysex_str = self.app.sysex_commands[key]
                    try:
                        hex_bytes = self._parse_sysex_string(sysex_str)
                        if hex_bytes:
                            msg = mido.Message('sysex', data=hex_bytes)
                            self.midi_out.send(msg)
                            self.app.log_midi("OUT", msg)
                            logging.info(f"Sent custom transport: {key}")
                            return True
                    except Exception as e:
                        logging.error(f"Error parsing custom transport SysEx: {e}")
            
            if start:
                msg = mido.Message('start')
            else:
                msg = mido.Message('stop')
            
            self.midi_out.send(msg)
            self.app.log_midi("OUT", msg)
            logging.info(f"Sent transport: {'START' if start else 'STOP'}")
            return True
        except Exception as e:
            logging.error(f"Error sending transport: {e}")
            return False
    
    def send_program_change(self, program):
        if not self.midi_out:
            return False
        
        try:
            if program >= 1 and program <= 10:
                msg = mido.Message('program_change', program=program-1)
                self.midi_out.send(msg)
                self.app.log_midi("OUT", msg)
                logging.info(f"Sent program change: {program}")
                return True
            else:
                logging.warning(f"Invalid program number: {program}")
                return False
        except Exception as e:
            logging.error(f"Error sending program change: {e}")
            return False
    
    def send_custom_sysex(self, sysex_str):
        if not self.midi_out:
            return False
        
        try:
            hex_bytes = self._parse_sysex_string(sysex_str)
            if not hex_bytes:
                logging.error("No valid hex values in SysEx string")
                return False
            
            msg = mido.Message('sysex', data=hex_bytes)
            self.midi_out.send(msg)
            self.app.log_midi("OUT", msg)
            logging.info(f"Sent custom SysEx: {sysex_str}")
            return True
        except Exception as e:
            logging.error(f"Error sending custom SysEx: {e}")
            return False
    
    def send_chord_midi(self, chord_name):
        if not self.midi_out:
            return False
        
        try:
            chord_key = f"CHORD_{chord_name.replace('#', 'S').replace('b', 'B')}"
            if hasattr(self.app, 'sysex_commands') and chord_key in self.app.sysex_commands:
                sysex_str = self.app.sysex_commands[chord_key]
                if sysex_str:
                    hex_bytes = self._parse_sysex_string(sysex_str)
                    if hex_bytes:
                        msg = mido.Message('sysex', data=hex_bytes)
                        self.midi_out.send(msg)
                        self.app.log_midi("OUT", msg)
                        logging.info(f"Sent custom SysEx for chord {chord_name}: {sysex_str}")
                        return True
            
            notes = self.parse_chord_to_notes(chord_name, self.chord_octave)
            for note in notes:
                msg = mido.Message('note_on', note=note, velocity=100)
                self.midi_out.send(msg)
                self.app.log_midi("OUT", msg)
            
            logging.info(f"Sent chord MIDI: {chord_name} (octave: {self.chord_octave})")
            return True
        except Exception as e:
            logging.error(f"Error sending chord MIDI: {e}")
            return False
    
    def parse_chord_to_notes(self, chord_name, octave=4):
        root_match = re.match(r'([A-G][#b]?)(.*)', chord_name)
        if not root_match:
            return [60, 64, 67]
        
        root_note = root_match.group(1)
        suffix = root_match.group(2)
        
        root_notes = {"C": 0, "C#": 1, "Db": 1, "D": 2, "D#": 3, "Eb": 3, "E": 4, "F": 5, "F#": 6, "Gb": 6, "G": 7, "G#": 8, "Ab": 8, "A": 9, "A#": 10, "Bb": 10, "B": 11}
        
        if root_note not in root_notes:
            root_note = "C"
        
        base_note = root_notes[root_note] + (octave * 12)
        
        if suffix.lower() == "m" or suffix.lower() == "min":
            return [base_note, base_note + 3, base_note + 7]
        elif suffix.lower() == "7":
            return [base_note, base_note + 4, base_note + 7, base_note + 10]
        elif suffix.lower() == "maj7":
            return [base_note, base_note + 4, base_note + 7, base_note + 11]
        elif suffix.lower() == "sus2":
            return [base_note, base_note + 2, base_note + 7]
        elif suffix.lower() == "sus4":
            return [base_note, base_note + 5, base_note + 7]
        elif suffix.lower() == "dim":
            return [base_note, base_note + 3, base_note + 6]
        else:
            return [base_note, base_note + 4, base_note + 7]
    
    def set_chord_octave(self, octave):
        self.chord_octave = max(0, min(8, octave))
        logging.info(f"Set chord octave to: {self.chord_octave}")
    
    def get_chord_octave(self):
        return self.chord_octave

class AbleChordApp(ctk.CTk):
    def __init__(self):
        super().__init__()
        self.title("Chord Manager by Supun Nirman")
        self.geometry("1366x768")
        self.state("zoomed")
        self.configure(fg_color=COLORS["background"])
        
        self.midi_handler = MIDIHandler(self)
        self._init_state_variables()
        self._setup_directories()
        self.load_sysex_commands()
        self.setup_ui()
        self.setup_menu_bar()
        
        self._start_background_tasks()
        self._bind_keyboard_shortcuts()
        self.protocol("WM_DELETE_WINDOW", self.on_closing)
        
        self.after(100, self.load_local_data)
        self.after(500, self.update_library_counts)
        self.after(1000, self.start_mobile_server)
        logging.info("Chord Manager application initialized")
    
    def _init_state_variables(self):
        self.voice_library = parse_voice_file("Yamaha PSR-SX720.txt")
        self.current_font_size = 26
        self.chord_grid_font_size = 14
        self.timer_running = False
        self.elapsed_time = 0
        self.current_tab = "songs"
        self.active_xml_file = None
        self.active_setlist_name = None
        self.filtered_songs = None
        self.grid_rows = []
        self.is_grid_edit_mode = False
        self.current_scale_offset = 0
        self.song_original_scale = "C"
        self.transpose_semitones = 0
        self.data_source = "local"
        self.chord_separate_mode = False
        self.broadcast_enabled = False
        self.web_server = None
        self.web_thread = None
        self.web_ip = None
        self.web_hostname = None
        self.mobile_server = None
        self.mobile_thread = None
        self.midi_config_window = None
        self.note_win = None
        self.txt_note = None
        self.monitor_win = None
        self.monitor_text = None
        self.sysex_commands = {}
        self.github_url = "https://github.com/supunnirman/chordsbook"
        self.github_raw_base = "https://raw.githubusercontent.com/supunnirman/chordsbook/main"
        self.github_data_dir = "github_data"
        self.github_songs_dir = os.path.join(self.github_data_dir, "songs")
        self.github_setlists_dir = os.path.join(self.github_data_dir, "setlists")
        self.github_activity_log = []
        self.section_dropdown_widgets = []
    
    def _setup_directories(self):
        self.songs_dir = "songs"
        self.setlists_dir = "setlists"
        self.github_data_dir = "github_data"
        self.github_songs_dir = os.path.join(self.github_data_dir, "songs")
        self.github_setlists_dir = os.path.join(self.github_data_dir, "setlists")
        
        for d in [self.songs_dir, self.setlists_dir, self.github_songs_dir, self.github_setlists_dir]:
            if not os.path.exists(d):
                os.makedirs(d)
                logging.info(f"Created directory: {d}")
    
    def load_sysex_commands(self):
        sysex_file = "SysEx.xml"
        self.sysex_commands = DEFAULT_SYSEX.copy()
        
        if os.path.exists(sysex_file):
            try:
                tree = ET.parse(sysex_file)
                root = tree.getroot()
                for cmd in root.findall('command'):
                    name = cmd.get('name')
                    value = cmd.text.strip() if cmd.text else ""
                    if name and value:
                        self.sysex_commands[name] = value
                        logging.info(f"Loaded SysEx command: {name} = {value}")
                logging.info(f"Loaded {len(root.findall('command'))} custom SysEx commands")
            except Exception as e:
                logging.error(f"Error loading SysEx.xml: {e}")
        else:
            logging.info("No SysEx.xml found, using default commands")
    
    def save_sysex_commands(self):
        sysex_file = "SysEx.xml"
        try:
            root = ET.Element("sysex_commands")
            for name, value in self.sysex_commands.items():
                cmd = ET.SubElement(root, "command", name=name)
                cmd.text = value
            
            ET.ElementTree(root).write(sysex_file, encoding='utf-8', xml_declaration=True)
            logging.info(f"Saved {len(self.sysex_commands)} SysEx commands to {sysex_file}")
            return True
        except Exception as e:
            logging.error(f"Error saving SysEx commands: {e}")
            return False
    
    def setup_menu_bar(self):
        self.menu_bar = tk.Menu(self)
        self.configure(menu=self.menu_bar)
        
        file_menu = tk.Menu(self.menu_bar, tearoff=0, bg="#1e1e1e", fg="white")
        self.menu_bar.add_cascade(label="File", menu=file_menu)
        file_menu.add_command(label="MIDI Configuration", command=self.open_midi_config_window)
        file_menu.add_separator()
        file_menu.add_command(label="Export All", command=self.export_all)
        file_menu.add_command(label="Import", command=self.import_data)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.on_closing)
        
        view_menu = tk.Menu(self.menu_bar, tearoff=0, bg="#1e1e1e", fg="white")
        self.menu_bar.add_cascade(label="View", menu=view_menu)
        view_menu.add_command(label="Toggle Chord Grid", command=self.toggle_chord_column)
        view_menu.add_command(label="Toggle Chord Separation", command=self.toggle_chord_separation)
        view_menu.add_separator()
        view_menu.add_command(label="Toggle Fullscreen", command=self.toggle_fullscreen)
        view_menu.add_command(label="Exit Perform Mode", command=self.exit_perform_mode)
        
        tools_menu = tk.Menu(self.menu_bar, tearoff=0, bg="#1e1e1e", fg="white")
        self.menu_bar.add_cascade(label="Tools", menu=tools_menu)
        tools_menu.add_command(label="SysEx Editor", command=self.open_sysex_editor)
        tools_menu.add_command(label="MIDI Monitor", command=self.open_midi_monitor)
        tools_menu.add_command(label="Sticky Note", command=self.open_sticky_note)
        
        broadcast_menu = tk.Menu(self.menu_bar, tearoff=0, bg="#1e1e1e", fg="white")
        self.menu_bar.add_cascade(label="Broadcast", menu=broadcast_menu)
        broadcast_menu.add_command(label="Start/Stop Broadcast", command=self.toggle_broadcast)
        broadcast_menu.add_command(label="Open Web View", command=self.open_web_view)
        
        help_menu = tk.Menu(self.menu_bar, tearoff=0, bg="#1e1e1e", fg="white")
        self.menu_bar.add_cascade(label="Help", menu=help_menu)
        help_menu.add_command(label="About", command=self.show_about)
    
    def export_all(self):
        try:
            filename = filedialog.asksaveasfilename(defaultextension=".zip", filetypes=[("ZIP files", "*.zip"), ("All files", "*.*")])
            if not filename:
                return
            
            with zipfile.ZipFile(filename, 'w', zipfile.ZIP_DEFLATED) as zipf:
                if os.path.exists(self.songs_dir):
                    for root, dirs, files in os.walk(self.songs_dir):
                        for file in files:
                            if file.endswith('.xml'):
                                file_path = os.path.join(root, file)
                                arcname = os.path.relpath(file_path, self.songs_dir)
                                zipf.write(file_path, os.path.join('songs', arcname))
                
                if os.path.exists(self.setlists_dir):
                    for root, dirs, files in os.walk(self.setlists_dir):
                        for file in files:
                            if file.endswith('.xml'):
                                file_path = os.path.join(root, file)
                                arcname = os.path.relpath(file_path, self.setlists_dir)
                                zipf.write(file_path, os.path.join('setlists', arcname))
                
                if os.path.exists("SysEx.xml"):
                    zipf.write("SysEx.xml", "SysEx.xml")
            
            messagebox.showinfo("Export Successful", f"All data exported to:\n{filename}")
            logging.info(f"Exported all data to: {filename}")
        except Exception as e:
            logging.error(f"Error exporting data: {e}")
            messagebox.showerror("Export Error", f"Failed to export: {str(e)}")
    
    def import_data(self):
        try:
            filename = filedialog.askopenfilename(filetypes=[("ZIP files", "*.zip"), ("All files", "*.*")])
            if not filename:
                return
            
            if not messagebox.askyesno("Import", "This will overwrite existing songs and setlists. Continue?"):
                return
            
            with zipfile.ZipFile(filename, 'r') as zipf:
                file_list = zipf.namelist()
                
                for file in file_list:
                    if file.startswith('songs/') and file.endswith('.xml'):
                        zipf.extract(file, '.')
                
                for file in file_list:
                    if file.startswith('setlists/') and file.endswith('.xml'):
                        zipf.extract(file, '.')
                
                for file in file_list:
                    if file == 'SysEx.xml':
                        zipf.extract(file, '.')
            
            self.refresh_list()
            messagebox.showinfo("Import Successful", f"Data imported from:\n{filename}")
            logging.info(f"Imported data from: {filename}")
        except Exception as e:
            logging.error(f"Error importing data: {e}")
            messagebox.showerror("Import Error", f"Failed to import: {str(e)}")
    
    def open_midi_config_window(self):
        if self.midi_config_window and self.midi_config_window.winfo_exists():
            self.midi_config_window.focus()
            return
        
        self.midi_config_window = ctk.CTkToplevel(self)
        self.midi_config_window.title("MIDI Configuration")
        self.midi_config_window.geometry("400x300")
        self.midi_config_window.attributes('-topmost', True)
        
        container = ctk.CTkFrame(self.midi_config_window)
        container.pack(fill="both", expand=True, padx=20, pady=20)
        
        ctk.CTkLabel(container, text="MIDI Device Configuration", font=("Arial", 16, "bold"), text_color=COLORS["accent"]).pack(pady=(0, 20))
        
        ctk.CTkButton(container, text="🔄 Scan MIDI Ports", width=200, height=40, font=("Arial", 12, "bold"), fg_color=COLORS["primary"], command=self._refresh_midi_ports).pack(pady=10)
        
        connect_frame = ctk.CTkFrame(container, fg_color="transparent")
        connect_frame.pack(fill="x", pady=10)
        ctk.CTkButton(connect_frame, text="🎵 Auto Connect", width=150, height=35, fg_color=COLORS["success"], font=("Arial", 11), command=self.auto_connect_midi).pack(side="left", padx=5)
        ctk.CTkButton(connect_frame, text="📊 MIDI Monitor", width=150, height=35, fg_color=COLORS["warning"], font=("Arial", 11), command=self.open_midi_monitor).pack(side="right", padx=5)
        
        status_frame = ctk.CTkFrame(container, fg_color="transparent")
        status_frame.pack(fill="x", pady=20)
        self.connection_status = ctk.CTkLabel(status_frame, text="●", font=("Arial", 24), text_color=COLORS["danger"])
        self.connection_status.pack(side="left", padx=(0, 10))
        
        self.midi_status_label = ctk.CTkLabel(status_frame, text="MIDI: Not Connected", font=("Arial", 12, "bold"), text_color=COLORS["danger"])
        self.midi_status_label.pack(side="left")
        
        self._refresh_midi_ports()
    
    def auto_connect_midi(self):
        try:
            out_ports, in_ports = self.midi_handler.scan_ports()
            if out_ports:
                if self.midi_handler.connect(out_ports[0], None):
                    self._update_midi_status()
                    messagebox.showinfo("Success", f"Connected to MIDI output: {out_ports[0]}")
                    return True
            messagebox.showwarning("Warning", "No MIDI output ports found")
            return False
        except Exception as e:
            logging.error(f"Error auto-connecting MIDI: {e}")
            messagebox.showerror("Error", f"Failed to connect: {e}")
            return False
    
    def open_web_view(self):
        if self.broadcast_enabled:
            webbrowser.open("http://localhost:5000")
        else:
            messagebox.showwarning("Warning", "Broadcast is not enabled. Start broadcast first.")
    
    def show_about(self):
        about_text = """Chord Manager by Supun Nirman

Version 1.0
Developed for Yamaha SX720 Keyboard

Features:
- Song and Setlist Management
- Chord Grid Display
- MIDI Control for Yamaha SX720
- Web Broadcast View
- Mobile Remote Control

Developed by: Supun Nirman Karunarathne
Mobile: 0775726873

© 2024 Chord Manager Project"""
        messagebox.showinfo("About Chord Manager", about_text)
    
    def _start_background_tasks(self):
        self.update_clock()
        self.refresh_list()
    
    def _bind_keyboard_shortcuts(self):
        self.bind("<Left>", lambda e: self.navigate_song(-1) if self.attributes("-fullscreen") else None)
        self.bind("<Right>", lambda e: self.navigate_song(1) if self.attributes("-fullscreen") else None)
        self.bind("<Escape>", lambda e: self.exit_perform_mode())
        self.bind("<Control-n>", lambda e: self.handle_add_click())
        self.bind("<Control-f>", lambda e: self.search_bar.focus() if hasattr(self, 'search_bar') else None)
        self.bind("<Control-s>", lambda e: self._save_current_song())
    
    def _save_current_song(self):
        if self.active_xml_file:
            self.save_chord_grid()
    
    def setup_ui(self):
        # Performance bar
        self.perf_bar = ctk.CTkFrame(self, height=DIMENSIONS["perf_bar_height"], fg_color=COLORS["secondary"], corner_radius=0)
        self.perf_bar.pack(fill="x", side="top", padx=0, pady=0)
        
        # Create horizontal scrollable frame for buttons
        self.perf_bar_canvas = tk.Canvas(self.perf_bar, height=DIMENSIONS["perf_bar_height"], bg=COLORS["secondary"], highlightthickness=0)
        self.perf_bar_scrollbar = ctk.CTkScrollbar(self.perf_bar, orientation="horizontal", command=self.perf_bar_canvas.xview)
        self.perf_bar_scrollable_frame = ctk.CTkFrame(self.perf_bar_canvas, fg_color=COLORS["secondary"])
        
        self.perf_bar_scrollable_frame.bind(
            "<Configure>",
            lambda e: self.perf_bar_canvas.configure(scrollregion=self.perf_bar_canvas.bbox("all"))
        )
        
        self.perf_bar_canvas.create_window((0, 0), window=self.perf_bar_scrollable_frame, anchor="nw")
        self.perf_bar_canvas.configure(xscrollcommand=self.perf_bar_scrollbar.set)
        
        self.perf_bar_canvas.pack(side="top", fill="x", expand=True)
        self.perf_bar_scrollbar.pack(side="bottom", fill="x")
        
        # Now add buttons to the scrollable frame
        ctk.CTkButton(self.perf_bar_scrollable_frame, text="⚡ PERFORM", fg_color=COLORS["warning"], width=120, height=50, font=FONTS["medium"], command=self.toggle_fullscreen).pack(side="left", padx=10)
        
        ctk.CTkButton(self.perf_bar_scrollable_frame, text="A-", width=50, height=50, font=FONTS["medium"], command=lambda: self.change_font(-2)).pack(side="left", padx=2)
        ctk.CTkButton(self.perf_bar_scrollable_frame, text="A+", width=50, height=50, font=FONTS["medium"], command=lambda: self.change_font(2)).pack(side="left", padx=2)
        
        # Scale offset with label on top
        scale_frame = ctk.CTkFrame(self.perf_bar_scrollable_frame, fg_color="transparent")
        scale_frame.pack(side="left", padx=10)
        ctk.CTkLabel(scale_frame, text="Transpose:", font=("Arial", 10, "bold"), text_color=COLORS["info"]).pack(side="top", pady=(0, 2))
        self.scale_offset_values = [f"+{i}" for i in range(10, 0, -1)] + ["0"] + [f"-{i}" for i in range(1, 11)]
        self.scale_offset_var = ctk.StringVar(value="0")
        self.scale_offset_dropdown = ctk.CTkOptionMenu(scale_frame, variable=self.scale_offset_var, values=self.scale_offset_values, width=80, height=35, font=("Arial", 12, "bold"), fg_color=COLORS["primary"], button_color=COLORS["accent"], button_hover_color=COLORS["warning"], command=self.on_scale_offset_change)
        self.scale_offset_dropdown.pack(side="top")
        
        # Sync Data button with two lines
        sync_data_btn = ctk.CTkButton(self.perf_bar_scrollable_frame, text="SYNC\nDATA", width=100, height=50, fg_color="#6e5494", font=("Arial", 10, "bold"), command=self.open_github_window)
        sync_data_btn.pack(side="left", padx=10)
        
        # Library count
        self.library_count_frame = ctk.CTkFrame(self.perf_bar_scrollable_frame, fg_color="transparent")
        self.library_count_frame.pack(side="left", padx=10)
        self.songs_count_label = ctk.CTkLabel(self.library_count_frame, text="Songs: 0", font=("Arial", 14, "bold"), text_color=COLORS["info"])
        self.songs_count_label.pack(side="top", pady=1)
        self.setlists_count_label = ctk.CTkLabel(self.library_count_frame, text="Setlists: 0", font=("Arial", 14, "bold"), text_color=COLORS["info"])
        self.setlists_count_label.pack(side="top", pady=1)
        self.data_source_label = ctk.CTkLabel(self.library_count_frame, text="Source: Local", font=("Arial", 10), text_color="#7f8c8d")
        self.data_source_label.pack(side="top", pady=1)
        
        # Clock
        self.clock_frame = ctk.CTkFrame(self.perf_bar_scrollable_frame, fg_color="transparent")
        self.clock_frame.pack(side="left", padx=25)
        self.clock_time_label = ctk.CTkLabel(self.clock_frame, text="00:00:00", font=FONTS["large"], text_color=COLORS["info"])
        self.clock_time_label.pack(side="left")
        self.ampm_frame = ctk.CTkFrame(self.clock_frame, fg_color="transparent")
        self.ampm_frame.pack(side="left", padx=5)
        self.am_label = ctk.CTkLabel(self.ampm_frame, text="AM", font=("Arial", 12, "bold"), text_color="#444444")
        self.am_label.pack(side="top")
        self.pm_label = ctk.CTkLabel(self.ampm_frame, text="PM", font=("Arial", 12, "bold"), text_color="#444444")
        self.pm_label.pack(side="top")
        
        # Timer
        self.timer_frame = ctk.CTkFrame(self.perf_bar_scrollable_frame, fg_color="transparent")
        self.timer_frame.pack(side="left", padx=5)
        self.timer_label = ctk.CTkLabel(self.timer_frame, text="00:00", font=("Arial", 24, "bold"))
        self.timer_label.pack(side="left", padx=10)
        ctk.CTkButton(self.timer_frame, text="▶ START", width=80, height=45, command=self.toggle_timer).pack(side="left", padx=2)
        ctk.CTkButton(self.timer_frame, text="🔄 RESET", width=80, height=45, fg_color="#7f8c8d", command=self.reset_timer).pack(side="left", padx=2)
        ctk.CTkButton(self.timer_frame, text="📌 STICKY", width=100, height=45, fg_color=COLORS["warning"], text_color="black", font=("Arial", 13, "bold"), command=self.open_sticky_note).pack(side="left", padx=5)
        ctk.CTkButton(self.timer_frame, text="▦ GRID", width=80, height=45, fg_color=COLORS["primary"], command=self.toggle_chord_column).pack(side="left", padx=5)
        self.broadcast_button = ctk.CTkButton(self.timer_frame, text="📡 BROADCAST", width=100, height=45, fg_color="#2ecc71", command=self.toggle_broadcast)
        self.broadcast_button.pack(side="left", padx=2)
        self.mobile_server_indicator = ctk.CTkLabel(self.timer_frame, text="📱", font=("Arial", 20), text_color=COLORS["info"])
        self.mobile_server_indicator.pack(side="left", padx=10)
        
        # Left navigation
        self.nav_column = ctk.CTkFrame(self, width=DIMENSIONS["nav_width"], corner_radius=0, fg_color=COLORS["secondary"])
        self.nav_column.pack(side="left", fill="y", padx=1)
        self.nav_column.pack_propagate(False)
        
        self.tab_frame = ctk.CTkFrame(self.nav_column, fg_color="transparent")
        self.tab_frame.pack(fill="x", pady=5, padx=5)
        ctk.CTkButton(self.tab_frame, text="🎵 SONGS", width=120, font=("Arial", 10), command=lambda: self.switch_tab("songs")).pack(side="left", padx=2)
        ctk.CTkButton(self.tab_frame, text="📋 SETLISTS", width=120, font=("Arial", 10), command=lambda: self.switch_tab("setlists")).pack(side="left", padx=2)
        
        self.search_var = ctk.StringVar()
        self.search_var.trace_add("write", lambda *args: self.refresh_list())
        self.search_bar = ctk.CTkEntry(self.nav_column, placeholder_text="🔍 Search...", font=("Arial", 10), height=35)
        self.search_bar.pack(fill="x", padx=10, pady=5)
        
        self.btn_dynamic_add = ctk.CTkButton(self.nav_column, text="➕ ADD SONG", fg_color=COLORS["success"], font=("Arial", 10), height=35, command=self.handle_add_click)
        self.btn_dynamic_add.pack(fill="x", pady=5, padx=10)
        
        self.scroll_list = ctk.CTkScrollableFrame(self.nav_column, fg_color="transparent")
        self.scroll_list.pack(fill="both", expand=True)
        
        # Chord column
        self.chord_column = ctk.CTkFrame(self, width=DIMENSIONS["chord_width"], corner_radius=0, fg_color=COLORS["secondary"])
        self.chord_column.pack(side="right", fill="y", padx=1)
        self.chord_column.pack_propagate(False)
        
        ctk.CTkLabel(self.chord_column, text="CHORD GRID", font=("Arial", 14, "bold"), text_color=COLORS["accent"]).pack(pady=10)
        
        self.grid_ctrl = ctk.CTkFrame(self.chord_column, fg_color="transparent")
        self.grid_ctrl.pack(fill="x", padx=10)
        ctk.CTkButton(self.grid_ctrl, text="A-", width=40, height=30, font=("Arial", 10), command=lambda: self.change_chord_grid_font(-1)).pack(side="left", padx=2)
        ctk.CTkButton(self.grid_ctrl, text="A+", width=40, height=30, font=("Arial", 10), command=lambda: self.change_chord_grid_font(1)).pack(side="left", padx=2)
        ctk.CTkButton(self.grid_ctrl, text="+", width=40, height=30, font=("Arial", 10), command=lambda: self.add_grid_row("chords")).pack(side="left", padx=5)
        ctk.CTkButton(self.grid_ctrl, text="SECTION", width=80, height=30, font=("Arial", 10), command=lambda: self.add_grid_row("section")).pack(side="left", padx=5)
        
        self.grid_scroll = ctk.CTkScrollableFrame(self.chord_column, fg_color="transparent")
        self.grid_scroll.pack(fill="both", expand=True, padx=5, pady=5)
        
        self.grid_save_frame = ctk.CTkFrame(self.chord_column, fg_color="transparent")
        self.grid_save_frame.pack(fill="x", padx=10, pady=10)
        self.btn_save_chords = ctk.CTkButton(self.grid_save_frame, text="💾 SAVE", fg_color=COLORS["info"], height=35, width=170, font=("Arial", 11), command=self.save_chord_grid)
        self.btn_save_chords.pack(side="left", padx=2)
        self.btn_edit_chords = ctk.CTkButton(self.grid_save_frame, text="✏️ EDIT", fg_color="#7f8c8d", height=35, width=170, font=("Arial", 11), command=self.toggle_grid_edit)
        self.btn_edit_chords.pack(side="left", padx=2)
        
        # Main display
        self.main_display = ctk.CTkFrame(self, corner_radius=0, fg_color=COLORS["background"])
        self.main_display.pack(side="right", fill="both", expand=True)
        
        self.yamaha_bar = ctk.CTkFrame(self.main_display, height=70, fg_color=COLORS["secondary"])
        self.yamaha_bar.pack(fill="x", side="top", padx=10, pady=0)
        self.song_info_lbl = ctk.CTkLabel(self.yamaha_bar, text="Select Song or Setlist", font=("Arial", 14, "bold"), text_color=COLORS["accent"])
        self.song_info_lbl.pack(side="left", padx=15)
        self.btn_toggle_view = ctk.CTkButton(self.yamaha_bar, text="👁 SEPARATE VIEW", fg_color=COLORS["info"], height=35, font=("Arial", 11), command=self.toggle_chord_separation)
        
        self.section_order_bar = ctk.CTkFrame(self.main_display, height=40, fg_color=COLORS["panel"])
        self.section_order_bar.pack(fill="x", side="top", padx=10, pady=(0, 5))
        
        self.perf_nav_bar = ctk.CTkFrame(self.main_display, height=70, fg_color=COLORS["secondary"])
        self.btn_prev_song = ctk.CTkButton(self.perf_nav_bar, text="⏮ PREVIOUS", fg_color=COLORS["primary"], height=50, font=("Arial", 16, "bold"), command=lambda: self.navigate_song(-1))
        self.btn_prev_song.pack(side="left", fill="x", expand=True, padx=10, pady=10)
        self.btn_next_song = ctk.CTkButton(self.perf_nav_bar, text="NEXT ⏭", fg_color=COLORS["primary"], height=50, font=("Arial", 16, "bold"), command=lambda: self.navigate_song(1))
        self.btn_next_song.pack(side="left", fill="x", expand=True, padx=10, pady=10)
        
        self.content_container = ctk.CTkFrame(self.main_display, fg_color="transparent")
        self.content_container.pack(fill="both", expand=True, padx=20, pady=10)
        
        self.display_text = ctk.CTkTextbox(self.content_container, font=("Consolas", self.current_font_size), padx=30, spacing3=12, wrap="none")
        self.display_text.pack(fill="both", expand=True)
        
        self.setlist_view_frame = ctk.CTkScrollableFrame(self.content_container, fg_color=COLORS["background"])
        
        self.refresh_list()
        self.update_library_counts()
    
    def scroll_display(self, lines):
        if self.display_text.winfo_viewable():
            current_pos = self.display_text.yview()
            new_pos = max(0.0, min(1.0, current_pos[0] + (lines * 0.01)))
            self.display_text.yview_moveto(new_pos)
    
    def scroll_chord_grid(self, rows):
        if self.grid_scroll.winfo_viewable():
            current_pos = self.grid_scroll._parent_canvas.yview()
            new_pos = max(0.0, min(1.0, current_pos[0] + (rows * 0.05)))
            self.grid_scroll._parent_canvas.yview_moveto(new_pos)
    
    def update_library_counts(self):
        try:
            if self.data_source == "local":
                songs_dir = self.songs_dir
                setlists_dir = self.setlists_dir
            else:
                songs_dir = self.github_songs_dir
                setlists_dir = self.github_setlists_dir
            
            if os.path.exists(songs_dir):
                songs_count = len([f for f in os.listdir(songs_dir) if f.endswith('.xml')])
            else:
                songs_count = 0
            
            if os.path.exists(setlists_dir):
                setlists_count = len([f for f in os.listdir(setlists_dir) if f.endswith('.xml')])
            else:
                setlists_count = 0
            
            self.songs_count_label.configure(text=f"Songs: {songs_count}")
            self.setlists_count_label.configure(text=f"Setlists: {setlists_count}")
            
            source_text = f"Source: {'Local' if self.data_source == 'local' else 'GitHub Cache'}"
            self.data_source_label.configure(text=source_text)
        except Exception as e:
            logging.error(f"Error updating library counts: {e}")
    
    def toggle_fullscreen(self):
        is_fs = not self.attributes("-fullscreen")
        self.attributes("-fullscreen", is_fs)
        
        if is_fs:
            self.nav_column.pack_forget()
            self.grid_save_frame.pack_forget()
            self.grid_ctrl.pack_forget()
            self.perf_nav_bar.pack(side="bottom", fill="x", pady=5)
            self.btn_toggle_view.pack(side="right", padx=15, pady=10)
        else:
            self.perf_nav_bar.pack_forget()
            self.btn_toggle_view.pack_forget()
            self.nav_column.pack(side="left", fill="y", padx=1)
            self.grid_save_frame.pack(fill="x", padx=10, pady=10)
            self.chord_column.pack(side="right", fill="y", padx=1, before=self.main_display)
        
        if self.active_xml_file:
            try:
                path = os.path.join(self.songs_dir, self.active_xml_file)
                content = ET.parse(path).getroot().findtext('content', '')
                self.parse_content(content)
            except Exception as e:
                logging.error(f"Error refreshing content: {e}")
    
    def parse_content(self, text):
        self.display_text.configure(state="normal")
        self.display_text.delete("1.0", "end")
        is_perform = self.attributes("-fullscreen")
        current_font = "Consolas" if is_perform else "Tahoma"
        self.display_text.configure(font=(current_font, self.current_font_size))
        chord_separation = is_perform and self.chord_separate_mode
        
        for raw_line in text.split('\n'):
            if not chord_separation:
                parts = re.split(r'(\[.*?\])', raw_line)
                for p in parts:
                    if p.startswith('[') and p[1:-1].upper() in PROTECTED_SECTIONS:
                        tag = "label"
                    elif p.startswith('['):
                        chord_content = p[1:-1]
                        if chord_content.upper() not in PROTECTED_SECTIONS:
                            transposed_chord = self.transpose_chord(chord_content, self.transpose_semitones)
                            p = f"[{transposed_chord}]"
                        tag = "chord"
                    else:
                        tag = None
                    self.display_text.insert("end", p, tag)
                self.display_text.insert("end", "\n")
            else:
                chord_line = ""
                lyric_line = ""
                parts = re.split(r'(\[.*?\])', raw_line)
                current_lyric_len = 0
                
                for p in parts:
                    if p.startswith('[') and p.endswith(']'):
                        content = p[1:-1]
                        if content.upper() in PROTECTED_SECTIONS:
                            self.display_text.insert("end", "\n" + content + "\n", "label")
                        else:
                            transposed_content = self.transpose_chord(content, self.transpose_semitones)
                            padding_needed = current_lyric_len - len(chord_line)
                            if padding_needed > 0:
                                chord_line += " " * padding_needed
                            chord_line += transposed_content
                    else:
                        lyric_line += p
                        current_lyric_len += len(p)
                
                if chord_line.strip():
                    self.display_text.insert("end", chord_line + "\n", "chord")
                if lyric_line.strip():
                    self.display_text.insert("end", lyric_line + "\n")
        
        self.display_text.tag_config("chord", foreground=COLORS["accent"])
        self.display_text.tag_config("label", foreground=COLORS["info"])
        self.display_text.configure(state="disabled")
    
    def change_font(self, delta):
        self.current_font_size += delta
        self.current_font_size = max(8, min(72, self.current_font_size))
        
        if self.active_xml_file:
            try:
                path = os.path.join(self.songs_dir, self.active_xml_file)
                content = ET.parse(path).getroot().findtext('content', '')
                self.parse_content(content)
            except Exception as e:
                logging.error(f"Error changing font: {e}")
    
    def transpose_chord(self, chord, semitones):
        if not chord or chord.upper() in PROTECTED_SECTIONS:
            return chord
        
        match = re.match(r'([A-G][#b]?)(.*)', chord)
        if not match:
            return chord
        
        root = match.group(1)
        suffix = match.group(2)
        chromatic_scale = ["C", "C#", "D", "Eb", "E", "F", "F#", "G", "Ab", "A", "Bb", "B"]
        enharmonic_map = {"Db": "C#", "D#": "Eb", "Gb": "F#", "G#": "Ab", "A#": "Bb"}
        
        if root in enharmonic_map:
            root = enharmonic_map[root]
        elif root not in chromatic_scale:
            root_upper = root.upper()
            if root_upper in enharmonic_map:
                root = enharmonic_map[root_upper]
            elif root_upper in chromatic_scale:
                root = root_upper
            else:
                return chord
        
        try:
            current_index = chromatic_scale.index(root)
        except ValueError:
            return chord
        
        new_index = (current_index + semitones) % 12
        new_root = chromatic_scale[new_index]
        return f"{new_root}{suffix}"
    
    def on_scale_offset_change(self, new_offset_str):
        if not self.active_xml_file:
            return
        
        try:
            if new_offset_str.startswith('+'):
                self.current_scale_offset = int(new_offset_str[1:])
            elif new_offset_str.startswith('-'):
                self.current_scale_offset = -int(new_offset_str[1:])
            else:
                self.current_scale_offset = int(new_offset_str)
            
            self.transpose_semitones = self.current_scale_offset
            self.update_display_for_scale()
            logging.info(f"Changed semitone offset to: {new_offset_str} ({self.transpose_semitones:+d} semitones)")
        except ValueError:
            logging.error(f"Invalid semitone offset: {new_offset_str}")
    
    def update_display_for_scale(self):
        if self.active_xml_file:
            try:
                path = os.path.join(self.songs_dir, self.active_xml_file)
                content = ET.parse(path).getroot().findtext('content', '')
                self.parse_content(content)
                
                if self.grid_rows:
                    self.refresh_grid_ui()
            except Exception as e:
                logging.error(f"Error updating display for scale: {e}")
    
    def update_clock(self):
        current_time = time.strftime("%I:%M:%S")
        period = time.strftime("%p")
        self.clock_time_label.configure(text=current_time)
        
        if period == "AM":
            self.am_label.configure(text_color=COLORS["info"])
            self.pm_label.configure(text_color="#444444")
        else:
            self.am_label.configure(text_color="#444444")
            self.pm_label.configure(text_color=COLORS["info"])
        
        self.after(1000, self.update_clock)
    
    def reset_timer(self):
        self.timer_running = False
        self.elapsed_time = 0
        self.timer_label.configure(text="00:00")
    
    def toggle_timer(self):
        self.timer_running = not self.timer_running
        if self.timer_running:
            self.start_time = time.time() - self.elapsed_time
            self.run_timer()
        else:
            self.elapsed_time = time.time() - self.start_time
    
    def run_timer(self):
        if self.timer_running:
            self.elapsed_time = time.time() - self.start_time
            m, s = divmod(int(self.elapsed_time), 60)
            self.timer_label.configure(text=f"{m:02d}:{s:02d}")
            self.after(1000, self.run_timer)
    
    def refresh_list(self):
        for w in self.scroll_list.winfo_children():
            w.destroy()
        
        if self.current_tab == "songs":
            if self.data_source == "local":
                dir_path = self.songs_dir
            else:
                dir_path = self.github_songs_dir
        else:
            if self.data_source == "local":
                dir_path = self.setlists_dir
            else:
                dir_path = self.github_setlists_dir
        
        query = self.search_var.get().lower()
        
        try:
            files = sorted([f for f in os.listdir(dir_path) if f.endswith(".xml")])
        except Exception as e:
            logging.error(f"Error listing files in {dir_path}: {e}")
            return
        
        for f in files:
            name = f.replace(".xml", "")
            if query and query not in name.lower():
                continue
            
            row = ctk.CTkFrame(self.scroll_list, fg_color="transparent")
            row.pack(fill="x", pady=1)
            
            if self.current_tab == "songs":
                ctk.CTkButton(row, text=name, anchor="w", font=("Arial", 10), command=lambda x=f: self.load_song_content(x)).pack(side="left", fill="x", expand=True)
            else:
                ctk.CTkButton(row, text=name, anchor="w", font=("Arial", 10), command=lambda x=f: self.show_setlist_in_main(x)).pack(side="left", fill="x", expand=True)
                ctk.CTkButton(row, text="LOAD", width=45, fg_color="#e67e22", font=("Arial", 9, "bold"), command=lambda x=f: self.show_setlist_in_main(x)).pack(side="left", padx=1)
            
            ctk.CTkButton(row, text="✎", width=35, font=("Arial", 10), command=lambda x=f: (self.open_song_editor(x) if self.current_tab=="songs" else self.open_setlist_editor(x))).pack(side="left", padx=1)
            ctk.CTkButton(row, text="🗑", width=35, fg_color=COLORS["danger"], font=("Arial", 10), command=lambda x=f: self.delete_item(x)).pack(side="left")
    
    def load_song_content(self, filename):
        if self.note_win and self.note_win.winfo_exists():
            self.save_current_note()
        
        self.setlist_view_frame.pack_forget()
        self.display_text.pack(fill="both", expand=True)
        self.active_xml_file = filename
        
        if self.data_source == "local":
            path = os.path.join(self.songs_dir, filename)
        else:
            path = os.path.join(self.github_songs_dir, filename)
        
        if not os.path.exists(path):
            logging.warning(f"Song file not found: {path}")
            messagebox.showerror("Error", f"Song file not found: {filename}")
            return
        
        try:
            tree = ET.parse(path)
            root = tree.getroot()
            
            # Check for required tags and handle missing ones
            title = root.findtext('title', '')
            if not title:
                title = filename.replace('.xml', '')
            
            tempo = root.findtext('tempo', '120')
            
            self.song_info_lbl.configure(text=f"{title} | BPM: {tempo}")
            
            song_scale = root.findtext('scale', 'C')
            self.song_original_scale = song_scale
            self.scale_offset_var.set("0")
            self.current_scale_offset = 0
            self.transpose_semitones = 0
            
            # Try to get content from various possible tags
            content = root.findtext('content', '')
            if not content:
                # Try other possible tags
                content = root.findtext('lyrics', '')
                if not content:
                    content = root.findtext('text', '')
                if not content:
                    # If no content found, use filename as content
                    content = f"[VERSE]\n{title}\n"
            
            self.parse_content(content)
            self.load_chord_grid(root)
            self.load_section_order(root)
            self.update_nav_buttons()
            logging.info(f"Loaded song: {filename} (Original Scale: {song_scale})")
        except Exception as e:
            logging.error(f"Error loading song {filename}: {e}")
            # If XML parsing fails, create basic song from filename
            self.song_info_lbl.configure(text=f"{filename.replace('.xml', '')} | BPM: 120")
            self.song_original_scale = "C"
            self.scale_offset_var.set("0")
            self.current_scale_offset = 0
            self.transpose_semitones = 0
            content = f"[VERSE]\n{filename.replace('.xml', '')}\n"
            self.parse_content(content)
            messagebox.showwarning("Warning", f"Song loaded with basic info. Consider editing it properly.")
    
    def load_section_order(self, root):
        for widget in self.section_order_bar.winfo_children():
            widget.destroy()
        
        self.section_dropdowns = []
        self.section_dropdown_widgets = []
        section_order = root.find('section_order')
        
        if section_order is not None:
            sections = section_order.findall('section')
            if sections:
                section_options = ["ADLIB", "INTRO", "CHORUS", "VERSE", "INTER", "BRIDGE", "SOLO", "ENDING", "HOOK", "OUTRO"]
                for i, section in enumerate(sections):
                    if i < 20:
                        section_text = section.text
                        var = ctk.StringVar(value=section_text)
                        dropdown = ctk.CTkOptionMenu(self.section_order_bar, variable=var, values=section_options, width=80, height=30, fg_color=SECTION_COLORS.get(section_text, COLORS["primary"]), button_color=SECTION_COLORS.get(section_text, COLORS["accent"]), button_hover_color=SECTION_COLORS.get(section_text, COLORS["warning"]), dropdown_fg_color=COLORS["secondary"])
                        dropdown.pack(side="left", padx=2, pady=5)
                        self.section_dropdowns.append(var)
                        self.section_dropdown_widgets.append(dropdown)
                
                control_frame = ctk.CTkFrame(self.section_order_bar, fg_color="transparent")
                control_frame.pack(side="left", padx=10)
                ctk.CTkButton(control_frame, text="+", width=30, height=30, fg_color=COLORS["success"], command=self.add_section_dropdown).pack(side="left", padx=2)
                ctk.CTkButton(control_frame, text="-", width=30, height=30, fg_color=COLORS["danger"], command=self.remove_section_dropdown).pack(side="left", padx=2)
                
                save_clear_frame = ctk.CTkFrame(control_frame, fg_color="transparent")
                save_clear_frame.pack(side="left", padx=10)
                ctk.CTkButton(save_clear_frame, text="💾", width=30, height=30, fg_color=COLORS["info"], command=self.save_section_order).pack(side="left", padx=2)
                ctk.CTkButton(save_clear_frame, text="🗑", width=30, height=30, fg_color=COLORS["danger"], command=self.clear_section_order).pack(side="left", padx=2)
    
    def add_section_dropdown(self):
        if len(self.section_dropdowns) >= 20:
            messagebox.showwarning("Limit", "Maximum 20 sections allowed")
            return
        
        section_options = ["ADLIB", "INTRO", "CHORUS", "VERSE", "INTER", "BRIDGE", "SOLO", "ENDING", "HOOK", "OUTRO"]
        var = ctk.StringVar(value="")
        dropdown = ctk.CTkOptionMenu(self.section_order_bar, variable=var, values=section_options, width=80, height=30, fg_color=COLORS["primary"], button_color=COLORS["accent"], button_hover_color=COLORS["warning"], dropdown_fg_color=COLORS["secondary"])
        
        for widget in self.section_order_bar.winfo_children():
            if isinstance(widget, ctk.CTkFrame) and widget.winfo_children() and hasattr(widget.winfo_children()[0], 'cget') and widget.winfo_children()[0].cget('text') == '+':
                dropdown.pack(side="left", padx=2, pady=5, before=widget)
                break
        
        self.section_dropdowns.append(var)
        self.section_dropdown_widgets.append(dropdown)
    
    def remove_section_dropdown(self):
        if not self.section_dropdowns:
            return
        
        last_dropdown = self.section_dropdown_widgets.pop()
        last_dropdown.destroy()
        self.section_dropdowns.pop()
    
    def save_section_order(self):
        if not self.active_xml_file:
            messagebox.showwarning("Warning", "No song loaded")
            return
        
        try:
            if self.data_source == "local":
                path = os.path.join(self.songs_dir, self.active_xml_file)
            else:
                path = os.path.join(self.github_songs_dir, self.active_xml_file)
            
            tree = ET.parse(path)
            root = tree.getroot()
            section_order = root.find('section_order')
            
            if section_order is not None:
                root.remove(section_order)
            
            section_order = ET.SubElement(root, 'section_order')
            for i, var in enumerate(self.section_dropdowns):
                if var.get():
                    section = ET.SubElement(section_order, 'section')
                    section.text = var.get()
            
            tree.write(path)
            logging.info(f"Saved section order to: {path}")
            messagebox.showinfo("Success", "Section order saved!")
        except Exception as e:
            logging.error(f"Error saving section order: {e}")
            messagebox.showerror("Error", f"Failed to save section order: {e}")
    
    def clear_section_order(self):
        for dropdown in self.section_dropdown_widgets:
            dropdown.destroy()
        
        self.section_dropdowns = []
        self.section_dropdown_widgets = []
        self.load_section_order(ET.Element("dummy"))
        
        if self.active_xml_file:
            try:
                if self.data_source == "local":
                    path = os.path.join(self.songs_dir, self.active_xml_file)
                else:
                    path = os.path.join(self.github_songs_dir, self.active_xml_file)
                
                tree = ET.parse(path)
                root = tree.getroot()
                section_order = root.find('section_order')
                
                if section_order is not None:
                    root.remove(section_order)
                    tree.write(path)
                
                logging.info(f"Cleared section order for: {self.active_xml_file}")
            except Exception as e:
                logging.error(f"Error clearing section order: {e}")
    
    def toggle_chord_separation(self):
        self.chord_separate_mode = not self.chord_separate_mode
        if self.chord_separate_mode:
            self.btn_toggle_view.configure(text="👁 COMBINED VIEW", fg_color=COLORS["warning"])
        else:
            self.btn_toggle_view.configure(text="👁 SEPARATE VIEW", fg_color=COLORS["info"])
        
        if self.active_xml_file:
            try:
                if self.data_source == "local":
                    path = os.path.join(self.songs_dir, self.active_xml_file)
                else:
                    path = os.path.join(self.github_songs_dir, self.active_xml_file)
                
                content = ET.parse(path).getroot().findtext('content', '')
                self.parse_content(content)
            except Exception as e:
                logging.error(f"Error toggling chord separation: {e}")
    
    def exit_perform_mode(self):
        if self.attributes("-fullscreen"):
            self.toggle_fullscreen()
    
    def add_grid_row(self, row_type="chords", values=None):
        idx = len(self.grid_rows)
        
        if row_type == "section":
            bg_color = "#1a3a5a"
        else:
            bg_color = "#252525" if idx % 2 == 0 else "#1e1e1e"
        
        row_height = 35
        row_frame = ctk.CTkFrame(self.grid_scroll, fg_color=bg_color, corner_radius=4, height=row_height)
        row_frame.pack(fill="x", pady=1)
        row_frame.pack_propagate(False)
        
        data_items = []
        is_fullscreen = self.attributes("-fullscreen")
        
        if is_fullscreen:
            grid_font = ("Arial", self.chord_grid_font_size, "bold")
        else:
            grid_font = ("Arial", self.chord_grid_font_size)
        
        section_font = ("Arial", self.chord_grid_font_size + 1, "bold")
        delete_frame = None
        
        if self.is_grid_edit_mode:
            delete_frame = ctk.CTkFrame(row_frame, fg_color="transparent", width=40)
            delete_frame.pack(side="right", padx=(2, 0))
            delete_frame.pack_propagate(False)
            delete_button = ctk.CTkButton(delete_frame, text="🗑", width=35, height=row_height-10, fg_color=COLORS["danger"], font=("Arial", 10), command=lambda i=idx: self.delete_grid_row(i))
            delete_button.pack(side="right", padx=(0, 5))
        
        content_frame = ctk.CTkFrame(row_frame, fg_color="transparent")
        content_frame.pack(side="left", fill="both", expand=True, padx=(5, 0))
        
        if self.is_grid_edit_mode:
            move_frame = ctk.CTkFrame(content_frame, fg_color="transparent", width=55)
            move_frame.pack(side="left")
            move_frame.pack_propagate(False)
            ctk.CTkButton(move_frame, text="▲", width=25, height=row_height-10, font=("Arial", 10), command=lambda i=idx: self.move_grid_row(i, -1)).pack(side="left", padx=1)
            ctk.CTkButton(move_frame, text="▼", width=25, height=row_height-10, font=("Arial", 10), command=lambda i=idx: self.move_grid_row(i, 1)).pack(side="left", padx=1)
            
            if row_type == "section":
                entry = ctk.CTkEntry(content_frame, height=row_height-10, font=section_font, text_color=COLORS["info"])
                entry.pack(side="left", fill="x", expand=True, padx=2)
                if values:
                    entry.insert(0, values[0])
                data_items.append(entry)
            else:
                chords_frame = ctk.CTkFrame(content_frame, fg_color="transparent")
                chords_frame.pack(side="left", fill="both", expand=True)
                for i in range(4):
                    entry = ctk.CTkEntry(chords_frame, width=70, height=row_height-10, font=grid_font, justify="center")
                    entry.pack(side="left", padx=1, fill="x", expand=True)
                    if values and i < len(values):
                        chord = values[i]
                        if chord:
                            transposed_chord = self.transpose_chord(chord, self.transpose_semitones)
                            entry.insert(0, transposed_chord)
                        else:
                            entry.insert(0, "")
                    data_items.append(entry)
        else:
            if row_type == "section":
                label_text = values[0] if values else ""
                label = ctk.CTkLabel(content_frame, text=label_text, font=section_font, text_color=COLORS["accent"], height=row_height-10)
                label.pack(fill="x", expand=True, padx=5)
                data_items.append(label)
            else:
                chords_frame = ctk.CTkFrame(content_frame, fg_color="transparent")
                chords_frame.pack(side="left", fill="both", expand=True)
                for i in range(4):
                    text = values[i] if values and i < len(values) else ""
                    if text:
                        text = self.transpose_chord(text, self.transpose_semitones)
                    label = ctk.CTkLabel(chords_frame, text=text, height=row_height-10, font=grid_font, anchor="center")
                    label.pack(side="left", padx=1, fill="x", expand=True)
                    data_items.append(label)
        
        self.grid_rows.append({"frame": row_frame, "data": data_items, "type": row_type, "values": values if values else ["", "", "", ""]})
    
    def move_grid_row(self, index, direction):
        new_index = index + direction
        if 0 <= new_index < len(self.grid_rows):
            for row in self.grid_rows:
                row["values"] = [item.get() if hasattr(item, 'get') else item.cget("text") for item in row["data"]]
            
            self.grid_rows[index], self.grid_rows[new_index] = (self.grid_rows[new_index], self.grid_rows[index])
            self.refresh_grid_ui()
    
    def delete_grid_row(self, index):
        if 0 <= index < len(self.grid_rows):
            if 'frame' in self.grid_rows[index]:
                self.grid_rows[index]['frame'].destroy()
            self.grid_rows.pop(index)
            self.refresh_grid_ui()
    
    def refresh_grid_ui(self):
        stored_data = []
        for r in self.grid_rows:
            vals = [item.get() if hasattr(item, 'get') else item.cget("text") for item in r["data"]]
            stored_data.append({"type": r["type"], "vals": vals})
        
        for r in self.grid_rows:
            r["frame"].destroy()
        
        self.grid_rows = []
        for data in stored_data:
            self.add_grid_row(data["type"], data["vals"])
    
    def toggle_chord_column(self):
        if self.chord_column.winfo_viewable():
            self.chord_column.pack_forget()
        else:
            self.chord_column.pack(side="right", fill="y", padx=1, before=self.main_display)
    
    def toggle_grid_edit(self):
        self.is_grid_edit_mode = not self.is_grid_edit_mode
        self.btn_edit_chords.configure(text="👁 VIEW" if self.is_grid_edit_mode else "✏️ EDIT", fg_color=COLORS["danger"] if self.is_grid_edit_mode else "#7f8c8d")
        
        if self.active_xml_file:
            try:
                if self.data_source == "local":
                    path = os.path.join(self.songs_dir, self.active_xml_file)
                else:
                    path = os.path.join(self.github_songs_dir, self.active_xml_file)
                
                tree = ET.parse(path)
                root = tree.getroot()
                self.load_chord_grid(root)
            except Exception as e:
                logging.error(f"Error loading chord grid: {e}")
    
    def save_chord_grid(self):
        if not self.active_xml_file:
            logging.warning("No song selected for chord grid save")
            return
        
        try:
            if self.data_source == "local":
                path = os.path.join(self.songs_dir, self.active_xml_file)
            else:
                path = os.path.join(self.github_songs_dir, self.active_xml_file)
            
            if not os.path.exists(path):
                logging.error(f"Song file does not exist: {path}")
                return
            
            tree = ET.parse(path)
            root = tree.getroot()
            grid_xml = root.find('chord_grid')
            
            if grid_xml is not None:
                root.remove(grid_xml)
            
            grid_xml = ET.SubElement(root, 'chord_grid')
            for row in self.grid_rows:
                r_elem = ET.SubElement(grid_xml, 'row', type=row["type"])
                for item in row["data"]:
                    val = item.get() if hasattr(item, 'get') else item.cget("text")
                    original_val = val
                    if val and row["type"] == "chords":
                        original_val = self.transpose_chord(val, -self.transpose_semitones)
                    ET.SubElement(r_elem, 'cell').text = original_val
            
            tree.write(path)
            self.is_grid_edit_mode = False
            self.toggle_grid_edit()
            logging.info(f"Saved chord grid to: {path}")
        except Exception as e:
            logging.error(f"Error saving chord grid: {e}")
    
    def load_chord_grid(self, root):
        for r in self.grid_rows:
            r["frame"].destroy()
        
        self.grid_rows = []
        
        if self.is_grid_edit_mode:
            self.grid_ctrl.pack(fill="x", padx=10)
            self.grid_scroll.pack(fill="both", expand=True, padx=5, pady=5)
        else:
            self.grid_ctrl.pack_forget()
        
        grid_xml = root.find('chord_grid')
        if grid_xml is not None:
            for r_elem in grid_xml.findall('row'):
                rtype = r_elem.get('type', 'chords')
                vals = [c.text if c.text else "" for c in r_elem.findall('cell')]
                self.add_grid_row(rtype, vals)
        else:
            logging.info("No chord grid found in song file")
    
    def change_chord_grid_font(self, delta):
        self.chord_grid_font_size += delta
        self.chord_grid_font_size = max(8, min(24, self.chord_grid_font_size))
        
        if self.grid_rows:
            self.refresh_grid_ui()
        
        logging.info(f"Chord grid font size changed to: {self.chord_grid_font_size}")
    
    def open_sticky_note(self):
        if not self.active_xml_file:
            return
        
        if self.note_win and self.note_win.winfo_exists():
            self.note_win.focus()
            return
        
        try:
            if self.data_source == "local":
                path = os.path.join(self.songs_dir, self.active_xml_file)
            else:
                path = os.path.join(self.github_songs_dir, self.active_xml_file)
            
            root = ET.parse(path).getroot()
            note_text = root.findtext('notes', '')
            
            self.note_win = ctk.CTkToplevel(self)
            self.note_win.title("Note")
            self.note_win.geometry("300x350+50+50")
            self.note_win.attributes("-topmost", True)
            
            self.txt_note = ctk.CTkTextbox(self.note_win, fg_color="#fef3b7", text_color="black")
            self.txt_note.pack(fill="both", expand=True)
            self.txt_note.insert("1.0", note_text)
            
            self.note_win.protocol("WM_DELETE_WINDOW", lambda: [self.save_current_note(), self.note_win.destroy()])
        except Exception as e:
            logging.error(f"Error opening sticky note: {e}")
    
    def save_current_note(self):
        if not hasattr(self, 'txt_note') or not self.txt_note:
            return
        
        try:
            if self.data_source == "local":
                path = os.path.join(self.songs_dir, self.active_xml_file)
            else:
                path = os.path.join(self.github_songs_dir, self.active_xml_file)
            
            tree = ET.parse(path)
            root = tree.getroot()
            notes = root.find('notes')
            
            if notes is None:
                notes = ET.SubElement(root, 'notes')
            
            notes.text = self.txt_note.get("1.0", "end-1c")
            tree.write(path)
        except Exception as e:
            logging.error(f"Error saving note: {e}")
    
    def _refresh_midi_ports(self):
        out_ports, in_ports = self.midi_handler.scan_ports()
        if out_ports:
            self.midi_status_label.configure(text=f"Found {len(out_ports)} MIDI port(s)", text_color=COLORS["info"])
        else:
            self.midi_status_label.configure(text="No MIDI ports found", text_color=COLORS["danger"])
    
    def _update_midi_status(self):
        midi = self.midi_handler
        out_status = "✓" if midi.midi_out and not midi.midi_out.closed else "✗"
        status_text = f"MIDI: {out_status}"
        
        if midi.midi_out and not midi.midi_out.closed:
            color = COLORS["success"]
        else:
            color = COLORS["danger"]
        
        if hasattr(self, 'midi_status_label'):
            self.midi_status_label.configure(text=status_text, text_color=color)
        
        if hasattr(self, 'connection_status'):
            if midi.midi_out and not midi.midi_out.closed:
                self.connection_status.configure(text="●", text_color=COLORS["success"])
            else:
                self.connection_status.configure(text="●", text_color=COLORS["danger"])
    
    def log_midi(self, direction, msg):
        if self.monitor_win and self.monitor_win.winfo_exists():
            self.monitor_text.configure(state="normal")
            self.monitor_text.insert("end", f"[{direction}] {msg}\n")
            self.monitor_text.see("end")
            self.monitor_text.configure(state="disabled")
    
    def open_midi_monitor(self):
        if self.monitor_win and self.monitor_win.winfo_exists():
            self.monitor_win.focus()
            return
        
        self.monitor_win = ctk.CTkToplevel(self)
        self.monitor_win.title("MIDI MONITOR")
        self.monitor_win.geometry("500x600")
        self.monitor_win.attributes('-topmost', True)
        
        self.monitor_text = ctk.CTkTextbox(self.monitor_win, font=("Consolas", 12), fg_color="#000", text_color=COLORS["success"])
        self.monitor_text.pack(fill="both", expand=True, padx=10, pady=10)
        self.monitor_text.configure(state="disabled")
        
        ctk.CTkButton(self.monitor_win, text="CLEAR", command=lambda: [self.monitor_text.configure(state="normal"), self.monitor_text.delete("1.0", "end"), self.monitor_text.configure(state="disabled")]).pack(pady=5)
    
    def open_sysex_editor(self):
        try:
            editor_win = ctk.CTkToplevel(self)
            editor_win.title("SysEx Command Editor")
            editor_win.geometry("900x750")
            editor_win.attributes('-topmost', True)
            editor_win.grab_set()
            
            container = ctk.CTkScrollableFrame(editor_win)
            container.pack(fill="both", expand=True, padx=10, pady=10)
            
            self.sysex_entries = {}
            categories = {
                "MAIN VARIATIONS": ["A", "B", "C", "D"],
                "INTRO VARIATIONS": ["I1", "I2", "I3"],
                "ENDING VARIATIONS": ["E1", "E2", "E3"],
                "FILL-IN VARIATIONS": ["F1", "F2", "F3", "F4"],
                "SPECIAL": ["BREAK"],
                "CONTROL": ["ACMP_ON", "ACMP_OFF", "SYNC_START_ON", "SYNC_START_OFF", "START", "STOP"],
                "CHORD COMMANDS": ["CHORD_C", "CHORD_CM", "CHORD_G", "CHORD_GM"]
            }
            
            row = 0
            for category, commands in categories.items():
                ctk.CTkLabel(container, text=category, font=("Arial", 14, "bold"), text_color=COLORS["accent"]).grid(row=row, column=0, columnspan=4, sticky="w", pady=(10, 5), padx=5)
                row += 1
                
                for cmd in commands:
                    label_text = cmd
                    if cmd in ["A", "B", "C", "D"]:
                        label_text = f"VARIATION {cmd}"
                    elif cmd.startswith("I"):
                        label_text = f"INTRO {cmd[1:]}"
                    elif cmd.startswith("E"):
                        label_text = f"ENDING {cmd[1:]}"
                    elif cmd.startswith("F"):
                        label_text = f"FILL-IN {cmd[1:]}"
                    elif cmd == "ACMP_ON":
                        label_text = "ACMP ON"
                    elif cmd == "ACMP_OFF":
                        label_text = "ACMP OFF"
                    elif cmd == "SYNC_START_ON":
                        label_text = "SYNC START ON"
                    elif cmd == "SYNC_START_OFF":
                        label_text = "SYNC START OFF"
                    elif cmd == "START":
                        label_text = "STYLE START"
                    elif cmd == "STOP":
                        label_text = "STYLE STOP"
                    elif cmd.startswith("CHORD_"):
                        chord_name = cmd.replace("CHORD_", "")
                        if "S" in chord_name:
                            chord_name = chord_name.replace("S", "#")
                        elif "B" in chord_name and len(chord_name) > 1:
                            chord_name = chord_name.replace("B", "b")
                        label_text = f"CHORD {chord_name}"
                    
                    ctk.CTkLabel(container, text=label_text, width=120, font=("Arial", 10, "bold")).grid(row=row, column=0, sticky="w", padx=5, pady=2)
                    
                    entry = ctk.CTkEntry(container, width=400, font=("Consolas", 10))
                    entry.insert(0, self.sysex_commands.get(cmd, ""))
                    entry.grid(row=row, column=1, padx=5, pady=2)
                    self.sysex_entries[cmd] = entry
                    
                    ctk.CTkButton(container, text="TEST", width=60, height=28, fg_color=COLORS["warning"], command=lambda c=cmd, e=entry: self.test_sysex_command(c, e.get())).grid(row=row, column=2, padx=5, pady=2)
                    
                    ctk.CTkButton(container, text="DEFAULT", width=80, height=28, fg_color=COLORS["primary"], command=lambda c=cmd, e=entry: e.delete(0, "end") or e.insert(0, DEFAULT_SYSEX.get(c, ""))).grid(row=row, column=3, padx=5, pady=2)
                    row += 1
            
            ctk.CTkLabel(container, text="CHORD PLAYBACK SETTINGS", font=("Arial", 14, "bold"), text_color=COLORS["success"]).grid(row=row, column=0, columnspan=4, sticky="w", pady=(20, 5), padx=5)
            row += 1
            
            ctk.CTkLabel(container, text="Chord Octave:", width=120, font=("Arial", 10, "bold")).grid(row=row, column=0, sticky="w", padx=5, pady=2)
            octave_frame = ctk.CTkFrame(container, fg_color="transparent")
            octave_frame.grid(row=row, column=1, columnspan=3, sticky="w", padx=5, pady=2)
            ctk.CTkButton(octave_frame, text="-", width=30, height=30, command=lambda: [self.midi_handler.set_chord_octave(self.midi_handler.get_chord_octave() - 1), octave_label.configure(text=f"Octave: {self.midi_handler.get_chord_octave()}")]).pack(side="left", padx=2)
            octave_label = ctk.CTkLabel(octave_frame, text=f"Octave: {self.midi_handler.get_chord_octave()}", font=("Arial", 12, "bold"), text_color=COLORS["info"])
            octave_label.pack(side="left", padx=10)
            ctk.CTkButton(octave_frame, text="+", width=30, height=30, command=lambda: [self.midi_handler.set_chord_octave(self.midi_handler.get_chord_octave() + 1), octave_label.configure(text=f"Octave: {self.midi_handler.get_chord_octave()}")]).pack(side="left", padx=2)
            row += 1
            
            ctk.CTkLabel(container, text="Test Chord:", width=120, font=("Arial", 10, "bold")).grid(row=row, column=0, sticky="w", padx=5, pady=2)
            test_chord_frame = ctk.CTkFrame(container, fg_color="transparent")
            test_chord_frame.grid(row=row, column=1, columnspan=3, sticky="w", padx=5, pady=2)
            test_chord_var = ctk.StringVar(value="C")
            test_chord_menu = ctk.CTkOptionMenu(test_chord_frame, variable=test_chord_var, values=["C", "Cm", "C7", "G", "Gm", "G7", "D", "Dm", "D7", "A", "Am", "A7"], width=100)
            test_chord_menu.pack(side="left", padx=2)
            ctk.CTkButton(test_chord_frame, text="PLAY", width=60, height=30, fg_color=COLORS["success"], command=lambda: self.midi_handler.send_chord_midi(test_chord_var.get())).pack(side="left", padx=5)
            row += 1
            
            help_frame = ctk.CTkFrame(container, fg_color="transparent")
            help_frame.grid(row=row, column=0, columnspan=4, pady=20)
            ctk.CTkLabel(help_frame, text="SysEx Format: Enter hex values separated by spaces (e.g., 43 7E 00 00 7F)", font=("Arial", 10), text_color=COLORS["info"]).pack(side="top", pady=5)
            ctk.CTkLabel(help_frame, text="Note: F0 (start) and F7 (end) are added automatically. Do NOT include them.", font=("Arial", 10, "italic"), text_color=COLORS["warning"]).pack(side="top", pady=5)
            
            button_frame = ctk.CTkFrame(container, fg_color="transparent")
            button_frame.grid(row=row+1, column=0, columnspan=4, pady=20)
            ctk.CTkButton(button_frame, text="💾 SAVE ALL", width=120, height=40, fg_color=COLORS["success"], font=("Arial", 12, "bold"), command=self.save_sysex_from_editor).pack(side="left", padx=10)
            ctk.CTkButton(button_frame, text="CLOSE", width=120, height=40, fg_color=COLORS["danger"], font=("Arial", 12, "bold"), command=editor_win.destroy).pack(side="left", padx=10)
            ctk.CTkButton(button_frame, text="RESET ALL", width=120, height=40, fg_color=COLORS["warning"], font=("Arial", 12, "bold"), command=self.reset_all_sysex).pack(side="left", padx=10)
        except Exception as e:
            logging.error(f"Error opening SysEx editor: {e}")
            messagebox.showerror("Error", f"Failed to open SysEx editor: {e}")
    
    def test_sysex_command(self, command_name, sysex_str):
        if not sysex_str.strip():
            messagebox.showwarning("Warning", f"No SysEx entered for {command_name}")
            return
        
        if not self.midi_handler.midi_out:
            messagebox.showwarning("Warning", "MIDI output not connected. Use Auto Connect first.")
            return
        
        try:
            hex_values = [x.strip() for x in sysex_str.split() if x.strip()]
            if hex_values and hex_values[0].upper() == "F0":
                hex_values = hex_values[1:]
            if hex_values and hex_values[-1].upper() == "F7":
                hex_values = hex_values[:-1]
            
            if not hex_values:
                messagebox.showerror("Error", "No valid hex values in SysEx string")
                return
            
            data_bytes = []
            for val in hex_values:
                try:
                    data_bytes.append(int(val, 16))
                except ValueError:
                    messagebox.showerror("Error", f"Invalid hex value: {val}")
                    return
            
            msg = mido.Message('sysex', data=data_bytes)
            self.midi_handler.midi_out.send(msg)
            self.log_midi("TEST", msg)
            messagebox.showinfo("Success", f"SysEx sent for {command_name}")
            logging.info(f"Tested SysEx for {command_name}: {sysex_str}")
        except Exception as e:
            logging.error(f"Error testing SysEx for {command_name}: {e}")
            messagebox.showerror("Error", f"Failed to send SysEx: {str(e)}")
    
    def save_sysex_from_editor(self):
        try:
            for cmd, entry in self.sysex_entries.items():
                value = entry.get().strip()
                if value:
                    hex_values = [x for x in value.split() if x]
                    for val in hex_values:
                        int(val, 16)
                    self.sysex_commands[cmd] = value
                else:
                    if cmd in self.sysex_commands:
                        del self.sysex_commands[cmd]
            
            if self.save_sysex_commands():
                messagebox.showinfo("Success", "SysEx commands saved successfully!")
                logging.info("SysEx commands saved from editor")
            else:
                messagebox.showerror("Error", "Failed to save SysEx commands")
        except ValueError as e:
            messagebox.showerror("Error", f"Invalid hex value: {e}")
        except Exception as e:
            logging.error(f"Error saving SysEx from editor: {e}")
            messagebox.showerror("Error", f"Failed to save SysEx commands: {e}")
    
    def reset_all_sysex(self):
        if messagebox.askyesno("Reset", "Reset all SysEx commands to defaults?"):
            self.sysex_commands = DEFAULT_SYSEX.copy()
            self.save_sysex_commands()
            
            if hasattr(self, 'sysex_entries'):
                for cmd, entry in self.sysex_entries.items():
                    entry.delete(0, "end")
                    entry.insert(0, DEFAULT_SYSEX.get(cmd, ""))
            
            self.midi_handler.set_chord_octave(4)
            messagebox.showinfo("Reset", "All SysEx commands reset to defaults")
            logging.info("SysEx commands reset to defaults")
    
    def trigger_yamaha_load(self):
        if not self.active_xml_file or not self.midi_handler.midi_out:
            return
        
        try:
            if self.data_source == "local":
                path = os.path.join(self.songs_dir, self.active_xml_file)
            else:
                path = os.path.join(self.github_songs_dir, self.active_xml_file)
            
            reg = ET.parse(path).getroot().findtext('reg', 'None')
            if reg != "None":
                self.midi_handler.send_program_change(int(reg)-1)
        except Exception as e:
            logging.error(f"Error triggering Yamaha load: {e}")
    
    def update_nav_buttons(self):
        if not self.filtered_songs or not self.active_xml_file:
            return
        
        try:
            idx = self.filtered_songs.index(self.active_xml_file)
            if idx > 0:
                prev_name = self.filtered_songs[idx-1].replace('.xml', '')
                self.btn_prev_song.configure(text=f"⏮ PREV - {prev_name}", state="normal")
            else:
                self.btn_prev_song.configure(text="START", state="disabled")
            
            if idx < len(self.filtered_songs) - 1:
                next_name = self.filtered_songs[idx+1].replace('.xml', '')
                self.btn_next_song.configure(text=f"NEXT - {next_name} ⏭", state="normal")
            else:
                self.btn_next_song.configure(text="END", state="disabled")
        except ValueError:
            self.btn_prev_song.configure(text="⏮ PREVIOUS", state="disabled")
            self.btn_next_song.configure(text="NEXT ⏭", state="disabled")
        except Exception as e:
            logging.error(f"Error updating nav buttons: {e}")
    
    def navigate_song(self, delta):
        if not self.filtered_songs or not self.active_xml_file:
            return
        
        try:
            curr_idx = self.filtered_songs.index(self.active_xml_file)
            new_idx = curr_idx + delta
            if 0 <= new_idx < len(self.filtered_songs):
                self.load_song_content(self.filtered_songs[new_idx])
        except ValueError:
            pass
        except Exception as e:
            logging.error(f"Error navigating song: {e}")
    
    def show_setlist_in_main(self, filename):
        self.active_setlist_name = filename
        self.display_text.pack_forget()
        self.setlist_view_frame.pack(fill="both", expand=True)
        self.refresh_setlist_main_view()
    
    def refresh_setlist_main_view(self):
        for w in self.setlist_view_frame.winfo_children():
            w.destroy()
        
        if not self.active_setlist_name:
            return
        
        try:
            if self.data_source == "local":
                path = os.path.join(self.setlists_dir, self.active_setlist_name)
            else:
                path = os.path.join(self.github_setlists_dir, self.active_setlist_name)
            
            songs = [s.text for s in ET.parse(path).getroot().findall("song")]
            self.filtered_songs = songs
            
            for i, s in enumerate(songs):
                row = ctk.CTkFrame(self.setlist_view_frame, fg_color=COLORS["secondary"])
                row.pack(fill="x", pady=2, padx=10)
                ctk.CTkButton(row, text=s.replace(".xml", ""), height=50, font=("Arial", 18), fg_color="transparent", anchor="w", command=lambda x=s: self.load_song_content(x)).pack(side="left", fill="x", expand=True)
                ctk.CTkButton(row, text="▲", width=40, height=40, command=lambda idx=i: self.move_song_in_setlist(idx, -1)).pack(side="right", padx=2)
                ctk.CTkButton(row, text="▼", width=40, height=40, command=lambda idx=i: self.move_song_in_setlist(idx, 1)).pack(side="right", padx=2)
                ctk.CTkButton(row, text="🎹 LOAD", width=80, height=40, fg_color="#e67e22", command=lambda x=s: self.load_song_content(x)).pack(side="right", padx=10)
        except Exception as e:
            logging.error(f"Error refreshing setlist view: {e}")
    
    def move_song_in_setlist(self, index, direction):
        if not self.active_setlist_name:
            return
        
        try:
            if self.data_source == "local":
                path = os.path.join(self.setlists_dir, self.active_setlist_name)
            else:
                path = os.path.join(self.github_setlists_dir, self.active_setlist_name)
            
            tree = ET.parse(path)
            root = tree.getroot()
            songs = root.findall("song")
            new_index = index + direction
            
            if 0 <= new_index < len(songs):
                songs[index].text, songs[new_index].text = songs[new_index].text, songs[index].text
                tree.write(path)
                self.refresh_setlist_main_view()
        except Exception as e:
            logging.error(f"Error moving song in setlist: {e}")
    
    def open_song_editor(self, filename=None):
        try:
            editor_win = ctk.CTkToplevel(self)
            editor_win.title("Song Editor" if filename else "New Song")
            editor_win.geometry("900x700+50+50")
            editor_win.attributes('-topmost', True)
            
            container = ctk.CTkScrollableFrame(editor_win)
            container.pack(fill="both", expand=True, padx=20, pady=20)
            
            song_data = {'title': '', 'artist': '', 'tempo': '120', 'time_signature': '4/4', 'scale': 'C', 'content': '', 'notes': ''}
            
            if filename:
                try:
                    if self.data_source == "local":
                        path = os.path.join(self.songs_dir, filename)
                    else:
                        path = os.path.join(self.github_songs_dir, filename)
                    
                    tree = ET.parse(path)
                    root = tree.getroot()
                    song_data['title'] = root.findtext('title', '')
                    song_data['artist'] = root.findtext('artist', '')
                    song_data['tempo'] = root.findtext('tempo', '120')
                    song_data['time_signature'] = root.findtext('time_signature', '4/4')
                    song_data['scale'] = root.findtext('scale', 'C')
                    song_data['content'] = root.findtext('content', '')
                    song_data['notes'] = root.findtext('notes', '')
                except Exception as e:
                    logging.error(f"Error loading song data: {e}")
            
            info_frame = ctk.CTkFrame(container)
            info_frame.pack(fill="x", pady=(0, 20))
            ctk.CTkLabel(info_frame, text="SONG INFORMATION", font=("Arial", 16, "bold"), text_color=COLORS["accent"]).pack(anchor="w", pady=(10, 20))
            
            title_artist_frame = ctk.CTkFrame(info_frame, fg_color="transparent")
            title_artist_frame.pack(fill="x", padx=10, pady=(0, 10))
            ctk.CTkLabel(title_artist_frame, text="Song Title:", font=("Arial", 12, "bold")).pack(side="left", padx=(0, 10))
            title_entry = ctk.CTkEntry(title_artist_frame, width=200, placeholder_text="Enter song title")
            title_entry.insert(0, song_data['title'])
            title_entry.pack(side="left", padx=(0, 20))
            ctk.CTkLabel(title_artist_frame, text="Artist:", font=("Arial", 12, "bold")).pack(side="left", padx=(0, 10))
            artist_entry = ctk.CTkEntry(title_artist_frame, width=200, placeholder_text="Enter artist name")
            artist_entry.insert(0, song_data['artist'])
            artist_entry.pack(side="left")
            
            tempo_frame = ctk.CTkFrame(info_frame, fg_color="transparent")
            tempo_frame.pack(fill="x", padx=10, pady=(0, 10))
            ctk.CTkLabel(tempo_frame, text="Tempo (BPM):", font=("Arial", 12, "bold")).pack(side="left", padx=(0, 10))
            tempo_entry = ctk.CTkEntry(tempo_frame, width=100)
            tempo_entry.insert(0, song_data['tempo'])
            tempo_entry.pack(side="left", padx=(0, 40))
            ctk.CTkLabel(tempo_frame, text="Time Signature:", font=("Arial", 12, "bold")).pack(side="left", padx=(0, 10))
            time_sig_entry = ctk.CTkEntry(tempo_frame, width=100)
            time_sig_entry.insert(0, song_data['time_signature'])
            time_sig_entry.pack(side="left", padx=(0, 40))
            
            ctk.CTkLabel(container, text="SECTION ORDER", font=("Arial", 14, "bold"), text_color=COLORS["accent"]).pack(anchor="w", pady=(10, 5))
            editor_section_bar = ctk.CTkFrame(container, fg_color=COLORS["panel"], height=40)
            editor_section_bar.pack(fill="x", pady=(0, 20))
            editor_section_bar.pack_propagate(False)
            
            editor_section_dropdowns = []
            section_options = ["ADLIB", "INTRO", "CHORUS", "VERSE", "INTER", "BRIDGE", "SOLO", "ENDING", "HOOK", "OUTRO"]
            existing_sections = []
            
            if filename:
                try:
                    if self.data_source == "local":
                        path = os.path.join(self.songs_dir, filename)
                    else:
                        path = os.path.join(self.github_songs_dir, filename)
                    
                    tree = ET.parse(path)
                    root = tree.getroot()
                    section_order = root.find('section_order')
                    if section_order is not None:
                        existing_sections = [s.text for s in section_order.findall('section')]
                except:
                    pass
            
            for i in range(10):
                default_value = existing_sections[i] if i < len(existing_sections) else (section_options[i] if i < len(section_options) else "")
                var = ctk.StringVar(value=default_value)
                dropdown = ctk.CTkOptionMenu(editor_section_bar, variable=var, values=section_options, width=80, height=30, fg_color=SECTION_COLORS.get(default_value, COLORS["primary"]), button_color=SECTION_COLORS.get(default_value, COLORS["accent"]), button_hover_color=SECTION_COLORS.get(default_value, COLORS["warning"]), dropdown_fg_color=COLORS["secondary"])
                dropdown.pack(side="left", padx=2, pady=5)
                editor_section_dropdowns.append(var)
            
            editor_save_clear_frame = ctk.CTkFrame(editor_section_bar, fg_color="transparent")
            editor_save_clear_frame.pack(side="left", padx=10)
            ctk.CTkButton(editor_save_clear_frame, text="💾", width=30, height=30, fg_color=COLORS["success"], command=lambda: self.save_editor_section_order(editor_section_dropdowns, filename)).pack(side="left", padx=2)
            ctk.CTkButton(editor_save_clear_frame, text="🗑", width=30, height=30, fg_color=COLORS["danger"], command=lambda: self.clear_editor_section_order(editor_section_dropdowns)).pack(side="left", padx=2)
            
            ctk.CTkLabel(container, text="LYRICS & CHORDS", font=("Arial", 16, "bold"), text_color=COLORS["accent"]).pack(anchor="w", pady=(10, 10))
            content_text = ctk.CTkTextbox(container, height=300)
            content_text.pack(fill="both", expand=True, pady=(0, 20))
            content_text.insert("1.0", song_data['content'])
            content_text.tag_config("chord", foreground=COLORS["accent"])
            content_text.tag_config("label", foreground=COLORS["info"])
            
            def update_chord_coloring(event=None):
                content = content_text.get("1.0", "end-1c")
                lines = content.split('\n')
                content_text.tag_remove("chord", "1.0", "end")
                content_text.tag_remove("label", "1.0", "end")
                
                line_start = 0
                for line in lines:
                    if line:
                        for match in re.finditer(r'\[(.*?)\]', line):
                            start = f"1.0+{line_start + match.start()}c"
                            end = f"1.0+{line_start + match.end()}c"
                            chord_content = match.group(1)
                            if chord_content.upper() in PROTECTED_SECTIONS:
                                content_text.tag_add("label", start, end)
                            else:
                                content_text.tag_add("chord", start, end)
                    line_start += len(line) + 1
            
            content_text.bind("<KeyRelease>", update_chord_coloring)
            self.after(100, update_chord_coloring)
            
            ctk.CTkLabel(container, text="NOTES", font=("Arial", 16, "bold"), text_color=COLORS["accent"]).pack(anchor="w", pady=(0, 10))
            notes_text = ctk.CTkTextbox(container, height=100)
            notes_text.pack(fill="both", expand=True, pady=(0, 20))
            notes_text.insert("1.0", song_data['notes'])
            
            button_frame = ctk.CTkFrame(container, fg_color="transparent")
            button_frame.pack(fill="x", pady=20)
            
            def save_song():
                try:
                    song_title = title_entry.get().strip()
                    if not song_title:
                        messagebox.showwarning("Warning", "Song title is required")
                        return
                    
                    root = ET.Element("song")
                    ET.SubElement(root, "title").text = song_title
                    ET.SubElement(root, "artist").text = artist_entry.get().strip()
                    ET.SubElement(root, "tempo").text = tempo_entry.get().strip()
                    ET.SubElement(root, "time_signature").text = time_sig_entry.get().strip()
                    ET.SubElement(root, "scale").text = "C"
                    ET.SubElement(root, "content").text = content_text.get("1.0", "end-1c").strip()
                    ET.SubElement(root, "notes").text = notes_text.get("1.0", "end-1c").strip()
                    
                    section_order = ET.SubElement(root, "section_order")
                    for var in editor_section_dropdowns:
                        if var.get():
                            section = ET.SubElement(section_order, "section")
                            section.text = var.get()
                    
                    filename_safe = re.sub(r'[^\w\s-]', '', song_title).strip().replace(' ', '_')
                    xml_filename = f"{filename_safe}.xml"
                    xml_path = os.path.join(self.songs_dir, xml_filename)
                    ET.ElementTree(root).write(xml_path, encoding='utf-8', xml_declaration=True)
                    
                    if self.data_source == "github_cache":
                        self.data_source = "local"
                    
                    self.refresh_list()
                    editor_win.destroy()
                    
                    if filename and filename != xml_filename:
                        old_path = os.path.join(self.songs_dir, filename)
                        if os.path.exists(old_path):
                            os.remove(old_path)
                    
                    self.load_song_content(xml_filename)
                    logging.info(f"Saved song: {xml_filename}")
                except Exception as e:
                    logging.error(f"Error saving song: {e}")
                    messagebox.showerror("Error", f"Failed to save song: {e}")
            
            ctk.CTkButton(button_frame, text="💾 SAVE SONG", width=150, height=45, fg_color=COLORS["success"], font=("Arial", 12, "bold"), command=save_song).pack(side="left", padx=10)
            ctk.CTkButton(button_frame, text="✖ CANCEL", width=150, height=45, fg_color=COLORS["danger"], font=("Arial", 12, "bold"), command=editor_win.destroy).pack(side="right", padx=10)
        except Exception as e:
            logging.error(f"Error opening song editor: {e}")
            messagebox.showerror("Error", f"Failed to open song editor: {e}")
    
    def save_editor_section_order(self, dropdowns, filename):
        if not filename:
            return
        
        try:
            if self.data_source == "local":
                path = os.path.join(self.songs_dir, filename)
            else:
                path = os.path.join(self.github_songs_dir, filename)
            
            tree = ET.parse(path)
            root = tree.getroot()
            section_order = root.find('section_order')
            
            if section_order is not None:
                root.remove(section_order)
            
            section_order = ET.SubElement(root, 'section_order')
            for var in dropdowns:
                if var.get():
                    section = ET.SubElement(section_order, 'section')
                    section.text = var.get()
            
            tree.write(path)
            logging.info(f"Saved section order from editor: {filename}")
        except Exception as e:
            logging.error(f"Error saving editor section order: {e}")
    
    def clear_editor_section_order(self, dropdowns):
        for var in dropdowns:
            var.set("")
    
    def open_setlist_editor(self, filename=None):
        try:
            editor_win = ctk.CTkToplevel(self)
            editor_win.title("Setlist Manager" if filename else "New Setlist")
            editor_win.geometry("800x600")
            editor_win.attributes('-topmost', True)
            
            container = ctk.CTkFrame(editor_win)
            container.pack(fill="both", expand=True, padx=20, pady=20)
            
            setlist_data = {'name': '', 'songs': []}
            if filename:
                try:
                    if self.data_source == "local":
                        path = os.path.join(self.setlists_dir, filename)
                    else:
                        path = os.path.join(self.github_setlists_dir, filename)
                    
                    tree = ET.parse(path)
                    root = tree.getroot()
                    setlist_data['name'] = filename.replace('.xml', '')
                    setlist_data['songs'] = [s.text for s in root.findall("song")]
                except Exception as e:
                    logging.error(f"Error loading setlist data: {e}")
            
            ctk.CTkLabel(container, text="SETLIST MANAGER", font=("Arial", 18, "bold"), text_color=COLORS["accent"]).pack(anchor="w", pady=(0, 20))
            ctk.CTkLabel(container, text="Setlist Name:", font=("Arial", 12, "bold")).pack(anchor="w", pady=(0, 5))
            name_entry = ctk.CTkEntry(container, width=400)
            name_entry.insert(0, setlist_data['name'])
            name_entry.pack(fill="x", pady=(0, 20))
            
            songs_frame = ctk.CTkFrame(container, fg_color="transparent")
            songs_frame.pack(fill="both", expand=True, pady=(0, 20))
            
            left_col = ctk.CTkFrame(songs_frame, fg_color="transparent")
            left_col.pack(side="left", fill="both", expand=True, padx=(0, 10))
            ctk.CTkLabel(left_col, text="AVAILABLE SONGS", font=("Arial", 14, "bold"), text_color=COLORS["info"]).pack(anchor="w", pady=(0, 10))
            
            all_songs = []
            try:
                if self.data_source == "local":
                    songs_dir = self.songs_dir
                else:
                    songs_dir = self.github_songs_dir
                
                all_songs = sorted([f.replace('.xml', '') for f in os.listdir(songs_dir) if f.endswith(".xml")])
            except Exception as e:
                logging.error(f"Error listing songs: {e}")
            
            search_frame = ctk.CTkFrame(left_col, fg_color="transparent")
            search_frame.pack(fill="x", pady=(0, 10))
            search_var = ctk.StringVar()
            search_entry = ctk.CTkEntry(search_frame, placeholder_text="🔍 Search songs...", textvariable=search_var)
            search_entry.pack(side="left", fill="x", expand=True)
            
            available_list = ctk.CTkScrollableFrame(left_col)
            available_list.pack(fill="both", expand=True)
            
            right_col = ctk.CTkFrame(songs_frame, fg_color="transparent")
            right_col.pack(side="right", fill="both", expand=True, padx=(10, 0))
            ctk.CTkLabel(right_col, text="SETLIST SONGS", font=("Arial", 14, "bold"), text_color=COLORS["success"]).pack(anchor="w", pady=(0, 10))
            
            setlist_scroll = ctk.CTkScrollableFrame(right_col)
            setlist_scroll.pack(fill="both", expand=True)
            
            self.available_song_buttons = {}
            self.setlist_song_widgets = []
            
            def refresh_available_songs():
                for widget in available_list.winfo_children():
                    widget.destroy()
                
                self.available_song_buttons.clear()
                query = search_var.get().lower()
                filtered_songs = [song for song in all_songs if query in song.lower() and song not in setlist_data['songs']]
                
                for song in filtered_songs:
                    btn = ctk.CTkButton(available_list, text=song, anchor="w", command=lambda s=song: add_to_setlist(s))
                    btn.pack(fill="x", pady=2)
                    self.available_song_buttons[song] = btn
            
            def refresh_setlist_songs():
                for widget in setlist_scroll.winfo_children():
                    widget.destroy()
                
                self.setlist_song_widgets.clear()
                for i, song in enumerate(setlist_data['songs']):
                    row = ctk.CTkFrame(setlist_scroll, fg_color="transparent")
                    row.pack(fill="x", pady=2)
                    ctk.CTkLabel(row, text=f"{i+1}. {song}", anchor="w", font=("Arial", 11)).pack(side="left", fill="x", expand=True)
                    
                    if i > 0:
                        ctk.CTkButton(row, text="▲", width=30, height=30, command=lambda idx=i: move_song_up(idx)).pack(side="right", padx=2)
                    if i < len(setlist_data['songs']) - 1:
                        ctk.CTkButton(row, text="▼", width=30, height=30, command=lambda idx=i: move_song_down(idx)).pack(side="right", padx=2)
                    
                    ctk.CTkButton(row, text="✖", width=30, height=30, fg_color=COLORS["danger"], command=lambda s=song: remove_from_setlist(s)).pack(side="right", padx=2)
                    self.setlist_song_widgets.append(row)
            
            def add_to_setlist(song):
                if song not in setlist_data['songs']:
                    setlist_data['songs'].append(song)
                    refresh_available_songs()
                    refresh_setlist_songs()
            
            def remove_from_setlist(song):
                if song in setlist_data['songs']:
                    setlist_data['songs'].remove(song)
                    refresh_available_songs()
                    refresh_setlist_songs()
            
            def move_song_up(index):
                if index > 0:
                    setlist_data['songs'][index], setlist_data['songs'][index-1] = (setlist_data['songs'][index-1], setlist_data['songs'][index])
                    refresh_setlist_songs()
            
            def move_song_down(index):
                if index < len(setlist_data['songs']) - 1:
                    setlist_data['songs'][index], setlist_data['songs'][index+1] = (setlist_data['songs'][index+1], setlist_data['songs'][index])
                    refresh_setlist_songs()
            
            def save_setlist():
                try:
                    setlist_name = name_entry.get().strip()
                    if not setlist_name:
                        messagebox.showwarning("Warning", "Setlist name is required")
                        return
                    
                    root = ET.Element("setlist")
                    ET.SubElement(root, "name").text = setlist_name
                    for song in setlist_data['songs']:
                        ET.SubElement(root, "song").text = f"{song}.xml"
                    
                    filename_safe = re.sub(r'[^\w\s-]', '', setlist_name).strip().replace(' ', '_')
                    xml_filename = f"{filename_safe}.xml"
                    xml_path = os.path.join(self.setlists_dir, xml_filename)
                    ET.ElementTree(root).write(xml_path, encoding='utf-8', xml_declaration=True)
                    
                    if self.data_source == "github_cache":
                        self.data_source = "local"
                    
                    self.refresh_list()
                    editor_win.destroy()
                    
                    if filename and filename != xml_filename:
                        old_path = os.path.join(self.setlists_dir, filename)
                        if os.path.exists(old_path):
                            os.remove(old_path)
                    
                    self.show_setlist_in_main(xml_filename)
                    logging.info(f"Saved setlist: {xml_filename}")
                except Exception as e:
                    logging.error(f"Error saving setlist: {e}")
                    messagebox.showerror("Error", f"Failed to save setlist: {e}")
            
            search_var.trace_add("write", lambda *args: refresh_available_songs())
            refresh_available_songs()
            refresh_setlist_songs()
            
            button_frame = ctk.CTkFrame(container, fg_color="transparent")
            button_frame.pack(fill="x", pady=20)
            ctk.CTkButton(button_frame, text="💾 SAVE SETLIST", width=150, height=45, fg_color=COLORS["success"], font=("Arial", 12, "bold"), command=save_setlist).pack(side="left", padx=10)
            ctk.CTkButton(button_frame, text="✖ CANCEL", width=150, height=45, fg_color=COLORS["danger"], font=("Arial", 12, "bold"), command=editor_win.destroy).pack(side="right", padx=10)
        except Exception as e:
            logging.error(f"Error opening setlist editor: {e}")
            messagebox.showerror("Error", f"Failed to open setlist editor: {e}")
    
    def handle_add_click(self):
        if self.current_tab == "songs":
            self.open_song_editor()
        else:
            self.open_setlist_editor()
    
    def switch_tab(self, tab):
        self.current_tab = tab
        self.btn_dynamic_add.configure(text="➕ ADD SONG" if tab == "songs" else "➕ ADD SETLIST")
        self.refresh_list()
    
    def delete_item(self, filename):
        if not messagebox.askyesno("Delete", f"Delete {filename}?"):
            return
        
        try:
            if self.current_tab == "songs":
                if self.data_source == "local":
                    path = os.path.join(self.songs_dir, filename)
                else:
                    path = os.path.join(self.github_songs_dir, filename)
            else:
                if self.data_source == "local":
                    path = os.path.join(self.setlists_dir, filename)
                else:
                    path = os.path.join(self.github_setlists_dir, filename)
            
            os.remove(path)
            self.refresh_list()
            logging.info(f"Deleted: {filename}")
        except Exception as e:
            logging.error(f"Error deleting {filename}: {e}")
            messagebox.showerror("Error", f"Failed to delete {filename}: {e}")
    
    def get_network_info(self):
        try:
            hostname = socket.gethostname()
            ip_list = []
            
            try:
                s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
                s.settimeout(1)
                s.connect(("8.8.8.8", 80))
                local_ip = s.getsockname()[0]
                s.close()
                if local_ip and not local_ip.startswith('127.'):
                    ip_list.append(local_ip)
            except:
                pass
            
            try:
                all_ips = socket.gethostbyname_ex(hostname)[2]
                for ip in all_ips:
                    if not ip.startswith('127.') and ip not in ip_list:
                        ip_list.append(ip)
            except:
                pass
            
            try:
                ip = socket.gethostbyname(hostname)
                if not ip.startswith('127.') and ip not in ip_list:
                    ip_list.append(ip)
            except:
                pass
            
            if not ip_list:
                ip_list.append("127.0.0.1")
            
            return hostname, ip_list
        except Exception as e:
            logging.error(f"Error getting network info: {e}")
            return socket.gethostname(), ["127.0.0.1"]
    
    def filter_relevant_ips(self, ip_list):
        """Filter IP addresses to prioritize 10.x.x.x and 192.168.x.x addresses"""
        relevant_ips = []
        other_ips = []
        
        for ip in ip_list:
            if ip.startswith('10.') or ip.startswith('192.168.'):
                relevant_ips.append(ip)
            elif ip != '127.0.0.1':
                other_ips.append(ip)
        
        # If we have relevant IPs, return them, otherwise return all non-localhost IPs
        if relevant_ips:
            return relevant_ips
        elif other_ips:
            return other_ips
        else:
            return ['127.0.0.1']
    
    def create_web_server(self):
        app = Flask(__name__)
        
        html_template = """
        <!DOCTYPE html>
        <html>
        <head>
            <title>Chord Manager Broadcast - {{ title }}</title>
            <meta name="viewport" content="width=device-width, initial-scale=1.0">
            <style>
                body { font-family: Arial, sans-serif; background-color: #121212; color: white; margin: 0; padding: 20px; display: flex; flex-direction: column; height: 100vh; }
                .header { background-color: #1e1e1e; padding: 20px; border-radius: 10px; margin-bottom: 20px; }
                .song-info { color: #f1c40f; font-size: 24px; font-weight: bold; }
                .content-container { display: flex; flex: 1; gap: 20px; overflow: hidden; }
                .lyrics-section { flex: 2; background-color: #161616; padding: 30px; border-radius: 10px; font-size: {{ font_size }}px; line-height: 1.4; white-space: pre-wrap; overflow-y: auto; }
                .grid-section { flex: 1; background-color: #161616; padding: 20px; border-radius: 10px; overflow-y: auto; min-width: 300px; }
                .chord { color: #f1c40f; font-weight: bold; {% if chord_separation %} display: block; margin-bottom: 2px; {% endif %} }
                .label { color: #3498db; font-weight: bold; display: block; margin: 5px 0; }
                .grid-row { display: flex; margin-bottom: 5px; border-radius: 5px; overflow: hidden; }
                .grid-cell { flex: 1; padding: 10px; text-align: center; background-color: #252525; border-right: 1px solid #121212; }
                .grid-cell:last-child { border-right: none; }
                .grid-section-header { background-color: #1a3a5a; color: #3498db; font-weight: bold; padding: 15px; text-align: center; border-radius: 5px; margin-bottom: 10px; }
                .info { color: #7f8c8d; font-size: 12px; margin-top: 10px; }
                .chord-line { color: #f1c40f; margin-bottom: 2px; font-weight: bold; line-height: 1.2; }
                .lyric-line { margin-bottom: 8px; line-height: 1.2; }
                .grid-title { color: #f1c40f; font-size: 18px; font-weight: bold; margin-bottom: 15px; text-align: center; }
                .empty-line { height: 8px; }
                .section-break { height: 15px; }
                .scroll-buttons { position: fixed; right: 20px; bottom: 20px; display: flex; flex-direction: column; gap: 10px; }
                .scroll-btn { width: 60px; height: 60px; border-radius: 30px; font-size: 24px; font-weight: bold; border: none; cursor: pointer; display: flex; align-items: center; justify-content: center; transition: all 0.2s; }
                .scroll-up { background-color: #3498db; color: white; }
                .scroll-down { background-color: #9b59b6; color: white; }
                .scroll-btn:hover { transform: scale(1.1); }
            </style>
            <script>
                function scrollContent(direction) {
                    const lyricsSection = document.querySelector('.lyrics-section');
                    lyricsSection.scrollTop += direction * 50;
                }
                function scrollGrid(direction) {
                    const gridSection = document.querySelector('.grid-section');
                    gridSection.scrollTop += direction * 50;
                }
                function refreshData() {
                    fetch('/data')
                        .then(response => response.json())
                        .then(data => {
                            if (data.title !== document.getElementById('song-title').innerText) {
                                location.reload();
                            }
                            if (data.chord_separation !== {{ chord_separation|tojson }}) {
                                location.reload();
                            }
                        });
                }
                setInterval(refreshData, 2000);
            </script>
        </head>
        <body>
            <div class="header">
                <div class="song-info" id="song-title">{{ title }}</div>
                <div>Artist: {{ artist }} | BPM: {{ tempo }} | View: {{ view_mode }}</div>
                <div class="info">Connected from: {{ client_ip }} | Last updated: {{ timestamp }}</div>
            </div>
            
            <div class="content-container">
                <div class="lyrics-section">{{ content|safe }}</div>
                
                <div class="grid-section">
                    <div class="grid-title">CHORD GRID</div>
                    {% if grid_data %}
                        {% for row in grid_data %}
                            {% if row.type == 'section' %}
                                <div class="grid-section-header">{{ row.cells[0] }}</div>
                            {% else %}
                                <div class="grid-row">
                                    {% for cell in row.cells %}
                                        <div class="grid-cell">{{ cell }}</div>
                                    {% endfor %}
                                </div>
                            {% endif %}
                        {% endfor %}
                    {% else %}
                        <div class="info">No chord grid available</div>
                    {% endif %}
                </div>
            </div>
            
            <div class="scroll-buttons">
                <button class="scroll-btn scroll-up" onclick="scrollContent(-1)">↑</button>
                <button class="scroll-btn scroll-down" onclick="scrollContent(1)">↓</button>
                <button class="scroll-btn scroll-up" onclick="scrollGrid(-1)" style="background-color: #9b59b6;">↑</button>
                <button class="scroll-btn scroll-down" onclick="scrollGrid(1)" style="background-color: #e74c3c;">↓</button>
            </div>
            
            <div class="info">
                Chord Manager Broadcast Server | {{ server_ip }} | Hostname: {{ hostname }}
            </div>
        </body>
        </html>
        """
        
        @app.route('/')
        def index():
            try:
                title = "No song loaded"
                artist = "Unknown"
                tempo = "120"
                content = "Select a song in the Chord Manager application"
                grid_data = []
                
                if self.active_xml_file:
                    try:
                        if self.data_source == "local":
                            path = os.path.join(self.songs_dir, self.active_xml_file)
                        else:
                            path = os.path.join(self.github_songs_dir, self.active_xml_file)
                        
                        tree = ET.parse(path)
                        root = tree.getroot()
                        title = root.findtext('title', 'Unknown')
                        artist = root.findtext('artist', 'Unknown')
                        tempo = root.findtext('tempo', '120')
                        raw_content = root.findtext('content', '')
                        
                        if self.chord_separate_mode:
                            formatted_lines = []
                            lines = raw_content.split('\n')
                            for line_num, raw_line in enumerate(lines):
                                chord_line = ""
                                lyric_line = ""
                                parts = re.split(r'(\[.*?\])', raw_line)
                                current_lyric_len = 0
                                
                                for p in parts:
                                    if p.startswith('[') and p.endswith(']'):
                                        content = p[1:-1]
                                        if content.upper() in PROTECTED_SECTIONS:
                                            if chord_line.strip() or lyric_line.strip():
                                                if chord_line.strip():
                                                    formatted_lines.append(f'<div class="chord-line">{chord_line}</div>')
                                                if lyric_line.strip():
                                                    formatted_lines.append(f'<div class="lyric-line">{lyric_line}</div>')
                                                chord_line = ""
                                                lyric_line = ""
                                            formatted_lines.append(f'<div class="label">[{content}]</div>')
                                        else:
                                            padding_needed = current_lyric_len - len(chord_line)
                                            if padding_needed > 0:
                                                chord_line += " " * padding_needed
                                            chord_line += content
                                    else:
                                        lyric_line += p
                                        current_lyric_len += len(p)
                                
                                if chord_line.strip():
                                    formatted_lines.append(f'<div class="chord-line">{chord_line}</div>')
                                if lyric_line.strip():
                                    formatted_lines.append(f'<div class="lyric-line">{lyric_line}</div>')
                                
                                if line_num < len(lines) - 1 and not raw_line.strip().startswith('['):
                                    formatted_lines.append('<div class="empty-line"></div>')
                            
                            content = '\n'.join(formatted_lines)
                        else:
                            formatted_content = ""
                            lines = raw_content.split('\n')
                            for line_num, line in enumerate(lines):
                                if line.strip():
                                    if line.strip().startswith('[') and line.strip().endswith(']'):
                                        content_inner = line.strip()[1:-1]
                                        if content_inner.upper() in PROTECTED_SECTIONS:
                                            if line_num > 0:
                                                formatted_content += '<div class="section-break"></div>'
                                            formatted_content += f'<span class="label">[{content_inner}]</span><br>'
                                        else:
                                            formatted_content += f'<span class="chord">[{content_inner}]</span>'
                                    else:
                                        line_formatted = re.sub(r'\[(.*?)\]', r'<span class="chord">[\1]</span>', line)
                                        formatted_content += line_formatted + '<br>'
                                    
                                    if line_num < len(lines) - 1 and not line.strip().startswith('['):
                                        formatted_content += '<div class="empty-line"></div>'
                            
                            content = formatted_content
                        
                        grid_xml = root.find('chord_grid')
                        if grid_xml is not None:
                            for r_elem in grid_xml.findall('row'):
                                rtype = r_elem.get('type', 'chords')
                                cells = [c.text if c.text else "" for c in r_elem.findall('cell')]
                                transposed_cells = []
                                for cell in cells:
                                    if cell and rtype == "chords":
                                        transposed_cells.append(self.transpose_chord(cell, self.transpose_semitones))
                                    else:
                                        transposed_cells.append(cell)
                                grid_data.append({'type': rtype, 'cells': transposed_cells})
                    except Exception as e:
                        content = f"Error loading song: {str(e)}"
                
                client_ip = request.remote_addr if request else "Unknown"
                return render_template_string(html_template, title=title, artist=artist, tempo=tempo, content=content, grid_data=grid_data, font_size=self.current_font_size, chord_separation=self.chord_separate_mode, view_mode="Separate" if self.chord_separate_mode else "Combined", client_ip=client_ip, timestamp=time.strftime("%H:%M:%S"), server_ip=self.web_ip[0] if self.web_ip else "127.0.0.1", hostname=self.web_hostname)
            except Exception as e:
                return f"Error: {str(e)}"
        
        @app.route('/data')
        def get_data():
            title = "No song loaded"
            if self.active_xml_file:
                try:
                    if self.data_source == "local":
                        path = os.path.join(self.songs_dir, self.active_xml_file)
                    else:
                        path = os.path.join(self.github_songs_dir, self.active_xml_file)
                    
                    tree = ET.parse(path)
                    root = tree.getroot()
                    title = root.findtext('title', 'Unknown')
                except:
                    pass
            
            return jsonify({'title': title, 'chord_separation': self.chord_separate_mode, 'timestamp': time.time()})
        
        return app
    
    def start_mobile_server(self):
        try:
            self.mobile_server = self.create_mobile_server()
            self.mobile_thread = Thread(target=lambda: self.mobile_server.run(host='0.0.0.0', port=5001, debug=False, threaded=True, use_reloader=False))
            self.mobile_thread.daemon = True
            self.mobile_thread.start()
            time.sleep(1)
            
            self.web_hostname, ip_list = self.get_network_info()
            self.web_ip = self.filter_relevant_ips(ip_list)
            logging.info(f"Mobile web server started on port 5001")
            logging.info(f"Mobile access: http://localhost:5001")
            if self.web_ip and self.web_ip[0] != "127.0.0.1":
                logging.info(f"Mobile access from other devices: http://{self.web_ip[0]}:5001")
            self.mobile_server_indicator.configure(text="📱", text_color=COLORS["success"])
        except Exception as e:
            logging.error(f"Error starting mobile web server: {e}")
            self.mobile_server_indicator.configure(text="📱", text_color=COLORS["danger"])
    
    def create_mobile_server(self):
        app = Flask(__name__)
        
        html_template = """
        <!DOCTYPE html>
        <html>
        <head>
            <title>Mobile Remote</title>
            <meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=1.0, user-scalable=no">
            <style>
                * { margin: 0; padding: 0; box-sizing: border-box; -webkit-tap-highlight-color: transparent; }
                body { font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, Oxygen, Ubuntu, sans-serif; background: linear-gradient(135deg, #121212 0%, #1e1e1e 100%); color: white; min-height: 100vh; padding: 0; overflow-x: hidden; touch-action: manipulation; }
                .container { max-width: 100%; margin: 0 auto; padding: 15px; padding-bottom: 80px; }
                .header { background: linear-gradient(135deg, #2c3e50 0%, #34495e 100%); padding: 20px; border-radius: 20px; margin-bottom: 20px; text-align: center; box-shadow: 0 4px 15px rgba(0,0,0,0.3); border: 1px solid #404040; }
                .app-title { font-size: 28px; font-weight: 800; background: linear-gradient(45deg, #f1c40f, #f39c12); -webkit-background-clip: text; -webkit-text-fill-color: transparent; margin-bottom: 5px; letter-spacing: -0.5px; }
                .status-bar { display: flex; justify-content: space-between; align-items: center; background: rgba(255,255,255,0.05); padding: 12px 15px; border-radius: 15px; margin-bottom: 10px; border: 1px solid rgba(255,255,255,0.1); }
                .status-item { display: flex; align-items: center; gap: 8px; }
                .status-icon { font-size: 18px; }
                .status-text { font-size: 13px; color: #bdc3c7; }
                .status-online { color: #27ae60; }
                .status-offline { color: #e74c3c; }
                .control-btn-row { display: flex; justify-content: center; gap: 10px; margin: 20px 0; }
                .perform-btn { padding: 15px 30px; border-radius: 15px; font-weight: 700; font-size: 18px; background: linear-gradient(135deg, #f1c40f 0%, #f39c12 100%); color: black; border: none; cursor: pointer; transition: all 0.2s; }
                .perform-btn:hover { transform: scale(1.05); box-shadow: 0 4px 15px rgba(241, 196, 15, 0.4); }
                .perform-btn.active { background: linear-gradient(135deg, #e74c3c 0%, #c0392b 100%); color: white; }
                .song-info { background: rgba(52, 73, 94, 0.7); padding: 18px; border-radius: 15px; margin-bottom: 20px; border: 1px solid #404040; backdrop-filter: blur(10px); }
                .song-title { font-size: 22px; font-weight: 700; color: #f1c40f; margin-bottom: 8px; word-break: break-word; }
                .song-meta { display: flex; flex-wrap: wrap; gap: 15px; font-size: 14px; color: #bdc3c7; }
                .meta-item { display: flex; align-items: center; gap: 5px; }
                .section-title { font-size: 16px; font-weight: 600; color: #3498db; margin: 25px 0 15px 0; padding-bottom: 10px; border-bottom: 2px solid rgba(52, 152, 219, 0.3); }
                .tab-container { display: flex; background: rgba(255,255,255,0.05); border-radius: 15px; padding: 5px; margin-bottom: 20px; border: 1px solid rgba(255,255,255,0.1); }
                .tab { flex: 1; text-align: center; padding: 12px; border-radius: 12px; font-weight: 600; font-size: 15px; cursor: pointer; transition: all 0.2s ease; color: #95a5a6; user-select: none; -webkit-user-select: none; }
                .tab.active { background: linear-gradient(135deg, #3498db 0%, #2980b9 100%); color: white; box-shadow: 0 2px 8px rgba(52, 152, 219, 0.3); }
                .tab:active { transform: scale(0.98); }
                .search-box { margin-bottom: 20px; position: relative; }
                .search-input { width: 100%; padding: 16px 20px 16px 50px; background: rgba(255,255,255,0.07); border: 2px solid rgba(255,255,255,0.1); border-radius: 15px; color: white; font-size: 16px; outline: none; transition: all 0.3s ease; }
                .search-input:focus { border-color: #3498db; background: rgba(255,255,255,0.1); }
                .search-icon { position: absolute; left: 20px; top: 50%; transform: translateY(-50%); color: #7f8c8d; font-size: 18px; }
                .list-container { background: rgba(255,255,255,0.05); border-radius: 15px; overflow: hidden; border: 1px solid rgba(255,255,255,0.1); margin-bottom: 20px; max-height: 400px; overflow-y: auto; -webkit-overflow-scrolling: touch; }
                .list-item { padding: 18px 20px; border-bottom: 1px solid rgba(255,255,255,0.05); display: flex; align-items: center; justify-content: space-between; transition: all 0.2s ease; cursor: pointer; user-select: none; -webkit-user-select: none; }
                .list-item:active { background: rgba(52, 152, 219, 0.15); transform: translateX(2px); }
                .list-item:last-child { border-bottom: none; }
                .list-item:hover { background: rgba(255,255,255,0.08); }
                .item-name { font-size: 16px; font-weight: 500; color: #ecf0f1; flex: 1; word-break: break-word; }
                .item-actions { display: flex; gap: 8px; margin-left: 15px; }
                .action-btn { width: 36px; height: 36px; border-radius: 10px; display: flex; align-items: center; justify-content: center; font-size: 16px; cursor: pointer; transition: all 0.2s ease; user-select: none; -webkit-user-select: none; }
                .action-btn:active { transform: scale(0.9); }
                .btn-load { background: linear-gradient(135deg, #e67e22 0%, #d35400 100%); color: white; }
                .btn-edit { background: rgba(52, 152, 219, 0.2); color: #3498db; border: 1px solid rgba(52, 152, 219, 0.3); }
                .btn-delete { background: rgba(231, 76, 60, 0.2); color: #e74c3c; border: 1px solid rgba(231, 76, 60, 0.3); }
                .empty-state { text-align: center; padding: 40px 20px; color: #7f8c8d; }
                .empty-icon { font-size: 48px; margin-bottom: 15px; opacity: 0.5; }
                .empty-text { font-size: 16px; }
                .controls-bar { position: fixed; bottom: 0; left: 0; right: 0; background: rgba(30, 30, 30, 0.95); backdrop-filter: blur(20px); padding: 15px; border-top: 1px solid rgba(255,255,255,0.1); display: flex; justify-content: space-around; z-index: 1000; }
                .control-btn { padding: 12px 20px; border-radius: 12px; font-weight: 600; font-size: 15px; display: flex; align-items: center; justify-content: center; gap: 8px; cursor: pointer; transition: all 0.2s ease; user-select: none; -webkit-user-select: none; border: none; color: white; min-width: 120px; }
                .control-btn:active { transform: scale(0.95); }
                .btn-primary { background: linear-gradient(135deg, #3498db 0%, #2980b9 100%); }
                .btn-success { background: linear-gradient(135deg, #27ae60 0%, #219653 100%); }
                .btn-warning { background: linear-gradient(135deg, #f39c12 0%, #e67e22 100%); }
                .btn-danger { background: linear-gradient(135deg, #e74c3c 0%, #c0392b 100%); }
                .current-song-display { background: rgba(241, 196, 15, 0.1); border: 2px solid rgba(241, 196, 15, 0.3); border-radius: 15px; padding: 20px; margin-bottom: 20px; animation: pulse 2s infinite; }
                @keyframes pulse { 0% { border-color: rgba(241, 196, 15, 0.3); } 50% { border-color: rgba(241, 196, 15, 0.6); } 100% { border-color: rgba(241, 196, 15, 0.3); } }
                .current-song-title { font-size: 20px; font-weight: 700; color: #f1c40f; margin-bottom: 5px; display: flex; align-items: center; gap: 10px; }
                .nav-buttons { display: flex; gap: 10px; margin-top: 10px; }
                .nav-btn { flex: 1; padding: 12px; border-radius: 10px; text-align: center; font-weight: 600; background: rgba(52, 73, 94, 0.7); cursor: pointer; transition: all 0.2s ease; user-select: none; -webkit-user-select: none; }
                .nav-btn:active { transform: scale(0.95); }
                .nav-btn.prev { border: 2px solid #3498db; color: #3498db; }
                .nav-btn.next { border: 2px solid #27ae60; color: #27ae60; }
                .scale-control { background: rgba(255,255,255,0.05); border-radius: 15px; padding: 15px; margin-bottom: 20px; border: 1px solid rgba(255,255,255,0.1); }
                .scale-label { font-size: 14px; color: #bdc3c7; margin-bottom: 10px; display: flex; align-items: center; gap: 8px; }
                .scale-select { width: 100%; padding: 15px; background: rgba(52, 73, 94, 0.7); border: 2px solid #3498db; border-radius: 10px; color: white; font-size: 16px; font-weight: 600; outline: none; cursor: pointer; }
                .control-section { background: rgba(255,255,255,0.05); border-radius: 15px; padding: 20px; margin-bottom: 20px; border: 1px solid rgba(255,255,255,0.1); }
                .scroll-section { margin-bottom: 20px; }
                .scroll-title { font-size: 16px; font-weight: 600; color: #3498db; margin: 25px 0 15px 0; padding-bottom: 10px; border-bottom: 2px solid rgba(52, 152, 219, 0.3); }
                .scroll-grid { display: grid; grid-template-columns: repeat(2, 1fr); gap: 10px; margin-top: 10px; }
                .scroll-item { padding: 12px; border-radius: 10px; text-align: center; font-weight: 600; background: rgba(52, 73, 94, 0.7); cursor: pointer; transition: all 0.2s ease; user-select: none; -webkit-user-select: none; border: 2px solid transparent; }
                .scroll-item:active { transform: scale(0.95); }
                .scroll-up { border-color: #3498db; color: #3498db; }
                .scroll-down { border-color: #9b59b6; color: #9b59b6; }
                .scroll-lyrics-up { border-color: #3498db; color: #3498db; }
                .scroll-lyrics-down { border-color: #9b59b6; color: #9b59b6; }
                .scroll-grid-up { border-color: #e74c3c; color: #e74c3c; }
                .scroll-grid-down { border-color: #f1c40f; color: #f1c40f; }
                .control-grid { display: grid; grid-template-columns: repeat(2, 1fr); gap: 10px; margin-top: 10px; }
                .control-item { padding: 15px; border-radius: 10px; text-align: center; font-weight: 600; background: rgba(52, 73, 94, 0.7); cursor: pointer; transition: all 0.2s ease; user-select: none; -webkit-user-select: none; border: 2px solid transparent; }
                .control-item:active { transform: scale(0.95); }
                .control-item.font { border-color: #9b59b6; color: #9b59b6; }
                .control-item.view { border-color: #3498db; color: #3498db; }
                .control-item.timer { border-color: #2ecc71; color: #2ecc71; }
                .control-item.fullscreen { border-color: #f39c12; color: #f39c12; }
                .connection-info { font-size: 12px; color: #7f8c8d; text-align: center; margin-top: 20px; padding: 10px; background: rgba(0,0,0,0.2); border-radius: 10px; }
                .ip-list { margin-top: 10px; font-size: 11px; line-height: 1.4; }
                .qr-code-section { text-align: center; margin-top: 20px; padding: 15px; background: rgba(0,0,0,0.2); border-radius: 10px; }
                .qr-title { font-size: 14px; font-weight: bold; margin-bottom: 10px; color: #f1c40f; }
                .qr-image { max-width: 150px; margin: 0 auto 10px auto; }
                @media (max-width: 480px) {
                    .container { padding: 12px; padding-bottom: 70px; }
                    .header { padding: 15px; }
                    .app-title { font-size: 24px; }
                    .control-btn { min-width: 100px; padding: 10px 15px; font-size: 14px; }
                    .list-item { padding: 15px; }
                    .item-name { font-size: 15px; }
                }
                @supports (-webkit-touch-callout: none) {
                    .controls-bar { padding-bottom: calc(15px + env(safe-area-inset-bottom)); }
                    body { padding-bottom: env(safe-area-inset-bottom); }
                }
            </style>
            <script>
                let currentTab = 'songs';
                let currentSong = '';
                let songsData = [];
                let setlistsData = [];
                
                function updateTime() {
                    const now = new Date();
                    const timeString = now.toLocaleTimeString('en-US', { 
                        hour12: true, 
                        hour: '2-digit', 
                        minute: '2-digit',
                        second: '2-digit'
                    });
                    document.getElementById('current-time').textContent = timeString;
                }
                
                function switchTab(tabName) {
                    currentTab = tabName;
                    document.querySelectorAll('.tab').forEach(tab => {
                        tab.classList.remove('active');
                        if (tab.dataset.tab === tabName) {
                            tab.classList.add('active');
                        }
                    });
                    document.getElementById('add-btn').textContent = 
                        tabName === 'songs' ? '➕ Add Song' : '➕ Add Setlist';
                    refreshList();
                }
                
                function refreshList() {
                    const searchQuery = document.getElementById('search-input').value.toLowerCase();
                    const listContainer = document.getElementById('list-container');
                    listContainer.innerHTML = '';
                    
                    // Get the correct data based on current tab
                    let items = [];
                    if (currentTab === 'songs') {
                        items = songsData;
                    } else {
                        items = setlistsData;
                    }
                    
                    // Filter by search query
                    if (searchQuery) {
                        items = items.filter(item => 
                            item.name.toLowerCase().includes(searchQuery)
                        );
                    }
                    
                    if (items.length === 0) {
                        listContainer.innerHTML = `
                            <div class="empty-state">
                                <div class="empty-icon">🎵</div>
                                <div class="empty-text">No ${currentTab} found</div>
                            </div>
                        `;
                        return;
                    }
                    
                    items.forEach(item => {
                        const itemElement = document.createElement('div');
                        itemElement.className = 'list-item';
                        itemElement.innerHTML = `
                            <div class="item-name">${item.name}</div>
                            <div class="item-actions">
                                <div class="action-btn btn-load" onclick="loadItem('${item.name}')">🎹</div>
                                <div class="action-btn btn-delete" onclick="deleteItem('${item.name}')">🗑</div>
                            </div>
                        `;
                        listContainer.appendChild(itemElement);
                    });
                }
                
                function loadItem(itemName) {
                    const endpoint = currentTab === 'songs' ? '/api/load_song' : '/api/load_setlist';
                    const data = currentTab === 'songs' ? { song: itemName + '.xml' } : { setlist: itemName + '.xml' };
                    fetch(endpoint, {
                        method: 'POST',
                        headers: { 'Content-Type': 'application/json' },
                        body: JSON.stringify(data)
                    })
                    .then(response => response.json())
                    .then(data => {
                        if (data.success) {
                            currentSong = itemName;
                            updateCurrentSongDisplay();
                            refreshData();
                        }
                    })
                    .catch(error => console.error('Error:', error));
                }
                
                function deleteItem(itemName) {
                    if (confirm(`Delete ${itemName}?`)) {
                        const endpoint = currentTab === 'songs' ? '/api/delete_song' : '/api/delete_setlist';
                        fetch(endpoint, {
                            method: 'POST',
                            headers: { 'Content-Type': 'application/json' },
                            body: JSON.stringify({ name: itemName + '.xml' })
                        })
                        .then(response => response.json())
                        .then(data => {
                            if (data.success) {
                                refreshData();
                            }
                        })
                        .catch(error => console.error('Error:', error));
                    }
                }
                
                function addItem() {
                    alert(`Add new ${currentTab.slice(0, -1)}`);
                }
                
                function navigateSong(direction) {
                    fetch('/api/navigate_song', {
                        method: 'POST',
                        headers: { 'Content-Type': 'application/json' },
                        body: JSON.stringify({ direction: direction })
                    })
                    .then(response => response.json())
                    .then(data => {
                        if (data.success) {
                            refreshData();
                        }
                    })
                    .catch(error => console.error('Error:', error));
                }
                
                function updateCurrentSongDisplay() {
                    const display = document.getElementById('current-song-display');
                    if (currentSong) {
                        display.innerHTML = `
                            <div class="current-song-title">
                                <span>🎵</span>
                                <span>${currentSong}</span>
                            </div>
                            <div class="nav-buttons">
                                <div class="nav-btn prev" onclick="navigateSong(-1)">◀ Previous</div>
                                <div class="nav-btn next" onclick="navigateSong(1)">Next ▶</div>
                            </div>
                        `;
                        display.style.display = 'block';
                    } else {
                        display.style.display = 'none';
                    }
                }
                
                function changeScale(offset) {
                    fetch('/api/change_scale', {
                        method: 'POST',
                        headers: { 'Content-Type': 'application/json' },
                        body: JSON.stringify({ offset: offset })
                    })
                    .then(response => response.json())
                    .then(data => {
                        if (data.success) {
                            document.getElementById('scale-display').textContent = offset;
                        }
                    })
                    .catch(error => console.error('Error:', error));
                }
                
                function performAction(action) {
                    fetch('/api/perform_action', {
                        method: 'POST',
                        headers: { 'Content-Type': 'application/json' },
                        body: JSON.stringify({ action: action })
                    })
                    .then(response => response.json())
                    .then(data => {
                        if (data.success) {
                            if (action === 'toggle_perform') {
                                const btn = document.getElementById('perform-btn');
                                btn.textContent = btn.textContent.includes('⚡') ? 'Exit Perform' : '⚡ Perform';
                                btn.classList.toggle('active');
                            }
                        }
                    })
                    .catch(error => console.error('Error:', error));
                }
                
                function scrollContent(type, direction) {
                    fetch('/api/scroll_content', {
                        method: 'POST',
                        headers: { 'Content-Type': 'application/json' },
                        body: JSON.stringify({ type: type, direction: direction })
                    })
                    .then(response => response.json())
                    .then(data => {
                        if (data.success) {
                            console.log(`Scrolled ${type} ${direction > 0 ? 'down' : 'up'}`);
                        }
                    })
                    .catch(error => console.error('Error:', error));
                }
                
                function refreshData() {
                    fetch('/api/get_data')
                        .then(response => response.json())
                        .then(data => {
                            songsData = data.songs;
                            setlistsData = data.setlists;
                            currentSong = data.current_song;
                            document.getElementById('scale-display').textContent = data.scale_offset;
                            updateCurrentSongDisplay();
                            refreshList();
                        })
                        .catch(error => console.error('Error:', error));
                }
                
                document.addEventListener('DOMContentLoaded', function() {
                    updateTime();
                    setInterval(updateTime, 1000);
                    document.getElementById('search-input').addEventListener('input', refreshList);
                    refreshData();
                    setInterval(refreshData, 5000);
                });
            </script>
        </head>
        <body>
            <div class="container">
                <div class="header">
                    <div class="app-title">Mobile Remote</div>
                    <div class="status-bar">
                        <div class="status-item">
                            <span class="status-icon">📶</span>
                            <span class="status-text status-online">Connected</span>
                        </div>
                        <div class="status-item">
                            <span class="status-icon">🕒</span>
                            <span class="status-text" id="current-time">00:00:00</span>
                        </div>
                        <div class="status-item">
                            <span class="status-icon">🎵</span>
                            <span class="status-text">{{ songs_count }} songs</span>
                        </div>
                    </div>
                    <div class="control-btn-row">
                        <button class="perform-btn" id="perform-btn" onclick="performAction('toggle_perform')">⚡ Perform</button>
                    </div>
                </div>
                
                <div id="current-song-display" class="current-song-display" style="display: none;"></div>
                
                <div class="scale-control">
                    <div class="scale-label">
                        <span>🎼</span>
                        <span>Transpose: <span id="scale-display">0</span> semitones</span>
                    </div>
                    <select class="scale-select" onchange="changeScale(this.value)">
                        {% for offset in scale_offsets %}
                        <option value="{{ offset }}" {% if offset == '0' %}selected{% endif %}>{{ offset }}</option>
                        {% endfor %}
                    </select>
                </div>
                
                <div class="tab-container">
                    <div class="tab active" data-tab="songs" onclick="switchTab('songs')">
                        🎵 Songs
                    </div>
                    <div class="tab" data-tab="setlists" onclick="switchTab('setlists')">
                        📋 Setlists
                    </div>
                </div>
                
                <div class="search-box">
                    <div class="search-icon">🔍</div>
                    <input type="text" id="search-input" class="search-input" placeholder="Search {{ current_tab }}...">
                </div>
                
                <div class="list-container" id="list-container"></div>
                
                <div class="control-section">
                    <div class="scroll-title">Scroll Controls</div>
                    <div class="scroll-grid">
                        <div class="scroll-item scroll-lyrics-up" onclick="scrollContent('lyrics', -1)">Lyrics ↑</div>
                        <div class="scroll-item scroll-lyrics-down" onclick="scrollContent('lyrics', 1)">Lyrics ↓</div>
                        <div class="scroll-item scroll-grid-up" onclick="scrollContent('grid', -1)">Grid ↑</div>
                        <div class="scroll-item scroll-grid-down" onclick="scrollContent('grid', 1)">Grid ↓</div>
                    </div>
                </div>
                
                <div class="control-section">
                    <div class="section-title">Quick Controls</div>
                    <div class="control-grid">
                        <div class="control-item font" onclick="performAction('font_plus')">A+</div>
                        <div class="control-item font" onclick="performAction('font_minus')">A-</div>
                        <div class="control-item view" onclick="performAction('toggle_view')">👁 View</div>
                        <div class="control-item timer" onclick="performAction('toggle_timer')" id="timer-btn">▶ Timer</div>
                        <div class="control-item fullscreen" onclick="performAction('toggle_fullscreen')">Fullscreen</div>
                        <div class="control-item" onclick="performAction('toggle_broadcast')" style="border-color: #9b59b6; color: #9b59b6;">📡 Cast</div>
                    </div>
                </div>
                
                <div class="connection-info">
                    Connected to: {{ server_ip }}:5001<br>
                    {% if server_ip != "127.0.0.1" %}
                    <div class="ip-list">
                        Network IP: {{ server_ip }}<br>
                        Hostname: {{ hostname }}<br>
                        Port: 5001
                    </div>
                    {% endif %}
                    <div class="qr-code-section">
                        <div class="qr-title">📱 Scan for Mobile Access</div>
                        <div class="qr-image">
                            <img src="{{ qr_code_url }}" alt="QR Code for {{ server_ip }}:5001" style="width: 150px; height: 150px;">
                        </div>
                        <div>Scan QR code with your phone</div>
                    </div>
                </div>
            </div>
            
            <div class="controls-bar">
                <button class="control-btn btn-primary" onclick="refreshData()">🔄 Refresh</button>
                <button class="control-btn btn-success" onclick="addItem()" id="add-btn">➕ Add Song</button>
                <button class="control-btn btn-warning" onclick="performAction('trigger_yamaha')">🎹 Yamaha</button>
                <button class="control-btn btn-danger" onclick="performAction('stop_all')">⏹ Stop</button>
            </div>
        </body>
        </html>
        """
        
        @app.route('/')
        def mobile_index():
            try:
                songs_count = len([f for f in os.listdir(self.songs_dir) if f.endswith('.xml')]) if os.path.exists(self.songs_dir) else 0
                current_song = ""
                if self.active_xml_file:
                    try:
                        if self.data_source == "local":
                            path = os.path.join(self.songs_dir, self.active_xml_file)
                        else:
                            path = os.path.join(self.github_songs_dir, self.active_xml_file)
                        
                        tree = ET.parse(path)
                        root = tree.getroot()
                        current_song = root.findtext('title', self.active_xml_file.replace('.xml', ''))
                    except:
                        current_song = self.active_xml_file.replace('.xml', '')
                
                # Get the primary IP for QR code
                server_ip = self.web_ip[0] if self.web_ip and len(self.web_ip) > 0 else "127.0.0.1"
                
                # Generate QR code for the mobile server URL
                qr_code_url = "/qr_code"
                
                return render_template_string(html_template, 
                                           songs_count=songs_count, 
                                           current_tab=self.current_tab, 
                                           scale_offsets=self.scale_offset_values, 
                                           server_ip=server_ip,
                                           hostname=self.web_hostname,
                                           qr_code_url=qr_code_url,
                                           current_song=current_song)
            except Exception as e:
                return f"Error: {str(e)}"
        
        @app.route('/qr_code')
        def generate_qr_code():
            try:
                # Get the primary IP address (prefer non-localhost)
                server_ip = self.web_ip[0] if self.web_ip and len(self.web_ip) > 0 else "127.0.0.1"
                url = f"http://{server_ip}:5001"
                
                # Generate QR code
                qr = qrcode.QRCode(
                    version=1,
                    error_correction=qrcode.constants.ERROR_CORRECT_L,
                    box_size=10,
                    border=4,
                )
                qr.add_data(url)
                qr.make(fit=True)
                
                # Create PIL image
                qr_img = qr.make_image(fill_color="black", back_color="white")
                
                # Convert to PNG in memory
                img_io = BytesIO()
                qr_img.save(img_io, 'PNG')
                img_io.seek(0)
                
                return send_file(img_io, mimetype='image/png')
            except Exception as e:
                # Return a default QR code if there's an error
                logging.error(f"Error generating QR code: {e}")
                # Create a simple error QR code
                qr = qrcode.QRCode(
                    version=1,
                    error_correction=qrcode.constants.ERROR_CORRECT_L,
                    box_size=10,
                    border=4,
                )
                qr.add_data("http://localhost:5001")
                qr.make(fit=True)
                qr_img = qr.make_image(fill_color="black", back_color="white")
                img_io = BytesIO()
                qr_img.save(img_io, 'PNG')
                img_io.seek(0)
                return send_file(img_io, mimetype='image/png')
        
        @app.route('/api/get_data', methods=['GET'])
        def api_get_data():
            try:
                songs = []
                setlists = []
                current_song = ""
                
                try:
                    if self.data_source == "local":
                        songs_dir = self.songs_dir
                    else:
                        songs_dir = self.github_songs_dir
                    
                    songs = sorted([{"name": f.replace('.xml', '')} for f in os.listdir(songs_dir) if f.endswith('.xml')])
                except:
                    pass
                
                try:
                    if self.data_source == "local":
                        setlists_dir = self.setlists_dir
                    else:
                        setlists_dir = self.github_setlists_dir
                    
                    setlists = sorted([{"name": f.replace('.xml', '')} for f in os.listdir(setlists_dir) if f.endswith('.xml')])
                except:
                    pass
                
                if self.active_xml_file:
                    try:
                        if self.data_source == "local":
                            path = os.path.join(self.songs_dir, self.active_xml_file)
                        else:
                            path = os.path.join(self.github_songs_dir, self.active_xml_file)
                        
                        tree = ET.parse(path)
                        root = tree.getroot()
                        current_song = root.findtext('title', self.active_xml_file.replace('.xml', ''))
                    except:
                        current_song = self.active_xml_file.replace('.xml', '')
                
                return jsonify({'success': True, 'songs': songs, 'setlists': setlists, 'current_song': current_song, 'scale_offset': str(self.current_scale_offset) if self.current_scale_offset >= 0 else f"{self.current_scale_offset}"})
            except Exception as e:
                return jsonify({'success': False, 'error': str(e)})
        
        @app.route('/api/load_song', methods=['POST'])
        def api_load_song():
            try:
                data = request.json
                song_file = data.get('song', '')
                if song_file:
                    self.after(0, lambda: self.load_song_content(song_file))
                    return jsonify({'success': True})
                else:
                    return jsonify({'success': False, 'error': 'No song specified'})
            except Exception as e:
                return jsonify({'success': False, 'error': str(e)})
        
        @app.route('/api/load_setlist', methods=['POST'])
        def api_load_setlist():
            try:
                data = request.json
                setlist_file = data.get('setlist', '')
                if setlist_file:
                    self.after(0, lambda: self.show_setlist_in_main(setlist_file))
                    return jsonify({'success': True})
                else:
                    return jsonify({'success': False, 'error': 'No setlist specified'})
            except Exception as e:
                return jsonify({'success': False, 'error': str(e)})
        
        @app.route('/api/delete_song', methods=['POST'])
        def api_delete_song():
            try:
                data = request.json
                song_file = data.get('name', '')
                if song_file:
                    if self.data_source == "local":
                        path = os.path.join(self.songs_dir, song_file)
                    else:
                        path = os.path.join(self.github_songs_dir, song_file)
                    
                    if os.path.exists(path):
                        os.remove(path)
                        self.after(0, self.refresh_list)
                        return jsonify({'success': True})
                    else:
                        return jsonify({'success': False, 'error': 'File not found'})
                else:
                    return jsonify({'success': False, 'error': 'No song specified'})
            except Exception as e:
                return jsonify({'success': False, 'error': str(e)})
        
        @app.route('/api/delete_setlist', methods=['POST'])
        def api_delete_setlist():
            try:
                data = request.json
                setlist_file = data.get('name', '')
                if setlist_file:
                    if self.data_source == "local":
                        path = os.path.join(self.setlists_dir, setlist_file)
                    else:
                        path = os.path.join(self.github_setlists_dir, setlist_file)
                    
                    if os.path.exists(path):
                        os.remove(path)
                        self.after(0, self.refresh_list)
                        return jsonify({'success': True})
                    else:
                        return jsonify({'success': False, 'error': 'File not found'})
                else:
                    return jsonify({'success': False, 'error': 'No setlist specified'})
            except Exception as e:
                return jsonify({'success': False, 'error': str(e)})
        
        @app.route('/api/navigate_song', methods=['POST'])
        def api_navigate_song():
            try:
                data = request.json
                direction = data.get('direction', 1)
                self.after(0, lambda: self.navigate_song(direction))
                return jsonify({'success': True})
            except Exception as e:
                return jsonify({'success': False, 'error': str(e)})
        
        @app.route('/api/change_scale', methods=['POST'])
        def api_change_scale():
            try:
                data = request.json
                offset_str = data.get('offset', '0')
                self.after(0, lambda: self.on_scale_offset_change(offset_str))
                return jsonify({'success': True})
            except Exception as e:
                return jsonify({'success': False, 'error': str(e)})
        
        @app.route('/api/perform_action', methods=['POST'])
        def api_perform_action():
            try:
                data = request.json
                action = data.get('action', '')
                if action == 'font_plus':
                    self.after(0, lambda: self.change_font(2))
                elif action == 'font_minus':
                    self.after(0, lambda: self.change_font(-2))
                elif action == 'toggle_view':
                    self.after(0, self.toggle_chord_separation)
                elif action == 'toggle_timer':
                    self.after(0, self.toggle_timer)
                elif action == 'toggle_fullscreen':
                    self.after(0, self.toggle_fullscreen)
                elif action == 'toggle_broadcast':
                    self.after(0, self.toggle_broadcast)
                elif action == 'toggle_perform':
                    self.after(0, self.toggle_fullscreen)
                elif action == 'trigger_yamaha':
                    self.after(0, self.trigger_yamaha_load)
                elif action == 'stop_all':
                    if self.midi_handler.midi_out:
                        self.midi_handler.send_transport(False)
                return jsonify({'success': True})
            except Exception as e:
                return jsonify({'success': False, 'error': str(e)})
        
        @app.route('/api/scroll_content', methods=['POST'])
        def api_scroll_content():
            try:
                data = request.json
                content_type = data.get('type', 'lyrics')
                direction = data.get('direction', 1)
                
                if content_type == 'lyrics':
                    self.after(0, lambda: self.scroll_display(direction * 5))
                elif content_type == 'grid':
                    self.after(0, lambda: self.scroll_chord_grid(direction * 5))
                
                return jsonify({'success': True})
            except Exception as e:
                return jsonify({'success': False, 'error': str(e)})
        
        return app
    
    def start_web_server(self):
        try:
            self.web_hostname, ip_list = self.get_network_info()
            self.web_ip = self.filter_relevant_ips(ip_list)
            self.web_server = self.create_web_server()
            self.web_thread = Thread(target=lambda: self.web_server.run(host='0.0.0.0', port=5000, debug=False, threaded=True, use_reloader=False))
            self.web_thread.daemon = True
            self.web_thread.start()
            time.sleep(1)
            
            logging.info(f"Web server started on port 5000")
            logging.info(f"Hostname: {self.web_hostname}")
            logging.info(f"Filtered IP addresses: {', '.join(self.web_ip)}")
            
            # Create QR codes for relevant IPs
            self.show_broadcast_qr_codes()
            
            return True
        except Exception as e:
            logging.error(f"Error starting web server: {e}")
            return False
    
    def show_broadcast_qr_codes(self):
        """Show QR codes for broadcast server access"""
        try:
            # Create a new window for QR codes
            qr_win = ctk.CTkToplevel(self)
            qr_win.title("Broadcast Server Started")
            qr_win.geometry("800x600")
            qr_win.attributes('-topmost', True)
            
            container = ctk.CTkScrollableFrame(qr_win)
            container.pack(fill="both", expand=True, padx=20, pady=20)
            
            # Title
            ctk.CTkLabel(container, text="📡 Broadcast Server Started!", 
                        font=("Arial", 24, "bold"), text_color=COLORS["success"]).pack(pady=(0, 20))
            
            # Access URLs section
            ctk.CTkLabel(container, text="Access URLs:", 
                        font=("Arial", 16, "bold"), text_color=COLORS["accent"]).pack(anchor="w", pady=(0, 10))
            
            info_text = ""
            for ip in self.web_ip:
                if ip != "127.0.0.1":
                    info_text += f"• http://{ip}:5000\n"
            info_text += f"• http://localhost:5000\n• http://{self.web_hostname}:5000\n\n"
            info_text += f"Mobile App: http://localhost:5001\n\n"
            info_text += "Share any of these URLs with other devices on your network."
            
            ctk.CTkLabel(container, text=info_text, 
                        font=("Arial", 12), justify="left", wraplength=700).pack(anchor="w", pady=(0, 20))
            
            # QR Codes section
            ctk.CTkLabel(container, text="📱 Scan QR Codes:", 
                        font=("Arial", 16, "bold"), text_color=COLORS["accent"]).pack(anchor="w", pady=(0, 10))
            
            # Create a frame for QR codes
            qr_frame = ctk.CTkFrame(container, fg_color="transparent")
            qr_frame.pack(fill="x", pady=(0, 20))
            
            # Generate QR codes for each relevant IP
            col = 0
            row_frame = None
            
            for i, ip in enumerate(self.web_ip):
                if ip == "127.0.0.1":
                    continue
                    
                if i % 2 == 0:
                    row_frame = ctk.CTkFrame(qr_frame, fg_color="transparent")
                    row_frame.pack(fill="x", pady=10)
                
                # Create QR code
                url = f"http://{ip}:5000"
                qr = qrcode.QRCode(
                    version=1,
                    error_correction=qrcode.constants.ERROR_CORRECT_L,
                    box_size=6,
                    border=2,
                )
                qr.add_data(url)
                qr.make(fit=True)
                
                # Create PIL image
                qr_img = qr.make_image(fill_color="black", back_color="white")
                
                # Convert to PhotoImage
                tk_img = ImageTk.PhotoImage(qr_img)
                
                # Create frame for this QR code
                qr_item_frame = ctk.CTkFrame(row_frame, fg_color="transparent")
                qr_item_frame.pack(side="left", expand=True, padx=20)
                
                # Display QR code
                qr_label = ctk.CTkLabel(qr_item_frame, image=tk_img, text="")
                qr_label.image = tk_img  # Keep a reference
                qr_label.pack(pady=(0, 5))
                
                # Display IP address below QR code
                ctk.CTkLabel(qr_item_frame, text=ip, 
                            font=("Arial", 10, "bold"), text_color=COLORS["info"]).pack()
                ctk.CTkLabel(qr_item_frame, text=f"Port: 5000", 
                            font=("Arial", 9), text_color="#7f8c8d").pack()
            
            # Mobile app QR code
            ctk.CTkLabel(container, text="📲 Mobile App QR:", 
                        font=("Arial", 16, "bold"), text_color=COLORS["warning"]).pack(anchor="w", pady=(20, 10))
            
            mobile_frame = ctk.CTkFrame(container, fg_color="transparent")
            mobile_frame.pack(fill="x", pady=(0, 20))
            
            # Get primary IP for mobile QR code
            mobile_ip = self.web_ip[0] if self.web_ip and len(self.web_ip) > 0 else "127.0.0.1"
            if mobile_ip == "127.0.0.1":
                mobile_url = "http://localhost:5001"
            else:
                mobile_url = f"http://{mobile_ip}:5001"
            
            qr_mobile = qrcode.QRCode(
                version=1,
                error_correction=qrcode.constants.ERROR_CORRECT_L,
                box_size=6,
                border=2,
            )
            qr_mobile.add_data(mobile_url)
            qr_mobile.make(fit=True)
            qr_mobile_img = qr_mobile.make_image(fill_color="black", back_color="white")
            tk_mobile_img = ImageTk.PhotoImage(qr_mobile_img)
            
            mobile_qr_frame = ctk.CTkFrame(mobile_frame, fg_color="transparent")
            mobile_qr_frame.pack(side="left", padx=50)
            
            mobile_qr_label = ctk.CTkLabel(mobile_qr_frame, image=tk_mobile_img, text="")
            mobile_qr_label.image = tk_mobile_img
            mobile_qr_label.pack(pady=(0, 5))
            
            ctk.CTkLabel(mobile_qr_frame, text=mobile_ip if mobile_ip != "127.0.0.1" else "localhost:5001", 
                        font=("Arial", 10, "bold"), text_color=COLORS["warning"]).pack()
            ctk.CTkLabel(mobile_qr_frame, text="Mobile Control", 
                        font=("Arial", 9), text_color="#7f8c8d").pack()
            
            # Close button
            button_frame = ctk.CTkFrame(container, fg_color="transparent")
            button_frame.pack(fill="x", pady=20)
            ctk.CTkButton(button_frame, text="✖ CLOSE", width=150, height=45, 
                         fg_color=COLORS["danger"], font=("Arial", 12, "bold"), 
                         command=qr_win.destroy).pack()
            
            # Auto-open web view
            webbrowser.open(f"http://localhost:5000")
            
        except Exception as e:
            logging.error(f"Error showing QR codes: {e}")
            # Fallback to simple message box
            info_msg = f"Broadcast Server Started!\n\nAccess URLs:\n"
            for ip in self.web_ip:
                if ip != "127.0.0.1":
                    info_msg += f"• http://{ip}:5000\n"
            info_msg += f"• http://localhost:5000\n• http://{self.web_hostname}:5000\n\nMobile App: http://localhost:5001\nShare any of these URLs with other devices on your network."
            messagebox.showinfo("Broadcast Started", info_msg)
    
    def stop_web_server(self):
        try:
            self.web_server = None
            self.web_thread = None
            logging.info("Web server stopped")
            return True
        except Exception as e:
            logging.error(f"Error stopping web server: {e}")
            return False
    
    def toggle_broadcast(self):
        if not self.broadcast_enabled:
            if self.start_web_server():
                self.broadcast_enabled = True
                self.broadcast_button.configure(text="📡 BROADCAST ON", fg_color=COLORS["success"])
                if self.web_ip:
                    ip_info = f" | Web: http://{self.web_ip[0] if self.web_ip[0] != '127.0.0.1' else 'localhost'}:5000"
                    self.title(f"Chord Manager by Supun Nirman{ip_info}")
            else:
                messagebox.showerror("Error", "Failed to start web server")
        else:
            self.stop_web_server()
            self.broadcast_enabled = False
            self.broadcast_button.configure(text="📡 BROADCAST", fg_color="#2ecc71")
            self.title("Chord Manager by Supun Nirman")
            messagebox.showinfo("Broadcast Stopped", "Web server stopped.")
    
    def open_github_window(self):
        try:
            github_win = ctk.CTkToplevel(self)
            github_win.title("GitHub Import")
            github_win.geometry("700x600")
            github_win.attributes('-topmost', True)
            
            container = ctk.CTkFrame(github_win)
            container.pack(fill="both", expand=True, padx=20, pady=20)
            
            ctk.CTkLabel(container, text="GitHub Import", font=("Arial", 20, "bold"), text_color=COLORS["accent"]).pack(pady=(0, 20))
            ctk.CTkLabel(container, text="GitHub Repository URL:", font=("Arial", 12, "bold")).pack(anchor="w", pady=(0, 5))
            
            url_frame = ctk.CTkFrame(container, fg_color="transparent")
            url_frame.pack(fill="x", pady=(0, 20))
            self.github_url_var = ctk.StringVar(value=self.github_url)
            github_url_entry = ctk.CTkEntry(url_frame, textvariable=self.github_url_var, width=500)
            github_url_entry.pack(side="left", fill="x", expand=True, padx=(0, 10))
            
            activity_frame = ctk.CTkFrame(container)
            activity_frame.pack(fill="both", expand=True, pady=(0, 20))
            ctk.CTkLabel(activity_frame, text="Import Activity Log:", font=("Arial", 12, "bold")).pack(anchor="w", padx=10, pady=(10, 5))
            self.github_activity_text = ctk.CTkTextbox(activity_frame, height=150, font=("Consolas", 10))
            self.github_activity_text.pack(fill="both", expand=True, padx=10, pady=(0, 10))
            self.github_activity_text.configure(state="disabled")
            
            progress_frame = ctk.CTkFrame(container, fg_color="transparent")
            progress_frame.pack(fill="x", pady=(0, 20))
            self.github_progress = ctk.CTkProgressBar(progress_frame)
            self.github_progress.pack(fill="x")
            self.github_progress.set(0)
            self.github_status = ctk.CTkLabel(progress_frame, text="Ready to load from GitHub...", font=("Arial", 10), text_color=COLORS["info"])
            self.github_status.pack(pady=(10, 0))
            
            options_frame = ctk.CTkFrame(container, fg_color="transparent")
            options_frame.pack(fill="x", pady=(0, 20))
            self.github_songs_var = ctk.BooleanVar(value=True)
            self.github_setlists_var = ctk.BooleanVar(value=True)
            ctk.CTkCheckBox(options_frame, text="Load Songs", variable=self.github_songs_var, font=("Arial", 12)).pack(side="left", padx=20)
            ctk.CTkCheckBox(options_frame, text="Load Setlists", variable=self.github_setlists_var, font=("Arial", 12)).pack(side="left", padx=20)
            
            button_frame = ctk.CTkFrame(container, fg_color="transparent")
            button_frame.pack(fill="x", pady=(0, 10))
            
            def add_activity_log(message):
                self.github_activity_text.configure(state="normal")
                timestamp = time.strftime("%H:%M:%S")
                self.github_activity_text.insert("end", f"[{timestamp}] {message}\n")
                self.github_activity_text.see("end")
                self.github_activity_text.configure(state="disabled")
            
            def load_from_github():
                if not self.github_songs_var.get() and not self.github_setlists_var.get():
                    messagebox.showwarning("Warning", "Please select at least one option")
                    return
                
                self.github_url = self.github_url_var.get().strip()
                if not self.github_url:
                    messagebox.showwarning("Warning", "Please enter a GitHub URL")
                    return
                
                try:
                    if "github.com" in self.github_url:
                        parts = self.github_url.replace("https://github.com/", "").split("/")
                        if len(parts) >= 2:
                            user = parts[0]
                            repo = parts[1]
                            branch = "main" if len(parts) < 4 else parts[3]
                            self.github_raw_base = f"https://raw.githubusercontent.com/{user}/{repo}/{branch}"
                        else:
                            raise ValueError("Invalid GitHub URL")
                    else:
                        self.github_raw_base = self.github_url
                    
                    add_activity_log(f"Using repository: {self.github_url}")
                    add_activity_log(f"Raw base URL: {self.github_raw_base}")
                except Exception as e:
                    add_activity_log(f"Error parsing GitHub URL: {str(e)}")
                    self.github_status.configure(text=f"Error: Invalid GitHub URL", text_color=COLORS["danger"])
                    return
                
                self.github_status.configure(text="Connecting to GitHub...")
                self.github_progress.set(0.1)
                add_activity_log("Connecting to GitHub...")
                
                try:
                    # FLUSH github_data folder first
                    if os.path.exists(self.github_data_dir):
                        shutil.rmtree(self.github_data_dir)
                        add_activity_log(f"Flushed github_data folder")
                        # Recreate directories
                        os.makedirs(self.github_songs_dir, exist_ok=True)
                        os.makedirs(self.github_setlists_dir, exist_ok=True)
                        add_activity_log(f"Recreated github_data folder structure")
                    
                    if self.github_songs_var.get():
                        self.github_status.configure(text="Downloading songs from GitHub...")
                        self.github_progress.set(0.3)
                        add_activity_log("Downloading songs from GitHub to cache...")
                        song_count = self.download_github_songs()
                        self.github_progress.set(0.6)
                        add_activity_log(f"Downloaded {song_count} songs to cache")
                    
                    if self.github_setlists_var.get():
                        self.github_status.configure(text="Downloading setlists from GitHub...")
                        self.github_progress.set(0.8)
                        add_activity_log("Downloading setlists from GitHub to cache...")
                        setlist_count = self.download_github_setlists()
                        self.github_progress.set(1.0)
                        add_activity_log(f"Downloaded {setlist_count} setlists to cache")
                    
                    self.github_status.configure(text="Download complete! Use 'LOAD CACHE' to load into app.", text_color=COLORS["success"])
                    add_activity_log("GitHub download to cache completed successfully!")
                    logging.info("GitHub download to cache completed successfully")
                except Exception as e:
                    logging.error(f"Error loading from GitHub: {e}")
                    add_activity_log(f"Error: {str(e)}")
                    self.github_status.configure(text=f"Error: {str(e)}", text_color=COLORS["danger"])
            
            def load_from_cache():
                if not self.github_songs_var.get() and not self.github_setlists_var.get():
                    messagebox.showwarning("Warning", "Please select at least one option")
                    return
                
                add_activity_log("Loading from cache (github_data folder) to app...")
                try:
                    loaded_songs = 0
                    loaded_setlists = 0
                    
                    if self.github_songs_var.get() and os.path.exists(self.github_songs_dir):
                        song_files = [f for f in os.listdir(self.github_songs_dir) if f.endswith('.xml')]
                        for song_file in song_files:
                            src_path = os.path.join(self.github_songs_dir, song_file)
                            dst_path = os.path.join(self.songs_dir, song_file)
                            shutil.copy2(src_path, dst_path)
                            loaded_songs += 1
                            add_activity_log(f"Loaded song from cache: {song_file}")
                    
                    if self.github_setlists_var.get() and os.path.exists(self.github_setlists_dir):
                        setlist_files = [f for f in os.listdir(self.github_setlists_dir) if f.endswith('.xml')]
                        for setlist_file in setlist_files:
                            src_path = os.path.join(self.github_setlists_dir, setlist_file)
                            dst_path = os.path.join(self.setlists_dir, setlist_file)
                            shutil.copy2(src_path, dst_path)
                            loaded_setlists += 1
                            add_activity_log(f"Loaded setlist from cache: {setlist_file}")
                    
                    if loaded_songs == 0 and loaded_setlists == 0:
                        add_activity_log("Cache is empty - no files found in github_data folder")
                        self.github_status.configure(text="Cache is empty", text_color=COLORS["warning"])
                    else:
                        self.data_source = "local"
                        add_activity_log(f"Loaded {loaded_songs} songs and {loaded_setlists} setlists from cache to app")
                        self.github_status.configure(text=f"Loaded {loaded_songs+loaded_setlists} items from cache to app!", text_color=COLORS["success"])
                        self.after(500, self.refresh_list)
                        self.after(500, self.update_library_counts)
                except Exception as e:
                    logging.error(f"Error loading from cache: {e}")
                    add_activity_log(f"Error: {str(e)}")
                    self.github_status.configure(text=f"Error: {str(e)}", text_color=COLORS["danger"])
            
            def load_local_data():
                add_activity_log("Switching to local data...")
                try:
                    self.data_source = "local"
                    add_activity_log("Switched to local data source")
                    self.github_status.configure(text="Switched to local data!", text_color=COLORS["success"])
                    self.after(500, self.refresh_list)
                    self.after(500, self.update_library_counts)
                except Exception as e:
                    logging.error(f"Error loading local data: {e}")
                    add_activity_log(f"Error: {str(e)}")
                    self.github_status.configure(text=f"Error: {str(e)}", text_color=COLORS["danger"])
            
            ctk.CTkButton(button_frame, text="🚀 LOAD FROM GITHUB", width=180, height=45, fg_color="#6e5494", font=("Arial", 14, "bold"), command=load_from_github).pack(side="left", padx=5)
            ctk.CTkButton(button_frame, text="📂 LOAD CACHE", width=180, height=45, fg_color=COLORS["info"], font=("Arial", 14, "bold"), command=load_from_cache).pack(side="left", padx=5)
            ctk.CTkButton(button_frame, text="📁 LOAD LOCAL", width=180, height=45, fg_color=COLORS["success"], font=("Arial", 14, "bold"), command=load_local_data).pack(side="left", padx=5)
            ctk.CTkButton(button_frame, text="✖ CLOSE", width=100, height=45, fg_color=COLORS["danger"], font=("Arial", 12, "bold"), command=github_win.destroy).pack(side="right", padx=5)
            
            add_activity_log("GitHub import window opened")
            add_activity_log(f"Current repository: {self.github_url}")
            
            cache_songs = len([f for f in os.listdir(self.github_songs_dir) if f.endswith('.xml')]) if os.path.exists(self.github_songs_dir) else 0
            cache_setlists = len([f for f in os.listdir(self.github_setlists_dir) if f.endswith('.xml')]) if os.path.exists(self.github_setlists_dir) else 0
            add_activity_log(f"Cache contains: {cache_songs} songs, {cache_setlists} setlists")
        except Exception as e:
            logging.error(f"Error opening GitHub window: {e}")
            messagebox.showerror("Error", f"Failed to open GitHub window: {e}")
    
    def load_local_data(self):
        try:
            self.data_source = "local"
            local_songs = os.listdir(self.songs_dir) if os.path.exists(self.songs_dir) else []
            local_setlists = os.listdir(self.setlists_dir) if os.path.exists(self.setlists_dir) else []
            logging.info(f"Using local data: {len(local_songs)} songs, {len(local_setlists)} setlists")
            self.after(500, self.refresh_list)
            self.after(500, self.update_library_counts)
        except Exception as e:
            logging.error(f"Error loading local data on startup: {e}")
    
    def download_github_songs(self):
        try:
            downloaded_count = 0
            self.github_activity_log = []
            
            try:
                if "github.com" in self.github_url:
                    parts = self.github_url.replace("https://github.com/", "").split("/")
                    if len(parts) >= 2:
                        user = parts[0]
                        repo = parts[1]
                        api_url = f"https://api.github.com/repos/{user}/{repo}/contents/songs"
                        response = requests.get(api_url, timeout=10)
                        
                        if response.status_code == 200:
                            files = response.json()
                            for file_info in files:
                                if file_info['name'].endswith('.xml'):
                                    song_url = file_info['download_url']
                                    song_response = requests.get(song_url, timeout=10)
                                    if song_response.status_code == 200:
                                        song_path = os.path.join(self.github_songs_dir, file_info['name'])
                                        with open(song_path, 'wb') as f:
                                            f.write(song_response.content)
                                        downloaded_count += 1
                                        logging.info(f"Downloaded song from GitHub to cache: {file_info['name']}")
                                        self.github_activity_log.append(f"Downloaded: {file_info['name']}")
            except Exception as e:
                logging.warning(f"Could not use GitHub API: {e}")
                self.github_activity_log.append(f"API Error: {str(e)}")
            
            try:
                common_songs = ["example_song.xml", "test_song.xml", "demo_song.xml"]
                for song_file in common_songs:
                    try:
                        song_url = f"{self.github_raw_base}/songs/{song_file}"
                        response = requests.get(song_url, timeout=10)
                        if response.status_code == 200:
                            song_path = os.path.join(self.github_songs_dir, song_file)
                            with open(song_path, 'wb') as f:
                                f.write(response.content)
                            downloaded_count += 1
                            logging.info(f"Downloaded song from GitHub to cache: {song_file}")
                            self.github_activity_log.append(f"Downloaded: {song_file}")
                    except Exception as e:
                        logging.warning(f"Could not download song {song_file}: {e}")
                        self.github_activity_log.append(f"Failed: {song_file}")
            except Exception as e:
                logging.error(f"Error in fallback downloading: {e}")
                self.github_activity_log.append(f"Fallback Error: {str(e)}")
            
            logging.info(f"Downloaded {downloaded_count} songs from GitHub to github_data folder")
            return downloaded_count
        except Exception as e:
            logging.error(f"Error downloading songs from GitHub: {e}")
            self.github_activity_log.append(f"Fatal Error: {str(e)}")
            return 0
    
    def download_github_setlists(self):
        try:
            downloaded_count = 0
            
            try:
                if "github.com" in self.github_url:
                    parts = self.github_url.replace("https://github.com/", "").split("/")
                    if len(parts) >= 2:
                        user = parts[0]
                        repo = parts[1]
                        api_url = f"https://api.github.com/repos/{user}/{repo}/contents/setlists"
                        response = requests.get(api_url, timeout=10)
                        
                        if response.status_code == 200:
                            files = response.json()
                            for file_info in files:
                                if file_info['name'].endswith('.xml'):
                                    setlist_url = file_info['download_url']
                                    setlist_response = requests.get(setlist_url, timeout=10)
                                    if setlist_response.status_code == 200:
                                        setlist_path = os.path.join(self.github_setlists_dir, file_info['name'])
                                        with open(setlist_path, 'wb') as f:
                                            f.write(setlist_response.content)
                                        downloaded_count += 1
                                        logging.info(f"Downloaded setlist from GitHub to cache: {file_info['name']}")
                                        self.github_activity_log.append(f"Downloaded setlist: {file_info['name']}")
            except Exception as e:
                logging.warning(f"Could not use GitHub API for setlists: {e}")
                self.github_activity_log.append(f"Setlist API Error: {str(e)}")
            
            try:
                common_setlists = ["example_setlist.xml", "test_setlist.xml", "demo_setlist.xml"]
                for setlist_file in common_setlists:
                    try:
                        setlist_url = f"{self.github_raw_base}/setlists/{setlist_file}"
                        response = requests.get(setlist_url, timeout=10)
                        if response.status_code == 200:
                            setlist_path = os.path.join(self.github_setlists_dir, setlist_file)
                            with open(setlist_path, 'wb') as f:
                                f.write(response.content)
                            downloaded_count += 1
                            logging.info(f"Downloaded setlist from GitHub to cache: {setlist_file}")
                            self.github_activity_log.append(f"Downloaded setlist: {setlist_file}")
                    except Exception as e:
                        logging.warning(f"Could not download setlist {setlist_file}: {e}")
                        self.github_activity_log.append(f"Failed setlist: {setlist_file}")
            except Exception as e:
                logging.error(f"Error in setlist fallback downloading: {e}")
                self.github_activity_log.append(f"Setlist Fallback Error: {str(e)}")
            
            logging.info(f"Downloaded {downloaded_count} setlists from GitHub to github_data folder")
            return downloaded_count
        except Exception as e:
            logging.error(f"Error downloading setlists from GitHub: {e}")
            self.github_activity_log.append(f"Setlist Fatal Error: {str(e)}")
            return 0
    
    def on_closing(self):
        try:
            if self.note_win and self.note_win.winfo_exists():
                self.save_current_note()
            
            self.midi_handler.disconnect()
            
            if self.broadcast_enabled:
                self.stop_web_server()
            
            self.destroy()
            logging.info("Application closed")
        except Exception as e:
            logging.error(f"Error during shutdown: {e}")
            self.destroy()

if __name__ == "__main__":
    try:
        app = AbleChordApp()
        app.mainloop()
    except Exception as e:
        logging.error(f"Fatal error: {e}")
        raise