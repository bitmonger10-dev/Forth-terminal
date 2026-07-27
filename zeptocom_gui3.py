#!/usr/bin/env python3
"""
zeptocom_gui.py

A Python / PySimpleGUI (FreeSimpleGUI) desktop port of zeptocom.js -- a serial
terminal for talking to Forth systems (zeptoforth, Mecrisp, STM8 eForth,
ESP32Forth, FlashForth, Punyforth).

Original zeptocom.js/zeptocom.css/zeptocom.html:
    Copyright (c) 2022-2025 Travis Bemann, MIT License

This port replaces:
  - the Web Serial API              -> pyserial
  - xterm.js terminal widget        -> a Multiline "terminal" element
  - browser <select>/<button> DOM   -> FreeSimpleGUI Combo/Button elements
  - File System Access API          -> normal OS file dialogs + open()/os.path
  - async/await event handlers      -> a background reader thread per
                                        connection + worker threads for
                                        line-by-line sends that wait on
                                        ACK/NAK events

Notes on scope / fidelity:
  - The ACK/NAK "ok-prompt" detection for zeptoforth is a faithful port of the
    original single-byte (0x06/0x15) protocol.
  - For mecrisp / stm8eforth / esp32forth / flashforth / punyforth the
    original does byte-by-byte state-machine matching against several
    possible response strings ("ok", " ok", "(stack ...)", "Exeption: ",
    "Undefined word: ", etc). This port implements the same idea using a
    rolling text buffer and substring search, which is functionally
    equivalent for real hardware but is simplified compared to the original
    per-byte state machine.
  - "Examples" / "Libraries" drop-downs originally loaded lists from a web
    server (examples/list.txt, lib/list.txt) next to the HTML file. This
    port will load the same list files from disk (next to this script) if
    present, otherwise those drop-downs stay empty.
  - Directory/file pickers use native OS dialogs instead of the browser's
    File System Access API, and #include / #symbols work against real paths
    on disk instead of a sandboxed directory handle.
"""

import os
import re
import sys
import time
import queue
import threading

try:
    import FreeSimpleGUI as sg
except ImportError:
    import PySimpleGUI as sg

import serial
import serial.tools.list_ports

# --------------------------------------------------------------------------
# Constants (mirrors the <select> option lists in zeptocom.html)
# --------------------------------------------------------------------------

BAUD_RATES = [50, 75, 110, 134, 150, 200, 300, 600, 1200, 1800, 2400, 4800,
              9600, 14400, 19200, 28800, 38400, 57600, 76800, 115200, 230400,
              460800, 576000, 921600]
DATA_BITS = [8, 7]
STOP_BITS = [1, 2]
PARITIES = ['none', 'even', 'odd']
FLOW_CONTROLS = ['none', 'hardware']
TARGET_TYPES = ['zeptoforth', 'mecrisp', 'stm8eforth', 'esp32forth',
                 'flashforth', 'punyforth']
RX_NEWLINE_MODES = ['crlf', 'lf', 'cr']
TX_NEWLINE_MODES = ['cr', 'crlf', 'lf']
SAVE_FORMATS = ['crlf', 'lf']

PARITY_MAP = {'none': serial.PARITY_NONE, 'even': serial.PARITY_EVEN,
              'odd': serial.PARITY_ODD}
STOPBIT_MAP = {1: serial.STOPBITS_ONE, 2: serial.STOPBITS_TWO}

OK_STRINGS = {
    'mecrisp': ' ok',
    'esp32forth': ' ok',
    'flashforth': ' ok',
    'stm8eforth': ' ok',   # also accepts ' OK' below
}

# --------------------------------------------------------------------------
# Global (shared, non-per-tab) state -- matches the JS module-level `let`s
# --------------------------------------------------------------------------

history = []                # most-recent-first list of sent lines
word_flat_history = set()   # flat set of whitespace-separated "words" sent
current_history_idx = -1
global_symbols = {}          # name -> replacement text
working_dir = None           # str path, chosen via "Set Working Directory"
example_map = {}              # platform -> [(title, path), ...]
library_map = {}


def add_word_history(word):
    if word:
        word_flat_history.add(word)


def complete_word_history(text):
    """Simplified port of completeWordHistory(): finds the shortest word in
    history that starts with `text`, preferring an exact match, and only
    auto-completes if the completion is unambiguous (unique prefix)."""
    if text in word_flat_history:
        return text
    candidates = [w for w in word_flat_history if w.startswith(text)]
    if not candidates:
        return text
    # If all candidates share a longer common prefix, extend to it.
    common = candidates[0]
    for c in candidates[1:]:
        i = 0
        while i < len(common) and i < len(c) and common[i] == c[i]:
            i += 1
        common = common[:i]
    return common if len(common) >= len(text) else text


def add_to_history(line):
    for word in line.strip().split():
        add_word_history(word)
    global current_history_idx
    if line in history:
        history.remove(line)
    history.insert(0, line)
    current_history_idx = -1


def remove_comment(line):
    for i, ch in enumerate(line):
        if ch == '\\':
            before_ok = (i == 0 or line[i - 1] in ' \t')
            after_ok = (i == len(line) - 1 or line[i + 1] in ' \t')
            if before_ok and after_ok:
                return line[:i]
    return line


def parse_symbols(lines, symbols):
    for line in lines:
        main_part = remove_comment(line).strip()
        if main_part:
            for i, ch in enumerate(main_part):
                if ch in ' \t':
                    key = main_part[:i]
                    value = main_part[i:].strip()
                    symbols[key] = value
                    break


def lookup_symbol(symbol, symbol_stack):
    for symbols in reversed(symbol_stack):
        if symbol in symbols:
            return symbols[symbol]
    return symbol


def is_symbol_stack_empty(symbol_stack):
    return all(len(s) == 0 for s in symbol_stack)


def apply_symbols(line, symbol_stack):
    if is_symbol_stack_empty(symbol_stack):
        return line
    new_line = ''
    i = 0
    while i < len(line):
        if line[i] in ' \t':
            new_line += line[i]
            i += 1
        else:
            start = i
            while i < len(line) and line[i] not in ' \t':
                i += 1
            symbol = line[start:i]
            new_line += lookup_symbol(symbol, symbol_stack)
    return new_line


def get_file_in_dir(parts, dir_path):
    """parts: list of path components relative to dir_path[-1]."""
    if len(parts) == 1:
        candidate = os.path.join(dir_path[-1], parts[0])
        return candidate if os.path.isfile(candidate) else None
    if parts[0] == '.':
        return get_file_in_dir(parts[1:], dir_path)
    if parts[0] == '..':
        if len(dir_path) > 1:
            return get_file_in_dir(parts[1:], dir_path[:-1])
        return None
    sub = os.path.join(dir_path[-1], parts[0])
    if os.path.isdir(sub):
        return get_file_in_dir(parts[1:], dir_path + [sub])
    return None


def slurp_file(path):
    with open(path, 'r', encoding='utf-8', errors='replace') as f:
        text = f.read()
    return re.split(r'\r?\n', text)


def expand_lines(lines, symbol_stack, error_cb):
    """Port of expandLines(): expands #include and #symbols directives."""
    all_lines = []
    for line in lines:
        parts = line.strip().split(None, 1)
        if len(parts) > 1 and parts[0] == '#include':
            if not working_dir:
                error_cb('Canceled\r\n')
                return None
            file_parts = parts[1].strip().split('/')
            path = get_file_in_dir(file_parts, [working_dir])
            if not path:
                error_cb(parts[1].strip() + ': File not found\r\n')
                return None
            file_lines = slurp_file(path)
            expanded = expand_lines(file_lines, symbol_stack + [{}], error_cb)
            if expanded is None:
                return None
            all_lines.extend(expanded)
        elif len(parts) > 1 and parts[0] == '#symbols':
            if not working_dir:
                error_cb('Canceled\r\n')
                return None
            file_parts = parts[1].strip().split('/')
            path = get_file_in_dir(file_parts, [working_dir])
            if not path:
                error_cb(parts[1].strip() + ': File not found\r\n')
                return None
            file_lines = slurp_file(path)
            expanded = expand_lines(file_lines, [{}], error_cb)
            if expanded is None:
                return None
            parse_symbols(expanded, symbol_stack[-1])
        else:
            all_lines.append(apply_symbols(line, symbol_stack))
    return all_lines


def strip_line(line):
    line = line.strip()
    if line[:1] == '\\':
        return ''
    return line


def strip_code(lines):
    stripped = [strip_line(l) for l in lines]
    return [l for l in stripped if l]


# --------------------------------------------------------------------------
# TermTab: one serial connection + its terminal pane
# --------------------------------------------------------------------------

class TermTab:
    _next_id = 0

    def __init__(self, title):
        self.tab_id = TermTab._next_id
        TermTab._next_id += 1
        self.title = title
        self.key = f'-TERM{self.tab_id}-'

        self.port = None          # serial.Serial instance, or None
        self.reader_thread = None
        self.reader_stop = threading.Event()

        self.baud = 115200
        self.data_bits = 8
        self.stop_bits = 1
        self.parity = 'none'
        self.flow_control = 'none'
        self.target_type = 'zeptoforth'
        self.newline_mode = 'crlf'
        self.tx_newline_mode = 'cr'

        self.sending = False
        self.receiving = False
        self.trigger_close = False
        self.trigger_abort = False

        self.ack_event = threading.Event()
        self.nak_event = threading.Event()
        self.ack_count = 0
        self.nak_count = 0
        self.interrupt_count = 0
        self.reboot_count = 0
        self.attention_count = 0
        self.lost_count = 0

        # protocol scratch state (mecrisp/stm8/esp32/flashforth/punyforth)
        self.ok_count = 0
        self.compile_state = False
        self.recent_text = ''   # rolling buffer for substring protocol checks

        self.current_data = []  # for "Save Terminal"

    def tx_newline(self):
        return {'cr': '\r', 'crlf': '\r\n', 'lf': '\n'}.get(
            self.tx_newline_mode, '\r')


class EditTab:
    _next_id = 0

    def __init__(self, title, content=None):
        self.tab_id = EditTab._next_id
        EditTab._next_id += 1
        self.orig_name = title
        self.file_name = None
        self.key = f'-EDIT{self.tab_id}-'
        self.content = content if content is not None else (
            "\\ Put your Forth code to upload here.\r\n"
            "\\ \r\n"
            "\\ Clicking 'Send' without a selection will upload the "
            "contents of this area to the target.\r\n"
            "\\ \r\n"
            "\\ Clicking 'Send' with a selection will upload just the "
            "selection to the target.\r\n\r\n")

    @property
    def display_title(self):
        return self.file_name or self.orig_name


# --------------------------------------------------------------------------
# Application
# --------------------------------------------------------------------------

class ZeptocomApp:
    def __init__(self):
        self.window = None
        self.events_q = queue.Queue()
        self.load_code_lists()

        self.term_tab = TermTab('Terminal')
        self.term_tab.key = '-TERM-'
        self.term_tabs = [self.term_tab]          # kept for helper reuse
        self.current_term_tab = self.term_tab

        self.edit_tab = EditTab('Edit')
        self.edit_tab.key = '-EDIT-'
        self.edit_tabs = [self.edit_tab]          # kept for helper reuse
        self.current_edit_tab = self.edit_tab

        self.build_window()

    # ---- example/library list loading (offline equivalent) ----

    def load_code_lists(self):
        for fname, mp in (('examples/list.txt', example_map),
                           ('lib/list.txt', library_map)):
            path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                 fname)
            if os.path.isfile(path):
                try:
                    for line in slurp_file(path):
                        parts = line.strip().split(None, 2)
                        if len(parts) >= 3:
                            platform, rel_path, title = parts
                            mp.setdefault(platform, []).append(
                                (title, rel_path))
                except OSError:
                    pass

    # ---- window layout ----

    def build_window(self):
        top_row = [
            sg.Button('Connect', key='-CONNECT-',pad=2),
            sg.Button('Disconnect', key='-DISCONNECT-', disabled=True,pad=1),
            sg.Text('Baud:'), sg.Combo(BAUD_RATES, default_value=115200,
                                        key='-BAUD-', size=(8, 1),
                                        readonly=True),
            sg.Text('Data Bits:'), sg.Combo(DATA_BITS, default_value=8,
                                             key='-DATABITS-', size=(2, 1),
                                             readonly=True),
            sg.Text('Stop Bits:'), sg.Combo(STOP_BITS, default_value=1,
                                             key='-STOPBITS-', size=(2, 1),
                                             readonly=True),
            sg.Text('Parity:'), sg.Combo(PARITIES, default_value='none',
                                          key='-PARITY-', size=(6, 1),
                                          readonly=True),
            sg.Text('Flow Control:'), sg.Combo(FLOW_CONTROLS,
                                                default_value='none',
                                                key='-FLOWCONTROL-',
                                                size=(8, 1), readonly=True),
            sg.Text('Target Type:'), sg.Combo(TARGET_TYPES,
                                               default_value='zeptoforth',
                                               key='-TARGETTYPE-',
                                               size=(11, 1), readonly=True,
                                               enable_events=True),
            sg.Text('Rx Newline:'), sg.Combo(RX_NEWLINE_MODES,
                                              default_value='crlf',
                                              key='-NEWLINEMODE-',
                                              size=(4, 1), readonly=True),
            sg.Text('Tx Newline:'), sg.Combo(TX_NEWLINE_MODES,
                                              default_value='cr',
                                              key='-TXNEWLINEMODE-',
                                              size=(4, 1), readonly=True),
            sg.Button('Help', key='-HELP-'),
            sg.Button('License', key='-LICENSE-'),
												
        ]

        term_multiline = sg.Multiline('', key=self.term_tab.key, size=(84, 32),
                                       autoscroll=True, disabled=True,
                                       background_color='black',
                                       text_color='white', font='Courier 11',
                                       expand_x=True, expand_y=True,
                                       horizontal_scroll=True)
        edit_multiline = sg.Multiline(self.edit_tab.content,
                                       key=self.edit_tab.key, size=(92, 32),
                                       background_color='#444444',
                                       text_color='#FFFFFF',
                                       font='Courier 11',
                                       expand_x=True, expand_y=True,
                                       enable_events=True,
									   horizontal_scroll=True)

        tabs_row = [
            sg.Column(
                [[sg.Text('Terminal')], [term_multiline]],
                expand_x=True, expand_y=True),
            sg.Column(
                [[sg.Text('Edit')], [edit_multiline]],
                expand_x=True, expand_y=True),
        ]

        entry_row = [
            sg.Button('>>>', key='-PROMPT-', disabled=True),
            sg.Input(key='-LINE-', size=(90, 1), font='Courier 11',
                      background_color='#444444', text_color='#FFFFFF',
                      enable_events=True),
            sg.Combo([], key='-HISTORY-', size=(3, 1), readonly=True,
                     enable_events=True),
            sg.Text('Example:'), sg.Combo([], key='-EXAMPLES-', size=(18, 1),
                                           enable_events=True, readonly=True),
            sg.Text('Library:'), sg.Combo([], key='-LIBRARIES-', size=(18, 1),
                                           enable_events=True, readonly=True),
					 
        ]

        button_row1 = [
            sg.Button('Send', key='-SEND-', disabled=True,pad=1),
            sg.Button('Send File', key='-SENDFILE-', disabled=True,pad=1),
            sg.Button('Interrupt', key='-INTERRUPT-', disabled=True,pad=1),
            sg.Button('Reboot', key='-REBOOT-', disabled=True,pad=1),
            sg.Button('Attention', key='-ATTENTION-', disabled=True,pad=1),
            sg.Button('Clear Terminal', key='-CLEARTERM-',pad=1),
            sg.Button('Clear Edit', key='-CLEAREDIT-',pad=1),
            sg.Button('Save Terminal', key='-SAVETERM-',pad=1),
            sg.Button('Save Edit', key='-SAVEEDIT-',pad=1),
            sg.Button('Append File', key='-APPENDFILE-',pad=1),
            sg.Button('Expand Includes', key='-EXPANDINCLUDES-',pad=1),
            sg.Button('Set Working Directory', key='-SETWORKINGDIR-',pad=1),
            sg.Button('Set Symbols', key='-SETSYMBOLS-',pad=1),
            sg.Button('Clear Symbols', key='-CLEARSYMBOLS-',pad=1),
            sg.Checkbox('Strip Code', key='-STRIP-',pad=1),
            sg.Checkbox('Timeout (ms):', key='-TIMEOUTEN-',pad=1),
            sg.Input('5000', key='-TIMEOUTMS-', size=(5, 1),pad=1),
            sg.Text('Save Edit Format:',pad=1),
            sg.Combo(SAVE_FORMATS, default_value='lf', key='-SAVEFORMAT-',
                     size=(3, 1), readonly=True),

			]

        layout = [
            top_row,
            tabs_row,
            entry_row,
            button_row1,
			]

        self.window = sg.Window('zeptocom.py Forth Terminal', layout,
                                 resizable=True, finalize=True)
        self.refresh_code_dropdowns('zeptoforth')

    # ---- terminal output helpers ----

    def write_term(self, tab, text):
        tab.current_data.append(text)
        tab.recent_text = (tab.recent_text + text)[-256:]
        if self.window:
            self.window.write_event_value('-TERMOUTPUT-', (tab, text))

    def info_msg(self, tab, msg):
        self.write_term(tab, msg)

    def error_msg(self, tab, msg):
        self.write_term(tab, msg)

    # ---- connect params ----

    def save_connect_params(self, tab):
        v = self.window
        if not tab.port:
            tab.baud = int(v['-BAUD-'].get())
            tab.data_bits = int(v['-DATABITS-'].get())
            tab.stop_bits = int(v['-STOPBITS-'].get())
            tab.parity = v['-PARITY-'].get()
            tab.flow_control = v['-FLOWCONTROL-'].get()
        tab.target_type = v['-TARGETTYPE-'].get()
        tab.newline_mode = v['-NEWLINEMODE-'].get()
        tab.tx_newline_mode = v['-TXNEWLINEMODE-'].get()
        self.refresh_code_dropdowns(tab.target_type)
        self.update_button_enable()

    def update_connect_params(self, tab):
        v = self.window
        v['-BAUD-'].update(value=tab.baud)
        v['-DATABITS-'].update(value=tab.data_bits)
        v['-STOPBITS-'].update(value=tab.stop_bits)
        v['-PARITY-'].update(value=tab.parity)
        v['-FLOWCONTROL-'].update(value=tab.flow_control)
        v['-TARGETTYPE-'].update(value=tab.target_type)
        v['-NEWLINEMODE-'].update(value=tab.newline_mode)
        v['-TXNEWLINEMODE-'].update(value=tab.tx_newline_mode)
        self.refresh_code_dropdowns(tab.target_type)

    def refresh_code_dropdowns(self, platform):
        self.window['-EXAMPLES-'].update(
            values=[t for t, _ in example_map.get(platform, [])])
        self.window['-LIBRARIES-'].update(
            values=[t for t, _ in library_map.get(platform, [])])

    def update_button_enable(self):
        tab = self.current_term_tab
        if tab is None:
            return
        w = self.window
        connected = bool(tab.port) and not tab.trigger_close \
            and not tab.trigger_abort
        for k in ('-BAUD-', '-DATABITS-', '-STOPBITS-', '-PARITY-',
                  '-FLOWCONTROL-'):
            w[k].update(disabled=connected)
        w['-CONNECT-'].update(disabled=connected)
        w['-DISCONNECT-'].update(disabled=not connected)
        if connected:
            if tab.sending:
                w['-SEND-'].update(disabled=True)
                w['-SENDFILE-'].update(disabled=True)
                w['-PROMPT-'].update(disabled=True)
                w['-INTERRUPT-'].update(disabled=False)
            else:
                w['-SEND-'].update(disabled=False)
                w['-SENDFILE-'].update(disabled=False)
                w['-PROMPT-'].update(disabled=False)
                w['-INTERRUPT-'].update(disabled=True)
            zf = tab.target_type == 'zeptoforth'
            w['-REBOOT-'].update(disabled=not zf)
            w['-ATTENTION-'].update(disabled=not zf)
        else:
            for k in ('-SEND-', '-SENDFILE-', '-REBOOT-', '-ATTENTION-',
                      '-PROMPT-', '-INTERRUPT-'):
                w[k].update(disabled=True)

    # ---- serial connect / disconnect ----

    def connect(self, tab):
        self.save_connect_params(tab)
        ports = [p.device for p in serial.tools.list_ports.comports()]
        if not ports:
            sg.popup_error('No serial ports found.')
            return
        layout = [[sg.Text('Serial port:'),
                   sg.Combo(ports, default_value=ports[0], key='-PORT-',
                            readonly=True)],
                  [sg.Button('OK'), sg.Button('Cancel')]]
        picker = sg.Window('Select Port', layout, modal=True)
        chosen = None
        while True:
            pe, pv = picker.read()
            if pe in (sg.WIN_CLOSED, 'Cancel'):
                break
            if pe == 'OK':
                chosen = pv['-PORT-']
                break
        picker.close()
        if not chosen:
            return
        try:
            ser = serial.Serial()
            ser.port = chosen
            ser.baudrate = tab.baud
            ser.bytesize = serial.EIGHTBITS if tab.data_bits == 8 \
                else serial.SEVENBITS
            ser.stopbits = STOPBIT_MAP[tab.stop_bits]
            ser.parity = PARITY_MAP[tab.parity]
            ser.rtscts = (tab.flow_control == 'hardware')
            ser.timeout = 0.1
            ser.open()
            try:
                ser.dtr = True
            except Exception:
                pass
        except Exception as e:
            sg.popup_error(f'Could not open {chosen}: {e}')
            return
        tab.port = ser
        tab.lost_count = 0
        tab.trigger_close = False
        tab.trigger_abort = False
        tab.reader_stop.clear()
        tab.reader_thread = threading.Thread(
            target=self.reader_loop, args=(tab,), daemon=True)
        tab.reader_thread.start()
        self.info_msg(tab, 'Connected\r\n')
        self.update_button_enable()

    def disconnect(self, tab, lost=False, silent=False):
        if not tab.port:
            return
        if not lost:
            tab.interrupt_count += 1
            tab.nak_event.set()
        tab.trigger_close = True
        tab.trigger_abort = True
        tab.reader_stop.set()
        try:
            tab.port.close()
        except Exception:
            pass
        tab.port = None
        tab.trigger_abort = False
        tab.trigger_close = False
        if not silent:
            if not lost:
                self.info_msg(tab, 'Disconnected\r\n')
            else:
                self.error_msg(tab, 'Connection lost\r\n')
        self.update_button_enable()

    def send_ctrl_c(self, tab):
        if tab.port:
            try:
                tab.port.write(bytes([0x03]))
            except Exception:
                pass

    def send_ctrl_t(self, tab):
        if tab.port:
            try:
                tab.port.write(bytes([0x14]))
            except Exception:
                pass

    def interrupt(self, tab):
        tab.interrupt_count += 1
        tab.nak_event.set()

    def reboot(self, tab):
        if tab.sending:
            tab.reboot_count += 1
            tab.nak_event.set()
        else:
            self.error_msg(tab, 'Reboot\r\n')
            self.send_ctrl_c(tab)

    def attention(self, tab):
        if tab.sending:
            tab.attention_count += 1
            tab.nak_event.set()
        else:
            self.error_msg(tab, 'Attention\r\n')
            self.send_ctrl_t(tab)

    # ---- reader thread: reads bytes, does ack/nak + newline-fixup ----

    def reader_loop(self, tab):
        ser = tab.port
        tab.receiving = True
        while not tab.reader_stop.is_set() and ser and ser.is_open:
            try:
                data = ser.read(256)
            except Exception:
                self.events_q.put(('lost', tab))
                self.window.write_event_value('-CONNLOST-', tab)
                break
            if not data:
                continue
            self.process_incoming(tab, data)
        tab.receiving = False

    def process_incoming(self, tab, data):
        # zeptoforth: single-byte ACK (0x06) / NAK (0x15)
        if tab.target_type == 'zeptoforth':
            for b in data:
                if b == 0x06:
                    tab.ack_count += 1
                    tab.ack_event.set()
                if b == 0x15:
                    tab.nak_count += 1
                    tab.nak_event.set()

        # newline fix-up per Rx Newline mode
        fixed = bytearray()
        if tab.newline_mode == 'lf':
            for b in data:
                if b == 0x0A:
                    fixed += b'\r\n'
                elif not (tab.target_type == 'stm8eforth' and b == 0x0D):
                    fixed.append(b)
        elif tab.newline_mode == 'cr':
            for b in data:
                fixed.append(b)
                if b == 0x0D:
                    fixed.append(0x0A)
        else:
            fixed = bytearray(data)

        text = fixed.decode('latin-1', errors='replace')
        tab.recent_text = (tab.recent_text + text)[-256:]

        # simplified rolling-buffer "ok prompt" detection for the other
        # target types (see module docstring for caveats)
        if tab.target_type == 'punyforth':
            buf = tab.recent_text
            if ('Exeption: ' in buf or 'Loading Punyforth' in buf or
                    'Word has no interpretation semantics' in buf):
                if buf.rstrip().endswith(')') and '(stack' in buf:
                    tab.nak_count += 1
                    tab.nak_event.set()
                    tab.recent_text = ''
            elif 'Undefined word: ' in buf:
                if tab.compile_state and buf.rstrip().endswith('. '):
                    tab.nak_count += 1
                    tab.nak_event.set()
                    tab.recent_text = ''
                elif (not tab.compile_state and buf.rstrip().endswith(')')
                        and '(stack' in buf):
                    tab.nak_count += 1
                    tab.nak_event.set()
                    tab.recent_text = ''
            else:
                if tab.compile_state and buf.rstrip().endswith('. '):
                    tab.ack_count += 1
                    tab.ack_event.set()
                    tab.recent_text = ''
                elif (not tab.compile_state and buf.rstrip().endswith(')')
                        and '(stack' in buf):
                    tab.ack_count += 1
                    tab.ack_event.set()
                    tab.recent_text = ''
        elif tab.target_type in ('mecrisp', 'stm8eforth', 'esp32forth',
                                  'flashforth'):
            ok_str = OK_STRINGS.get(tab.target_type, ' ok')
            buf = tab.recent_text
            hit = buf.endswith(ok_str) or (
                tab.target_type == 'stm8eforth' and buf.endswith(' OK'))
            if hit:
                tab.ack_count += 1
                tab.ack_event.set()
                tab.recent_text = ''
            elif tab.target_type == 'flashforth' and (
                    buf.endswith(' COMPILE ONLY\r\n') or
                    buf.endswith(' ?\r\n')):
                tab.nak_count += 1
                tab.nak_event.set()
                tab.recent_text = ''

        self.write_term(tab, text)

    # ---- sending ----

    def write_line_bytes(self, tab, line):
        if tab.target_type in ('flashforth', 'punyforth'):
            for part in line.strip().split():
                p = part.strip()
                if p in (':', ':noname', ']'):
                    tab.compile_state = True
                elif p == ';' or (tab.target_type == 'flashforth' and
                                   p == ';i') or p == '[':
                    tab.compile_state = False
        if tab.target_type == 'punyforth':
            self.write_term(tab, line + '\r\n')
        line = line + tab.tx_newline()
        data = line.encode('utf-8', errors='replace')
        try:
            while tab.port and len(data) > 128:
                tab.port.write(data[:128])
                time.sleep(0.02)
                data = data[128:]
            if tab.port and data:
                tab.port.write(data)
        except Exception:
            pass

    def write_text_worker(self, tab, text):
        """Runs in a background thread: line-by-line send with ACK/NAK
        handshaking, mirroring writeText()/handleAck()/handleNak() in the
        original JS."""
        tab.sending = True
        self.window.write_event_value('-BUTTONSTATE-', None)

        def err(msg):
            self.error_msg(tab, msg)

        lines = expand_lines(re.split(r'\r?\n', text),
                              [global_symbols, {}], err)
        if lines is None:
            tab.sending = False
            tab.trigger_abort = False
            self.window.write_event_value('-BUTTONSTATE-', None)
            return
        while len(lines) > 1 and lines[-1] == '':
            lines = lines[:-1]
        if self.window['-STRIP-'].get():
            lines = strip_code(lines)
            if not lines:
                lines = ['']

        timeout_enabled = self.window['-TIMEOUTEN-'].get()
        try:
            timeout_ms = int(self.window['-TIMEOUTMS-'].get())
        except ValueError:
            timeout_ms = 5000

        current_interrupt = tab.interrupt_count
        current_reboot = tab.reboot_count
        current_attention = tab.attention_count
        current_lost = tab.lost_count

        for line in lines:
            if tab.trigger_abort or not tab.port:
                break
            tab.ack_event.clear()
            tab.nak_event.clear()
            self.write_line_bytes(tab, line)
            if len(lines) > 1 and line != lines[-1]:
                timed_out = not (tab.ack_event.wait(
                    timeout_ms / 1000.0 if timeout_enabled else None) or
                    tab.nak_event.is_set())
                if timed_out:
                    self.error_msg(tab, 'Timed out\r\n')
                    if tab.target_type in ('flashforth', 'punyforth'):
                        tab.compile_state = False
                    break
                if tab.nak_event.is_set():
                    if tab.lost_count != current_lost:
                        self.disconnect(tab, lost=True)
                        break
                    elif tab.interrupt_count != current_interrupt:
                        self.error_msg(tab, 'Interrupted\r\n')
                        if tab.target_type in ('flashforth', 'punyforth'):
                            tab.compile_state = False
                        break
                    elif tab.reboot_count != current_reboot:
                        self.error_msg(tab, 'Reboot\r\n')
                        if tab.target_type in ('flashforth', 'punyforth'):
                            tab.compile_state = False
                        self.send_ctrl_c(tab)
                        break
                    elif tab.attention_count != current_attention:
                        self.error_msg(tab, 'Attention\r\n')
                        self.send_ctrl_t(tab)
                        break
                    else:
                        self.error_msg(tab, 'Rejected\r\n')
                        break

        tab.sending = False
        tab.trigger_abort = False
        self.window.write_event_value('-BUTTONSTATE-', None)

    def send_text(self, tab, text):
        threading.Thread(target=self.write_text_worker, args=(tab, text),
                          daemon=True).start()

    # ---- main loop ----

    def run(self):
        w = self.window
        w['-TIMEOUTMS-'].update(disabled=False)
        while True:
            event, values = w.read(timeout=100)
            if event in (sg.WIN_CLOSED, None):
                for t in self.term_tabs:
                    self.disconnect(t, silent=True)
                break

            if event == '-TERMOUTPUT-':
                tab, text = values['-TERMOUTPUT-']
                w[tab.key].update(text, append=True)

            elif event == '-CONNLOST-':
                tab = values['-CONNLOST-']
                self.disconnect(tab, lost=True)

            elif event == '-BUTTONSTATE-':
                self.update_button_enable()

            elif event == '-TARGETTYPE-':
                tt = values['-TARGETTYPE-']
                if tt in ('mecrisp', 'stm8eforth'):
                    w['-NEWLINEMODE-'].update(value='lf')
                elif tt in ('zeptoforth', 'esp32forth', 'flashforth',
                            'punyforth'):
                    w['-NEWLINEMODE-'].update(value='crlf')
                w['-TXNEWLINEMODE-'].update(
                    value='crlf' if tt == 'punyforth' else 'cr')
                if self.current_term_tab:
                    self.save_connect_params(self.current_term_tab)

            elif event in ('-BAUD-', '-DATABITS-', '-STOPBITS-', '-PARITY-',
                           '-FLOWCONTROL-', '-NEWLINEMODE-',
                           '-TXNEWLINEMODE-'):
                if self.current_term_tab:
                    self.save_connect_params(self.current_term_tab)

            elif event == '-CONNECT-':
                if self.current_term_tab:
                    self.connect(self.current_term_tab)

            elif event == '-DISCONNECT-':
                if self.current_term_tab:
                    self.disconnect(self.current_term_tab)

            elif event == '-CLEARTERM-':
                if self.current_term_tab:
                    t = self.current_term_tab
                    w[t.key].update('')
                    t.current_data = []

            elif event == '-CLEAREDIT-':
                if self.current_edit_tab:
                    w[self.current_edit_tab.key].update('')

            elif event == '-SAVETERM-':
                if self.current_term_tab:
                    self.save_terminal(self.current_term_tab)

            elif event == '-SAVEEDIT-':
                self.save_edit(values)

            elif event == '-APPENDFILE-':
                self.append_file(values)

            elif event == '-EXPANDINCLUDES-':
                self.expand_includes_ui(values)

            elif event == '-SETWORKINGDIR-':
                folder = sg.popup_get_folder('Choose working directory')
                if folder:
                    global working_dir
                    working_dir = folder

            elif event == '-SETSYMBOLS-':
                self.set_global_symbols()

            elif event == '-CLEARSYMBOLS-':
                global_symbols.clear()
                if self.current_term_tab:
                    self.info_msg(self.current_term_tab,
                                  'Global symbols cleared\r\n')

            elif event == '-HELP-':
                self.show_help()

            elif event == '-LICENSE-':
                self.show_license()

            elif event == '-PROMPT-' or (
                    event == '-LINE-' and
                    values.get('-LINE-', '').endswith('\n')):
                self.send_entry(values)

            elif event == '-SEND-':
                self.send_area(values)

            elif event == '-SENDFILE-':
                self.send_file_ui()

            elif event == '-INTERRUPT-':
                if self.current_term_tab and self.current_term_tab.port:
                    self.interrupt(self.current_term_tab)

            elif event == '-REBOOT-':
                t = self.current_term_tab
                if t and t.port and t.target_type == 'zeptoforth':
                    self.reboot(t)

            elif event == '-ATTENTION-':
                t = self.current_term_tab
                if t and t.port and t.target_type == 'zeptoforth':
                    self.attention(t)

            elif event == '-HISTORY-':
                self.window['-LINE-'].update(values['-HISTORY-'])

            elif event == '-EXAMPLES-':
                self.load_code_selection(values, '-EXAMPLES-', example_map)

            elif event == '-LIBRARIES-':
                self.load_code_selection(values, '-LIBRARIES-', library_map)

        w.close()

    # ---- action helpers used from the main loop ----

    def send_entry(self, values):
        tab = self.current_term_tab
        line = values.get('-LINE-', '').rstrip('\n')
        add_to_history(line)
        self.window['-LINE-'].update('')
        self.window['-HISTORY-'].update(values=history)
        if tab:
            self.send_text(tab, line)

    def send_area(self, values):
        tab = self.current_term_tab
        et = self.current_edit_tab
        if not tab or not et:
            return
        try:
            widget = self.window[et.key].Widget
            sel = widget.tag_ranges('sel')
        except Exception:
            sel = None
        if sel:
            text = widget.get(sel[0], sel[1])
        else:
            text = values.get(et.key, '')
        self.send_text(tab, text)

    def send_file_ui(self):
        tab = self.current_term_tab
        if not tab:
            return
        path = sg.popup_get_file('Send file')
        if not path:
            return
        try:
            with open(path, 'r', encoding='utf-8', errors='replace') as f:
                text = f.read()
        except OSError as e:
            sg.popup_error(f'Could not read file: {e}')
            return
        self.send_text(tab, text)

    def save_terminal(self, tab):
        path = sg.popup_get_file('Save terminal output as', save_as=True)
        if not path:
            return
        try:
            with open(path, 'w', encoding='utf-8', errors='replace') as f:
                for item in tab.current_data:
                    f.write(item)
        except OSError as e:
            sg.popup_error(f'Could not save: {e}')

    def save_edit(self, values):
        et = self.current_edit_tab
        if not et:
            return
        path = sg.popup_get_file('Save edit tab as', save_as=True)
        if not path:
            return
        et.file_name = os.path.basename(path)
        newline = '\r\n' if values.get('-SAVEFORMAT-') == 'crlf' else '\n'
        content = values.get(et.key, '')
        try:
            with open(path, 'w', encoding='utf-8', errors='replace') as f:
                f.write(newline.join(re.split(r'\r?\n', content)))
        except OSError as e:
            sg.popup_error(f'Could not save: {e}')

    def append_file(self, values):
        et = self.current_edit_tab
        if not et:
            return
        path = sg.popup_get_file('Append file into edit tab')
        if not path:
            return
        try:
            with open(path, 'r', encoding='utf-8', errors='replace') as f:
                text = f.read()
        except OSError as e:
            sg.popup_error(f'Could not read file: {e}')
            return
        current = values.get(et.key, '')
        new_content = (current + ('' if current.endswith('\n') or not
                       current else '\n') + text)
        self.window[et.key].update(new_content)
        if not et.file_name:
            et.file_name = os.path.basename(path)

    def expand_includes_ui(self, values):
        et = self.current_edit_tab
        if not et:
            return
        text = values.get(et.key, '')

        def err(msg):
            if self.current_term_tab:
                self.error_msg(self.current_term_tab, msg)

        lines = expand_lines(re.split(r'\r?\n', text), [{}], err)
        if lines is None:
            return
        self.window[et.key].update('\n'.join(lines))

    def set_global_symbols(self):
        path = sg.popup_get_file('Load global symbols file')
        if not path:
            return
        try:
            lines = slurp_file(path)
        except OSError as e:
            sg.popup_error(f'Could not read file: {e}')
            return
        global_symbols.clear()
        parse_symbols(lines, global_symbols)
        if self.current_term_tab:
            self.info_msg(self.current_term_tab,
                          'New global symbols loaded\r\n')

    def load_code_selection(self, values, combo_key, mp):
        title = values.get(combo_key)
        tab = self.current_term_tab
        platform = tab.target_type if tab else 'zeptoforth'
        entries = mp.get(platform, [])
        match = next((p for t, p in entries if t == title), None)
        self.window[combo_key].update(value='')
        if not match:
            return
        base_dir = os.path.dirname(os.path.abspath(__file__))
        full_path = os.path.join(base_dir, match)
        try:
            with open(full_path, 'r', encoding='utf-8', errors='replace') \
                    as f:
                content = f.read()
        except OSError as e:
            sg.popup_error(f'Could not load {match}: {e}')
            return
        self.window[self.edit_tab.key].update(content)
        self.edit_tab.file_name = None
        self.edit_tab.orig_name = title

    def show_help(self):
        sg.popup_scrolled(
            "zeptocom.py Forth Terminal\n\n"
            "Connect: opens a serial port with the chosen settings.\n"
            "Send: uploads the current edit tab (or selection) to the "
            "target, line by line, waiting for an ack/ok prompt between "
            "lines.\n"
            "Send File: same, but reads the text from a file you pick.\n"
            "Interrupt / Reboot / Attention: control signals recognized "
            "by zeptoforth targets.\n"
            "History dropdown: recently sent single lines.\n"
            "Set Working Directory / Set Symbols: used by #include and "
            "#symbols directives inside code you send.\n",
            title='Help')

    def show_license(self):
        sg.popup_scrolled(
            "Copyright (c) 2022-2025 Travis Bemann\n\n"
            "Permission is hereby granted, free of charge, to any person "
            "obtaining a copy of this software and associated "
            "documentation files (the \"Software\"), to deal in the "
            "Software without restriction, including without limitation "
            "the rights to use, copy, modify, merge, publish, "
            "distribute, sublicense, and/or sell copies of the Software, "
            "and to permit persons to whom the Software is furnished to "
            "do so, subject to the following conditions:\n\n"
            "The above copyright notice and this permission notice shall "
            "be included in all copies or substantial portions of the "
            "Software.\n\n"
            "THE SOFTWARE IS PROVIDED \"AS IS\", WITHOUT WARRANTY OF ANY "
            "KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE "
            "WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR "
            "PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS "
            "OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR "
            "OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR "
            "OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE "
            "SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.\n",
            title='License')


def main():
    app = ZeptocomApp()
    app.run()


if __name__ == '__main__':
    main()
