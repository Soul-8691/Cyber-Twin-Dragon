import tkinter as tk
from tkinter import filedialog, messagebox
from tkinter.scrolledtext import ScrolledText
from tkinter import ttk
import os

# =========================
# CONSTANTS FOR THIS ROM
# =========================

# Pointer tables for card text
CARD_NAME_PTR_BASE = 0x15BB594
CARD_DESC_PTR_BASE = 0x15BD65C

# Text section base and limit
TEXT_BASE = 0x15BF724
TEXT_LIMIT = 0x162248A  # exclusive upper bound for searching free space

# Card stats table
CARD_STATS_BASE = 0x18169B8
CARD_STATS_SIZE = 0x16  # 0x16 bytes per card

# Card ID table (Konami ID -> card index)
CARD_ID_TABLE_BASE = 0x15B7CCC
KONAMI_ID_BASE = 4007  # Konami ID offset

# Number of entries in each table:
#   (0x15BD65C - 0x15BB594) / 4 = 2098
NUM_CARDS = 2098


class CardEntry:
    def __init__(self, index,
                 name, desc,
                 name_ptr_off, desc_ptr_off,
                 name_addr, desc_addr,
                 name_len, desc_len,
                 konami_id, card_id_index,
                 artwork_id, edited_flag,
                 atk, deff, level,
                 race, attribute, type_, st_race, padding):
        self.index = index

        # CURRENT text strings (edited in UI)
        self.name = name
        self.desc = desc

        # Pointer offsets (absolute file offsets where 4-byte relative pointers live)
        self.name_ptr_off = name_ptr_off
        self.desc_ptr_off = desc_ptr_off

        # CURRENT addresses (can change if repointed)
        self.name_addr = name_addr
        self.desc_addr = desc_addr

        # Slot sizes: how many bytes were originally / currently allocated
        # (string length + 1 terminator)
        self.name_slot_size = name_len + 1
        self.desc_slot_size = desc_len + 1

        # Card stats
        self.konami_id = konami_id
        # Card ID = index into card names list (from card ID table)
        self.card_id_index = card_id_index
        self.artwork_id = artwork_id
        self.edited_flag = edited_flag
        self.atk = atk
        self.deff = deff
        self.level = level
        self.race = race
        self.attribute = attribute
        self.type_ = type_
        self.st_race = st_race
        self.padding = padding  # normally not edited, but kept


class RomEditorApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Yu-Gi-Oh! UM 2006 – Card Editor")

        self.rom_path = None
        self.rom_data = None  # bytearray
        self.cards = []       # list[CardEntry]
        self.current_index = None  # selected card index in self.cards
        self.filtered_indices = []  # mapping listbox row -> card index

        # Optional text-based mappings for race/attribute/type/spell_trap_race
        self.races_list = []
        self.attributes_list = []
        self.types_list = []
        self.st_races_list = []

        # Card ID dropdown values (index + name)
        self.card_id_choices = []

        # flag to suppress Konami ID trace recursion
        self._updating_konami = False

        self._load_text_mappings()
        self._build_ui()

    # =========================
    # LOAD TEXT MAPPINGS
    # =========================

    def _load_text_mappings(self):
        """
        Load ../text/races.txt, ../text/attributes.txt, ../text/types.txt,
        ../text/spell_trap_races.txt relative to this script.
        """
        try:
            base_dir = os.path.dirname(os.path.abspath(__file__))
        except Exception:
            base_dir = os.getcwd()

        def load_lines(rel_path):
            full = os.path.join(base_dir, rel_path)
            if not os.path.isfile(full):
                return []
            with open(full, "r", encoding="utf-8", errors="ignore") as f:
                return [line.strip() for line in f.readlines() if line.strip()]

        self.races_list = load_lines(os.path.join("..", "text", "races.txt"))
        self.attributes_list = load_lines(os.path.join("..", "text", "attributes.txt"))
        self.types_list = load_lines(os.path.join("..", "text", "types.txt"))
        self.st_races_list = load_lines(os.path.join("..", "text", "spell_trap_races.txt"))

    # =========================
    # UI SETUP
    # =========================

    def _build_ui(self):
        # Menu
        menubar = tk.Menu(self)
        file_menu = tk.Menu(menubar, tearoff=False)
        file_menu.add_command(label="Open ROM...", command=self.open_rom)
        file_menu.add_command(label="Save ROM As...", command=self.save_rom_as)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.quit)
        menubar.add_cascade(label="File", menu=file_menu)
        self.config(menu=menubar)

        # Main layout: left list, right editor
        main_frame = tk.Frame(self)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        # Left: card list + search
        left_frame = tk.Frame(main_frame)
        left_frame.pack(side=tk.LEFT, fill=tk.Y)

        # Search box
        search_frame = tk.Frame(left_frame)
        search_frame.pack(fill=tk.X, pady=(0, 5))

        tk.Label(search_frame, text="Filter by name:").pack(side=tk.LEFT)
        self.search_var = tk.StringVar()
        search_entry = tk.Entry(search_frame, textvariable=self.search_var, width=20)
        search_entry.pack(side=tk.LEFT, padx=(3, 3))
        search_entry.bind("<Return>", lambda e: self.apply_filter())

        tk.Button(search_frame, text="Apply", command=self.apply_filter).pack(side=tk.LEFT)
        tk.Button(search_frame, text="Clear", command=self.clear_filter).pack(side=tk.LEFT, padx=(3, 0))

        tk.Label(left_frame, text="Cards").pack(anchor="w")

        self.card_listbox = tk.Listbox(left_frame, width=40)
        self.card_listbox.pack(side=tk.LEFT, fill=tk.Y, expand=False)

        scrollbar = tk.Scrollbar(left_frame, orient=tk.VERTICAL, command=self.card_listbox.yview)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.card_listbox.config(yscrollcommand=scrollbar.set)
        self.card_listbox.bind("<<ListboxSelect>>", self.on_card_selected)

        # Right: editor pane
        right_frame = tk.Frame(main_frame)
        right_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)

        self.info_label = tk.Label(right_frame, text="No ROM loaded.")
        self.info_label.pack(anchor="w", pady=(0, 5))

        # Name
        name_frame = tk.Frame(right_frame)
        name_frame.pack(fill=tk.X, pady=2)
        tk.Label(name_frame, text="Card Name:").pack(anchor="w")
        self.name_var = tk.StringVar()
        self.name_entry = tk.Entry(name_frame, textvariable=self.name_var)
        self.name_entry.pack(fill=tk.X)

        # Description
        desc_frame = tk.Frame(right_frame)
        desc_frame.pack(fill=tk.BOTH, expand=True, pady=(5, 0))
        tk.Label(desc_frame, text="Card Description:").pack(anchor="w")
        self.desc_text = ScrolledText(desc_frame, height=8, wrap=tk.WORD)
        self.desc_text.pack(fill=tk.BOTH, expand=True)

        # --- Card Stats section ---
        stats_frame = tk.LabelFrame(right_frame, text="Card Stats")
        stats_frame.pack(fill=tk.X, pady=(5, 0))

        # Variables
        self.konami_id_var = tk.IntVar()
        self.card_id_var = tk.StringVar()
        self.artwork_id_var = tk.IntVar()
        self.edited_flag_var = tk.IntVar()
        self.atk_var = tk.IntVar()
        self.def_var = tk.IntVar()
        self.level_var = tk.IntVar()
        self.race_var = tk.IntVar()
        self.attribute_var = tk.IntVar()
        self.type_var = tk.IntVar()
        self.st_race_var = tk.IntVar()
        self.padding_var = tk.IntVar()

        # Helper to build numeric Entry
        def add_numeric_row(row, label, var, width=8):
            tk.Label(stats_frame, text=label).grid(row=row, column=0, sticky="w", padx=2, pady=1)
            entry = tk.Entry(stats_frame, textvariable=var, width=width)
            entry.grid(row=row, column=1, sticky="w", padx=2, pady=1)
            return entry

        row = 0
        # Konami ID first
        self.konami_entry = add_numeric_row(row, "Konami ID:", self.konami_id_var); row += 1

        # Card ID (dropdown)
        tk.Label(stats_frame, text="Card ID (Name Index):").grid(row=row, column=0, sticky="w", padx=2, pady=1)
        self.card_id_combo = ttk.Combobox(stats_frame, textvariable=self.card_id_var, state="readonly", width=30)
        self.card_id_combo.grid(row=row, column=1, sticky="w", padx=2, pady=1)
        row += 1

        # Rest of stats
        self.artwork_entry = add_numeric_row(row, "Artwork #:", self.artwork_id_var); row += 1
        self.edited_entry = add_numeric_row(row, "Edited Art Flag:", self.edited_flag_var); row += 1
        self.atk_entry = add_numeric_row(row, "ATK:", self.atk_var); row += 1
        self.def_entry = add_numeric_row(row, "DEF:", self.def_var); row += 1
        self.level_entry = add_numeric_row(row, "Level:", self.level_var); row += 1

        # Helper to build Combobox with fallback
        def add_combo_row(row, label, values_list, numeric_var):
            tk.Label(stats_frame, text=label).grid(row=row, column=0, sticky="w", padx=2, pady=1)
            frame = tk.Frame(stats_frame)
            frame.grid(row=row, column=1, sticky="w", padx=2, pady=1)

            combo = None
            if values_list:
                combo = ttk.Combobox(frame, values=values_list, state="readonly", width=20)
                combo.pack(side=tk.LEFT)
            else:
                # Fallback numeric entry only
                entry = tk.Entry(frame, textvariable=numeric_var, width=8)
                entry.pack(side=tk.LEFT)

            return combo

        self.race_combo = add_combo_row(row, "Race:", self.races_list, self.race_var); row += 1
        self.attribute_combo = add_combo_row(row, "Attribute:", self.attributes_list, self.attribute_var); row += 1
        self.type_combo = add_combo_row(row, "Type:", self.types_list, self.type_var); row += 1
        self.st_race_combo = add_combo_row(row, "Spell/Trap Race:", self.st_races_list, self.st_race_var); row += 1

        # Padding (readonly-ish)
        tk.Label(stats_frame, text="Padding (raw):").grid(row=row, column=0, sticky="w", padx=2, pady=1)
        self.padding_entry = tk.Entry(stats_frame, textvariable=self.padding_var, width=8, state="disabled")
        self.padding_entry.grid(row=row, column=1, sticky="w", padx=2, pady=1)
        row += 1

        # Navigation / update buttons
        button_frame = tk.Frame(right_frame)
        button_frame.pack(fill=tk.X, pady=5)

        self.prev_btn = tk.Button(button_frame, text="<< Previous", command=self.prev_card, state=tk.DISABLED)
        self.prev_btn.pack(side=tk.LEFT)

        self.next_btn = tk.Button(button_frame, text="Next >>", command=self.next_card, state=tk.DISABLED)
        self.next_btn.pack(side=tk.LEFT, padx=(5, 0))

        self.apply_btn = tk.Button(button_frame, text="Apply Changes (in memory)", command=self.apply_changes, state=tk.DISABLED)
        self.apply_btn.pack(side=tk.RIGHT)

        # Trace Konami ID to auto-update Card ID
        self.konami_id_var.trace_add("write", self._on_konami_id_changed)

    # =========================
    # ROM HANDLING
    # =========================

    def open_rom(self):
        path = filedialog.askopenfilename(
            title="Select Yu-Gi-Oh! Ultimate Masters GBA ROM",
            filetypes=[("GBA ROM", "*.gba;*.bin;*.*"), ("All files", "*.*")]
        )
        if not path:
            return

        try:
            with open(path, "rb") as f:
                data = f.read()
        except Exception as e:
            messagebox.showerror("Error", f"Failed to open ROM:\n{e}")
            return

        # Make mutable
        self.rom_data = bytearray(data)
        self.rom_path = path

        try:
            self.cards = self._parse_cards()
        except Exception as e:
            messagebox.showerror("Error", f"Failed to parse ROM structures:\n{e}")
            self.rom_data = None
            self.cards = []
            return

        self._update_card_id_choices()

        self.current_index = 0
        self.clear_filter()  # populates full list
        self._load_card_into_editor(0)
        self._update_controls_state()
        self.info_label.config(text=f"Loaded ROM: {os.path.basename(self.rom_path)} ({NUM_CARDS} cards)")

    def save_rom_as(self):
        if not self.rom_data or not self.cards:
            messagebox.showinfo("No ROM", "Load a ROM first.")
            return

        # ensure current card edits are stored into self.cards
        self.apply_changes()

        save_path = filedialog.asksaveasfilename(
            title="Save modified ROM as",
            defaultextension=".gba",
            filetypes=[("GBA ROM", "*.gba;*.bin;*.*")]
        )
        if not save_path:
            return

        try:
            # Work on a copy so we don't corrupt the in-memory original if something goes wrong mid-way
            rom_copy = bytearray(self.rom_data)
            self._apply_all_changes_to_rom(rom_copy)
        except Exception as e:
            messagebox.showerror("Error", f"Error applying changes:\n{e}")
            return

        try:
            with open(save_path, "wb") as f:
                f.write(rom_copy)
        except Exception as e:
            messagebox.showerror("Error", f"Error saving ROM:\n{e}")
            return

        messagebox.showinfo("Success", f"ROM saved as:\n{save_path}")

    # =========================
    # PARSING STRUCTURES
    # =========================

    def _read_c_string(self, data, addr):
        """
        Read ASCII string from data starting at absolute address 'addr' until 0x00
        or until TEXT_LIMIT. Returns (string, length_without_terminator).
        """
        if addr < 0 or addr >= len(data):
            raise ValueError(f"String address {hex(addr)} out of range.")

        end_limit = min(TEXT_LIMIT, len(data))
        bytes_out = []
        pos = addr
        while pos < end_limit:
            b = data[pos]
            if b == 0:
                break
            bytes_out.append(b)
            pos += 1

        s = bytes(bytes_out).decode("ascii", errors="replace")
        return s, len(bytes_out)

    @staticmethod
    def _read_u16(data, offset):
        return int.from_bytes(data[offset:offset + 2], "little")

    @staticmethod
    def _write_u16(data, offset, value):
        data[offset:offset + 2] = int(value & 0xFFFF).to_bytes(2, "little")

    def _read_card_id_index_from_table(self, data, konami_id):
        """
        From Konami ID, read the card ID (card name index) from card ID table.
        """
        if konami_id < KONAMI_ID_BASE:
            return 0
        pos = konami_id - KONAMI_ID_BASE
        offset = CARD_ID_TABLE_BASE + pos * 2
        if offset + 2 > len(data):
            return 0
        return self._read_u16(data, offset)

    def _parse_cards(self):
        cards = []
        data = self.rom_data

        for i in range(NUM_CARDS):
            # ----- NAME POINTER -----
            name_ptr_off = CARD_NAME_PTR_BASE + i * 4
            name_rel = int.from_bytes(data[name_ptr_off:name_ptr_off + 4], "little")
            name_addr = TEXT_BASE + name_rel

            name_str, name_len = self._read_c_string(data, name_addr)

            # ----- DESCRIPTION POINTER -----
            desc_ptr_off = CARD_DESC_PTR_BASE + i * 4
            desc_rel = int.from_bytes(data[desc_ptr_off:desc_ptr_off + 4], "little")
            desc_addr = TEXT_BASE + desc_rel

            desc_str, desc_len = self._read_c_string(data, desc_addr)

            # ----- STATS STRUCT -----
            stats_off = CARD_STATS_BASE + i * CARD_STATS_SIZE
            if stats_off + CARD_STATS_SIZE > len(data):
                raise ValueError(f"Stats struct for card {i} goes beyond ROM size.")

            konami_id = self._read_u16(data, stats_off + 0x0)
            artwork_id = self._read_u16(data, stats_off + 0x2)
            edited_flag = self._read_u16(data, stats_off + 0x4)
            atk = self._read_u16(data, stats_off + 0x6)
            deff = self._read_u16(data, stats_off + 0x8)
            level = self._read_u16(data, stats_off + 0xA)
            race = self._read_u16(data, stats_off + 0xC)
            attribute = self._read_u16(data, stats_off + 0xE)
            type_ = self._read_u16(data, stats_off + 0x10)
            st_race = self._read_u16(data, stats_off + 0x12)
            padding = self._read_u16(data, stats_off + 0x14)

            # Card ID (card name index) from card ID table
            card_id_index = self._read_card_id_index_from_table(data, konami_id)

            card = CardEntry(
                index=i,
                name=name_str,
                desc=desc_str,
                name_ptr_off=name_ptr_off,
                desc_ptr_off=desc_ptr_off,
                name_addr=name_addr,
                desc_addr=desc_addr,
                name_len=name_len,
                desc_len=desc_len,
                konami_id=konami_id,
                card_id_index=card_id_index,
                artwork_id=artwork_id,
                edited_flag=edited_flag,
                atk=atk,
                deff=deff,
                level=level,
                race=race,
                attribute=attribute,
                type_=type_,
                st_race=st_race,
                padding=padding
            )
            cards.append(card)

        return cards

    # =========================
    # FREE SPACE SEARCH & WRITE
    # =========================

    def _find_free_space(self, rom_data, size):
        """
        Find a sequence of 'size' zero bytes between TEXT_BASE and TEXT_LIMIT.
        Returns absolute address or None.
        NOTE: Using run_start + 1 so we don't overwrite the very first 00 byte
        of the run (your requested behavior).
        """
        start = TEXT_BASE
        end = min(TEXT_LIMIT, len(rom_data))

        if size <= 0:
            return None

        run_start = None
        run_length = 0

        for addr in range(start, end):
            if rom_data[addr] == 0:
                if run_start is None:
                    run_start = addr
                    run_length = 1
                else:
                    run_length += 1

                if run_length >= size:
                    return run_start + 1
            else:
                run_start = None
                run_length = 0

        return None

    def _write_string_and_update_pointer(self, rom_data, card, is_name):
        """
        Write card.name or card.desc into ROM.
        - If fits current slot (slot_size), write in-place.
        - Otherwise, find free zero space, write there, update relative pointer,
          and zero out the original slot.
        - Always writes a 00 terminator after the text.
        """
        if is_name:
            text = card.name
            orig_addr = card.name_addr
            slot_size = card.name_slot_size
            ptr_off = card.name_ptr_off
        else:
            text = card.desc
            orig_addr = card.desc_addr
            slot_size = card.desc_slot_size
            ptr_off = card.desc_ptr_off

        encoded = text.encode("ascii", errors="replace")
        needed = len(encoded) + 1  # include 00 terminator

        # Decide where to put it
        if needed <= slot_size and 0 <= orig_addr < len(rom_data):
            # In-place
            write_addr = orig_addr
        else:
            # Need new space
            write_addr = self._find_free_space(rom_data, needed)
            if write_addr is None:
                raise RuntimeError(
                    f"Not enough free space for {'name' if is_name else 'description'} "
                    f"of card {card.index} (need {needed} bytes)."
                )

            # Zero out the allocated block fully before writing
            for i in range(write_addr, write_addr + needed):
                if i < len(rom_data):
                    rom_data[i] = 0

            # Zero out the old slot (replace original text with 00 bytes)
            if 0 <= orig_addr < len(rom_data):
                for offset in range(orig_addr, min(orig_addr + slot_size, len(rom_data))):
                    rom_data[offset] = 0

            # Update card's address and slot size in memory, and pointer in ROM
            if is_name:
                card.name_addr = write_addr
                card.name_slot_size = needed
            else:
                card.desc_addr = write_addr
                card.desc_slot_size = needed

            rel = write_addr - TEXT_BASE
            if rel < 0 or rel > 0xFFFFFFFF:
                raise RuntimeError("Relative pointer out of 32-bit range.")

            rom_data[ptr_off:ptr_off + 4] = rel.to_bytes(4, "little")

        # Actually write the new string
        if write_addr < 0 or write_addr + needed > len(rom_data):
            raise RuntimeError("Write address out of file bounds.")

        rom_data[write_addr:write_addr + len(encoded)] = encoded
        # Always ensure terminator is written
        if write_addr + len(encoded) < len(rom_data):
            rom_data[write_addr + len(encoded)] = 0
        else:
            raise RuntimeError("No space to write terminator byte.")

        # If we're writing in the original slot and the new string is shorter
        # than the slot, pad remaining slot with zeros to keep things clean.
        if write_addr == orig_addr and needed < slot_size:
            for offset in range(write_addr + needed, write_addr + slot_size):
                if offset < len(rom_data):
                    rom_data[offset] = 0

    def _write_stats(self, rom_data, card):
        """
        Write the card's stats back into the ROM at the correct struct location.
        """
        stats_off = CARD_STATS_BASE + card.index * CARD_STATS_SIZE
        if stats_off + CARD_STATS_SIZE > len(rom_data):
            raise RuntimeError(f"Stats struct for card {card.index} goes beyond ROM size.")

        self._write_u16(rom_data, stats_off + 0x0, card.konami_id)
        self._write_u16(rom_data, stats_off + 0x2, card.artwork_id)
        self._write_u16(rom_data, stats_off + 0x4, card.edited_flag)
        self._write_u16(rom_data, stats_off + 0x6, card.atk)
        self._write_u16(rom_data, stats_off + 0x8, card.deff)
        self._write_u16(rom_data, stats_off + 0xA, card.level)
        self._write_u16(rom_data, stats_off + 0xC, card.race)
        self._write_u16(rom_data, stats_off + 0xE, card.attribute)
        self._write_u16(rom_data, stats_off + 0x10, card.type_)
        self._write_u16(rom_data, stats_off + 0x12, card.st_race)
        self._write_u16(rom_data, stats_off + 0x14, card.padding)

    def _write_card_id_table_entry(self, rom_data, card):
        """
        Write card.card_id_index into the card ID table for card.konami_id.
        position = (KonamiID - 4007) * 2 bytes from CARD_ID_TABLE_BASE.
        """
        konami = card.konami_id
        if konami < KONAMI_ID_BASE:
            return
        pos = konami - KONAMI_ID_BASE
        offset = CARD_ID_TABLE_BASE + pos * 2
        if offset + 2 > len(rom_data):
            # out of ROM range; silently skip
            return
        self._write_u16(rom_data, offset, card.card_id_index)

    def _apply_all_changes_to_rom(self, rom_copy):
        """
        Apply all cards' name/desc changes, stats, and card ID mapping to rom_copy.
        """
        for card in self.cards:
            self._write_string_and_update_pointer(rom_copy, card, is_name=True)
            self._write_string_and_update_pointer(rom_copy, card, is_name=False)
            self._write_stats(rom_copy, card)
            self._write_card_id_table_entry(rom_copy, card)

    # =========================
    # CARD ID UI HELPERS
    # =========================

    def _card_id_display_for_index(self, idx):
        """
        Build display string like '0005: Some Card Name'.
        """
        if not (0 <= idx < len(self.cards)):
            return f"{idx:04d}"
        name = self.cards[idx].name.replace("\n", " ")
        if len(name) > 30:
            name = name[:30] + "..."
        return f"{idx:04d}: {name}"

    def _update_card_id_choices(self):
        """
        Populate the card ID dropdown with 'index: name' for all cards.
        """
        self.card_id_choices = [self._card_id_display_for_index(i) for i in range(len(self.cards))]
        self.card_id_combo["values"] = self.card_id_choices

    def _set_card_id_ui_from_index(self, index_val):
        """
        Set the Card ID combobox display from an integer index.
        """
        display = self._card_id_display_for_index(index_val)
        self.card_id_var.set(display)

    def _get_card_id_index_from_ui(self):
        """
        Parse the integer card ID index from the combobox string (e.g. '0005:...').
        """
        val = self.card_id_var.get()
        if not val:
            return 0
        # Expect 'NNNN: ...'
        part = val.split(":", 1)[0].strip()
        try:
            return int(part)
        except ValueError:
            return 0

    # =========================
    # UI – CARD LIST & EDITOR
    # =========================

    def _populate_card_list(self, filter_text=""):
        """
        Populate the listbox with card names, optionally filtered
        by a substring (case-insensitive).
        """
        filter_text = filter_text.lower()
        self.card_listbox.delete(0, tk.END)
        self.filtered_indices = []

        for i, card in enumerate(self.cards):
            if filter_text and filter_text not in card.name.lower():
                continue
            self.filtered_indices.append(i)

        for card_index in self.filtered_indices:
            card = self.cards[card_index]
            display_name = card.name.replace("\n", " ")
            if len(display_name) > 30:
                display_name = display_name[:30] + "..."
            self.card_listbox.insert(tk.END, f"{card.index:04d}: {display_name}")

        # Restore selection if possible
        if self.current_index is not None and self.current_index in self.filtered_indices:
            row = self.filtered_indices.index(self.current_index)
            self.card_listbox.selection_set(row)
            self.card_listbox.see(row)

    def _load_card_into_editor(self, index):
        if not (0 <= index < len(self.cards)):
            return

        card = self.cards[index]
        self.current_index = index

        self.info_label.config(
            text=f"Card #{card.index}   |   Name addr: {hex(card.name_addr)}   "
                 f"Desc addr: {hex(card.desc_addr)}"
        )

        # Text fields
        self.name_var.set(card.name)
        self.desc_text.delete("1.0", tk.END)
        self.desc_text.insert("1.0", card.desc)

        # Stats fields
        self._updating_konami = True
        self.konami_id_var.set(card.konami_id)
        self._updating_konami = False

        self._set_card_id_ui_from_index(card.card_id_index)

        self.artwork_id_var.set(card.artwork_id)
        self.edited_flag_var.set(card.edited_flag)
        self.atk_var.set(card.atk)
        self.def_var.set(card.deff)
        self.level_var.set(card.level)
        self.race_var.set(card.race)
        self.attribute_var.set(card.attribute)
        self.type_var.set(card.type_)
        self.st_race_var.set(card.st_race)
        self.padding_var.set(card.padding)

        # Update combobox selections if lists exist
        def set_combo_from_index(combo, index_val, values_list):
            if combo is None:
                return
            if 0 <= index_val < len(values_list):
                combo.current(index_val)
            else:
                combo.set(str(index_val))

        set_combo_from_index(self.race_combo, card.race, self.races_list)
        set_combo_from_index(self.attribute_combo, card.attribute, self.attributes_list)
        set_combo_from_index(self.type_combo, card.type_, self.types_list)
        set_combo_from_index(self.st_race_combo, card.st_race, self.st_races_list)

        # Update listbox selection with respect to current filter
        if self.filtered_indices:
            try:
                row = self.filtered_indices.index(index)
            except ValueError:
                self.card_listbox.selection_clear(0, tk.END)
            else:
                self.card_listbox.selection_clear(0, tk.END)
                self.card_listbox.selection_set(row)
                self.card_listbox.see(row)
        else:
            self.card_listbox.selection_clear(0, tk.END)
            if index < self.card_listbox.size():
                self.card_listbox.selection_set(index)
                self.card_listbox.see(index)

    def on_card_selected(self, event):
        if not self.cards or not self.filtered_indices:
            return
        # Save current card edits before switching
        self.apply_changes()
        sel = self.card_listbox.curselection()
        if not sel:
            return
        row = sel[0]
        card_index = self.filtered_indices[row]
        self._load_card_into_editor(card_index)

    def apply_changes(self):
        """
        Save the text and stats from the UI into the current CardEntry object.
        (Does NOT write to ROM yet.)
        """
        if self.current_index is None or not self.cards:
            return
        card = self.cards[self.current_index]

        # Text
        card.name = self.name_var.get()
        card.desc = self.desc_text.get("1.0", tk.END).rstrip("\n")

        # Stats - safe parsing helpers for combobox-backed fields
        def get_index_from_combo(combo, values_list, numeric_var):
            if combo is None:
                return numeric_var.get()
            val = combo.get()
            if not values_list:
                try:
                    return int(val)
                except ValueError:
                    return numeric_var.get()
            if val in values_list:
                return values_list.index(val)
            try:
                return int(val)
            except ValueError:
                return numeric_var.get()

        card.konami_id = self.konami_id_var.get()
        card.card_id_index = self._get_card_id_index_from_ui()
        card.artwork_id = self.artwork_id_var.get()
        card.edited_flag = self.edited_flag_var.get()
        card.atk = self.atk_var.get()
        card.deff = self.def_var.get()
        card.level = self.level_var.get()
        card.race = get_index_from_combo(self.race_combo, self.races_list, self.race_var)
        card.attribute = get_index_from_combo(self.attribute_combo, self.attributes_list, self.attribute_var)
        card.type_ = get_index_from_combo(self.type_combo, self.types_list, self.type_var)
        card.st_race = get_index_from_combo(self.st_race_combo, self.st_races_list, self.st_race_var)
        # padding: left as-is (from ROM)

    def prev_card(self):
        if self.current_index is None:
            return
        if self.current_index > 0:
            self.apply_changes()
            self._load_card_into_editor(self.current_index - 1)

    def next_card(self):
        if self.current_index is None:
            return
        if self.current_index < len(self.cards) - 1:
            self.apply_changes()
            self._load_card_into_editor(self.current_index + 1)

    def _update_controls_state(self):
        state = tk.NORMAL if self.cards else tk.DISABLED
        self.prev_btn.config(state=state)
        self.next_btn.config(state=state)
        self.apply_btn.config(state=state)
        if not self.cards:
            self.name_entry.config(state=tk.DISABLED)
            self.desc_text.config(state=tk.DISABLED)
        else:
            self.name_entry.config(state=tk.NORMAL)
            self.desc_text.config(state=tk.NORMAL)

    # =========================
    # SEARCH FILTER ACTIONS
    # =========================

    def apply_filter(self):
        text = self.search_var.get().strip()
        self._populate_card_list(text)

    def clear_filter(self):
        self.search_var.set("")
        self._populate_card_list("")

    # =========================
    # KONAMI ID CHANGE HANDLER
    # =========================

    def _on_konami_id_changed(self, *args):
        """
        When Konami ID is changed in the UI, automatically update Card ID
        from the ROM card ID table for that Konami ID.
        """
        if self._updating_konami:
            return
        if self.rom_data is None:
            return
        if self.current_index is None or not self.cards:
            return

        try:
            konami = self.konami_id_var.get()
        except tk.TclError:
            return

        # Read mapping from original ROM card ID table
        card_id_index = self._read_card_id_index_from_table(self.rom_data, konami)
        self._set_card_id_ui_from_index(card_id_index)

        # Update current CardEntry's in-memory mapping too
        card = self.cards[self.current_index]
        card.konami_id = konami
        card.card_id_index = card_id_index


if __name__ == "__main__":
    app = RomEditorApp()
    app.mainloop()
