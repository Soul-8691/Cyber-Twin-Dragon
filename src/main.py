import tkinter as tk
from tkinter import filedialog, messagebox
from tkinter.scrolledtext import ScrolledText
import os

# =========================
# CONSTANTS FOR THIS ROM
# =========================

# Pointer tables
CARD_NAME_PTR_BASE = 0x15BB594
CARD_DESC_PTR_BASE = 0x15BD65C

# Text section base and limit
TEXT_BASE = 0x15BF724
TEXT_LIMIT = 0x162248A  # exclusive upper bound for searching free space

# Number of entries in each table:
#   (0x15BD65C - 0x15BB594) / 4 = 2098
NUM_CARDS = 2098


class CardEntry:
    def __init__(self, index,
                 name, desc,
                 name_ptr_off, desc_ptr_off,
                 name_addr, desc_addr,
                 name_len, desc_len):
        self.index = index

        # CURRENT strings (edited in UI)
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


class RomEditorApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Yu-Gi-Oh! UM 2006 – Card Name/Description Editor")

        self.rom_path = None
        self.rom_data = None  # bytearray
        self.cards = []       # list[CardEntry]
        self.current_index = None  # selected card index in self.cards
        self.filtered_indices = []  # mapping listbox row -> card index

        self._build_ui()

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
        self.desc_text = ScrolledText(desc_frame, height=10, wrap=tk.WORD)
        self.desc_text.pack(fill=tk.BOTH, expand=True)

        # Navigation / update buttons
        button_frame = tk.Frame(right_frame)
        button_frame.pack(fill=tk.X, pady=5)

        self.prev_btn = tk.Button(button_frame, text="<< Previous", command=self.prev_card, state=tk.DISABLED)
        self.prev_btn.pack(side=tk.LEFT)

        self.next_btn = tk.Button(button_frame, text="Next >>", command=self.next_card, state=tk.DISABLED)
        self.next_btn.pack(side=tk.LEFT, padx=(5, 0))

        self.apply_btn = tk.Button(button_frame, text="Apply Changes (in memory)", command=self.apply_changes, state=tk.DISABLED)
        self.apply_btn.pack(side=tk.RIGHT)

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

            card = CardEntry(
                index=i,
                name=name_str,
                desc=desc_str,
                name_ptr_off=name_ptr_off,
                desc_ptr_off=desc_ptr_off,
                name_addr=name_addr,
                desc_addr=desc_addr,
                name_len=name_len,
                desc_len=desc_len
            )
            cards.append(card)

        return cards

    def _read_c_string(self, data, addr):
        """
        Read ASCII string from data starting at absolute address 'addr' until 0x00
        or until TEXT_LIMIT. Returns (string, length_without_terminator).
        """
        if addr < 0 or addr >= len(data):
            raise ValueError(f"String address {hex(addr)} out of range.")

        # Ensure we don't read past TEXT_LIMIT or end of file
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

    # =========================
    # FREE SPACE SEARCH & WRITE
    # =========================

    def _find_free_space(self, rom_data, size):
        """
        Find a sequence of 'size' zero bytes between TEXT_BASE and TEXT_LIMIT.
        Returns absolute address or None.
        NOTE: We return run_start + 1 so we don't overwrite the very first 00.
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
                    # your requested fix: skip the first 00 byte in the run
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

        # encode ASCII; replace non-ASCII just in case
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

            # Update card's address and slot size in memory, and pointer in ROM
            if is_name:
                # Zero out the old slot (replace original text with 00 bytes)
                if 0 <= orig_addr < len(rom_data):
                    for offset in range(orig_addr, min(orig_addr + slot_size, len(rom_data))):
                        rom_data[offset] = 0

                card.name_addr = write_addr
                card.name_slot_size = needed
            else:
                if 0 <= orig_addr < len(rom_data):
                    for offset in range(orig_addr, min(orig_addr + slot_size, len(rom_data))):
                        rom_data[offset] = 0

                card.desc_addr = write_addr
                card.desc_slot_size = needed

            rel = write_addr - TEXT_BASE
            if rel < 0 or rel > 0xFFFFFFFF:
                raise RuntimeError("Relative pointer out of 32-bit range.")

            rom_data[ptr_off:ptr_off + 4] = rel.to_bytes(4, "little")

        # Actually write the new string (either in old slot or newly allocated free space)
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

    def _apply_all_changes_to_rom(self, rom_copy):
        """
        Apply all cards' name/desc changes to rom_copy.
        """
        for card in self.cards:
            self._write_string_and_update_pointer(rom_copy, card, is_name=True)
            self._write_string_and_update_pointer(rom_copy, card, is_name=False)

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

        self.name_var.set(card.name)
        self.desc_text.delete("1.0", tk.END)
        self.desc_text.insert("1.0", card.desc)

        # Update listbox selection with respect to current filter
        if self.filtered_indices:
            try:
                row = self.filtered_indices.index(index)
            except ValueError:
                # card not in filtered set
                self.card_listbox.selection_clear(0, tk.END)
            else:
                self.card_listbox.selection_clear(0, tk.END)
                self.card_listbox.selection_set(row)
                self.card_listbox.see(row)
        else:
            # no filter; should not really happen if we always maintain filtered_indices
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
        Save the text from the UI into the current CardEntry object.
        (Does NOT write to ROM yet.)
        """
        if self.current_index is None or not self.cards:
            return
        card = self.cards[self.current_index]
        card.name = self.name_var.get()
        card.desc = self.desc_text.get("1.0", tk.END).rstrip("\n")

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


if __name__ == "__main__":
    app = RomEditorApp()
    app.mainloop()
