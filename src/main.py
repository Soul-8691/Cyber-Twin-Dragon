import tkinter as tk
from tkinter import filedialog, messagebox
from tkinter.scrolledtext import ScrolledText
from tkinter import ttk
import os
import json
from PIL import Image, ImageTk
import subprocess
import tempfile
import traceback

# =========================
# CONSTANTS FOR THIS ROM
# =========================

# Pointer tables for card text
CARD_NAME_PTR_BASE = 0x15BB594
CARD_DESC_PTR_BASE = 0x15BD65C

# Text section base and limit
TEXT_BASE = 0x15BF724
TEXT_LIMIT = 0x162248A  # exclusive upper bound for searching free space

# Primary card stats table
CARD_STATS_BASE = 0x18169B8
CARD_STATS_SIZE = 0x16  # 0x16 bytes per card

# Secondary card stats table
SECOND_CARD_STATS_BASE = 0x1821E04
SECOND_CARD_STATS_SIZE = 0x16
SECOND_STATS_COUNT = 2648  # you specified this

# Card ID table (Konami ID -> card name index or 0xFFFF)
CARD_ID_TABLE_BASE = 0x15B7CCC
KONAMI_ID_BASE = 4007  # Konami ID offset

# Number of card name entries
NUM_CARDS = 2098

# Card artwork table
ARTWORK_TABLE_BASE = 0x15B5C00

# Card name alphabetical sort table
NAME_SORT_TABLE_BASE = 0x1832606  # 2 bytes per entry, little endian

NAME_SORT_EXCLUDE_START = 2080  # 0-indexed, inclusive
NAME_SORT_EXCLUDE_END = 2097    # 0-indexed, inclusive

# =========================
# CARD ART CONSTANTS
# =========================

CARD_GFX_BASE = 0x510640       # start of 6bpp card graphics
CARD_GFX_SIZE = 0x12C0         # bytes per card graphic (80x80 @ 6bpp -> 4800 bytes)
CARD_PAL_BASE = 0x4C76C0       # start of card palettes
CARD_PAL_SIZE = 0x80           # bytes per card palette (64 colors * 2 bytes)
NUM_CARD_GFX = 2331            # total graphics slots

# Path to gbagfx executable (adjust to where you keep it)
GBAGFX_PATH = "deps/gbagfx"

class ArtworkEntry:
    def __init__(self, index, unk_halfword, card_name_index):
        self.index = index                 # artwork slot index (0..2330)
        self.unk_halfword = unk_halfword   # first 2 bytes, unknown but editable
        self.card_name_index = card_name_index  # second 2 bytes: index into card names table

class CardEntry:
    def __init__(
        self, index,
        name, desc,
        name_ptr_off, desc_ptr_off,
        name_addr, desc_addr,
        name_len, desc_len,
        konami_id, card_id_index,
        artwork_id, edited_flag,
        atk, deff, level,
        race, attribute, type_, st_race, padding
    ):
        self.index = index

        # Text
        self.name = name
        self.desc = desc
        self.name_ptr_off = name_ptr_off
        self.desc_ptr_off = desc_ptr_off
        self.name_addr = name_addr
        self.desc_addr = desc_addr
        self.name_slot_size = name_len + 1
        self.desc_slot_size = desc_len + 1

        # Primary stats
        self.konami_id = konami_id
        self.card_id_index = card_id_index  # card name index or 0xFFFF
        self.artwork_id = artwork_id
        self.edited_flag = edited_flag
        self.atk = atk
        self.deff = deff
        self.level = level
        self.race = race
        self.attribute = attribute
        self.type_ = type_
        self.st_race = st_race
        self.padding = padding

        # Secondary stats (filled later from second table)
        self.second_stats_index = -1  # which row in the 2648-entry second table we came from
        self.konami2 = 0
        self.card_id_index2 = 0xFFFF  # card name index or 0xFFFF (default: none)
        self.artwork2 = 0
        self.edited_flag2 = 0
        self.atk2 = 0
        self.deff2 = 0
        self.level2 = 0
        self.race2 = 0
        self.attribute2 = 0
        self.type2 = 0
        self.st_race2 = 0
        self.padding2 = 0


class RomEditorApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Yu-Gi-Oh! UM 2006 – Card Editor")

        self.rom_path = None
        self.rom_data = None
        self.cards = []
        self.current_index = None
        self.filtered_indices = []

        # Lookup text lists
        self.races_list = []
        self.attributes_list = []
        self.types_list = []
        self.st_races_list = []

        # Card ID dropdown choices ("0000: Name")
        self.card_id_choices = []

        # YGOPRODeck Konami ID -> name
        self.konami_name_map = {}

        # Trace guards
        self._updating_konami_main = False
        self._updating_konami_sec = False

        self.artworks = []                 # list[ArtworkEntry]
        self.current_artwork_index = 0
        self._updating_artwork_index = False

        self.artwork_names = []

        self._load_text_mappings()
        self._load_json_mappings()
        self._build_ui()

    def _write_name_sort_table(self, rom_data):
        """
        Build an alphabetical index of card names based on the ASCII
        names currently in memory, and write it to the sort table at
        NAME_SORT_TABLE_BASE.

        Rules (per user spec):
          - Use card.name (ASCII text) for comparison.
          - Exclude card indices 2081–2097 (0-indexed).
          - If two names are the same, they get the same number.
          - Numbers do NOT have to count up to 2081.
          - We write (alphabetical_index + 1) because index 0 is unused.

        We write values in card index order, i.e., entry for card i
        goes to NAME_SORT_TABLE_BASE + i*2, for all i NOT in the excluded
        range. Excluded indices are left unchanged in the ROM.
        """
        if not self.cards:
            return

        # 1) Build list of (name, index) for the included cards
        included = []
        for i, card in enumerate(self.cards[1:]):
            if NAME_SORT_EXCLUDE_START <= i <= NAME_SORT_EXCLUDE_END:
                continue  # skip these
            included.append((card.name, i))

        if not included:
            return

        # 2) Sort by ASCII name
        included.sort(key=lambda x: x[0])

        # 3) Assign an alphabetical rank to each unique name
        #    same name => same rank
        name_to_rank = {}
        rank = 0
        last_name = None

        for name, _idx in included:
            if name != last_name:
                # new unique name -> new rank
                name_to_rank[name] = rank
                rank += 1
                last_name = name
            # if name == last_name, it reuses the same rank

        # 4) For each card index (0..len(self.cards)-1),
        #    write its alphabetical index+1 at NAME_SORT_TABLE_BASE + i*2
        for i, card in enumerate(self.cards[1:]):
            # Skip excluded range entirely, leave whatever is currently in the ROM
            if NAME_SORT_EXCLUDE_START <= i <= NAME_SORT_EXCLUDE_END:
                continue

            name = card.name
            # Should always be present, but fall back to 0 if something is odd
            rank = name_to_rank.get(name, 0)
            sort_value = rank + 1  # 1-based, since 0 is unused

            off = NAME_SORT_TABLE_BASE + i * 2
            if off + 2 > len(rom_data):
                break

            self._write_u16(rom_data, off, sort_value)

    def _parse_artworks(self):
        data = self.rom_data
        artworks = []
        for i in range(NUM_CARDS):
            off = ARTWORK_TABLE_BASE + i * 4
            if off + 4 > len(data):
                break
            unk = self._read_u16(data, off)

            stored = self._read_u16(data, off + 2)
            # Artwork table stores (card_name_index - 1)
            if stored == 0xFFFF:
                card_idx = 0xFFFF  # optional sentinel handling, if ever used
            else:
                card_idx = stored + 1

            artworks.append(ArtworkEntry(i, unk, card_idx))
        self.artworks = artworks

    def _decode_6bpp_to_8bpp(self, data_6bpp: bytes) -> bytes:
        """
        Convert 80x80 6bpp data (4800 bytes) into 80x80 8bpp (6400 bytes).

        We treat every 3 bytes as a little-endian 24-bit integer:
        v = a | (b << 8) | (c << 16)

        Then extract 4 successive 6-bit indices:
        p0 = bits  0..5
        p1 = bits  6..11
        p2 = bits 12..17
        p3 = bits 18..23

        Each 6-bit value (0..63) is stored in a full byte so gbagfx
        can treat it as 8bpp indexed data.
        """
        if len(data_6bpp) != CARD_GFX_SIZE:
            raise ValueError(f"Expected {CARD_GFX_SIZE} bytes of 6bpp data, got {len(data_6bpp)}")

        out = bytearray()

        for i in range(0, len(data_6bpp), 3):
            a = data_6bpp[i]
            b = data_6bpp[i + 1]
            c = data_6bpp[i + 2]

            v = a | (b << 8) | (c << 16)

            out.append((v >> 0)  & 0x3F)
            out.append((v >> 6)  & 0x3F)
            out.append((v >> 12) & 0x3F)
            out.append((v >> 18) & 0x3F)

        if len(out) != 80 * 80:
            raise ValueError(f"Decoded 6bpp length mismatch: {len(out)} pixels")

        return bytes(out)

    def _render_card_image(self, card: CardEntry):
        """
        Extracts this card's 6bpp art and palette from the ROM,
        converts to 8bpp, runs gbagfx to make a PNG, horizontally
        flips it with Pillow, and displays it in the Tkinter label.
        """
        if self.rom_data is None:
            self.card_image_label.config(image="", text="(no ROM)")
            self.card_photo = None
            return

        gfx_index = self._get_graphics_index_for_card(card)
        if gfx_index is None:
            self.card_image_label.config(image="", text="(no art)")
            self.card_photo = None
            return

        # --- Compute ROM offsets for this graphic + palette ---
        gfx_off = CARD_GFX_BASE + gfx_index * CARD_GFX_SIZE
        pal_off = CARD_PAL_BASE + gfx_index * CARD_PAL_SIZE

        if gfx_off + CARD_GFX_SIZE > len(self.rom_data) or pal_off + CARD_PAL_SIZE > len(self.rom_data):
            self.card_image_label.config(image="", text="(art out of range)")
            self.card_photo = None
            return

        data_6bpp = bytes(self.rom_data[gfx_off:gfx_off + CARD_GFX_SIZE])
        pal_raw  = bytes(self.rom_data[pal_off:pal_off + CARD_PAL_SIZE])

        # --- Convert 6bpp → 8bpp ---
        data_8bpp = self._decode_6bpp_to_8bpp(data_6bpp)

        # --- Prepare temp files for gbagfx ---
        with tempfile.TemporaryDirectory() as tmpdir:
            gfx_path = os.path.join(tmpdir, "card.8bpp")
            pal_path = os.path.join(tmpdir, "card.gbapal")
            png_path = os.path.join(tmpdir, "card.png")

            # Write 6400 bytes of 8bpp index data
            with open(gfx_path, "wb") as f:
                f.write(data_8bpp)

            # gbagfx expects a 256-color palette (0x200 bytes) for 8bpp;
            # we have 64 entries (0x80 bytes), so just pad with zeros.
            pal_data = pal_raw + b"\x00" * (0x200 - len(pal_raw))
            with open(pal_path, "wb") as f:
                f.write(pal_data)

            # --- Call gbagfx to build the PNG ---
            # Adjust flags if your gbagfx version uses different syntax.
            cmd = [
                GBAGFX_PATH,
                gfx_path,
                png_path,
                "-palette", pal_path,
                "-mwidth", "10",
            ]

            try:
                subprocess.run(cmd, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            except Exception as e:
                traceback.print_exc()
                self.card_photo = None
                return

            # --- Open PNG, flip horizontally, and show in Tkinter ---
            try:
                img = Image.open(png_path)
                self.card_photo = ImageTk.PhotoImage(img)
                self.card_image_label.config(image=self.card_photo, text="")
            except Exception:
                self.card_image_label.config(image="", text="(image load error)")
                self.card_photo = None

    def _get_graphics_index_for_card(self, card: CardEntry):
        """
        Returns the 0-based graphics index to use for this card:
        - Use the artwork slot (Artwork #) just to pick the row
        - Then use that row's second halfword ("Card (Name Index)")
            as the actual graphics/palette index.
        """
        if self.rom_data is None:
            return None

        # Which artwork slot are we using? (primary here, adjust if you prefer secondary)
        slot = card.card_id_index
        if slot < 0:
            return None

        # Second halfword of artwork entry = Card (Name Index) (0-based)
        off = ARTWORK_TABLE_BASE + slot * 4 + 2
        if off + 2 > len(self.rom_data):
            return None

        gfx_index = self._read_u16(self.rom_data, off)  # 0..2330
        if not (0 <= gfx_index < NUM_CARD_GFX):
            return None

        return gfx_index

    # =========================
    # LOAD TEXT / JSON MAPPINGS
    # =========================

    def _load_text_mappings(self):
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

        # NEW: artwork names (one per line, 2331 total)
        self.artwork_names = load_lines(os.path.join("..", "text", "card_graphics_indexes.txt"))

    def _load_json_mappings(self):
        try:
            base_dir = os.path.dirname(os.path.abspath(__file__))
        except Exception:
            base_dir = os.getcwd()

        json_path = os.path.join(base_dir, "..", "json", "ygoprodeck_card_info.json")
        if not os.path.isfile(json_path):
            self.konami_name_map = {}
            return

        try:
            with open(json_path, "r", encoding="utf-8", errors="ignore") as f:
                data = json.load(f)
        except Exception:
            self.konami_name_map = {}
            return

        mapping = {}
        if isinstance(data, dict) and "data" in data and isinstance(data["data"], list):
            for card_info in data["data"]:
                try:
                    misc = card_info.get("misc_info")
                    if not misc or not isinstance(misc, list):
                        continue
                    konami_id = misc[0].get("konami_id")
                    name = card_info.get("name")
                    if isinstance(konami_id, int) and isinstance(name, str):
                        mapping[konami_id] = name
                except Exception:
                    continue
        self.konami_name_map = mapping

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

        # Main layout
        main_frame = tk.Frame(self)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        # Left: list + search
        left_frame = tk.Frame(main_frame)
        left_frame.pack(side=tk.LEFT, fill=tk.Y)

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

        # Right: editor
        right_frame = tk.Frame(main_frame)
        right_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)

        self.info_label = tk.Label(right_frame, text="No ROM loaded.")
        self.info_label.pack(anchor="w", pady=(0, 5))

        self.info_label = tk.Label(right_frame, text="No ROM loaded.")
        self.info_label.pack(anchor="w", pady=(0, 5))

        # --- Card artwork preview ---
        image_frame = tk.Frame(right_frame)
        image_frame.pack(anchor="center", pady=(0, 5))
        self.card_image_label = tk.Label(image_frame, text="(no art)")
        self.card_image_label.pack()
        self.card_photo = None  # keep reference to avoid GC

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

        # Stats notebook
        stats_notebook = ttk.Notebook(right_frame)
        stats_notebook.pack(fill=tk.X, pady=(5, 0))

        stats_main_frame = tk.Frame(stats_notebook)
        stats_sec_frame = tk.Frame(stats_notebook)
        artwork_frame = tk.Frame(stats_notebook)

        stats_notebook.add(stats_main_frame, text="Main Stats")
        stats_notebook.add(stats_sec_frame, text="Secondary Stats")
        stats_notebook.add(artwork_frame, text="Artwork Table")

        # MAIN stats vars
        self.konami_main_var = tk.IntVar()
        self.card_id_main_var = tk.StringVar()
        self.artwork_main_var = tk.IntVar()
        self.edited_main_var = tk.IntVar()
        self.atk_main_var = tk.IntVar()
        self.def_main_var = tk.IntVar()
        self.level_main_var = tk.IntVar()
        self.race_main_var = tk.IntVar()
        self.attribute_main_var = tk.IntVar()
        self.type_main_var = tk.IntVar()
        self.st_race_main_var = tk.IntVar()
        self.padding_main_var = tk.IntVar()

        # SECONDARY stats vars
        self.konami_sec_var = tk.IntVar()
        self.card_id_sec_var = tk.StringVar()
        self.artwork_sec_var = tk.IntVar()
        self.edited_sec_var = tk.IntVar()
        self.atk_sec_var = tk.IntVar()
        self.def_sec_var = tk.IntVar()
        self.level_sec_var = tk.IntVar()
        self.race_sec_var = tk.IntVar()
        self.attribute_sec_var = tk.IntVar()
        self.type_sec_var = tk.IntVar()
        self.st_race_sec_var = tk.IntVar()
        self.padding_sec_var = tk.IntVar()

        # Artwork table vars
        self.artwork_index_var = tk.IntVar(value=0)
        self.artwork_unk_var = tk.StringVar()
        self.artwork_card_var = tk.StringVar()
        self.artwork_name_var = tk.StringVar()  # resolved artwork name from card_graphics_indexes.txt

        def add_numeric_row(frame, row, label, var, width=8):
            tk.Label(frame, text=label).grid(row=row, column=0, sticky="w", padx=2, pady=1)
            entry = tk.Entry(frame, textvariable=var, width=width)
            entry.grid(row=row, column=1, sticky="w", padx=2, pady=1)
            return entry

        def add_combo_row(frame, row, label, values_list, numeric_var):
            tk.Label(frame, text=label).grid(row=row, column=0, sticky="w", padx=2, pady=1)
            container = tk.Frame(frame)
            container.grid(row=row, column=1, sticky="w", padx=2, pady=1)
            combo = None
            if values_list:
                combo = ttk.Combobox(container, values=values_list, state="readonly", width=20)
                combo.pack(side=tk.LEFT)
            else:
                entry = tk.Entry(container, textvariable=numeric_var, width=8)
                entry.pack(side=tk.LEFT)
            return combo

        # MAIN stats UI
        row = 0
        self.konami_main_entry = add_numeric_row(stats_main_frame, row, "Konami ID:", self.konami_main_var); row += 1
        tk.Label(stats_main_frame, text="Card ID (Name Index):").grid(row=row, column=0, sticky="w", padx=2, pady=1)
        self.card_id_main_combo = ttk.Combobox(stats_main_frame, textvariable=self.card_id_main_var,
                                               state="readonly", width=30)
        self.card_id_main_combo.grid(row=row, column=1, sticky="w", padx=2, pady=1)
        row += 1
        self.artwork_main_entry = add_numeric_row(stats_main_frame, row, "Artwork #:", self.artwork_main_var); row += 1
        self.edited_main_entry = add_numeric_row(stats_main_frame, row, "Edited Art Flag:", self.edited_main_var); row += 1
        self.atk_main_entry = add_numeric_row(stats_main_frame, row, "ATK:", self.atk_main_var); row += 1
        self.def_main_entry = add_numeric_row(stats_main_frame, row, "DEF:", self.def_main_var); row += 1
        self.level_main_entry = add_numeric_row(stats_main_frame, row, "Level:", self.level_main_var); row += 1
        self.race_main_combo = add_combo_row(stats_main_frame, row, "Race:", self.races_list, self.race_main_var); row += 1
        self.attribute_main_combo = add_combo_row(stats_main_frame, row, "Attribute:", self.attributes_list, self.attribute_main_var); row += 1
        self.type_main_combo = add_combo_row(stats_main_frame, row, "Type:", self.types_list, self.type_main_var); row += 1
        self.st_race_main_combo = add_combo_row(stats_main_frame, row, "Spell/Trap Race:", self.st_races_list, self.st_race_main_var); row += 1
        tk.Label(stats_main_frame, text="Padding (raw):").grid(row=row, column=0, sticky="w", padx=2, pady=1)
        self.padding_main_entry = tk.Entry(stats_main_frame, textvariable=self.padding_main_var,
                                           width=8, state="disabled")
        self.padding_main_entry.grid(row=row, column=1, sticky="w", padx=2, pady=1)
        row += 1

        # SECONDARY stats UI
        row = 0
        self.konami_sec_entry = add_numeric_row(stats_sec_frame, row, "Konami ID:", self.konami_sec_var); row += 1
        tk.Label(stats_sec_frame, text="Card ID (Name Index):").grid(row=row, column=0, sticky="w", padx=2, pady=1)
        self.card_id_sec_combo = ttk.Combobox(stats_sec_frame, textvariable=self.card_id_sec_var,
                                              state="readonly", width=30)
        self.card_id_sec_combo.grid(row=row, column=1, sticky="w", padx=2, pady=1)
        row += 1
        self.artwork_sec_entry = add_numeric_row(stats_sec_frame, row, "Artwork #:", self.artwork_sec_var); row += 1
        self.edited_sec_entry = add_numeric_row(stats_sec_frame, row, "Edited Art Flag:", self.edited_sec_var); row += 1
        self.atk_sec_entry = add_numeric_row(stats_sec_frame, row, "ATK:", self.atk_sec_var); row += 1
        self.def_sec_entry = add_numeric_row(stats_sec_frame, row, "DEF:", self.def_sec_var); row += 1
        self.level_sec_entry = add_numeric_row(stats_sec_frame, row, "Level:", self.level_sec_var); row += 1
        self.race_sec_combo = add_combo_row(stats_sec_frame, row, "Race:", self.races_list, self.race_sec_var); row += 1
        self.attribute_sec_combo = add_combo_row(stats_sec_frame, row, "Attribute:", self.attributes_list, self.attribute_sec_var); row += 1
        self.type_sec_combo = add_combo_row(stats_sec_frame, row, "Type:", self.types_list, self.type_sec_var); row += 1
        self.st_race_sec_combo = add_combo_row(stats_sec_frame, row, "Spell/Trap Race:", self.st_races_list, self.st_race_sec_var); row += 1
        tk.Label(stats_sec_frame, text="Padding (raw):").grid(row=row, column=0, sticky="w", padx=2, pady=1)
        self.padding_sec_entry = tk.Entry(stats_sec_frame, textvariable=self.padding_sec_var,
                                          width=8, state="disabled")
        self.padding_sec_entry.grid(row=row, column=1, sticky="w", padx=2, pady=1)
        row += 1

        # ---------- Artwork Table UI ----------
        row = 0
        tk.Label(artwork_frame, text="Unknown halfword:").grid(row=row, column=0, sticky="w", padx=2, pady=1)
        self.artwork_unk_combo = ttk.Combobox(
            artwork_frame,
            textvariable=self.artwork_unk_var,
            values=self.artwork_names,
            state="readonly",
            width=40
        )
        self.artwork_unk_combo.grid(row=row, column=1, sticky="w", padx=2, pady=1)
        row += 1

        tk.Label(artwork_frame, text="Card (Name Index):").grid(row=row, column=0, sticky="w", padx=2, pady=1)
        self.artwork_card_combo = ttk.Combobox(
            artwork_frame,
            textvariable=self.artwork_card_var,
            values=self.artwork_names,
            state="readonly",
            width=40
        )
        self.artwork_card_combo.grid(row=row, column=1, sticky="w", padx=2, pady=1)
        row += 1

        # Load/import art for the currently selected artwork entry
        self.load_gfx_button = tk.Button(
            artwork_frame,
            text="Load Card Graphics...",
            command=self.load_card_graphics,
            state=tk.DISABLED  # enabled once a ROM is loaded
        )
        self.load_gfx_button.grid(row=row, column=0, columnspan=2, pady=(5, 0), sticky="w")
        row += 1

        # Buttons
        button_frame = tk.Frame(right_frame)
        button_frame.pack(fill=tk.X, pady=5)
        self.prev_btn = tk.Button(button_frame, text="<< Previous", command=self.prev_card, state=tk.DISABLED)
        self.prev_btn.pack(side=tk.LEFT)
        self.next_btn = tk.Button(button_frame, text="Next >>", command=self.next_card, state=tk.DISABLED)
        self.next_btn.pack(side=tk.LEFT, padx=(5, 0))
        self.apply_btn = tk.Button(button_frame, text="Apply Changes (in memory)",
                                   command=self.apply_changes, state=tk.DISABLED)
        self.apply_btn.pack(side=tk.RIGHT)

        # Traces
        self.konami_main_var.trace_add("write", self._on_konami_main_changed)
        self.konami_sec_var.trace_add("write", self._on_konami_sec_changed)

    # =========================
    # ROM HANDLING
    # =========================

    def open_rom(self):
        path = filedialog.askopenfilename(
            title="Select Yu-Gi-Oh! Ultimate Masters GBA ROM",
            filetypes=[("GBA ROM", "*.gba"), ("All files", "*.*")]
        )
        if not path:
            return
        try:
            with open(path, "rb") as f:
                data = f.read()
        except Exception as e:
            messagebox.showerror("Error", f"Failed to open ROM:\n{e}")
            return

        self.rom_data = bytearray(data)
        self.rom_path = path

        try:
            self.cards = self._parse_cards()
            self._parse_artworks()
        except Exception as e:
            messagebox.showerror("Error", f"Failed to parse ROM:\n{e}")
            self.rom_data = None
            self.cards = []
            return

        self._update_card_id_choices()
        self.current_index = 0
        self.clear_filter()
        self._load_card_into_editor(0)
        if self.artworks:
            self._load_artwork_into_editor(0)
        self._update_controls_state()
        self.info_label.config(text=f"Loaded ROM: {os.path.basename(self.rom_path)} ({NUM_CARDS} cards)")

    def save_rom_as(self):
        if not self.rom_data or not self.cards:
            messagebox.showinfo("No ROM", "Load a ROM first.")
            return

        self.apply_changes()

        save_path = filedialog.asksaveasfilename(
            title="Save modified ROM as",
            defaultextension=".gba",
            filetypes=[("GBA ROM", "*.gba")]
        )
        if not save_path:
            return

        try:
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
        if addr < 0 or addr >= len(data):
            raise ValueError(f"String address {hex(addr)} out of range.")
        end_limit = min(TEXT_LIMIT, len(data))
        out = []
        pos = addr
        while pos < end_limit:
            b = data[pos]
            if b == 0:
                break
            out.append(b)
            pos += 1
        s = bytes(out).decode("ascii", errors="replace")
        return s, len(out)

    @staticmethod
    def _read_u16(data, offset):
        return int.from_bytes(data[offset:offset + 2], "little")

    @staticmethod
    def _write_u16(data, offset, value):
        data[offset:offset + 2] = int(value & 0xFFFF).to_bytes(2, "little")

    def _read_card_id_index_from_table(self, data, konami_id):
        """
        From Konami ID, read the card ID value (card name index or 0xFFFF)
        from card ID table.
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

        # First pass: names, descriptions, PRIMARY stats
        for i in range(NUM_CARDS):
            name_ptr_off = CARD_NAME_PTR_BASE + i * 4
            name_rel = int.from_bytes(data[name_ptr_off:name_ptr_off + 4], "little")
            name_addr = TEXT_BASE + name_rel
            name_str, name_len = self._read_c_string(data, name_addr)

            desc_ptr_off = CARD_DESC_PTR_BASE + i * 4
            desc_rel = int.from_bytes(data[desc_ptr_off:desc_ptr_off + 4], "little")
            desc_addr = TEXT_BASE + desc_rel
            desc_str, desc_len = self._read_c_string(data, desc_addr)

            stats_off = CARD_STATS_BASE + i * CARD_STATS_SIZE
            if stats_off + CARD_STATS_SIZE > len(data):
                raise ValueError(f"Primary stats for card {i} out of range.")

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

        # Second pass: SECONDARY stats (2648 entries)
        # Map by second-table index -> card ID table slot -> card name index.
        for sec_idx in range(SECOND_STATS_COUNT):
            stats2_off = SECOND_CARD_STATS_BASE + sec_idx * SECOND_CARD_STATS_SIZE
            if stats2_off + SECOND_CARD_STATS_SIZE > len(data):
                break

            konami2 = self._read_u16(data, stats2_off + 0x0)
            artwork2 = self._read_u16(data, stats2_off + 0x2)
            edited_flag2 = self._read_u16(data, stats2_off + 0x4)
            atk2 = self._read_u16(data, stats2_off + 0x6)
            deff2 = self._read_u16(data, stats2_off + 0x8)
            level2 = self._read_u16(data, stats2_off + 0xA)
            race2 = self._read_u16(data, stats2_off + 0xC)
            attribute2 = self._read_u16(data, stats2_off + 0xE)
            type2 = self._read_u16(data, stats2_off + 0x10)
            st_race2 = self._read_u16(data, stats2_off + 0x12)
            padding2 = self._read_u16(data, stats2_off + 0x14)

            # Use second table index as "card ID index - 4007".
            # So slot sec_idx in the card ID table gives us the card name index.
            card_name_index = self._read_u16(data, CARD_ID_TABLE_BASE + sec_idx * 2)

            if card_name_index == 0xFFFF:
                # "None" slot – doesn't map to an internal card name index.
                continue
            if not (0 <= card_name_index < NUM_CARDS):
                continue

            card = cards[card_name_index]
            # If multiple second entries would map to same card name index, keep the first.
            if card.second_stats_index != -1:
                continue

            card.second_stats_index = sec_idx
            card.konami2 = konami2
            # Derive the display card ID index from Konami2 at parse-time,
            # so the secondary Card ID label is correct immediately.
            konami_based_idx = self._read_card_id_index_from_table(data, konami2)
            card.card_id_index2 = konami_based_idx
            card.artwork2 = artwork2
            card.edited_flag2 = edited_flag2
            card.atk2 = atk2
            card.deff2 = deff2
            card.level2 = level2
            card.race2 = race2
            card.attribute2 = attribute2
            card.type2 = type2
            card.st_race2 = st_race2
            card.padding2 = padding2

        # Any card without second_stats_index keeps card_id_index2 as 0xFFFF (None)
        return cards

    # =========================
    # FREE SPACE / WRITE
    # =========================

    def _find_free_space(self, rom_data, size):
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
                    # Place the pointer at run_start + 1 per your request
                    return run_start + 1
            else:
                run_start = None
                run_length = 0
        return None

    def _write_string_and_update_pointer(self, rom_data, card, is_name):
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
        needed = len(encoded) + 1  # include 0 terminator

        if needed <= slot_size and 0 <= orig_addr < len(rom_data):
            write_addr = orig_addr
        else:
            write_addr = self._find_free_space(rom_data, needed)
            if write_addr is None:
                raise RuntimeError(
                    f"Not enough free space for {'name' if is_name else 'description'} "
                    f"of card {card.index} (need {needed} bytes)."
                )
            # Zero-out the new block
            for i in range(write_addr, write_addr + needed):
                if i < len(rom_data):
                    rom_data[i] = 0
            # Zero-out the old slot
            if 0 <= orig_addr < len(rom_data):
                for o in range(orig_addr, min(orig_addr + slot_size, len(rom_data))):
                    rom_data[o] = 0

            # Update card slot info & pointer
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

        if write_addr < 0 or write_addr + needed > len(rom_data):
            raise RuntimeError("Write address out of bounds.")

        rom_data[write_addr:write_addr + len(encoded)] = encoded
        if write_addr + len(encoded) < len(rom_data):
            rom_data[write_addr + len(encoded)] = 0
        else:
            raise RuntimeError("No space to write terminator byte.")

        # Clean remaining bytes in slot if shorter
        if write_addr == orig_addr and needed < slot_size:
            for o in range(write_addr + needed, write_addr + slot_size):
                if o < len(rom_data):
                    rom_data[o] = 0

    def _write_stats_primary(self, rom_data, card):
        off = CARD_STATS_BASE + card.index * CARD_STATS_SIZE
        if off + CARD_STATS_SIZE > len(rom_data):
            raise RuntimeError(f"Primary stats for card {card.index} out of range.")
        self._write_u16(rom_data, off + 0x0, card.konami_id)
        self._write_u16(rom_data, off + 0x2, card.artwork_id)
        self._write_u16(rom_data, off + 0x4, card.edited_flag)
        self._write_u16(rom_data, off + 0x6, card.atk)
        self._write_u16(rom_data, off + 0x8, card.deff)
        self._write_u16(rom_data, off + 0xA, card.level)
        self._write_u16(rom_data, off + 0xC, card.race)
        self._write_u16(rom_data, off + 0xE, card.attribute)
        self._write_u16(rom_data, off + 0x10, card.type_)
        self._write_u16(rom_data, off + 0x12, card.st_race)
        self._write_u16(rom_data, off + 0x14, card.padding)

    def _write_stats_secondary(self, rom_data, card):
        if card.second_stats_index < 0:
            return
        off = SECOND_CARD_STATS_BASE + card.second_stats_index * SECOND_CARD_STATS_SIZE
        if off + SECOND_CARD_STATS_SIZE > len(rom_data):
            return
        self._write_u16(rom_data, off + 0x0, card.konami2)
        self._write_u16(rom_data, off + 0x2, card.artwork2)
        self._write_u16(rom_data, off + 0x4, card.edited_flag2)
        self._write_u16(rom_data, off + 0x6, card.atk2)
        self._write_u16(rom_data, off + 0x8, card.deff2)
        self._write_u16(rom_data, off + 0xA, card.level2)
        self._write_u16(rom_data, off + 0xC, card.race2)
        self._write_u16(rom_data, off + 0xE, card.attribute2)
        self._write_u16(rom_data, off + 0x10, card.type2)
        self._write_u16(rom_data, off + 0x12, card.st_race2)
        self._write_u16(rom_data, off + 0x14, card.padding2)

    def _write_card_id_entry(self, rom_data, konami_id, card_id_index):
        """
        Write primary mapping: Konami ID -> card name index (card_id_index)
        into the card ID table.
        """
        if konami_id < KONAMI_ID_BASE:
            return
        pos = konami_id - KONAMI_ID_BASE
        offset = CARD_ID_TABLE_BASE + pos * 2
        if offset + 2 > len(rom_data):
            return
        self._write_u16(rom_data, offset, card_id_index)

    def _apply_all_changes_to_rom(self, rom_copy):
        for card in self.cards:
            self._write_string_and_update_pointer(rom_copy, card, is_name=True)
            self._write_string_and_update_pointer(rom_copy, card, is_name=False)
            self._write_stats_primary(rom_copy, card)
            self._write_stats_secondary(rom_copy, card)
            self._write_card_id_entry(rom_copy, card.konami_id, card.card_id_index)

        # After all cards, write artwork table
        self._write_artwork_table(rom_copy)

        # Finally, rebuild and write the alphabetical name sort table
        self._write_name_sort_table(rom_copy)

    # =========================
    # CARD ID UI
    # =========================

    def _card_id_display_for_index(self, idx):
        if 0 <= idx < len(self.cards):
            name = self.cards[idx].name.replace("\n", " ")
            if len(name) > 30:
                name = name[:30] + "..."
            return f"{idx:04d}: {name}"
        return f"{idx:04d}"

    def _update_card_id_choices(self):
        self.card_id_choices = [self._card_id_display_for_index(i) for i in range(len(self.cards))]
        self.card_id_main_combo["values"] = self.card_id_choices
        self.card_id_sec_combo["values"] = self.card_id_choices
        if hasattr(self, "artwork_card_combo"):
            self.artwork_card_combo["values"] = self.card_id_choices
        self.artwork_unk_combo["values"] = self.artwork_names
        self.artwork_card_combo["values"] = self.artwork_names

    def _load_artwork_into_editor(self, idx):
        if not self.artworks or not (0 <= idx < len(self.artworks)):
            return

        entry = self.artworks[idx]
        self.current_artwork_index = idx

        # Prevent spinbox recursion
        self._updating_artwork_index = True
        self.artwork_index_var.set(idx)
        self._updating_artwork_index = False

        # ------- FIRST HALFWORD -------
        unk_idx = entry.unk_halfword
        if 0 <= unk_idx < len(self.artwork_names):
            self.artwork_unk_var.set(self.artwork_names[unk_idx])
        else:
            self.artwork_unk_var.set("")

        # ------- SECOND HALFWORD -------
        # Read raw second halfword
        off2 = ARTWORK_TABLE_BASE + idx*4 + 2
        stored = self._read_u16(self.rom_data, off2)
        if 0 <= stored < len(self.artwork_names):
            self.artwork_card_var.set(self.artwork_names[stored])
        else:
            self.artwork_card_var.set("")

        # ------- Resolved name label (optional) -------
        self.artwork_name_var.set(
            f"Unk→ {self.artwork_unk_var.get()}   |   CardIdx→ {self.artwork_card_var.get()}"
        )

    def on_artwork_index_changed(self):
        if self._updating_artwork_index:
            return
        # Save current artwork entry before switching
        self._apply_artwork_ui_to_entry()
        idx = self.artwork_index_var.get()
        self._load_artwork_into_editor(idx)

    def _apply_artwork_ui_to_entry(self):
        if not self.artworks:
            return
        idx = self.artwork_index_var.get()
        if not (0 <= idx < len(self.artworks)):
            return

        entry = self.artworks[idx]

        # -------- FIRST HALFWORD --------
        unk_name = self.artwork_unk_var.get()
        if unk_name in self.artwork_names:
            entry.unk_halfword = self.artwork_names.index(unk_name)

        # -------- SECOND HALFWORD --------
        card_name = self.artwork_card_var.get()
        if card_name in self.artwork_names:
            entry.card_name_index = self.artwork_names.index(card_name)

    def _set_card_id_ui(self, var_obj, index_val, konami_id=None):
        """
        index_val == 0xFFFF -> use YGOPRODeck (None) style label.
        Otherwise -> "nnnn: Name".
        """
        if index_val == 0xFFFF:
            if konami_id is not None and konami_id in self.konami_name_map:
                base_name = self.konami_name_map[konami_id]
                label = f"{base_name} (None)"
            elif konami_id is not None:
                label = f"Konami {konami_id} (None)"
            else:
                label = "None"
            var_obj.set(label)
        else:
            var_obj.set(self._card_id_display_for_index(index_val))

    @staticmethod
    def _get_card_id_index_from_ui(var_obj):
        val = var_obj.get()
        if not val:
            return 0
        if val.endswith("(None)"):
            return 0xFFFF
        part = val.split(":", 1)[0].strip()
        try:
            return int(part)
        except ValueError:
            return 0

    # =========================
    # LIST & EDITOR UI
    # =========================

    def _populate_card_list(self, filter_text=""):
        filter_text = filter_text.lower()
        self.card_listbox.delete(0, tk.END)
        self.filtered_indices = []
        for i, card in enumerate(self.cards):
            if filter_text and filter_text not in card.name.lower():
                continue
            self.filtered_indices.append(i)
        for idx in self.filtered_indices:
            card = self.cards[idx]
            display = card.name.replace("\n", " ")
            if len(display) > 30:
                display = display[:30] + "..."
            self.card_listbox.insert(tk.END, f"{card.index:04d}: {display}")
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

        # Text
        self.name_var.set(card.name)
        self.desc_text.delete("1.0", tk.END)
        self.desc_text.insert("1.0", card.desc)

        # MAIN
        self._updating_konami_main = True
        self.konami_main_var.set(card.konami_id)
        self._updating_konami_main = False
        self._set_card_id_ui(self.card_id_main_var, card.card_id_index, card.konami_id)
        self.artwork_main_var.set(card.artwork_id)
        self.edited_main_var.set(card.edited_flag)
        self.atk_main_var.set(card.atk)
        self.def_main_var.set(card.deff)
        self.level_main_var.set(card.level)
        self.race_main_var.set(card.race)
        self.attribute_main_var.set(card.attribute)
        self.type_main_var.set(card.type_)
        self.st_race_main_var.set(card.st_race)
        self.padding_main_var.set(card.padding)

        def set_combo(combo, index_val, values_list, var_obj):
            if combo is None:
                var_obj.set(index_val)
                return
            if 0 <= index_val < len(values_list):
                combo.current(index_val)
            else:
                combo.set(str(index_val))

        set_combo(self.race_main_combo, card.race, self.races_list, self.race_main_var)
        set_combo(self.attribute_main_combo, card.attribute, self.attributes_list, self.attribute_main_var)
        set_combo(self.type_main_combo, card.type_, self.types_list, self.type_main_var)
        set_combo(self.st_race_main_combo, card.st_race, self.st_races_list, self.st_race_main_var)

        # SECONDARY
        self._updating_konami_sec = True
        self.konami_sec_var.set(card.konami2)
        self._updating_konami_sec = False
        self._set_card_id_ui(self.card_id_sec_var, card.card_id_index2, card.konami2)
        self.artwork_sec_var.set(card.artwork2)
        self.edited_sec_var.set(card.edited_flag2)
        self.atk_sec_var.set(card.atk2)
        self.def_sec_var.set(card.deff2)
        self.level_sec_var.set(card.level2)
        self.race_sec_var.set(card.race2)
        self.attribute_sec_var.set(card.attribute2)
        self.type_sec_var.set(card.type2)
        self.st_race_sec_var.set(card.st_race2)
        self.padding_sec_var.set(card.padding2)

        set_combo(self.race_sec_combo, card.race2, self.races_list, self.race_sec_var)
        set_combo(self.attribute_sec_combo, card.attribute2, self.attributes_list, self.attribute_sec_var)
        set_combo(self.type_sec_combo, card.type2, self.types_list, self.type_sec_var)
        set_combo(self.st_race_sec_combo, card.st_race2, self.st_races_list, self.st_race_sec_var)

        # Listbox selection
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
        
        # --- NEW: sync Artwork tab to this card's Artwork # ---
        if self.artworks:
            art_idx = card.card_id_index - 1
            if 0 <= art_idx < len(self.artworks):
                self._load_artwork_into_editor(art_idx)

        # --- NEW: render card artwork image ---
        self._render_card_image(card)

    def on_card_selected(self, event):
        if not self.cards or not self.filtered_indices:
            return
        self.apply_changes()
        sel = self.card_listbox.curselection()
        if not sel:
            return
        row = sel[0]
        idx = self.filtered_indices[row]
        self._load_card_into_editor(idx)

    def _write_artwork_table(self, rom_data):
        for entry in self.artworks:
            off = ARTWORK_TABLE_BASE + entry.index * 4
            if off + 4 > len(rom_data):
                break

            # Write first halfword
            self._write_u16(rom_data, off, entry.unk_halfword)

            # Write second halfword
            if entry.card_name_index > 0:
                self._write_u16(rom_data, off + 2, entry.card_name_index - 1)

    def apply_changes(self):
        if self.current_index is None or not self.cards:
            return
        card = self.cards[self.current_index]

        card.name = self.name_var.get()
        card.desc = self.desc_text.get("1.0", tk.END).rstrip("\n")

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

        # MAIN
        card.konami_id = self.konami_main_var.get()
        card.card_id_index = self._get_card_id_index_from_ui(self.card_id_main_var)
        card.artwork_id = self.artwork_main_var.get()
        card.edited_flag = self.edited_main_var.get()
        card.atk = self.atk_main_var.get()
        card.deff = self.def_main_var.get()
        card.level = self.level_main_var.get()
        card.race = get_index_from_combo(self.race_main_combo, self.races_list, self.race_main_var)
        card.attribute = get_index_from_combo(self.attribute_main_combo, self.attributes_list, self.attribute_main_var)
        card.type_ = get_index_from_combo(self.type_main_combo, self.types_list, self.type_main_var)
        card.st_race = get_index_from_combo(self.st_race_main_combo, self.st_races_list, self.st_race_main_var)

        # SECONDARY
        card.konami2 = self.konami_sec_var.get()
        card.card_id_index2 = self._get_card_id_index_from_ui(self.card_id_sec_var)
        card.artwork2 = self.artwork_sec_var.get()
        card.edited_flag2 = self.edited_sec_var.get()
        card.atk2 = self.atk_sec_var.get()
        card.deff2 = self.def_sec_var.get()
        card.level2 = self.level_sec_var.get()
        card.race2 = get_index_from_combo(self.race_sec_combo, self.races_list, self.race_sec_var)
        card.attribute2 = get_index_from_combo(self.attribute_sec_combo, self.attributes_list, self.attribute_sec_var)
        card.type2 = get_index_from_combo(self.type_sec_combo, self.types_list, self.type_sec_var)
        card.st_race2 = get_index_from_combo(self.st_race_sec_combo, self.st_races_list, self.st_race_sec_var)

        # Refresh dropdown labels after renames
        self._update_card_id_choices()
        self._set_card_id_ui(self.card_id_main_var, card.card_id_index, card.konami_id)
        self._set_card_id_ui(self.card_id_sec_var, card.card_id_index2, card.konami2)

        # Also store current artwork entry edits
        self._apply_artwork_ui_to_entry()

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

    def _get_gfx_index_from_current_artwork(self):
        """
        Uses the current artwork table entry and reads its second halfword
        ("Card (Name Index)" in the Artwork tab) directly from the ROM.
        That value is the 0-based graphics/palette index.
        """
        if self.rom_data is None or not self.artworks:
            return None

        # Prefer the artwork entry currently shown in the Artwork tab
        art_idx = getattr(self, "current_artwork_index", None)
        if art_idx is None:
            # Fallback: use the primary Artwork # field for the current card
            if self.current_index is None:
                return None
            card = self.cards[self.current_index]
            art_idx = card.artwork_id

        if not (0 <= art_idx < len(self.artworks)):
            return None

        # Second halfword = Card (Name Index), 0-based index into card_graphics_indexes / art tables
        off = ARTWORK_TABLE_BASE + art_idx * 4 + 2
        if off + 2 > len(self.rom_data):
            return None

        stored = self._read_u16(self.rom_data, off)
        if stored == 0xFFFF:  # if you ever use this sentinel
            return None

        # stored is the 0-based graphics index you described earlier
        return stored

    def load_card_graphics(self):
        """
        Import a square PNG for the current artwork entry, process it, and
        write the resulting 6bpp graphic and palette into the ROM:

          - resize to 80x80
          - reduce to 64 colors
          - flip each 8x8 tile horizontally
          - convert to 6bpp via custom gbagfx
          - insert at CARD_GFX_BASE / CARD_PAL_BASE for this graphics index
        """
        if self.rom_data is None or not self.cards:
            messagebox.showinfo("No ROM", "Load a ROM first.")
            return

        if self.current_index is None:
            messagebox.showinfo("No card selected", "Select a card first.")
            return

        gfx_index = self._get_gfx_index_from_current_artwork()
        if gfx_index is None:
            messagebox.showerror("Error", "Could not resolve Card (Name Index) / graphics index.")
            return

        if not (0 <= gfx_index < NUM_CARD_GFX):
            messagebox.showerror("Error", f"Graphics index {gfx_index} is out of range.")
            return

        gfx_off = CARD_GFX_BASE + gfx_index * CARD_GFX_SIZE
        pal_off = CARD_PAL_BASE + gfx_index * CARD_PAL_SIZE
        if gfx_off + CARD_GFX_SIZE > len(self.rom_data) or pal_off + CARD_PAL_SIZE > len(self.rom_data):
            messagebox.showerror("Error", "Graphics/palette location out of ROM range.")
            return

        # --- Select PNG file ---
        png_path = filedialog.askopenfilename(
            title="Select card artwork PNG",
            filetypes=[("PNG Images", "*.png"), ("All Files", "*.*")]
        )
        if not png_path:
            return

        try:
            img = Image.open(png_path).convert("RGBA")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load image:\n{e}")
            return

        # --- Validate / resize to 80x80 ---
        w, h = img.size
        if w != h:
            messagebox.showerror("Error", f"Image must be square. Got {w}x{h}.")
            return

        img = img.resize((80, 80), Image.LANCZOS)

        # Flatten alpha onto a solid background (e.g. transparent→black)
        # so quantization doesn't depend on PNG alpha weirdness.
        bg = Image.new("RGB", (80, 80), (0, 0, 0))
        bg.paste(img, mask=img.split()[3])  # use alpha channel as mask
        img = bg  # now RGB

        # --- Quantize to 64 colors ---
        img = img.convert("P", palette=Image.ADAPTIVE, colors=64)

        # --- Flip each 8x8 tile horizontally ---
        pixels = img.load()
        for ty in range(0, 80, 8):       # tile rows
            for tx in range(0, 80, 8):   # tile columns
                for y in range(8):
                    for x in range(4):   # swap pairs within tile row
                        x1 = tx + x
                        x2 = tx + (7 - x)
                        p1 = pixels[x1, ty + y]
                        p2 = pixels[x2, ty + y]
                        pixels[x1, ty + y] = p2
                        pixels[x2, ty + y] = p1

        # --- Run your custom gbagfx to generate 6bpp and palette ---
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp_png = os.path.join(tmpdir, "card_in.png")
            tmp_gfx = os.path.join(tmpdir, "card_in.6bpp")
            tmp_pal = os.path.join(tmpdir, "card_in.gbapal")

            img.save(tmp_png)

            cmd = [
                GBAGFX_PATH,
                tmp_png,
                tmp_gfx,
                "-mwidth", "10",
            ]

            try:
                res = subprocess.run(cmd, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            except Exception as e:
                messagebox.showerror("Error", f"gbagfx failed:\n{e}")
                return
            
            cmd = [
                GBAGFX_PATH,
                tmp_png,
                tmp_pal,
            ]

            try:
                res = subprocess.run(cmd, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            except Exception as e:
                messagebox.showerror("Error", f"gbagfx failed:\n{e}")
                return

            # --- Read back 6bpp data + palette ---
            try:
                with open(tmp_gfx, "rb") as f:
                    gfx_data = f.read()
                with open(tmp_pal, "rb") as f:
                    pal_data = f.read()
            except Exception as e:
                messagebox.showerror("Error", f"Failed to read gbagfx output:\n{e}")
                return

        # Sanity checks
        if len(gfx_data) != CARD_GFX_SIZE:
            messagebox.showerror(
                "Error",
                f"6bpp data wrong size: expected {CARD_GFX_SIZE:#x}, got {len(gfx_data):#x}"
            )
            return

        if len(pal_data) < CARD_PAL_SIZE:
            messagebox.showerror(
                "Error",
                f"Palette data too small: need at least {CARD_PAL_SIZE:#x} bytes, got {len(pal_data):#x}"
            )
            return

        # --- Write into ROM (only first 0x80 bytes of palette are used per entry) ---
        self.rom_data[gfx_off:gfx_off + CARD_GFX_SIZE] = gfx_data
        self.rom_data[pal_off:pal_off + CARD_PAL_SIZE] = pal_data[:CARD_PAL_SIZE]

        messagebox.showinfo(
            "Card graphics updated",
            f"Updated graphics slot {gfx_index} at {hex(gfx_off)} and palette at {hex(pal_off)}."
        )

        # Optionally refresh your preview image, if you already have that hooked up
        try:
            # Replace this with whatever function you're using now to draw the card art
            self._render_card_image(self.cards[self.current_index])
        except Exception:
            pass

    def _update_controls_state(self):
        state = tk.NORMAL if self.cards else tk.DISABLED
        self.prev_btn.config(state=state)
        self.next_btn.config(state=state)
        self.apply_btn.config(state=state)
        if hasattr(self, "load_gfx_button"):
            self.load_gfx_button.config(state=state)
        if not self.cards:
            self.name_entry.config(state=tk.DISABLED)
            self.desc_text.config(state=tk.DISABLED)
        else:
            self.name_entry.config(state=tk.NORMAL)
            self.desc_text.config(state=tk.NORMAL)

    # =========================
    # SEARCH & KONAMI TRACES
    # =========================

    def apply_filter(self):
        text = self.search_var.get().strip()
        self._populate_card_list(text)

    def clear_filter(self):
        self.search_var.set("")
        self._populate_card_list("")

    def _on_konami_main_changed(self, *args):
        if self._updating_konami_main:
            return
        if self.rom_data is None or self.current_index is None or not self.cards:
            return
        try:
            konami = self.konami_main_var.get()
        except tk.TclError:
            return
        card_id_index = self._read_card_id_index_from_table(self.rom_data, konami)
        self._set_card_id_ui(self.card_id_main_var, card_id_index, konami)
        card = self.cards[self.current_index]
        card.konami_id = konami
        card.card_id_index = card_id_index

    def _on_konami_sec_changed(self, *args):
        """
        For secondary stats, the 'Card ID (Name Index)' display should always be
        derived from the *current* Konami ID in the secondary stats, using the
        card ID table:
            - If entry != 0xFFFF: it's a normal card name index.
            - If entry == 0xFFFF: show YGOPRODeck name + ' (None)'.
        This does NOT change which secondary stats row is attached to the card
        (that's controlled by second_stats_index).
        """
        if self._updating_konami_sec:
            return
        if self.rom_data is None or self.current_index is None or not self.cards:
            return

        try:
            konami2 = self.konami_sec_var.get()
        except tk.TclError:
            return
        

        card = self.cards[self.current_index]
        card.konami2 = konami2

        # Recompute the card-name index from the card ID table using Konami2
        if konami2 >= KONAMI_ID_BASE:
            idx_val = self._read_card_id_index_from_table(self.rom_data, konami2)
        else:
            idx_val = 0

        # Store it (used only for display / saving, not for mapping the row)
        card.card_id_index2 = idx_val

        # Update the UI label; if idx_val == 0xFFFF, this will show 'Name (None)'
        # using the YGOPRODeck mapping.
        self._set_card_id_ui(self.card_id_sec_var, idx_val, konami2)


if __name__ == "__main__":
    app = RomEditorApp()
    app.mainloop()
