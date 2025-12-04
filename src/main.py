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
from io import BytesIO
from urllib.request import urlopen

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

# =========================
# CARD ICON CONSTANTS
# =========================

LARGE_ICON_BASE       = 0xFBC080   # 8bpp, 0x600 bytes per icon
LARGE_ICON_SIZE       = 0x600

SMALL_ICON_BASE       = 0x1326280  # 8bpp, 0x480 bytes per entry
SMALL_ICON_ENTRY_SIZE = 0x480      # 0x240 regular + 0x240 sideways
SMALL_ICON_SIZE       = 0x240      # bytes for *one* small icon

ICON_PAL_BASE         = 0x510440   # shared icon palette
ICON_PAL_SIZE         = 0x120      # 144 colors (0x120 bytes)

# Dimensions (tweak if you confirm different sizes)
LARGE_ICON_WIDTH  = 32
LARGE_ICON_HEIGHT = 48  # 32 * 48 = 1536 = 0x600

SMALL_ICON_WIDTH  = 24
SMALL_ICON_HEIGHT = 24  # 24 * 24 = 576 = 0x240

IMAGES_DIR = os.path.join(os.path.dirname(__file__), "../images")

# Password & price tables (indexed by card name index)
PASSWORD_TABLE_BASE = 0x15B94CC  # 4 bytes per card, little endian
PRICE_TABLE_BASE    = 0x1CEDFA4  # 4 bytes per card, little endian
PASSWORD_ENTRY_SIZE = 4
PRICE_ENTRY_SIZE    = 4

# Deck pointer table
DECK_PTR_TABLE_BASE = 0x1E63BEC  # 4-byte little-endian pointers, ROM-address (0x08000000-based)
DECK_PTR_ENTRY_SIZE = 4
GBA_ROM_BASE        = 0x08000000  # for converting ROM addresses -> file offsets
NUM_DECKS           = 215
FREE_SPACE_START    = 0x162248C

# =========================
# PACK CONSTANTS
# =========================
PACK_TABLE_BASE   = 0x1E5E2E8  # pack structs
PACK_ENTRY_SIZE   = 0x10       # 16 bytes per pack
NUM_PACKS         = 45         # total packs

class ArtworkEntry:
    def __init__(self, index, unk_halfword, card_name_index):
        self.index = index                 # artwork slot index (0..2330)
        self.unk_halfword = unk_halfword   # first 2 bytes, unknown but editable
        self.card_name_index = card_name_index  # second 2 bytes: index into card names table

class DeckEntry:
    def __init__(self, index, ptr_off, struct_off,
                 unk_values, main_cards, extra_cards, original_size):
        self.index = index                  # deck index in pointer table
        self.ptr_off = ptr_off              # offset of pointer in ROM
        self.struct_off = struct_off        # current deck structure offset in ROM
        self.unk = list(unk_values)         # [unk0, unk1, unk2, unk3] as u16
        self.main_cards = list(main_cards)  # list of Konami IDs (u16)
        self.extra_cards = list(extra_cards)
        self.original_size = original_size  # bytes originally allocated

class PackEntry:
    def __init__(self, index, struct_off, ptr_off,
                 cost, cards_per_pack, card_amount,
                 unk0, unk1, padding,
                 contents_off, contents, original_contents_size):
        self.index = index               # pack index (0..NUM_PACKS-1)
        self.struct_off = struct_off     # offset of pack header in ROM
        self.ptr_off = ptr_off           # offset of contents pointer (struct_off + 12)
        self.cost = cost
        self.cards_per_pack = cards_per_pack
        self.card_amount = card_amount
        self.unk0 = unk0
        self.unk1 = unk1
        self.padding = padding

        # contents: list of (konami_id, rarity_index)
        self.contents_off = contents_off
        self.contents = list(contents)
        self.original_contents_size = original_contents_size  # bytes

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
        race, attribute, type_, st_race, padding,
        password, price,          # <<< add these
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

        # Misc info
        self.password = password  # 32-bit value, usually shown as 8-digit code
        self.price    = price     # 32-bit value (shop price, etc.)

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
        self.ygo_cards_by_name = {}
        self.ygo_card_names = []

        # Trace guards
        self._updating_konami_main = False
        self._updating_konami_sec = False

        self.artworks = []                 # list[ArtworkEntry]
        self.current_artwork_index = 0
        self._updating_artwork_index = False

        self.artwork_names = []

        self.decks = []                     # list[DeckEntry]
        self.konami_to_card_index = {}      # filled after parsing cards
        self.deck_card_choices = []         # "ID: Name" for deck dropdowns
        self.deck_card_choice_konami = []   # konami_id list aligned with above
        self.konami_to_deck_choice_index = {}
        self.deck_names = []  # index -> name from text/decks.txt

        self.password_to_konami = {}  # password (int) -> konami_id
        
        self.packs = []          # list[PackEntry]
        self.pack_names = []     # from text/packs.txt
        self.rarities = []       # from text/rarities.txt

        self._load_text_mappings()
        self._load_json_mappings()
        self._build_ui()

    def _load_rarities(self):
        """
        Load rarities from text/rarities.txt: one per line.
        The line index is the rarity index stored in ROM.
        """
        try:
            base_dir = os.path.dirname(os.path.abspath(__file__))
        except Exception:
            base_dir = os.getcwd()

        path = os.path.join(base_dir, "..", "text", "rarities.txt")
        rarities = []
        try:
            with open(path, "r", encoding="utf-8", errors="ignore") as f:
                for line in f:
                    rarities.append(line.strip())
        except Exception:
            rarities = []

        if not rarities:
            rarities = ["(None)"]

        self.rarities = rarities

    def _load_pack_names(self):
        """
        Load pack names from text/packs.txt.
        Each line corresponds to a pack index.
        """
        try:
            base_dir = os.path.dirname(os.path.abspath(__file__))
        except Exception:
            base_dir = os.getcwd()

        path = os.path.join(base_dir, "..", "text", "packs.txt")
        names = []
        try:
            with open(path, "r", encoding="utf-8", errors="ignore") as f:
                for line in f:
                    names.append(line.strip())
        except Exception:
            names = []

        self.pack_names = names

    def _write_deck_to_rom(self, deck: DeckEntry):
        """
        Write a single deck back into self.rom_data.
        If the new deck structure is larger than the original, repoint it
        to a fresh 0xFF region and update the pointer table.
        """
        if self.rom_data is None:
            return

        rom = self.rom_data
        blob = self._encode_deck_structure(deck)
        new_size = len(blob)

        # If we can fit in the original space, write in-place
        if new_size <= deck.original_size:
            write_off = deck.struct_off
            rom[write_off:write_off + new_size] = blob
            # Optional: fill leftover bytes with 0xFF
            if new_size < deck.original_size:
                rom[write_off + new_size:write_off + deck.original_size] = b"\xFF" * (deck.original_size - new_size)
            return

        # Otherwise, find new free space of 0xFF
        new_off = self._find_free_space_ff(rom, new_size)
        if new_off is None:
            messagebox.showerror("Error", f"No free space large enough for deck {deck.index}.")
            return

        # Mark old region as free
        rom[deck.struct_off:deck.struct_off + deck.original_size] = b"\xFF" * deck.original_size

        # Write new deck
        rom[new_off:new_off + new_size] = blob

        # Update pointer
        new_ptr_val = new_off + GBA_ROM_BASE
        self._write_u32(rom, deck.ptr_off, new_ptr_val)

        # Update deck metadata for future edits
        deck.struct_off = new_off
        deck.original_size = new_size

    def _load_deck_names(self):
        """
        Load deck names from text/decks.txt.
        Each line corresponds to the deck at that index.
        """
        try:
            base_dir = os.path.dirname(os.path.abspath(__file__))
        except Exception:
            base_dir = os.getcwd()

        path = os.path.join(base_dir, "..", "text", "decks.txt")
        names = []
        try:
            with open(path, "r", encoding="utf-8", errors="ignore") as f:
                for line in f:
                    name = line.strip()
                    names.append(name)
        except FileNotFoundError:
            names = []
        except Exception:
            names = []

        self.deck_names = names

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

    def _get_icon_template_path(self, card, label: str) -> str:
        """
        Build the filename for the icon template PNG, using the same logic
        as in _decode_icon_to_photoimage:

            type_name = self.types_list[card.type_]
            safe = type_name.replace(' ', '_').replace('/', '_').lower()
            filename = f"{safe}_{label}.png"
        """
        type_name = self.types_list[card.type_]
        safe = type_name.replace(' ', '_').replace('/', '_').lower()
        filename = f"{safe}_{label}.png"
        return os.path.join(IMAGES_DIR, filename)

    def _import_icons_from_card_image(self, card, card_rgb_80: Image.Image):
        """
        From full card image (80x80 RGB), build and import:
          - Large icon (32x48, card shrunk to 30x30 at (1, 9))
          - Small icon (24x24, card shrunk to 14x14 at (5, 5))
          - Small sideways icon (same 14x14, rotated right 90°, pasted at (5, 5))

        Each icon is created by:
          - starting from a card sprite
          - pasting the type template PNG on top
          - quantizing to the shared icon palette
          - encoding to 8bpp and writing into the icon tables
        """
        if self.rom_data is None:
            return

        icon_idx = self._get_gfx_index_from_current_artwork()
        if icon_idx is None or icon_idx < 0:
            return

        # Offsets in the icon tables
        large_off = LARGE_ICON_BASE + icon_idx * LARGE_ICON_SIZE
        small_off = SMALL_ICON_BASE + icon_idx * SMALL_ICON_ENTRY_SIZE

        if (large_off + LARGE_ICON_SIZE > len(self.rom_data) or
            small_off + SMALL_ICON_ENTRY_SIZE > len(self.rom_data)):
            messagebox.showerror("Error", "Icon data would be written out of ROM bounds.")
            return

        # --- prepare base sprites from the 80x80 card image ---
        # Work in RGBA so we can paste under transparent templates
        def _get_icon_template_path(self, card, label: str) -> str:
            type_name = self.types_list[card.type_]
            safe = type_name.replace(' ', '_').replace('/', '_').lower()
            filename = f"{safe}_{label}.png"
            return os.path.join(IMAGES_DIR, filename)

        # Helper to build final icon using a template
        card_rgba_80 = card_rgb_80.convert("RGBA")
        large_sprite = card_rgba_80.resize((30, 30), Image.LANCZOS)
        small_sprite = card_rgba_80.resize((14, 14), Image.LANCZOS)
        small_side_sprite = small_sprite.rotate(-90, expand=False)  # 90° right

        def build_icon_with_template(sprite: Image.Image,
                                     label: str,
                                     icon_w: int,
                                     icon_h: int,
                                     offset: tuple[int, int]) -> Image.Image:
            """
            Start from the type template PNG, then paste the card sprite on top.
            """
            tpl_path = self._get_icon_template_path(card, label)
            try:
                tpl = Image.open(tpl_path).convert("RGBA")
            except FileNotFoundError:
                messagebox.showerror("Error", f"Template not found:\n{tpl_path}")
                raise
            except Exception as e:
                messagebox.showerror("Error", f"Failed to load template {tpl_path}:\n{e}")
                raise

            if tpl.size != (icon_w, icon_h):
                tpl = tpl.resize((icon_w, icon_h), Image.LANCZOS)

            # Start from the template
            base = tpl.copy()

            # Paste sprite ON TOP of the template, preserving sprite alpha if present
            if sprite.mode != "RGBA":
                sprite = sprite.convert("RGBA")
            base.paste(sprite, offset, sprite)

            # Final icon to quantize: RGB
            return base.convert("RGB")

        large_icon_rgb = build_icon_with_template(
            large_sprite, "large",
            LARGE_ICON_WIDTH, LARGE_ICON_HEIGHT,
            (1, 9)
        )
        small_icon_rgb = build_icon_with_template(
            small_sprite, "small",
            SMALL_ICON_WIDTH, SMALL_ICON_HEIGHT,
            (5, 5)
        )
        small_side_icon_rgb = build_icon_with_template(
            small_side_sprite, "small_side",
            SMALL_ICON_WIDTH, SMALL_ICON_HEIGHT,
            (5, 5)
        )

        # --- Quantize to the icon palette ---
        try:
            large_p = self._quantize_to_icon_palette(large_icon_rgb)
            small_p = self._quantize_to_icon_palette(small_icon_rgb)
            small_side_p = self._quantize_to_icon_palette(small_side_icon_rgb)
        except Exception as e:
            messagebox.showerror("Error", f"Failed to quantize icons to icon palette:\n{e}")
            return

        # --- Encode with gbagfx to raw 8bpp data and write into ROM ---
        import tempfile, subprocess, os

        with tempfile.TemporaryDirectory() as tmpdir:
            def encode_icon_png(img_p, fname, w, h, expected_size):
                png_path = os.path.join(tmpdir, fname + ".png")
                bin_path = os.path.join(tmpdir, fname + ".8bpp")

                img_p.save(png_path)

                cmd = [
                    GBAGFX_PATH,
                    png_path,
                    bin_path,
                    "-mwidth", str(w / 8),
                ]
                subprocess.run(cmd, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

                with open(bin_path, "rb") as f:
                    data = f.read()
                if len(data) != expected_size:
                    raise ValueError(
                        f"{fname}: expected {expected_size:#x} bytes, got {len(data):#x}"
                    )
                return data

            try:
                large_data = encode_icon_png(
                    large_p, "large_icon",
                    LARGE_ICON_WIDTH, LARGE_ICON_HEIGHT,
                    LARGE_ICON_SIZE
                )
                small_data = encode_icon_png(
                    small_p, "small_icon",
                    SMALL_ICON_WIDTH, SMALL_ICON_HEIGHT,
                    SMALL_ICON_SIZE
                )
                small_side_data = encode_icon_png(
                    small_side_p, "small_side_icon",
                    SMALL_ICON_WIDTH, SMALL_ICON_HEIGHT,
                    SMALL_ICON_SIZE
                )
            except Exception as e:
                messagebox.showerror("Error", f"Failed to encode icons with gbagfx:\n{e}")
                return

        # Write into ROM
        self.rom_data[large_off:large_off + LARGE_ICON_SIZE] = large_data
        self.rom_data[small_off:small_off + SMALL_ICON_SIZE] = small_data
        self.rom_data[small_off + SMALL_ICON_SIZE:small_off + SMALL_ICON_ENTRY_SIZE] = small_side_data

    def _parse_artworks(self):
        data = self.rom_data
        artworks = []
        for i in range(NUM_CARDS):
            off = ARTWORK_TABLE_BASE + i * 4
            if off + 4 > len(data):
                break

            unk = self._read_u16(data, off)

            stored = self._read_u16(data, off + 2)
            if stored == 0xFFFF:
                card_idx = 0xFFFF
            else:
                card_idx = stored  # direct index into card names

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
            self.ygo_cards_by_name = {}
            self.ygo_card_names = []
            return

        try:
            with open(json_path, "r", encoding="utf-8", errors="ignore") as f:
                data = json.load(f)
        except Exception:
            self.konami_name_map = {}
            self.ygo_cards_by_name = {}
            self.ygo_card_names = []
            return

        mapping = {}
        ygo_by_name = {}
        ygo_names = []

        if isinstance(data, dict) and "data" in data and isinstance(data["data"], list):
            for card_info in data["data"]:
                try:
                    # YGOPRODeck piece used for Konami->name (you already had this)
                    misc = card_info.get("misc_info")
                    if misc and isinstance(misc, list):
                        konami_id = misc[0].get("konami_id")
                        name = card_info.get("name")
                        if isinstance(konami_id, int) and isinstance(name, str):
                            mapping[konami_id] = name

                    # NEW: keep full card info and names for dropdown
                    name = card_info.get("name")
                    if isinstance(name, str):
                        if name not in ygo_by_name:
                            ygo_by_name[name] = card_info
                            ygo_names.append(name)
                except Exception:
                    continue

        self.konami_name_map = mapping
        self.ygo_cards_by_name = ygo_by_name
        self.ygo_card_names = sorted(ygo_names, key=str.lower)

    def _render_card_icons(self, card: CardEntry):
        """
        Render:
          - large icon
          - small regular icon
          - small sideways icon

        All are 8bpp indexed, using the shared palette at ICON_PAL_BASE.
        Table indices are based on current_artwork_index (or card.artwork_id fallback).
        """
        # Clear by default
        def clear_icons(msg=""):
            self.large_icon_label.config(image="", text=msg or "(large)")
            self.small_icon_label.config(image="", text=msg or "(small)")
            self.small_side_icon_label.config(image="", text=msg or "(sideways)")
            self.large_icon_photo = self.small_icon_photo = self.small_side_icon_photo = None

        if self.rom_data is None:
            clear_icons("(no ROM)")
            return

        icon_idx = self._get_gfx_index_from_current_artwork()
        if icon_idx is None or icon_idx < 0:
            clear_icons("(no icon)")
            return

        pal_data = self._get_icon_palette()
        if pal_data is None:
            clear_icons("(no palette)")
            return

        # Compute ROM offsets
        large_off = LARGE_ICON_BASE + icon_idx * LARGE_ICON_SIZE
        small_off = SMALL_ICON_BASE + icon_idx * SMALL_ICON_ENTRY_SIZE

        if (large_off + LARGE_ICON_SIZE > len(self.rom_data) or
            small_off + SMALL_ICON_ENTRY_SIZE > len(self.rom_data)):
            clear_icons("(out of range)")
            return

        large_data = bytes(self.rom_data[large_off:large_off + LARGE_ICON_SIZE])
        small_entry = bytes(self.rom_data[small_off:small_off + SMALL_ICON_ENTRY_SIZE])
        small_reg_data = small_entry[:SMALL_ICON_SIZE]
        small_side_data = small_entry[SMALL_ICON_SIZE:SMALL_ICON_ENTRY_SIZE]

        # gbagfx expects a 256-color palette (0x200 bytes) for 8bpp; pad with zeros.
        pal_256 = pal_data + b"\x00" * (0x200 - len(pal_data))

        try:
            self.large_icon_photo = self._decode_icon_to_photoimage(
                card, 'large', large_data, pal_256, LARGE_ICON_WIDTH, LARGE_ICON_HEIGHT
            )
            self.small_icon_photo = self._decode_icon_to_photoimage(
                card, 'small', small_reg_data, pal_256, SMALL_ICON_WIDTH, SMALL_ICON_HEIGHT
            )
            self.small_side_icon_photo = self._decode_icon_to_photoimage(
                card, 'small_side', small_side_data, pal_256, SMALL_ICON_WIDTH, SMALL_ICON_HEIGHT
            )
        except Exception:
            clear_icons("(decode error)")
            return

        # Attach to labels
        self.large_icon_label.config(image=self.large_icon_photo, text="")
        self.small_icon_label.config(image=self.small_icon_photo, text="")
        self.small_side_icon_label.config(image=self.small_side_icon_photo, text="")

    def _decode_icon_to_photoimage(self, card: CardEntry, label: str, gfx_data: bytes, pal_256: bytes,
                                   width: int, height: int) -> ImageTk.PhotoImage:
        """
        Take raw 8bpp tile data + GBA-format palette and turn it into
        a Tk PhotoImage via gbagfx + Pillow.
        """
        import tempfile, os

        if len(gfx_data) != width * height:
            # If this happens, your width/height constants are wrong.
            raise ValueError("Icon size mismatch for given dimensions")

        with tempfile.TemporaryDirectory() as tmpdir:
            gfx_path = os.path.join(tmpdir, "icon.8bpp")
            pal_path = os.path.join(tmpdir, "icon.gbapal")
            png_path = os.path.join(tmpdir, "icon.png")

            with open(gfx_path, "wb") as f:
                f.write(gfx_data)
            with open(pal_path, "wb") as f:
                f.write(pal_256)

            cmd = [
                GBAGFX_PATH,
                gfx_path,
                png_path,
                "-palette", pal_path,
                "-mwidth", str(width / 8),
            ]

            subprocess.run(cmd, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

            img = Image.open(png_path)
            # No flips/rotations here unless you *want* to adjust sideways icon visually.
            return ImageTk.PhotoImage(img)

    def import_from_ygoprodeck(self):
        if self.rom_data is None or not self.cards:
            messagebox.showinfo("No ROM", "Load a ROM first.")
            return
        if self.current_index is None:
            messagebox.showinfo("No card selected", "Select a card first.")
            return

        name = (self.ygo_import_var.get() or "").strip()
        if not name:
            messagebox.showinfo("No YGOPRODeck card", "Choose a card from the dropdown first.")
            return

        if not hasattr(self, "ygo_cards_by_name") or name not in self.ygo_cards_by_name:
            # Try case-insensitive match
            lowered = name.lower()
            match = None
            for n, ci in self.ygo_cards_by_name.items():
                if n.lower() == lowered:
                    match = ci
                    break
            if match is None:
                messagebox.showerror("Error", f"No YGOPRODeck entry found for '{name}'.")
                return
            card_info = match
        else:
            card_info = self.ygo_cards_by_name[name]

        card = self.cards[self.current_index]

        # ---------- Basic text + password ----------
        card_name = card_info.get("name") or card.name
        desc = card_info.get("desc") or card.desc
        ygo_id = card_info.get("id")

        card.name = card_name
        card.desc = desc

        # Password: YGOPRODeck 'id' is numeric; we treat it as the decimal password
        try:
            if isinstance(ygo_id, int):
                card.password = ygo_id
            elif isinstance(ygo_id, str) and ygo_id.isdigit():
                card.password = int(ygo_id)
        except Exception:
            pass  # fall back to existing value if something weird happens

        # ---------- Type / race / attribute / stats ----------
        type_str = card_info.get("type") or ""
        human_type_str = card_info.get("humanReadableCardType") or ""
        race_str = card_info.get("race") or ""
        attr_str = card_info.get("attribute") or ""
        atk_val = card_info.get("atk", card.atk)
        def_val = card_info.get("def", card.deff)
        lvl_val = card_info.get("level", card.level)

        type_str = str(type_str)
        human_type_str = str(human_type_str)
        race_str = str(race_str)
        attr_str = str(attr_str)

        is_spell = type_str == "Spell Card"
        is_trap = type_str == "Trap Card"

        if is_spell or is_trap:
            # Spell / Trap: Race, Attribute, and Type are all Spell/Trap Card,
            # with ATK/DEF/Level set to 0. Spell/Trap race from YGOPRO 'race'.
            base_type_name = "Spell Card" if is_spell else "Trap Card"

            # Type
            if base_type_name in self.types_list:
                card.type_ = self.types_list.index(base_type_name)

            # Race (monster race field)
            if base_type_name in self.races_list:
                card.race = self.races_list.index(base_type_name)

            # Attribute
            if base_type_name in self.attributes_list:
                card.attribute = self.attributes_list.index(base_type_name)

            # Spell/Trap Race (Normal, Continuous, Equip, etc.)
            if race_str in self.st_races_list:
                card.st_race = self.st_races_list.index(race_str)
            else:
                card.st_race = 0

            card.atk = 0
            card.deff = 0
            card.level = 0
        else:
            # Monster (or other non-spell/trap types)
            if human_type_str == 'Fusion Effect Monster':
                type_str = human_type_str

            if type_str in self.types_list:
                card.type_ = self.types_list.index(type_str)

            if race_str in self.races_list:
                card.race = self.races_list.index(race_str)

            if attr_str in self.attributes_list:
                card.attribute = self.attributes_list.index(attr_str)

            # Not a spell/trap, so spell/trap race is 0
            card.st_race = 0

            # ATK / DEF: -1 means "?" → 65535 in the ROM
            if isinstance(atk_val, int):
                card.atk = 65535 if atk_val == -1 else max(0, atk_val) & 0xFFFF
            if isinstance(def_val, int):
                card.deff = 65535 if def_val == -1 else max(0, def_val) & 0xFFFF

            if isinstance(lvl_val, int):
                card.level = lvl_val & 0xFFFF

        # ---------- SECONDARY: mirror primary stats ----------
        # Only if this card actually has a secondary stats row
        if card.second_stats_index >= 0:
            # Usually you want secondary Konami / name index to follow primary
            card.konami2 = card.konami_id
            card.card_id_index2 = card.card_id_index

            # Artwork + edited flag
            card.artwork2 = card.artwork_id
            card.edited_flag2 = card.edited_flag

            # Stats (these already include your Spell/Trap + -1→65535 logic)
            card.atk2 = card.atk
            card.deff2 = card.deff
            card.level2 = card.level
            card.race2 = card.race
            card.attribute2 = card.attribute
            card.type2 = card.type_
            card.st_race2 = card.st_race
            card.padding2 = card.padding

        # ---------- Download cropped image and import graphics ----------
        image_url = None
        images = card_info.get("card_images") or []
        if isinstance(images, list) and images:
            first_img = images[0] or {}
            image_url = first_img.get("image_url_cropped") or first_img.get("image_url")

        if image_url:
            try:
                resp = urlopen(image_url)
                data = resp.read()
                pil_img = Image.open(BytesIO(data))
                # Use the same pipeline as your "Load Card Graphics..." feature
                self._import_card_graphics_from_pil(card, pil_img)
            except Exception as e:
                messagebox.showerror("Image Error", f"Failed to download or import card image:\n{e}")

        # Refresh UI from updated CardEntry
        self._load_card_into_editor(self.current_index)

    def _import_card_graphics_from_pil(self, card, pil_img):
        """
        Shared pipeline to take any PIL image and:
          - resize to 80x80
          - do your existing JPG->PNG / alpha / 64-color card art conversion
          - import the main card graphic (6bpp + palette)
          - generate/update icons (large + 2 small) using your templates
        """
        # This is basically the body of your existing load_card_graphics method,
        # but starting from a PIL image instead of a file path.

        # Example sketch (adapt to your current implementation):
        img = pil_img.convert("RGBA")

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
        
        # This is the “master” card image for icons
        card_rgb_80 = bg.copy()
        
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

        # --- Write into ROM (only first 0x80 bytes of palette are used per entry) ---
        self.rom_data[gfx_off:gfx_off + CARD_GFX_SIZE] = gfx_data
        self.rom_data[pal_off:pal_off + CARD_PAL_SIZE] = pal_data[:CARD_PAL_SIZE]

        messagebox.showinfo(
            "Card graphics updated",
            f"Updated graphics slot {gfx_index} at {hex(gfx_off)} and palette at {hex(pal_off)}."
        )

        # After writing gfx/pal for the main 6bpp artwork:
        card = self.cards[self.current_index]
        self._import_icons_from_card_image(card, card_rgb_80)

        # Optionally refresh your preview image, if you already have that hooked up
        try:
            # Replace this with whatever function you're using now to draw the card art
            self._render_card_image(card)
            self._render_card_icons(card)
        except Exception:
            pass

    def _on_ygo_import_filter(self, event):
        """Filter YGOPRODeck combo by substring in name."""
        if not hasattr(self, "ygo_card_names"):
            return
        pattern = self.ygo_import_var.get().lower()
        if not pattern:
            filtered = self.ygo_card_names
        else:
            filtered = [n for n in self.ygo_card_names if pattern in n.lower()]
        self.ygo_import_combo["values"] = filtered
        # Optional: expand dropdown as you type
        # self.ygo_import_combo.event_generate("<Down>")

    def _get_icon_palette(self):
        if self.rom_data is None:
            return None

        if not hasattr(self, "_icon_palette_cache"):
            if ICON_PAL_BASE + ICON_PAL_SIZE > len(self.rom_data):
                self._icon_palette_cache = None
            else:
                self._icon_palette_cache = bytes(
                    self.rom_data[ICON_PAL_BASE:ICON_PAL_BASE + ICON_PAL_SIZE]
                )
        return self._icon_palette_cache

    def open_deck_editor(self):
        if self.rom_data is None or not self.cards:
            messagebox.showinfo("No ROM", "Load a ROM first.")
            return
        if not self.decks:
            self._parse_decks()
        DeckEditorWindow(self)

    def open_pack_editor(self):
        if self.rom_data is None or not self.cards:
            messagebox.showinfo("No ROM", "Load a ROM first.")
            return
        if not self.packs:
            self._parse_packs()
        PackEditorWindow(self)

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

        # Deck menu
        deck_menu = tk.Menu(menubar, tearoff=False)
        deck_menu.add_command(label="Deck Editor...", command=self.open_deck_editor)
        deck_menu.add_command(label="Pack Editor...", command=self.open_pack_editor)
        menubar.add_cascade(label="Other Editors", menu=deck_menu)

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

        # --- Card artwork + icons row ---
        art_row = tk.Frame(right_frame)
        art_row.pack(anchor="w", pady=(0, 5))

        # Main card image
        image_frame = tk.Frame(art_row)
        image_frame.grid(row=0, column=0, sticky="nw")
        self.card_image_label = tk.Label(image_frame, text="(no art)")
        self.card_image_label.pack()
        self.card_photo = None

        # Card icon previews, to the right of main art
        icon_frame = tk.Frame(art_row)
        icon_frame.grid(row=0, column=1, sticky="nw", padx=6)

        self.large_icon_label = tk.Label(icon_frame, text="(large)")
        self.large_icon_label.grid(row=0, column=0, padx=2)

        self.small_icon_label = tk.Label(icon_frame, text="(small)")
        self.small_icon_label.grid(row=0, column=1, padx=2)

        self.small_side_icon_label = tk.Label(icon_frame, text="(sideways)")
        self.small_side_icon_label.grid(row=0, column=2, padx=2)

        # Keep references so Tk doesn't GC the images
        self.large_icon_photo = None
        self.small_icon_photo = None
        self.small_side_icon_photo = None

        # Name
        name_frame = tk.Frame(right_frame)
        name_frame.pack(fill=tk.X, pady=2)
        tk.Label(name_frame, text="Card Name:").pack(anchor="w")
        self.name_var = tk.StringVar()
        self.name_entry = tk.Entry(name_frame, textvariable=self.name_var)
        self.name_entry.pack(fill=tk.X)

        # YGOPRODeck import
        import_frame = tk.Frame(right_frame)
        import_frame.pack(fill=tk.X, pady=(2, 0))

        tk.Label(import_frame, text="Import from YGOPRODeck:").pack(side=tk.LEFT)

        self.ygo_import_var = tk.StringVar()
        self.ygo_import_combo = ttk.Combobox(
            import_frame,
            textvariable=self.ygo_import_var,
            width=30
        )
        # All card names from the JSON
        self.ygo_import_combo["values"] = self.ygo_card_names
        self.ygo_import_combo.pack(side=tk.LEFT, padx=(3, 3))

        # Filter as you type
        self.ygo_import_combo.bind("<KeyRelease>", self._on_ygo_import_filter)

        tk.Button(
            import_frame,
            text="Import",
            command=self.import_from_ygoprodeck
        ).pack(side=tk.LEFT)

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
        stats_notebook.add(artwork_frame, text="Misc Info")

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

        # NEW: misc info vars
        self.password_var = tk.StringVar()  # 8-digit password as string
        self.price_var    = tk.IntVar()     # numeric price

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

        # ---------- Misc Info UI (password/price + artwork) ----------
        row = 0

        # Password
        tk.Label(artwork_frame, text="Password:").grid(row=row, column=0, sticky="w", padx=2, pady=1)
        self.password_entry = tk.Entry(artwork_frame, textvariable=self.password_var, width=12)
        self.password_entry.grid(row=row, column=1, sticky="w", padx=2, pady=1)
        row += 1

        # Price
        tk.Label(artwork_frame, text="Price:").grid(row=row, column=0, sticky="w", padx=2, pady=1)
        self.price_entry = tk.Entry(artwork_frame, textvariable=self.price_var, width=12)
        self.price_entry.grid(row=row, column=1, sticky="w", padx=2, pady=1)
        row += 1

        # Existing artwork table controls follow
        tk.Label(artwork_frame, text="Unused Card (Name Index):").grid(row=row, column=0, sticky="w", padx=2, pady=1)
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
            state=tk.DISABLED
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

    def _parse_decks(self):
        """
        Parse up to NUM_DECKS decks from the deck pointer table.
        Each pointer is a 4-byte ROM address (0x08000000-based).
        """
        self.decks = []
        if self.rom_data is None:
            return

        data = self.rom_data
        ptr_off = DECK_PTR_TABLE_BASE

        for deck_idx in range(NUM_DECKS):
            if ptr_off + DECK_PTR_ENTRY_SIZE > len(data):
                break

            ptr_val = self._read_u32(data, ptr_off)

            # If you know unused entries are zeroed, you can break on 0
            if ptr_val in (0, 0xFFFFFFFF):
                break

            struct_off = ptr_val - GBA_ROM_BASE
            if not (0 <= struct_off < len(data)):
                break

            deck = self._parse_single_deck(deck_idx, ptr_off, struct_off)
            if deck is None:
                break

            self.decks.append(deck)
            ptr_off += DECK_PTR_ENTRY_SIZE

    def _parse_single_deck(self, index, ptr_off, struct_off):
        data = self.rom_data
        if struct_off + 8 + 2 > len(data):
            return None

        # 8 bytes of unknowns: 4 halfwords
        unk_values = [self._read_u16(data, struct_off + 2 * i) for i in range(4)]
        pos = struct_off + 8

        # Main deck
        main_count = self._read_u16(data, pos)
        pos += 2
        main_cards = []
        for _ in range(main_count):
            if pos + 2 > len(data):
                return None
            main_cards.append(self._read_u16(data, pos))
            pos += 2

        # Extra deck
        extra_count = self._read_u16(data, pos)
        pos += 2
        extra_cards = []
        for _ in range(extra_count):
            if pos + 2 > len(data):
                return None
            extra_cards.append(self._read_u16(data, pos))
            pos += 2

        # Terminator
        term = self._read_u16(data, pos) if pos + 2 <= len(data) else 0
        pos += 2

        original_size = pos - struct_off
        return DeckEntry(index, ptr_off, struct_off, unk_values, main_cards, extra_cards, original_size)

    def _encode_deck_structure(self, deck: DeckEntry) -> bytes:
        """
        Encode a DeckEntry back into raw bytes:

        unk0..unk3 (4x u16)
        main_count (u16)
        main_cards (u16 each)
        extra_count (u16)
        extra_cards (u16 each)
        0x0000 terminator (u16)
        """
        buf = bytearray()
        for val in deck.unk:
            buf += int(val & 0xFFFF).to_bytes(2, "little")

        main_count = len(deck.main_cards)
        extra_count = len(deck.extra_cards)

        buf += int(main_count & 0xFFFF).to_bytes(2, "little")
        for kid in deck.main_cards:
            buf += int(kid & 0xFFFF).to_bytes(2, "little")

        buf += int(extra_count & 0xFFFF).to_bytes(2, "little")
        for kid in deck.extra_cards:
            buf += int(kid & 0xFFFF).to_bytes(2, "little")

        buf += b"\x00\x00"  # terminator
        return bytes(buf)

    def _parse_packs(self):
        """
        Parse all packs from PACK_TABLE_BASE.
        """
        self.packs = []
        if self.rom_data is None:
            return

        data = self.rom_data
        for i in range(NUM_PACKS):
            struct_off = PACK_TABLE_BASE + i * PACK_ENTRY_SIZE
            if struct_off + PACK_ENTRY_SIZE > len(data):
                break

            cost           = self._read_u16(data, struct_off + 0)
            cards_per_pack = self._read_u16(data, struct_off + 2)
            card_amount    = self._read_u16(data, struct_off + 4)
            unk0           = self._read_u16(data, struct_off + 6)
            unk1           = self._read_u16(data, struct_off + 8)
            padding        = self._read_u16(data, struct_off + 10)
            ptr_val        = self._read_u32(data, struct_off + 12)
            ptr_off        = struct_off + 12

            if ptr_val == 0 or ptr_val == 0xFFFFFFFF:
                contents_off = -1
                contents = []
                original_size = 0
            else:
                contents_off = ptr_val - GBA_ROM_BASE
                contents = []
                original_size = 0

                if 0 <= contents_off < len(data):
                    pos = contents_off
                    for _ in range(card_amount):
                        if pos + 4 > len(data):
                            break
                        kid = self._read_u16(data, pos)
                        rar = self._read_u16(data, pos + 2)
                        contents.append((kid, rar))
                        pos += 4
                    original_size = pos - contents_off
                else:
                    contents_off = -1

            pack = PackEntry(
                index=i,
                struct_off=struct_off,
                ptr_off=ptr_off,
                cost=cost,
                cards_per_pack=cards_per_pack,
                card_amount=card_amount,
                unk0=unk0,
                unk1=unk1,
                padding=padding,
                contents_off=contents_off,
                contents=contents,
                original_contents_size=original_size,
            )
            self.packs.append(pack)

    def _encode_pack_contents(self, pack: PackEntry) -> bytes:
        """
        Encode pack contents: [ (konami_id, rarity) * cards_per_pack ]
        Each entry is 4 bytes: 2-byte Konami ID, 2-byte rarity index.
        """
        buf = bytearray()
        for i in range(pack.card_amount):
            if i < len(pack.contents):
                kid, rar = pack.contents[i]
            else:
                kid, rar = 0, 0
            buf += int(kid & 0xFFFF).to_bytes(2, "little")
            buf += int(rar & 0xFFFF).to_bytes(2, "little")
        return bytes(buf)

    def _write_pack_to_rom(self, pack: PackEntry):
        """
        Write a PackEntry to self.rom_data.
        Handles repointing contents if size grows beyond original.
        """
        if self.rom_data is None:
            return

        rom = self.rom_data

        # --- header ---
        off = pack.struct_off
        self._write_u16(rom, off + 0,  pack.cost & 0xFFFF)
        self._write_u16(rom, off + 2,  pack.cards_per_pack & 0xFFFF)
        self._write_u16(rom, off + 4,  pack.card_amount & 0xFFFF)
        self._write_u16(rom, off + 6,  pack.unk0 & 0xFFFF)
        self._write_u16(rom, off + 8,  pack.unk1 & 0xFFFF)
        self._write_u16(rom, off + 10, pack.padding & 0xFFFF)

        contents_blob = self._encode_pack_contents(pack)
        new_size = len(contents_blob)

        # contents_off may be -1 if pointer was invalid; treat as needing new space
        need_new_space = pack.contents_off < 0 or new_size > pack.original_contents_size

        if not need_new_space:
            # write in place
            write_off = pack.contents_off
            rom[write_off:write_off + new_size] = contents_blob
            # Optional: clear leftover
            leftover = pack.original_contents_size - new_size
            if leftover > 0:
                rom[write_off + new_size:write_off + pack.original_contents_size] = b"\xFF" * leftover
        else:
            # find new FF space
            new_off = self._find_free_space_ff(rom, new_size)
            if new_off is None:
                messagebox.showerror("Pack Editor", f"No free space for pack {pack.index}.")
                return

            # free old region if valid
            if pack.contents_off >= 0 and pack.original_contents_size > 0:
                rom[pack.contents_off:pack.contents_off + pack.original_contents_size] = (
                    b"\xFF" * pack.original_contents_size
                )

            # write new
            rom[new_off:new_off + new_size] = contents_blob

            # update pointer
            new_ptr_val = new_off + GBA_ROM_BASE
            self._write_u32(rom, pack.ptr_off, new_ptr_val)

            pack.contents_off = new_off
            pack.original_contents_size = new_size

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
        self._build_deck_card_choices()
        self._load_deck_names()
        self._load_rarities()
        self._load_pack_names()
        self._parse_packs()
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
    def _read_u32(data, offset):
        return int.from_bytes(data[offset:offset + 4], "little")

    @staticmethod
    def _write_u32(data, offset, value):
        data[offset:offset + 4] = int(value & 0xFFFFFFFF).to_bytes(4, "little")

    def _find_free_space_ff(self, rom_data, size, alignment=4):
        """
        Find a run of 0xFF bytes of at least 'size' **starting at an aligned offset**.

        alignment=4 means offsets end in 0, 4, 8, or C (4-byte aligned).
        """
        if size <= 0:
            return None
        if alignment <= 0:
            alignment = 1

        end = len(rom_data)
        # Start from the first aligned offset
        addr = FREE_SPACE_START
        if addr % alignment != 0:
            addr += alignment - (addr % alignment)

        while addr + size <= end:
            # Check this aligned candidate
            chunk = rom_data[addr:addr + size]
            if chunk and all(b == 0xFF for b in chunk):
                return addr

            # Move to the next aligned candidate
            addr += alignment

        return None

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

            # --- NEW: password + price (4 bytes each, indexed by card name index) ---
            pw_off = PASSWORD_TABLE_BASE + i * 4
            pw_raw = data[pw_off:pw_off + 4]

            # Reverse byte order
            pw_raw = pw_raw[::-1]

            digits = []
            for b in pw_raw:
                hi = (b >> 4) & 0xF
                lo = b & 0xF
                digits.append(str(hi if hi <= 9 else 0))
                digits.append(str(lo if lo <= 9 else 0))

            password = int("".join(digits))

            price_off = PRICE_TABLE_BASE    + i * PRICE_ENTRY_SIZE

            if price_off + 4 <= len(data):
                price = int.from_bytes(data[price_off:price_off + 4], "little")
            else:
                price = 0
            
            gfx_off = CARD_GFX_BASE + card_id_index * CARD_GFX_SIZE
            pal_off = CARD_PAL_BASE + card_id_index * CARD_PAL_SIZE
            if gfx_off + CARD_GFX_SIZE > len(self.rom_data) or pal_off + CARD_PAL_SIZE > len(self.rom_data):
                messagebox.showerror("Error", "Graphics/palette location out of ROM range.")
                return

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
                padding=padding,
                password=password,      # <<< new
                price=price,            # <<< new
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
            if not (0 <= card_name_index < NUM_CARD_GFX):
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

        # Build Konami ID -> card index mapping
        self.konami_to_card_index = {}
        for c in cards:
            if c.konami_id not in self.konami_to_card_index:
                self.konami_to_card_index[c.konami_id] = c.index

        # NEW: build password -> konami_id mapping
        self.password_to_konami = {}
        for c in cards:
            pw = getattr(c, "password", 0)
            if pw and isinstance(pw, int):
                # Don't overwrite if duplicates (shouldn't happen, but be safe)
                self.password_to_konami.setdefault(pw, c.konami_id)

        # Any card without second_stats_index keeps card_id_index2 as 0xFFFF (None)
        return cards

    def _build_deck_card_choices(self):
        """
        Build display list for deck editor: 'KonamiID: Name'.
        """
        self.deck_card_choices = []
        self.deck_card_choice_konami = []
        self.konami_to_deck_choice_index = {}

        # Sort by Konami ID
        sorted_cards = sorted(self.cards, key=lambda c: c.konami_id)

        for c in sorted_cards:
            name = c.name.replace("\n", " ")
            if len(name) > 30:
                name = name[:30] + "..."
            label = f"{c.konami_id:04d}: {name}"
            self.deck_card_choices.append(label)
            self.deck_card_choice_konami.append(c.konami_id)

        self.konami_to_deck_choice_index = {
            kid: idx for idx, kid in enumerate(self.deck_card_choice_konami)
        }

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
            self._write_password_and_price(rom_copy, card)

        # Make sure the currently-selected artwork row is flushed from the UI
        self._apply_artwork_ui_to_entry()

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
        card_name_idx = entry.card_name_index
        if 0 <= card_name_idx < len(self.artwork_names):
            self.artwork_card_var.set(self.artwork_names[card_name_idx])
        else:
            self.artwork_card_var.set("")

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

        # --- Misc Info: password + price ---
        # Show password as 8-digit zero-padded decimal (standard YGO style)
        self.password_var.set(f"{card.password:08d}")
        self.price_var.set(card.price)
        
        # --- NEW: sync Artwork tab to this card's Artwork # ---
        if self.artworks:
            art_idx = card.card_id_index
            if 0 <= art_idx < len(self.artworks):
                self._load_artwork_into_editor(art_idx)

        # --- NEW: render card artwork image ---
        self._render_card_image(card)
        self._render_card_icons(card)

        # --- Also persist Artwork tab changes for the current artwork slot ---
        self._apply_artwork_ui_to_entry()

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

    def _write_password_and_price(self, rom_data, card):
        # ----- Password: 8-digit decimal → 4 BCD bytes -----
        pw_off = PASSWORD_TABLE_BASE + card.index * PASSWORD_ENTRY_SIZE
        pw_text = f"{card.password:08d}"
        pw_bytes = bytearray()

        # Build four bytes from the editor string (forward order)
        for i in range(0, 8, 2):
            hi = int(pw_text[i])
            lo = int(pw_text[i + 1])
            pw_bytes.append((hi << 4) | lo)

        # Reverse *before writing to ROM*
        pw_bytes = pw_bytes[::-1]

        rom_data[pw_off:pw_off + 4] = pw_bytes

        # ----- Price (still plain little-endian 32-bit) -----
        price_off = PRICE_TABLE_BASE + card.index * PRICE_ENTRY_SIZE
        if price_off + 4 <= len(rom_data):
            rom_data[price_off:price_off + 4] = int(card.price & 0xFFFFFFFF).to_bytes(4, "little")

        # Price
        price_off = PRICE_TABLE_BASE + card.index * PRICE_ENTRY_SIZE
        if price_off + 4 <= len(rom_data):
            rom_data[price_off:price_off + 4] = int(card.price & 0xFFFFFFFF).to_bytes(4, "little")

    def _write_artwork_table(self, rom_data):
        for entry in self.artworks:
            off = ARTWORK_TABLE_BASE + entry.index * 4
            if off + 4 > len(rom_data):
                break

            # First halfword: unknown field
            self._write_u16(rom_data, off, entry.unk_halfword & 0xFFFF)

            # Second halfword: card name index or 0xFFFF
            idx = entry.card_name_index

            if idx is None or idx == 0xFFFF:
                self._write_u16(rom_data, off + 2, 0xFFFF)
            else:
                idx = int(idx)
                # Clamp to valid range; if bad, treat as "none"
                if not (0 <= idx < NUM_CARD_GFX):
                    idx = 0xFFFF
                self._write_u16(rom_data, off + 2, idx)

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

        # --- Misc Info from UI back into card ---
        pw_text = self.password_var.get().strip()
        if pw_text:
            # Accept only digits; keep old value on bad input
            try:
                pw_val = int(pw_text)
            except ValueError:
                pw_val = card.password
        else:
            pw_val = 0

        card.password = pw_val & 0xFFFFFFFF  # clamp to 32-bit

        try:
            price_val = int(self.price_var.get())
        except (ValueError, tk.TclError):
            price_val = card.price

        card.price = price_val & 0xFFFFFFFF

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

    def _build_pillow_icon_palette(self):
        """
        Build a Pillow 'P' image containing the 144-color icon palette
        from ICON_PAL_BASE (0x510440), padded to 256 colors.
        """
        pal_raw = self._get_icon_palette()
        if pal_raw is None:
            return None

        # GBA 15-bit color: 0-4 red, 5-9 green, 10-14 blue
        colors = []
        for i in range(0, len(pal_raw), 2):
            val = pal_raw[i] | (pal_raw[i + 1] << 8)
            r = (val & 0x1F) * 255 // 31
            g = ((val >> 5) & 0x1F) * 255 // 31
            b = ((val >> 10) & 0x1F) * 255 // 31
            colors.extend([r, g, b])

        # Pad to 256 entries
        while len(colors) < 256 * 3:
            colors.extend([0, 0, 0])

        pal_img = Image.new("P", (1, 1))
        pal_img.putpalette(colors)
        return pal_img
    
    def _quantize_to_icon_palette(self, img_rgb: Image.Image) -> Image.Image:
        """
        Takes an RGB image and quantizes it to the card icon palette at 0x510440.

        Requirements:
          - Palette index 0 is allowed (often background/transparent).
          - Palette indices 1–15 must NOT be used.
          - Palette indices 16–143 are valid.

        Implementation:
          - Build full icon palette from ROM.
          - Build a temporary palette:
              * entry 0   -> original palette[0]
              * entries 1..128 -> original palette[16..143]
          - Quantize against that temporary palette.
          - Remap:
              * 0   -> 0
              * 1..128 -> 16..143 (p -> p-1+16)
          - Attach original ROM palette and return.
        """
        pal_img = self._build_pillow_icon_palette()
        if pal_img is None:
            raise RuntimeError("Icon palette not available")

        full_pal = pal_img.getpalette()
        if full_pal is None or len(full_pal) < 256 * 3:
            raise RuntimeError("Icon palette is malformed")

        # --- Build restricted quantization palette ---
        # Keep original color 0 at index 0
        tmp_pal_list = []
        tmp_pal_list.extend(full_pal[0:3])  # palette index 0 (R,G,B)

        # Next 128 entries (1..128) = original 16..143
        tmp_pal_list.extend(full_pal[16 * 3:144 * 3])  # 128 * 3 bytes

        # Now we have 1 + 128 = 129 colors so far (0..128).
        # Pad to 256 entries so Pillow is happy.
        num_colors_so_far = 1 + 128
        tmp_pal_list.extend([0, 0, 0] * (256 - num_colors_so_far))

        tmp_pal_img = Image.new("P", (1, 1))
        tmp_pal_img.putpalette(tmp_pal_list)

        # Quantize using the restricted palette
        q = img_rgb.convert("RGB").quantize(
            palette=tmp_pal_img,
            dither=Image.NONE
        )

        # Remap indices:
        #   0      -> 0
        #   1..128 -> 16..143  (p -> p - 1 + 16)
        q_data = list(q.getdata())
        remapped = []
        for p in q_data:
            p = int(p)
            if p == 0:
                new_idx = 0
            elif 1 <= p <= 128:
                new_idx = (p - 1) + 16  # 16..143
            else:
                # Shouldn't happen, but clamp to 0 as a fallback
                new_idx = 0
            remapped.append(new_idx & 0xFF)

        out = Image.new("P", q.size)
        out.putdata(remapped)
        # Attach the original ROM icon palette so indices map correctly
        out.putpalette(full_pal)

        return out

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

        # --- Select PNG file ---
        img_path = filedialog.askopenfilename(
            title="Select card artwork PNG",
            filetypes=[("PNG Images", "*.png"), ("JPEG Images", "*.jpg"), ("All Files", "*.*")]
        )
        if not img_path:
            return

        try:
            img = Image.open(img_path)

            # JPGs have no alpha; PNGs may or may not.
            if img.mode not in ("RGB", "RGBA"):
                img = img.convert("RGBA")
            else:
                # If it's RGB (e.g., JPG), add alpha channel for consistency:
                if img.mode == "RGB":
                    img = img.convert("RGBA")

        except Exception as e:
            messagebox.showerror("Error", f"Failed to load image:\n{e}")
            return

        card = self.cards[self.current_index]
        self._import_card_graphics_from_pil(card, img)

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

class PackEditorWindow(tk.Toplevel):
    def __init__(self, app: RomEditorApp):
        super().__init__(app)
        self.app = app
        self.title("Yu-Gi-Oh! UM 2006 – Pack Editor")

        self.packs = app.packs
        self.current_pack_index = 0

        # Header vars
        self.cost_var = tk.IntVar()
        self.cards_per_pack_var = tk.IntVar()
        self.card_amount_var = tk.IntVar()
        self.unk0_var = tk.StringVar()
        self.unk1_var = tk.StringVar()
        self.padding_var = tk.StringVar()

        # Contents vars
        self.card_vars = []    # list[StringVar] for Konami IDs (dropdown labels)
        self.rarity_vars = []  # list[StringVar] rarity names

        self._build_ui()
        if self.packs:
            self._load_pack_into_editor(0)

    def _on_pack_selected(self, event):
        sel = self.pack_listbox.curselection()
        if not sel:
            return
        idx = sel[0]
        self._apply_ui_to_pack()
        self._load_pack_into_editor(idx)

    def _load_pack_into_editor(self, idx):
        if not (0 <= idx < len(self.packs)):
            return
        self.current_pack_index = idx
        pack = self.packs[idx]

        name = ""
        if 0 <= pack.index < len(self.app.pack_names):
            name = self.app.pack_names[pack.index].strip()
        if not name:
            name = f"Pack {pack.index}"

        self.pack_info_label.config(
            text=f"{name} (index {pack.index}) @ 0x{pack.struct_off:08X}"
        )

        # header
        self.cost_var.set(pack.cost)
        self.cards_per_pack_var.set(pack.cards_per_pack)
        self.card_amount_var.set(pack.card_amount)
        self.unk0_var.set(f"0x{pack.unk0:04X}")
        self.unk1_var.set(f"0x{pack.unk1:04X}")
        self.padding_var.set(f"0x{pack.padding:04X}")

        self._rebuild_contents()

        self.pack_listbox.selection_clear(0, tk.END)
        self.pack_listbox.selection_set(idx)
        self.pack_listbox.see(idx)

    def _on_card_amount_changed(self):
        self._apply_ui_to_pack()
        self._rebuild_contents()

    def _label_for_konami(self, kid):
        idx = self.app.konami_to_deck_choice_index.get(kid)
        if idx is not None:
            return self.app.deck_card_choices[idx]
        return f"{kid:04d}"

    def _filter_card_combo(self, event, combo: ttk.Combobox, var: tk.StringVar):
        pattern = var.get().lower()
        if not pattern:
            filtered = self.app.deck_card_choices
        else:
            filtered = [lbl for lbl in self.app.deck_card_choices if pattern in lbl.lower()]
        combo["values"] = filtered

    def _rebuild_contents(self):
        pack = self.packs[self.current_pack_index]

        # normalize contents length to card_amount
        n = max(0, self.card_amount_var.get())
        pack.card_amount = n

        while len(pack.contents) < n:
            default_kid = self.app.deck_card_choice_konami[0] if self.app.deck_card_choice_konami else 0
            pack.contents.append((default_kid, 0))
        pack.contents = pack.contents[:n]

        # clear old widgets
        for child in self.contents_inner.winfo_children():
            child.destroy()
        self.card_vars = []
        self.rarity_vars = []

        for i, (kid, rar) in enumerate(pack.contents):
            row = i
            tk.Label(self.contents_inner, text=f"{i+1:02d}").grid(row=row, column=0, sticky="e", padx=2, pady=1)

            # Card ID dropdown
            card_var = tk.StringVar()
            card_var.set(self._label_for_konami(kid))
            card_combo = ttk.Combobox(
                self.contents_inner,
                textvariable=card_var,
                values=self.app.deck_card_choices,
                width=30
            )
            card_combo.grid(row=row, column=1, sticky="w", padx=2, pady=1)
            card_combo.bind(
                "<KeyRelease>",
                lambda e, cb=card_combo, v=card_var: self._filter_card_combo(e, cb, v)
            )
            self.card_vars.append(card_var)

            # Rarity dropdown
            rarity_var = tk.StringVar()
            rar_idx = rar if 0 <= rar < len(self.app.rarities) else 0
            rarity_var.set(self.app.rarities[rar_idx])
            rar_combo = ttk.Combobox(
                self.contents_inner,
                textvariable=rarity_var,
                values=self.app.rarities,
                width=18,
                state="readonly"
            )
            rar_combo.grid(row=row, column=2, sticky="w", padx=2, pady=1)
            self.rarity_vars.append(rarity_var)

    def _apply_ui_to_pack(self):
        if not self.packs:
            return
        pack = self.packs[self.current_pack_index]

        # header
        try:
            pack.cost = int(self.cost_var.get()) & 0xFFFF
        except (ValueError, tk.TclError):
            pass

        try:
            cpp = int(self.cards_per_pack_var.get())
            pack.cards_per_pack = max(0, cpp) & 0xFFFF
        except (ValueError, tk.TclError):
            pass

        try:
            pack.card_amount = int(self.card_amount_var.get()) & 0xFFFF
        except (ValueError, tk.TclError):
            pass

        # hex fields
        def _parse_hex_or_dec(txt, default):
            txt = txt.strip()
            if not txt:
                return default
            if txt.lower().startswith("0x"):
                try:
                    return int(txt, 16) & 0xFFFF
                except ValueError:
                    return default
            try:
                return int(txt) & 0xFFFF
            except ValueError:
                return default

        pack.unk0 = _parse_hex_or_dec(self.unk0_var.get(), pack.unk0)
        pack.unk1 = _parse_hex_or_dec(self.unk1_var.get(), pack.unk1)
        pack.padding = _parse_hex_or_dec(self.padding_var.get(), pack.padding)

        # contents
        new_contents = []
        for card_var, rar_var in zip(self.card_vars, self.rarity_vars):
            lbl = card_var.get()
            if ":" in lbl:
                kid_txt = lbl.split(":", 1)[0].strip()
            else:
                kid_txt = lbl.strip()
            try:
                kid = int(kid_txt)
            except ValueError:
                kid = 0

            rar_name = rar_var.get()
            if rar_name in self.app.rarities:
                rar_idx = self.app.rarities.index(rar_name)
            else:
                rar_idx = 0

            new_contents.append((kid & 0xFFFF, rar_idx & 0xFFFF))

        pack.contents = new_contents[:pack.card_amount]

    def _on_save_clicked(self):
        self._apply_ui_to_pack()
        pack = self.packs[self.current_pack_index]
        self.app._write_pack_to_rom(pack)
        messagebox.showinfo("Pack Editor", f"Pack {pack.index} saved to ROM.")

    def _build_ui(self):
        main_frame = tk.Frame(self)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        # Left: pack list
        left_frame = tk.Frame(main_frame)
        left_frame.pack(side=tk.LEFT, fill=tk.Y)

        tk.Label(left_frame, text="Packs").pack(anchor="w")
        self.pack_listbox = tk.Listbox(left_frame, width=32, height=20)
        self.pack_listbox.pack(side=tk.LEFT, fill=tk.Y)
        sb = tk.Scrollbar(left_frame, orient=tk.VERTICAL, command=self.pack_listbox.yview)
        sb.pack(side=tk.RIGHT, fill=tk.Y)
        self.pack_listbox.config(yscrollcommand=sb.set)
        self.pack_listbox.bind("<<ListboxSelect>>", self._on_pack_selected)

        # populate
        for p in self.packs:
            name = ""
            if 0 <= p.index < len(self.app.pack_names):
                name = self.app.pack_names[p.index].strip()
            if not name:
                name = f"Pack {p.index}"
            self.pack_listbox.insert(tk.END, name)

        # Right: pack details
        right_frame = tk.Frame(main_frame)
        right_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(8, 0))

        self.pack_info_label = tk.Label(right_frame, text="No pack loaded")
        self.pack_info_label.pack(anchor="w")

        # Header fields
        header = tk.LabelFrame(right_frame, text="Pack Header")
        header.pack(fill=tk.X, pady=4)

        row = 0
        tk.Label(header, text="Cost:").grid(row=row, column=0, sticky="e")
        tk.Entry(header, textvariable=self.cost_var, width=8).grid(row=row, column=1, sticky="w", padx=2)
        tk.Label(header, text="Cards per pack:").grid(row=row, column=2, sticky="e")
        e_card_amount = tk.Entry(header, textvariable=self.cards_per_pack_var, width=8)
        e_card_amount.grid(row=row, column=3, sticky="w", padx=2)
        e_card_amount.bind("<FocusOut>", lambda e: self._on_card_amount_changed())
        row += 1

        tk.Label(header, text="Card amount:").grid(row=row, column=0, sticky="e")
        tk.Entry(header, textvariable=self.card_amount_var, width=8).grid(row=row, column=1, sticky="w", padx=2)

        tk.Label(header, text="Unk0:").grid(row=row, column=2, sticky="e")
        tk.Entry(header, textvariable=self.unk0_var, width=8).grid(row=row, column=3, sticky="w", padx=2)
        row += 1

        tk.Label(header, text="Unk1:").grid(row=row, column=0, sticky="e")
        tk.Entry(header, textvariable=self.unk1_var, width=8).grid(row=row, column=1, sticky="w", padx=2)
        tk.Label(header, text="Padding:").grid(row=row, column=2, sticky="e")
        tk.Entry(header, textvariable=self.padding_var, width=8).grid(row=row, column=3, sticky="w", padx=2)

        # Contents (scrollable)
        contents_outer = tk.Frame(right_frame)
        contents_outer.pack(fill=tk.BOTH, expand=True, pady=4)

        self.contents_canvas = tk.Canvas(contents_outer, borderwidth=0)
        self.contents_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        contents_scrollbar = tk.Scrollbar(
            contents_outer, orient="vertical", command=self.contents_canvas.yview
        )
        contents_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.contents_canvas.configure(yscrollcommand=contents_scrollbar.set)

        self.contents_inner = tk.Frame(self.contents_canvas)
        self.contents_canvas.create_window((0, 0), window=self.contents_inner, anchor="nw")

        def _on_inner_config(event):
            self.contents_canvas.configure(scrollregion=self.contents_canvas.bbox("all"))

        self.contents_inner.bind("<Configure>", _on_inner_config)

        # Buttons
        btn_frame = tk.Frame(right_frame)
        btn_frame.pack(fill=tk.X, pady=(6, 0))

        tk.Button(btn_frame, text="Save Pack Changes", command=self._on_save_clicked).pack(side=tk.LEFT)
        tk.Button(btn_frame, text="Close", command=self.destroy).pack(side=tk.RIGHT)

class DeckEditorWindow(tk.Toplevel):
    def __init__(self, app: RomEditorApp):
        super().__init__(app)
        self.app = app
        self.title("Yu-Gi-Oh! UM 2006 – Deck Editor")

        self.decks = app.decks
        self.current_deck_index = 0

        # UI state
        self.unk_vars = [tk.StringVar() for _ in range(4)]
        self.main_count_var = tk.IntVar()
        self.extra_count_var = tk.IntVar()
        self.main_card_vars = []   # list[StringVar]
        self.extra_card_vars = []  # list[StringVar]

        self._build_ui()
        if self.decks:
            self._load_deck_into_editor(0)

    def _filter_card_combo(self, event, combo: ttk.Combobox, var: tk.StringVar):
        """
        Filter card choices in this combobox based on current text.
        """
        pattern = var.get().lower()
        if not pattern:
            filtered = self.app.deck_card_choices
        else:
            filtered = [
                lbl for lbl in self.app.deck_card_choices
                if pattern in lbl.lower()
            ]
        combo["values"] = filtered
        # Optional: open dropdown as you type
        # combo.event_generate("<Down>")

    def _build_ui(self):
        main_frame = tk.Frame(self)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        # Left: deck list
        left_frame = tk.Frame(main_frame)
        left_frame.pack(side=tk.LEFT, fill=tk.Y)

        tk.Label(left_frame, text="Decks").pack(anchor="w")
        self.deck_listbox = tk.Listbox(left_frame, width=24, height=20)
        self.deck_listbox.pack(side=tk.LEFT, fill=tk.Y)
        sb = tk.Scrollbar(left_frame, orient=tk.VERTICAL, command=self.deck_listbox.yview)
        sb.pack(side=tk.RIGHT, fill=tk.Y)
        self.deck_listbox.config(yscrollcommand=sb.set)
        self.deck_listbox.bind("<<ListboxSelect>>", self._on_deck_selected)

        for d in self.decks:
            name = ""
            if 0 <= d.index < len(self.app.deck_names):
                name = self.app.deck_names[d.index].strip()
            if not name:
                name = f"Deck {d.index}"
            self.deck_listbox.insert(tk.END, name)

        # Right: deck details
        right_frame = tk.Frame(main_frame)
        right_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(8, 0))

        self.deck_info_label = tk.Label(right_frame, text="No deck loaded")
        self.deck_info_label.pack(anchor="w")

        # Unknowns
        unk_frame = tk.LabelFrame(right_frame, text="Unknown Header (8 bytes)")
        unk_frame.pack(fill=tk.X, pady=4)

        for i in range(4):
            tk.Label(unk_frame, text=f"unk{i}:").grid(row=0, column=2*i, sticky="e", padx=2)
            e = tk.Entry(unk_frame, textvariable=self.unk_vars[i], width=8)
            e.grid(row=0, column=2*i+1, sticky="w", padx=2)

        # Counts
        counts_frame = tk.Frame(right_frame)
        counts_frame.pack(fill=tk.X, pady=4)

        tk.Label(counts_frame, text="Main count:").grid(row=0, column=0, sticky="e")
        main_entry = tk.Entry(counts_frame, textvariable=self.main_count_var, width=5)
        main_entry.grid(row=0, column=1, sticky="w", padx=2)
        main_entry.bind("<FocusOut>", lambda e: self._on_counts_changed())

        tk.Label(counts_frame, text="Extra count:").grid(row=0, column=2, sticky="e")
        extra_entry = tk.Entry(counts_frame, textvariable=self.extra_count_var, width=5)
        extra_entry.grid(row=0, column=3, sticky="w", padx=2)
        extra_entry.bind("<FocusOut>", lambda e: self._on_counts_changed())

        # Card lists (scrollable)
        lists_outer = tk.Frame(right_frame)
        lists_outer.pack(fill=tk.BOTH, expand=True, pady=4)

        self.lists_canvas = tk.Canvas(lists_outer, borderwidth=0)
        self.lists_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        lists_scrollbar = tk.Scrollbar(
            lists_outer,
            orient="vertical",
            command=self.lists_canvas.yview
        )
        lists_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        self.lists_canvas.configure(yscrollcommand=lists_scrollbar.set)

        # Inner frame that actually holds the main/extra frames
        self.lists_inner = tk.Frame(self.lists_canvas)
        self.lists_canvas.create_window((0, 0), window=self.lists_inner, anchor="nw")

        def _on_inner_config(event):
            # Update scrollregion when content size changes
            self.lists_canvas.configure(scrollregion=self.lists_canvas.bbox("all"))

        self.lists_inner.bind("<Configure>", _on_inner_config)

        # Now create main/extra frames inside the inner frame
        self.main_cards_frame = tk.LabelFrame(self.lists_inner, text="Main Deck")
        self.main_cards_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 4))

        self.extra_cards_frame = tk.LabelFrame(self.lists_inner, text="Extra Deck")
        self.extra_cards_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(4, 0))

        # Bottom: buttons
        btn_frame = tk.Frame(right_frame)
        btn_frame.pack(fill=tk.X, pady=(6, 0))

        tk.Button(
            btn_frame,
            text="Import YDK...",
            command=self._import_ydk
        ).pack(side=tk.LEFT)

        tk.Button(
            btn_frame,
            text="Save Deck Changes",
            command=self._on_save_clicked
        ).pack(side=tk.LEFT, padx=(4, 0))

        tk.Button(
            btn_frame,
            text="Close",
            command=self.destroy
        ).pack(side=tk.RIGHT)

    def _parse_ydk_file(self, path):
        """
        Parse a .ydk file and return (main_pw_list, extra_pw_list),
        where each list contains integer passwords from #main / #extra.
        """
        main_pw = []
        extra_pw = []
        section = None

        try:
            with open(path, "r", encoding="utf-8", errors="ignore") as f:
                for line in f:
                    line = line.strip()
                    if not line:
                        continue

                    # Strip full-line comments beginning with --
                    if line.startswith("--"):
                        continue

                    # Strip inline comments after --
                    comment_pos = line.find("--")
                    if comment_pos != -1:
                        line = line[:comment_pos].strip()
                        if not line:
                            continue  # Line becomes empty after removing comment

                    # YDK section markers (#main, #extra, #side)
                    if line.startswith("#"):
                        if line.lower() == "#main":
                            section = "main"
                        elif line.lower() == "#extra":
                            section = "extra"
                        elif line.lower() == "#side":
                            section = None  # ignore side deck
                        continue

                    # Some YDK variants mark comments with '!'
                    if line.startswith("!"):
                        continue

                    # Now read card-password lines if we're in #main or #extra
                    if section in ("main", "extra"):
                        if line.isdigit():
                            val = int(line)
                            if section == "main":
                                main_pw.append(val)
                            else:
                                extra_pw.append(val)
        except Exception as e:
            messagebox.showerror("YDK Error", f"Failed to read YDK file:\n{e}")
            return [], []

        return main_pw, extra_pw

    def _import_ydk(self):
        """
        Import card passwords from a .ydk file and fill the current deck:
          - #main  -> main deck slots
          - #extra -> extra deck slots

        For each YDK password:
          - if it matches a ROM card password, we get its Konami ID
          - we write that Konami ID into the first available slot
            (0 or 0xFFFF) in main/extra
          - if no free slot exists, we expand the deck by adding a slot
        """
        if not self.decks:
            messagebox.showinfo("Deck Editor", "No decks available.")
            return

        deck = self.decks[self.current_deck_index]

        # Make sure we have the latest UI->deck values
        self._apply_ui_to_deck()

        path = filedialog.askopenfilename(
            title="Select YDK deck file",
            filetypes=[("YGOPro Deck Files", "*.ydk"), ("All Files", "*.*")]
        )
        if not path:
            return

        main_pw, extra_pw = self._parse_ydk_file(path)
        app = self.app

        if not main_pw and not extra_pw:
            messagebox.showinfo("YDK Import", "No #main or #extra cards found in the YDK file.")
            return

        # --- Helper to fill deck slots given a list of passwords + target list ---

        def fill_deck_slots_sequential(pw_list, cards_list):
            """
            For each password (in order):
              - convert to Konami ID using app.password_to_konami
              - replace cards_list[target_index] starting from 0
              - if target_index >= len(cards_list), append (expand deck)
              - passwords that don't exist in the ROM are skipped and do NOT
                advance target_index.
            """
            changed = False
            target_index = 0

            for pw in pw_list:
                konami_id = app.password_to_konami.get(pw)
                if konami_id is None:
                    # Not present in this ROM; skip without advancing target_index
                    continue

                if target_index < len(cards_list):
                    cards_list[target_index] = konami_id & 0xFFFF
                else:
                    cards_list.append(konami_id & 0xFFFF)

                target_index += 1
                changed = True

            return changed

        # Fill main and extra lists
        main_changed = fill_deck_slots_sequential(main_pw, deck.main_cards)
        extra_changed = fill_deck_slots_sequential(extra_pw, deck.extra_cards)

        if not (main_changed or extra_changed):
            messagebox.showinfo(
                "YDK Import",
                "No cards from the YDK file matched any passwords in this ROM."
            )
            return

        # Update counts based on new sizes
        self.main_count_var.set(len(deck.main_cards))
        self.extra_count_var.set(len(deck.extra_cards))

        # Rebuild UI lists to reflect changes
        self._rebuild_card_lists()

        messagebox.showinfo("YDK Import", "YDK deck imported into current deck.")

    # ---- deck loading ----

    def _on_deck_selected(self, event):
        sel = self.deck_listbox.curselection()
        if not sel:
            return
        idx = sel[0]
        self._apply_ui_to_deck()
        self._load_deck_into_editor(idx)

    def _load_deck_into_editor(self, idx):
        if not (0 <= idx < len(self.decks)):
            return
        self.current_deck_index = idx
        deck = self.decks[idx]

        name = ""
        if 0 <= deck.index < len(self.app.deck_names):
            name = self.app.deck_names[deck.index].strip()
        if not name:
            name = f"Deck {deck.index}"

        self.deck_info_label.config(
            text=f"{name} (index {deck.index}) @ 0x{deck.struct_off:08X} (size {deck.original_size} bytes)"
        )

        # Unknowns as hex
        for i in range(4):
            self.unk_vars[i].set(f"0x{deck.unk[i]:04X}")

        self.main_count_var.set(len(deck.main_cards))
        self.extra_count_var.set(len(deck.extra_cards))

        self._rebuild_card_lists()

        # select in listbox
        self.deck_listbox.selection_clear(0, tk.END)
        self.deck_listbox.selection_set(idx)
        self.deck_listbox.see(idx)

    def _on_counts_changed(self):
        self._apply_ui_to_deck()
        self._rebuild_card_lists()

    def _rebuild_card_lists(self):
        deck = self.decks[self.current_deck_index]

        # Normalize counts vs list lengths
        main_count = max(0, self.main_count_var.get())
        extra_count = max(0, self.extra_count_var.get())

        # Grow / shrink lists to match counts
        while len(deck.main_cards) < main_count:
            # default to first known Konami ID
            if self.app.deck_card_choice_konami:
                deck.main_cards.append(self.app.deck_card_choice_konami[0])
            else:
                deck.main_cards.append(0)
        deck.main_cards = deck.main_cards[:main_count]

        while len(deck.extra_cards) < extra_count:
            if self.app.deck_card_choice_konami:
                deck.extra_cards.append(self.app.deck_card_choice_konami[0])
            else:
                deck.extra_cards.append(0)
        deck.extra_cards = deck.extra_cards[:extra_count]

        # Clear frames
        for child in self.main_cards_frame.winfo_children():
            child.destroy()
        for child in self.extra_cards_frame.winfo_children():
            child.destroy()

        self.main_card_vars = []
        self.extra_card_vars = []

        # Build main deck rows
        for i, kid in enumerate(deck.main_cards):
            row = i
            tk.Label(self.main_cards_frame, text=f"{i+1:02d}").grid(row=row, column=0, sticky="e", padx=2, pady=1)
            var = tk.StringVar()
            label = self._label_for_konami(kid)
            var.set(label)
            cmb = ttk.Combobox(
                self.main_cards_frame,
                textvariable=var,
                values=self.app.deck_card_choices,
                width=30
            )
            cmb.grid(row=row, column=1, sticky="w", padx=2, pady=1)
            # Filter on typing
            cmb.bind(
                "<KeyRelease>",
                lambda e, cb=cmb, v=var: self._filter_card_combo(e, cb, v)
            )
            self.main_card_vars.append(var)

        # Build extra deck rows
        for i, kid in enumerate(deck.extra_cards):
            row = i
            tk.Label(self.extra_cards_frame, text=f"{i+1:02d}").grid(row=row, column=0, sticky="e", padx=2, pady=1)
            var = tk.StringVar()
            label = self._label_for_konami(kid)
            var.set(label)
            cmb = ttk.Combobox(
                self.extra_cards_frame,
                textvariable=var,
                values=self.app.deck_card_choices,
                width=30
            )
            cmb.grid(row=row, column=1, sticky="w", padx=2, pady=1)
            cmb.bind(
                "<KeyRelease>",
                lambda e, cb=cmb, v=var: self._filter_card_combo(e, cb, v)
            )
            self.extra_card_vars.append(var)

    def _label_for_konami(self, kid):
        # Use the prebuilt choices if we know where this Konami ID lives
        idx = self.app.konami_to_deck_choice_index.get(kid)
        if idx is not None:
            return self.app.deck_card_choices[idx]
        # Fallback: raw ID
        return f"{kid:04d}"

    # ---- apply UI → DeckEntry ----

    def _apply_ui_to_deck(self):
        if not self.decks:
            return
        deck = self.decks[self.current_deck_index]

        # Unknowns: accept hex like 0x1234 or decimal
        for i in range(4):
            txt = self.unk_vars[i].get().strip()
            if txt.lower().startswith("0x"):
                try:
                    deck.unk[i] = int(txt, 16) & 0xFFFF
                except ValueError:
                    pass
            else:
                try:
                    deck.unk[i] = int(txt) & 0xFFFF
                except ValueError:
                    pass

        # Counts already normalized in _rebuild_card_lists

        # Main cards
        new_main = []
        for var in self.main_card_vars:
            lbl = var.get()
            if ":" in lbl:
                kid_txt = lbl.split(":", 1)[0].strip()
            else:
                kid_txt = lbl.strip()
            try:
                kid = int(kid_txt)
            except ValueError:
                kid = 0
            new_main.append(kid & 0xFFFF)
        deck.main_cards = new_main

        # Extra cards
        new_extra = []
        for var in self.extra_card_vars:
            lbl = var.get()
            if ":" in lbl:
                kid_txt = lbl.split(":", 1)[0].strip()
            else:
                kid_txt = lbl.strip()
            try:
                kid = int(kid_txt)
            except ValueError:
                kid = 0
            new_extra.append(kid & 0xFFFF)
        deck.extra_cards = new_extra

    def _on_save_clicked(self):
        self._apply_ui_to_deck()
        deck = self.decks[self.current_deck_index]
        self.app._write_deck_to_rom(deck)
        messagebox.showinfo("Deck Editor", f"Deck {deck.index} saved to ROM.")


if __name__ == "__main__":
    app = RomEditorApp()
    app.mainloop()
