#!/usr/bin/env python3
"""
tile_palette_tool.py

Two-stage tool for duelist-coinflip-style backgrounds:

1) quantize:
   - Use 4 * 16-color palettes (64 total colors) to convert any image
     into a 64-color indexed PNG.
   - For each 8x8 tile, choose the palette bank (0..3) that best fits
     that tile (min total RGB error), and map each pixel in that tile
     into that palette's 16 colors.
   - Output is a paletted PNG with exactly those 64 colors.

2) mapbin:
   - Read the quantized PNG.
   - For each 8x8 tile, look only at the FIRST pixel in the tile.
     Its palette index (0..63) determines the palette bank:
         bank = index // 16
     and thus the high byte to store:
         high = bank * 0x10
   - Open an existing .bin that has 2 bytes per pixel (same size as
     the image), and for *every pixel* in that tile, update the
     second byte to 'high'. Low bytes remain unchanged.
   - Write patched .bin.

Assumptions:
- Palette source is a 64-color paletted PNG (mode "P") where entries 0..63
  are the 4 banks of 16 colors each:
    0-15  -> bank 0
    16-31 -> bank 1
    32-47 -> bank 2
    48-63 -> bank 3
- Images have width & height multiples of 8.
- .bin length == 2 * (image_width * image_height).
"""

import argparse
from pathlib import Path
from typing import List, Tuple

from PIL import Image


# ---------- Shared helpers ----------

def load_palette64(pal_path: Path) -> List[Tuple[int, int, int]]:
    """
    Load a paletted PNG with at least 64 entries and return the first 64 as (R,G,B).
    """
    pal_img = Image.open(pal_path)
    if pal_img.mode != "P":
        raise SystemExit(f"Palette PNG {pal_path} must be in 'P' (paletted) mode.")
    pal = pal_img.getpalette()
    if pal is None or len(pal) < 64 * 3:
        raise SystemExit("Palette PNG must contain at least 64 palette entries.")
    colors = []
    for i in range(64):
        r, g, b = pal[3*i:3*i+3]
        colors.append((r, g, b))
    return colors


def rgb_distance_sq(c1: Tuple[int, int, int], c2: Tuple[int, int, int]) -> int:
    dr = c1[0] - c2[0]
    dg = c1[1] - c2[1]
    db = c1[2] - c2[2]
    return dr*dr + dg*dg + db*db


# ---------- quantize command ----------

def cmd_quantize(args: argparse.Namespace) -> None:
    src_path = Path(args.input)
    pal_path = Path(args.palette)
    out_path = Path(args.output)

    # Load target palette (64 colors, 4 banks of 16)
    palette64 = load_palette64(pal_path)
    banks = [palette64[i*16:(i+1)*16] for i in range(4)]  # 4 lists of 16 colors

    # Load source image, convert to RGB
    src_img = Image.open(src_path).convert("RGB")
    w, h = src_img.size
    if w % 8 != 0 or h % 8 != 0:
        raise SystemExit(f"Image size {w}x{h} is not multiple of 8.")

    src_pixels = list(src_img.getdata())

    # We'll build a new indexed image with 64-color palette
    out_img = Image.new("P", (w, h))
    # Flatten palette64 to [R,G,B,...]
    flat_palette = []
    for (r, g, b) in palette64:
        flat_palette.extend([r, g, b])
    # pad palette to 256 entries for PNG
    flat_palette.extend([0, 0, 0] * (256 - 64))
    out_img.putpalette(flat_palette)

    out_data = [0] * (w * h)

    tiles_x = w // 8
    tiles_y = h // 8

    # For each 8x8 tile, pick best bank and map pixels
    for ty in range(tiles_y):
        for tx in range(tiles_x):
            # Gather pixels for this tile
            tile_indices = []
            tile_colors = []
            for y in range(8):
                for x in range(8):
                    ix = (ty*8 + y) * w + (tx*8 + x)
                    tile_indices.append(ix)
                    tile_colors.append(src_pixels[ix])

            # For each bank, compute total error
            best_bank = 0
            best_error = None
            best_per_pixel_indices = None  # per-pixel index within bank

            for bank_id, bank_colors in enumerate(banks):
                total_error = 0
                per_pixel_idx = []

                for c in tile_colors:
                    # find nearest color within this bank's 16 colors
                    best_idx = 0
                    best_dist = None
                    for idx_in_bank, pal_color in enumerate(bank_colors):
                        d = rgb_distance_sq(c, pal_color)
                        if best_dist is None or d < best_dist:
                            best_dist = d
                            best_idx = idx_in_bank
                    per_pixel_idx.append(best_idx)
                    total_error += best_dist

                if best_error is None or total_error < best_error:
                    best_error = total_error
                    best_bank = bank_id
                    best_per_pixel_indices = per_pixel_idx

            # Now assign output indices for this tile
            for local_i, ix in enumerate(tile_indices):
                idx_in_bank = best_per_pixel_indices[local_i]
                global_index = best_bank * 16 + idx_in_bank  # 0..63
                out_data[ix] = global_index

    out_img.putdata(out_data)
    out_img.save(out_path)
    print(f"Quantized image saved to: {out_path}")


# ---------- mapbin command ----------

def cmd_mapbin(args: argparse.Namespace) -> None:
    png_path = Path(args.image)
    bin_in_path = Path(args.bin_in)
    bin_out_path = Path(args.bin_out)

    # Load quantized PNG
    img = Image.open(png_path)
    if img.mode != "P":
        raise SystemExit(f"Image {png_path} must be paletted ('P') for mapbin.")
    w, h = img.size
    if w % 8 != 0 or h % 8 != 0:
        raise SystemExit(f"Image size {w}x{h} is not multiple of 8.")

    pixels = list(img.getdata())

    tiles_x = w // 8
    tiles_y = h // 8
    num_tiles = tiles_x * tiles_y

    # Load existing bin (2 bytes per 8x8 tile)
    data = bytearray(bin_in_path.read_bytes())
    expected_len = num_tiles * 2
    if len(data) < expected_len:
        raise SystemExit(
            f"Bin file too small: {len(data)} bytes; "
            f"need at least {expected_len} bytes for {num_tiles} tiles."
        )

    # For each tile:
    #   - Look at the FIRST pixel of the tile to determine palette bank
    #   - bank = (index // 16)
    #   - Write (bank * 0x10) into the second byte of that tile's 2-byte entry.
    #
    # Tile index t = ty * tiles_x + tx
    #   -> entry at offsets (2*t, 2*t+1)
    for ty in range(tiles_y):
        for tx in range(tiles_x):
            tile_index = ty * tiles_x + tx

            # First pixel index of this tile in the image
            p0 = (ty * 8) * w + (tx * 8)
            idx0 = pixels[p0]
            if not isinstance(idx0, int):
                idx0 = int(idx0)

            bank = (idx0 // 16) & 0xFF  # 0..3
            high_byte = (bank * 0x10) & 0xFF

            # Second byte of tile's 2-byte entry
            byte_index = 2 * tile_index + 1
            if byte_index >= len(data):
                # Safety check; shouldn't happen if length check passed
                continue
            data[byte_index] = data[byte_index] + high_byte

    bin_out_path.write_bytes(data)
    print(
        f"Patched bin written to: {bin_out_path} "
        f"(length {len(data)} bytes, 0x{len(data):X})"
    )


# ---------- CLI ----------

def build_argparser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        description="Tile palette quantizer + bin palette mapping tool."
    )
    sub = p.add_subparsers(dest="command", required=True)

    # quantize subcommand
    p_q = sub.add_parser(
        "quantize",
        help="Quantize an image using 4x16-color palettes on 8x8 tiles."
    )
    p_q.add_argument("input", help="Input image (any mode, will be converted to RGB)")
    p_q.add_argument("palette", help="64-color palette PNG (mode 'P')")
    p_q.add_argument("output", help="Output 64-color indexed PNG")
    p_q.set_defaults(func=cmd_quantize)

    # mapbin subcommand
    p_m = sub.add_parser(
        "mapbin",
        help="Update an existing bin's per-pixel palette bytes from a quantized PNG."
    )
    p_m.add_argument("image", help="Quantized 64-color PNG used to derive palette banks")
    p_m.add_argument("bin_in", help="Existing .bin file (2 bytes per pixel)")
    p_m.add_argument("bin_out", help="Output .bin file (patched)")
    p_m.set_defaults(func=cmd_mapbin)

    return p


def main():
    parser = build_argparser()
    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
