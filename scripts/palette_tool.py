#!/usr/bin/env python3
"""
coinflip_palette_tool.py

Tool for analyzing and remapping 4bpp-style multi-palette PNGs
used for duelist coinflip wallpaper backgrounds.

Assumptions:
- PNG is paletted (P mode) with up to 64 colors.
- Palette entries 0–15 = palette 1, 16–31 = palette 2,
  32–47 = palette 3, 48–63 = palette 4.
- The engine switches between the 4 palettes per tile via tilemap.

Commands:
  analyze  - show which palette bank and index each color uses
  reindex  - remap indices so that 0–15 all palettes collapse to 0–15
             (16–31 -> -16, 32–47 -> -32, 48–63 -> -48).
"""

import argparse
from collections import Counter
from pathlib import Path

from PIL import Image


def load_paletted_image(path: Path) -> Image.Image:
    """Load an image and ensure it's in paletted (P) mode."""
    img = Image.open(path)
    if img.mode != "P":
        # Best-effort conversion to paletted mode
        img = img.convert("P", palette=Image.ADAPTIVE, colors=256)
    return img


def cmd_analyze(args: argparse.Namespace) -> None:
    """
    Analyze a paletted PNG and print which palette bank each used index belongs to.
    Palette bank is 1–4, index-in-bank is 0–15.
    """
    img_path = Path(args.input)
    img = load_paletted_image(img_path)
    palette = img.getpalette()
    data = list(img.getdata())
    counts = Counter(data)
    used_indices = sorted(counts.keys())

    print(f"Image: {img_path}")
    print(f"Mode: {img.mode}, Size: {img.size[0]}x{img.size[1]}")
    print()
    print("Idx  Bank  In-Bank  RGB       PixelCount")
    print("-----------------------------------------")

    for idx in used_indices:
        bank = (idx // 16) + 1          # 1..4
        in_bank = idx % 16              # 0..15
        r, g, b = palette[3 * idx:3 * idx + 3]
        print(
            f"{idx:3d}   {bank:4d}   {in_bank:7d}   "
            f"#{r:02X}{g:02X}{b:02X}   {counts[idx]}"
        )


def cmd_reindex(args: argparse.Namespace) -> None:
    """
    Reindex palette indices so that:
      0–15  stay 0–15
      16–31 -> minus 16
      32–47 -> minus 32
      48–63 -> minus 48
    i.e. new_index = old_index % 16

    This makes the indices line up with a single 16-color 4bpp palette.

    NOTE: This does NOT adjust the PNG's palette colors, only the indices.
    So the resulting PNG will look wrong visually, but the indices will be
    correct for exporting raw 4bpp data while using per-tile palette banks
    in the game.
    """
    in_path = Path(args.input)
    out_path = Path(args.output)

    img = load_paletted_image(in_path)
    data = list(img.getdata())

    new_data = []
    for idx in data:
        # Only care about first 64; anything beyond also collapsed mod 16
        new_idx = idx % 16
        new_data.append(new_idx)

    img.putdata(new_data)

    # Optionally, you can also clamp the palette to its first 16 entries
    # so the preview isn't completely wild; but that would destroy info
    # about the other banks' colors. Here we leave the palette as-is.
    # If you want, uncomment this to zero out entries 16+:
    #
    # pal = img.getpalette()
    # for i in range(16, 256):
    #     pal[3*i:3*i+3] = [0, 0, 0]
    # img.putpalette(pal)

    img.save(out_path)
    print(f"Reindexed image saved to: {out_path}")


def build_argparser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        description="Duelist coinflip background palette/indices tool"
    )
    sub = p.add_subparsers(dest="command", required=True)

    # analyze
    p_an = sub.add_parser(
        "analyze",
        help="Show which palette bank and index each color uses"
    )
    p_an.add_argument("input", help="Input PNG file")
    p_an.set_defaults(func=cmd_analyze)

    # reindex
    p_re = sub.add_parser(
        "reindex",
        help="Reindex palette indices so all banks collapse to 0–15 (for 4bpp export)"
    )
    p_re.add_argument("input", help="Input PNG file")
    p_re.add_argument("output", help="Output PNG file")
    p_re.set_defaults(func=cmd_reindex)

    return p


def main():
    parser = build_argparser()
    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
