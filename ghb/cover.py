"""The covers: one hue for each volume, and a grid with one square for each chapter of the plan. A square is
filled by the words of its chapter against the target of the chapter (spec 09.3)."""

from __future__ import annotations

import textwrap

from .fonts import _find, ensure_fonts
from .util import volume_hue

BOOK = "THE GRH LEAN HANDBOOK"
SITE = "github.com/tamnd/grh-lean-handbook"


def _rgb(hexs: str):
    return tuple(int(hexs[i:i + 2], 16) for i in (0, 2, 4))


def cover_png(number: int | None, title: str, summary: str, squares: list[float], edition: str, path: str,
              w: int = 1600, h: int = 2286):
    from PIL import Image, ImageDraw, ImageFont
    ensure_fonts()
    hue = _rgb(volume_hue(number or 0))
    img = Image.new("RGB", (w, h), hue)
    d = ImageDraw.Draw(img)
    sans_b = lambda s: ImageFont.truetype(_find("LibertinusSans-Bold.otf"), s)
    sans = lambda s: ImageFont.truetype(_find("LibertinusSans-Regular.otf"), s)
    serif_i = lambda s: ImageFont.truetype(_find("LibertinusSerif-Italic.otf"), s)
    white = (255, 255, 255)
    soft = tuple(int(c + (255 - c) * 0.55) for c in hue)
    m = 130
    cols, size, gap = 8, 110, 24
    rows = -(-len(squares) // cols) if squares else 0
    y0 = h - m - 140 - rows * (size + gap)
    for i, frac in enumerate(squares):
        r, c = divmod(i, cols)
        x, y = m + c * (size + gap), y0 + r * (size + gap)
        d.rectangle([x, y, x + size, y + size], outline=soft, width=3)
        if frac:
            d.rectangle([x, y + size - int(size * frac), x + size, y + size], fill=soft)
    d.rectangle([m, m, w - m, m + 14], fill=white)
    d.text((m, m + 60), BOOK, font=sans(46), fill=white)
    if number is not None:
        d.text((m, 520), f"Volume {number}", font=sans_b(84), fill=soft)
    # the largest title size at which the title and the summary fit above the grid
    for fs in (170, 140, 120, 100, 84):
        tl = textwrap.wrap(title, max(8, int(14 * 170 / fs)))
        sl = textwrap.wrap(summary.strip(), 40)
        if 630 + len(tl) * fs * 1.12 + 30 + len(sl) * 72 < y0 - 60:
            break
    y = 630
    for line in tl:
        d.text((m, y), line, font=sans_b(fs), fill=white)
        y += int(fs * 1.12)
    y += 30
    for line in sl:
        if y > y0 - 120:
            break
        d.text((m, y), line, font=serif_i(58), fill=soft)
        y += 72
    d.text((m, h - m - 40), f"Edition {edition}  ·  {SITE}", font=sans(42), fill=soft)
    img.save(path)
    return path
