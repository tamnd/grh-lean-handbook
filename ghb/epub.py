"""The EPUB of a volume: the Markdown of the volume → pandoc → EPUB 3 with MathML. Each chapter is a file of
its own. The filter puts the number of a heading in front of its text. The front pages (the copyright page and
"About this edition") come first; pandoc makes the title page from the metadata."""

from __future__ import annotations

import os
import re
import subprocess
import time
import zipfile

from .cover import cover_png
from .util import volume_hue

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BOOK = "The GRH Lean Handbook"
REPO = "https://github.com/tamnd/grh-lean-handbook"


def volume_css(number: int, outdir: str) -> str:
    """tex/epub.css with the blue of the template replaced by the hue of the volume."""
    hue = volume_hue(number)
    rgb = [int(hue[i:i + 2], 16) for i in (0, 2, 4)]
    dark = "".join(f"{int(c * 0.75):02X}" for c in rgb)
    tint = "".join(f"{int(c + (255 - c) * 0.94):02X}" for c in rgb)
    soft = "".join(f"{int(c + (255 - c) * 0.6):02X}" for c in rgb)
    css = open(os.path.join(ROOT, "tex", "epub.css")).read()
    css = (css.replace("#2B59C3", f"#{hue}").replace("#20448f", f"#{dark}")
              .replace("#F1F4FB", f"#{tint}").replace("#A9B9E3", f"#{soft}"))
    path = os.path.join(outdir, "epub.css")
    open(path, "w").write(css)
    return path


def metadata(book, vol, edition: str, date: str) -> str:
    q = lambda s: s.replace('"', '\\"')
    tfm = book.front.get("title", ({}, ""))[0]
    if vol is None:
        title, sub, ident = tfm.get("title", BOOK), str(tfm.get("subtitle", "")), "front"
        desc = sub
    else:
        title, sub, ident = vol.title, f"{BOOK}, Volume {vol.number}", f"{vol.number:02d}-{vol.id}"
        desc = vol.summary
    return f"""---
title:
- type: main
  text: "{q(title)}"
- type: subtitle
  text: "{q(sub)}"
creator:
- role: author
  text: "The grh-lean-handbook contributors"
publisher: "github.com/tamnd/grh-lean-handbook"
date: "{date}"
lang: en
identifier:
- scheme: URI
  text: "{REPO}/releases/tag/v{edition}#{ident}"
rights: "Text CC BY 4.0; builder MIT. Edition {edition}. Source lsernau/grh-lean at commit {book.pin[:12]}."
description: "{q(desc)}"
subject: "Number theory"
...
"""


def front_md(book, vol, edition: str, date: str) -> str:
    values = book.front_values(vol, edition, date)
    _, cbody = book.front_md("copyright", values)
    efm, ebody = book.front_md("edition", values)
    return (f"# Copyright {{#front-copyright .unnumbered .unlisted}}\n\n{cbody}\n\n"
            f"# {efm.get('title', 'About this edition')} {{#front-edition .unnumbered}}\n\n{ebody}\n")


# TeX that pandoc's MathML writer (texmath) cannot read and prints as source. XeTeX reads all of it; the EPUB
# gets equivalent forms: `{n \atop k}` (Stirling and Eulerian numbers), `\xRightarrow{a}`, `\textsc{update}` (a
# procedure name; MathML has no small capitals, so capitals), `{\rm best}`, `\cfrac`, `\tbinom` and `\bmod`.
_MATH = re.compile(r"\$\$.*?\$\$|(?<![\\$])\$[^$\n]+\$", re.S)
_MATHML = [
    (re.compile(r"(?<!\\)\{\s*([^{}$]*?)\s*\\atop\s*([^{}$]*?)\s*(?<!\\)\}"),
     lambda m: "{\\begin{matrix}" + m[1] + "\\\\" + m[2] + "\\end{matrix}}"),
    (re.compile(r"(\\left(?:\\[A-Za-z]+|\\.|.))\s*([^{}$]*?)\s*\\atop\s*([^{}$]*?)\s*(\\right(?:\\[A-Za-z]+|\\.|.))"),
     lambda m: m[1] + " \\begin{matrix}" + m[2] + "\\\\" + m[3] + "\\end{matrix} " + m[4]),
    (re.compile(r"\\texttt\{([^{}$]*)\}"), lambda m: "\\texttt{" + m[1].replace("\\dots", "...") + "}"),
    (re.compile(r"\\dbinom(?![A-Za-z])"), lambda m: "\\binom"),
    (re.compile(r"\\xRightarrow\{([^{}$]*)\}"), lambda m: "\\overset{" + m[1] + "}{\\Rightarrow}"),
    (re.compile(r"\\textsc\{([^{}$]*)\}"), lambda m: "\\text{" + m[1].upper() + "}"),
    (re.compile(r"\{\\rm\s+([^{}$]*)\}"), lambda m: "\\mathrm{" + m[1] + "}"),
    (re.compile(r"\\cfrac(?![A-Za-z])"), lambda m: "\\dfrac"),
    # texmath has no \varprojlim and \varinjlim: the limit with an arrow under it
    (re.compile(r"\\varprojlim(?![A-Za-z])"), lambda m: "\\underset{\\longleftarrow}{\\lim}"),
    (re.compile(r"\\varinjlim(?![A-Za-z])"), lambda m: "\\underset{\\longrightarrow}{\\lim}"),
    (re.compile(r"\\tbinom(?![A-Za-z])"), lambda m: "\\binom"),
    (re.compile(r"\\bmod(?![A-Za-z])"), lambda m: "\\mathbin{\\mathrm{mod}}"),
    # texmath cannot read \not before a group, as in the negated "|~" of nonmonotonic reasoning
    (re.compile(r"\\not\s*\\mathrel\{\|\\!\\sim\}"), lambda m: "\\mathrel{|\\!\\nsim}"),
    # texmath has \big but not the relation sizes \bigm, \Bigm, \biggm, \Biggm (as in P(A \bigm| B))
    (re.compile(r"\\(big|Big|bigg|Bigg)m(?![A-Za-z])\s*(\\\||\\[A-Za-z]+|.)"),
     lambda m: "\\mathrel{\\" + m[1] + m[2] + "}"),
]


def mathml_safe(md: str) -> str:
    def span(m: re.Match) -> str:
        t = m.group(0)
        for rx, f in _MATHML:
            t = rx.sub(f, t)
        return t
    return _MATH.sub(span, md)


_HEADING = re.compile(r"^(#{1,6} .*?)(?:\s*(?<!\])\{([^{}]*)\})?\s*$")
_FENCE = re.compile(r"^\s*(`{3,}|~{3,})")


def heading_ids(md: str) -> str:
    """Give every heading without an identifier one of its own (`h-1`, `h-2`, …). Pandoc's EPUB writer would
    otherwise make one from the text, and the section "Termination" of one entry would take the identifier of
    the entry `termination`, and its links."""
    out, fence, n = [], None, 0
    for ln in md.split("\n"):
        f = _FENCE.match(ln)
        if f:
            if fence is None:
                fence = f.group(1)[0]
            elif f.group(1)[0] == fence:
                fence = None
        elif fence is None and ln.startswith("#") and (m := _HEADING.match(ln)):
            attrs = m.group(2) or ""
            if not re.search(r"(^|\s)#", attrs):
                n += 1
                ln = f"{m.group(1)} {{#h-{n}{' ' + attrs if attrs else ''}}}"
        out.append(ln)
    return "\n".join(out)


def build(book, vol, md: str, outdir: str, edition: str, date: str) -> dict:
    os.makedirs(outdir, exist_ok=True)
    t = time.time()
    src = os.path.join(outdir, "epub.md")
    open(src, "w").write(metadata(book, vol, edition, date) + "\n" + front_md(book, vol, edition, date)
                         + "\n\n" + heading_ids(mathml_safe(md)))
    cover = os.path.join(outdir, "cover.png")
    if vol is None:
        tfm = book.front.get("title", ({}, ""))[0]
        cover_png(None, str(tfm.get("title", BOOK)), str(tfm.get("subtitle", "")), [], edition, cover)
    else:
        cover_png(vol.number, vol.title, vol.summary, vol.squares, edition, cover)
    out = os.path.join(outdir, "main.epub")
    cmd = ["pandoc", src, "-f", "markdown-auto_identifiers-raw_tex", "-t", "epub3", "-o", out,
           "--lua-filter", os.path.join(ROOT, "filters", "ghb.lua"),
           "--math-method=mathml", "--toc", "--toc-depth=3", "--split-level=1",
           "--css", volume_css(vol.number if vol else 0, outdir),
           "--epub-cover-image", cover, "--resource-path", outdir,
           "--syntax-highlighting=pygments"]
    r = subprocess.run(cmd, capture_output=True, text=True)
    info = {"epub_s": round(time.time() - t, 1), "epub_ok": r.returncode == 0}
    if r.returncode:
        info["error"] = r.stderr[-4000:]
    elif r.stderr.strip():
        info["epub_warnings"] = r.stderr.count("[WARNING]")
        open(os.path.join(outdir, "epub.log"), "w").write(r.stderr)
    if os.path.exists(out):
        space_functions(out)
        info["epub"] = out
        info["epub_mb"] = round(os.path.getsize(out) / 1e6, 1)
    return info


# `log n` in MathML is <mi>log</mi><mo>&#8289;</mo>; WebKit and Blink, which most reading systems use, put no
# space around it, so `n log n` prints as `nlogn`. A thin space on both sides, as TeX gives.
_FN = re.compile(r'(<mrow>)?(<mi mathvariant="normal">[A-Za-z]{2,}\*?</mi><mo>&#8289;</mo>)(</mrow>)?')
_SP = '<mspace width="0.1667em"></mspace>'


def space_functions(path: str) -> None:
    tmp = path + ".tmp"
    with zipfile.ZipFile(path) as zin, zipfile.ZipFile(tmp, "w") as zout:
        for item in zin.infolist():
            data = zin.read(item.filename)
            if item.filename.endswith(".xhtml"):
                data = _FN.sub(lambda m: (m.group(1) or "") + _SP + m.group(2) + _SP + (m.group(3) or ""),
                               data.decode()).encode()
            # mimetype first and stored, as EPUB requires
            zout.writestr(item, data, compress_type=zipfile.ZIP_STORED if item.filename == "mimetype"
                          else zipfile.ZIP_DEFLATED)
    os.replace(tmp, path)
