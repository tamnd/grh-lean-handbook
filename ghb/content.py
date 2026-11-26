"""The content of the handbook: content/front and the volumes content/NN-<id>/.

Each volume folder has a file volume.yaml with the plan of the volume: its number, title, summary, target words,
and its chapters in order. A chapter is a folder <chapter id>/ in the volume folder. Each section of a chapter is
one file NN-<slug>.md with YAML front matter (spec 08.2). A chapter of the plan with no section files is not
written yet. The build skips it, and it skips a volume with no written chapter.
"""

from __future__ import annotations

import glob
import os
import re
from dataclasses import dataclass, field

import yaml

STATUSES = ("drafted", "checked", "reviewed")


def front(text: str) -> tuple[dict, str]:
    """Split a Markdown file into its YAML front matter and its body. A bad YAML block raises ValueError."""
    if text.startswith("---\n"):
        end = text.find("\n---\n", 4)
        if end < 0 and text.rstrip().endswith("\n---"):
            end = len(text.rstrip()) - 4
        if end > 0:
            try:
                fm = yaml.safe_load(text[4:end]) or {}
            except yaml.YAMLError as e:
                raise ValueError(f"the front matter is not valid YAML: {e}") from None
            if not isinstance(fm, dict):
                raise ValueError("the front matter is not a mapping")
            return fm, text[end + 5:]
    return {}, text


def words(text: str) -> int:
    """Words as `wc -w` counts them."""
    return len(text.split())


@dataclass
class Section:
    path: str
    fm: dict
    body: str
    error: str = ""   # a problem with the front matter

    @property
    def status(self) -> str:
        s = str(self.fm.get("status") or "drafted")
        return s if s in STATUSES else "drafted"


@dataclass
class Chapter:
    id: str
    title: str
    num: int                 # the place of the chapter in volume.yaml, from 1
    dir: str
    plan: str = ""
    research: str = ""
    source: list[str] = field(default_factory=list)   # path prefixes under grh/src
    generated: str = ""      # "lean-index": the build writes this chapter
    sections: list[Section] = field(default_factory=list)

    @property
    def written(self) -> bool:
        return bool(self.sections)

    @property
    def text(self) -> str:
        return "\n\n".join(s.body.strip("\n") for s in self.sections)

    @property
    def decls(self) -> list[str]:
        out = []
        for s in self.sections:
            out += [str(d) for d in (s.fm.get("decls") or []) if d]
        return out

    @property
    def words(self) -> int:
        return sum(words(s.body) for s in self.sections)

    @property
    def status(self) -> str:
        """The status of a chapter is the lowest status of its sections."""
        if not self.sections:
            return "planned"
        return min((s.status for s in self.sections), key=STATUSES.index)

    def people(self, key: str) -> list[str]:
        out = []
        for s in self.sections:
            v = s.fm.get(key)
            for p in (v if isinstance(v, list) else [v]):
                if p and str(p) not in out:
                    out.append(str(p))
        return out


@dataclass
class Volume:
    number: int
    id: str
    dir: str
    title: str
    summary: str
    words: int
    chapters: list[Chapter]
    plan: dict = field(default_factory=dict)   # volume.yaml as read

    @property
    def written(self) -> list[Chapter]:
        return [c for c in self.chapters if c.written]

    @property
    def target(self) -> int:
        """The target words of one chapter: the words of the volume over its chapters."""
        return self.words // max(1, len(self.chapters))

    @property
    def squares(self) -> list[float]:
        """The cover: one square for each chapter of the plan, filled by its words against the target."""
        t = max(1, self.target)
        return [min(1.0, c.words / t) for c in self.chapters]


def read_sections(cdir: str) -> list[Section]:
    out = []
    for p in sorted(glob.glob(os.path.join(cdir, "[0-9][0-9]-*.md"))):
        text = open(p, encoding="utf-8").read()
        try:
            fm, body = front(text)
            out.append(Section(p, fm, body))
        except ValueError as e:
            out.append(Section(p, {}, text, str(e)))
    return out


def load_volumes(content: str) -> list[Volume]:
    """Every volume of the plan, written or not."""
    out = []
    for d in sorted(glob.glob(os.path.join(content, "[0-9][0-9]-*"))):
        vy = os.path.join(d, "volume.yaml")
        if not os.path.isfile(vy):
            continue
        v = yaml.safe_load(open(vy, encoding="utf-8")) or {}
        base = os.path.basename(d)
        chapters = []
        for num, c in enumerate(v.get("chapters") or [], 1):
            cdir = os.path.join(d, c["id"])
            src = c.get("source") or []
            chapters.append(Chapter(c["id"], c.get("title", c["id"]), num, cdir, (c.get("plan") or "").strip(),
                                    str(c.get("research") or ""), [str(s) for s in src],
                                    str(c.get("generated") or ""), read_sections(cdir)))
        out.append(Volume(int(v.get("number", base[:2])), base[3:], d, v.get("title", base),
                          (v.get("summary") or "").strip(), int(v.get("words") or 0), chapters, v))
    return out


FRONT = ("title", "copyright", "edition")


def front_pages(content: str) -> dict[str, tuple[dict, str]]:
    """content/front/title.md, copyright.md and edition.md: their front matter and body."""
    out = {}
    for name in FRONT:
        p = os.path.join(content, "front", name + ".md")
        if os.path.exists(p):
            out[name] = front(open(p, encoding="utf-8").read())
    return out


def fill(text: str, values: dict[str, str]) -> str:
    """Put the values of the edition into the placeholders {{version}}, {{date}}, {{pin}} and {{volume}}."""
    return re.sub(r"\{\{\s*(\w+)\s*\}\}", lambda m: str(values.get(m[1], m[0])), text)


_SLUG = re.compile(r"[^a-z0-9 -]")


def anchor(heading: str) -> str:
    """The anchor of a heading: lower case, spaces become hyphens, other punctuation goes."""
    s = heading.strip().lower()
    s = _SLUG.sub("", s)
    return re.sub(r" +", "-", s).strip("-")
