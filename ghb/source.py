"""The pinned clone of lsernau/grh-lean, read as text.

The scan does not build Lean. It reads each file of grh/src (and of grh-compact/src) and finds:

- the module docstring (`/-! ... -/`) and its first heading;
- the declarations `theorem`, `lemma`, `def`, `structure`, `class`, `instance`, `abbrev` and `inductive`, with
  the scopes `namespace`, `section`, `noncomputable section` and `mutual`, and `_root_`;
- the fields and the constructor of each structure and class, and the constructors of each inductive type.

Comments and strings are removed before the scan, so a word in a docstring is not a declaration. An anonymous
instance has a name that Lean makes, and the scan does not know it.
"""

from __future__ import annotations

import glob
import hashlib
import os
import re
import subprocess
from dataclasses import dataclass, field

KINDS = ("theorem", "lemma", "def", "structure", "class", "instance", "abbrev", "inductive")

_MODS = r"(?:(?:@\[[^\]]*\]|private|protected|noncomputable|nonrec|partial|unsafe|scoped|local)\s+)*"
_PRE = r"(?:(?:open|omit|include|set_option)\b[^\n]*?\bin\s+)*"
_DECL = re.compile(r"^[ \t]*" + _PRE + _MODS + r"(theorem|lemma|def|structure|class(?:\s+inductive)?|instance|abbrev|inductive)"
                   r"\s+(?:\(priority\s*:=[^)]*\)\s+)?([^\s:(){}\[\]⦃⦄,]+)")
_NS = re.compile(r"^[ \t]*namespace\s+([^\s]+)")
_SEC = re.compile(r"^[ \t]*(?:noncomputable\s+)?section\b|^[ \t]*mutual\b")
_END = re.compile(r"^[ \t]*end\b(?:\s+([^\s]+))?\s*$")
_FIELD = re.compile(r"^[ \t]{2,}\(?([A-Za-z_Ͱ-Ͽᴀ-ᶿ][\w'!?₀-ₜᵢ-ᵪ.]*)\s*(?:[{(\[⦃:]|:=)")
_CTOR = re.compile(r"^[ \t]{2,}([A-Za-z_][\w']*)\s*::")
_ICTOR = re.compile(r"^[ \t]*\|\s*([^\s:(){}\[\]⦃⦄,]+)")


_TOKENS = re.compile(r'/-|-/|--|"|\n')
_IN_COMMENT = re.compile(r"/-|-/|\n")


def strip_comments(text: str) -> str:
    """Remove comments and string literals; keep the newlines, so that line numbers stay right."""
    out = []
    pos, n = 0, len(text)
    while True:
        m = _TOKENS.search(text, pos)
        if not m:
            out.append(text[pos:])
            break
        t, i = m.group(0), m.start()
        out.append(text[pos:i])
        if t == "/-":
            depth, j = 1, m.end()
            while depth:
                c = _IN_COMMENT.search(text, j)
                if not c:
                    j = n
                    break
                if c.group(0) == "/-":
                    depth += 1
                elif c.group(0) == "-/":
                    depth -= 1
                else:
                    out.append("\n")
                j = c.end()
            pos = j
        elif t == "--":
            j = text.find("\n", i)
            pos = n if j < 0 else j
        elif t == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append('""' + "\n" * text.count("\n", i, j))
            pos = j + 1
        else:
            out.append(t)
            pos = m.end()
    return "".join(out)


def module_doc(text: str) -> tuple[str, str]:
    """The module docstring of a file and its first heading."""
    m = re.search(r"/-!(.*?)-/", text, flags=re.S)
    if not m:
        return "", ""
    doc = m.group(1).strip()
    h = re.search(r"^#\s+(.+)$", doc, flags=re.M)
    return doc, (h.group(1).strip() if h else "")


@dataclass
class Decl:
    name: str
    kind: str
    file: str       # relative to the src folder, with .lean
    line: int
    digest: str = ""   # a hash of the text of the declaration, for `ghb ledger --diff`


def scan_text(text: str, rel: str) -> list[Decl]:
    """The declarations of one file."""
    clean = strip_comments(text)
    lines = clean.split("\n")
    scopes: list[str | None] = []
    out: list[Decl] = []
    owner: list | None = None   # [full name, kind, after `where`, has a constructor] of a structure being read
    owners: list[list] = []
    for no, ln in enumerate(lines, 1):
        if owner and ln.strip() and not ln[:1].isspace() and not ln.lstrip().startswith("|"):
            owner = None
        if owner:
            full, kind, open_ = owner[0], owner[1], owner[2]
            if not open_:
                if re.search(r"\bwhere\b", ln):
                    owner[2] = True
                continue
            if kind == "inductive":
                m = _ICTOR.match(ln)
                if m:
                    out.append(Decl(f"{full}.{m.group(1)}", "constructor", rel, no))
                    continue
            else:
                m = _CTOR.match(ln)
                if m:
                    owner[3] = True
                    out.append(Decl(f"{full}.{m.group(1)}", "constructor", rel, no))
                    continue
                m = _FIELD.match(ln)
                if m and m.group(1) not in ("where", "extends", "deriving", "with"):
                    out.append(Decl(f"{full}.{m.group(1)}", "field", rel, no))
                    continue
        m = _NS.match(ln)
        if m:
            # Lean 4: `namespace A.B` opens one scope for each component, so `end B` closes only `B`.
            scopes.extend(m.group(1).split("."))
            continue
        if _SEC.match(ln):
            scopes.append(None)
            continue
        m = _END.match(ln)
        if m:
            for _ in range(len(m.group(1).split(".")) if m.group(1) else 1):
                if scopes:
                    scopes.pop()
            continue
        m = _DECL.match(ln)
        if not m:
            continue
        kind = m.group(1).split()[0]
        if kind == "class" and "inductive" in m.group(1):
            kind = "inductive"
        name = m.group(2)
        if name.startswith("_root_."):
            full = name[len("_root_."):]
        else:
            ns = ".".join(s for s in scopes if s)
            full = f"{ns}.{name}" if ns else name
        full = full.replace("«", "").replace("»", "")
        out.append(Decl(full, kind, rel, no))
        if kind in ("structure", "class", "inductive"):
            owner = [full, kind, bool(re.search(r"\bwhere\b", ln)), False, no]
            owners.append(owner)
    for o in owners:   # a structure or class with no constructor of its own name has `mk`
        if o[1] != "inductive" and not o[3]:
            out.append(Decl(f"{o[0]}.mk", "constructor", rel, o[4]))
    # the text of each declaration: from its line to the line of the next one
    starts = [d.line for d in out if d.kind in KINDS] + [len(lines) + 1]
    raw = text.split("\n")
    k = 0
    for d in out:
        if d.kind not in KINDS:
            continue
        end = starts[k + 1]
        d.digest = hashlib.sha1("\n".join(raw[d.line - 1:end - 1]).encode()).hexdigest()[:12]
        k += 1
    return out


@dataclass
class LeanFile:
    path: str        # relative to src, with .lean
    lines: int
    title: str       # the first heading of the module docstring
    doc: str


@dataclass
class Edition:
    """One edition of the source: grh (readable) or grh-compact."""
    name: str
    src: str
    files: dict[str, LeanFile] = field(default_factory=dict)
    decls: dict[str, Decl] = field(default_factory=dict)
    by_last: dict[str, list[str]] = field(default_factory=dict)   # the last part of a name → the full names

    def load(self) -> "Edition":
        for p in sorted(glob.glob(os.path.join(self.src, "**", "*.lean"), recursive=True)):
            rel = os.path.relpath(p, self.src)
            text = open(p, encoding="utf-8").read()
            doc, title = module_doc(text)
            self.files[rel] = LeanFile(rel, text.count("\n") + (0 if text.endswith("\n") else 1), title, doc)
            for d in scan_text(text, rel):
                self.decls.setdefault(d.name, d)
        for name in self.decls:
            self.by_last.setdefault(name.rsplit(".", 1)[-1], []).append(name)
        return self

    def has_file(self, path: str) -> bool:
        path = path.split("#", 1)[0].strip("/")
        if path in self.files:
            return True
        # a folder of the source, as in `New/Reduction/Data/`
        return any(f.startswith(path.rstrip("/") + "/") for f in self.files)

    def suggest(self, name: str, k: int = 3) -> list[str]:
        """Full names that end like `name`, for the message of a failed check."""
        return sorted(self.by_last.get(name.rsplit(".", 1)[-1], []))[:k]


def commit(path: str) -> str:
    try:
        return subprocess.run(["git", "-C", path, "rev-parse", "HEAD"], capture_output=True, text=True,
                              check=True).stdout.strip()
    except Exception:
        return ""


class Source:
    """The clone of lsernau/grh-lean at the pin: `grh` is the readable edition the book follows, `compact` is
    grh-compact, which the book uses for its table of names only."""

    def __init__(self, root: str, pin: str):
        self.root = root
        self.pin = pin
        self.commit = commit(root) if os.path.isdir(root) else ""
        self.grh = Edition("grh", os.path.join(root, "grh", "src"))
        self.compact = Edition("grh-compact", os.path.join(root, "grh-compact", "src"))
        if os.path.isdir(self.grh.src):
            self.grh.load()
        if os.path.isdir(self.compact.src):
            self.compact.load()

    @property
    def present(self) -> bool:
        return bool(self.grh.files)

    def warning(self) -> str:
        if not self.present:
            return f"no source at {self.root}: the names and paths are not checked"
        if self.commit and self.pin and self.commit != self.pin:
            return f"the clone is at {self.commit[:12]}, the pin in EDITION is {self.pin[:12]}"
        return ""


def edition_at(root: str, rev: str, name: str = "grh") -> Edition:
    """An edition at another commit of the clone, read with git (for `ghb ledger --diff`)."""
    ed = Edition(name, "")
    r = subprocess.run(["git", "-C", root, "ls-tree", "-r", "--name-only", rev, f"{name}/src"],
                       capture_output=True, text=True, check=True)
    for p in r.stdout.split():
        if not p.endswith(".lean"):
            continue
        text = subprocess.run(["git", "-C", root, "show", f"{rev}:{p}"], capture_output=True, text=True).stdout
        rel = p[len(f"{name}/src/"):]
        doc, title = module_doc(text)
        ed.files[rel] = LeanFile(rel, text.count("\n"), title, doc)
        for d in scan_text(text, rel):
            ed.decls.setdefault(d.name, d)
    return ed
