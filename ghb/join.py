"""The PDF of all volumes (spec 09.5): the built volume PDFs joined in order, front then 00 to 12.

Each volume keeps its outline under a top-level bookmark with its title, its links, and its page labels with the
prefix "N:" (the front pages "front:"). The named destinations of each volume get the same prefix, since the
volumes use the same names (chapter.1, page.1, ...).
"""

from __future__ import annotations

import os
import re

import yaml

NAME = "grh-lean-handbook"


def parts(folder: str, version: str) -> list[tuple[str, str]]:
    """The volume PDFs of the version in folder, in order: (key, path); key is 'front' or 'NN-<id>'."""
    pat = re.compile(rf"^{re.escape(NAME)}-(front|\d\d-[a-z0-9-]+)-{re.escape(version)}\.pdf$")
    found = [(m.group(1), os.path.join(folder, f)) for f in os.listdir(folder) if (m := pat.match(f))]
    return sorted(found, key=lambda kp: (kp[0] != "front", kp[0]))


def title(content: str, key: str) -> str:
    if key == "front":
        return "The front pages"
    p = os.path.join(content, key, "volume.yaml")
    plan = yaml.safe_load(open(p)) if os.path.exists(p) else {}
    return f"Volume {int(key[:2])}: {plan.get('title') or key[3:]}"


def _rename(reader, prefix: str) -> None:
    """Prefix the named destinations of reader, in the name tree and in the links and outline that use them."""
    from pypdf.generic import ArrayObject, NameObject, TextStringObject

    def name(s):
        return TextStringObject(prefix + str(s))

    def tree(node):
        node = node.get_object()
        if "/Names" in node:
            arr = node["/Names"].get_object()
            for i in range(0, len(arr), 2):
                arr[i] = name(arr[i])
        if "/Limits" in node:
            node[NameObject("/Limits")] = ArrayObject([name(x) for x in node["/Limits"]])
        for kid in node.get("/Kids", []):
            tree(kid)

    def use(obj):
        obj = obj.get_object()
        if isinstance(obj.get("/Dest"), str):
            obj[NameObject("/Dest")] = name(obj["/Dest"])
        a = obj.get("/A")
        if a is not None:
            a = a.get_object()
            if a.get("/S") == "/GoTo" and isinstance(a.get("/D"), str):
                a[NameObject("/D")] = name(a["/D"])

    root = reader.trailer["/Root"]
    names = root.get("/Names")
    if names is not None and "/Dests" in names.get_object():
        tree(names.get_object()["/Dests"])
    for page in reader.pages:
        for an in page.get("/Annots") or []:
            use(an)
    stack = []
    if "/Outlines" in root and "/First" in root["/Outlines"].get_object():
        stack.append(root["/Outlines"].get_object()["/First"])
    while stack:
        item = stack.pop().get_object()
        use(item)
        for k in ("/First", "/Next"):
            if k in item:
                stack.append(item[k])
    reader._named_destinations = {}


def _labels(reader) -> list[tuple[int, str, int]]:
    """The page label ranges of reader: (first page, style, start)."""
    nums = reader.trailer["/Root"].get("/PageLabels", {}).get_object().get("/Nums")
    if not nums:
        return [(0, "/D", 1)]
    nums = nums.get_object()
    return [(int(nums[i]), nums[i + 1].get_object().get("/S", "/D"), int(nums[i + 1].get_object().get("/St", 1)))
            for i in range(0, len(nums), 2)]


def join(folder: str, out: str, version: str, content: str) -> dict:
    from pypdf import PdfReader, PdfWriter

    found = parts(folder, version)
    if not found:
        raise SystemExit(f"no {NAME}-*-{version}.pdf in {folder}")
    w = PdfWriter()
    ranges = []
    for key, path in found:
        r = PdfReader(path)
        tag = "front" if key == "front" else str(int(key[:2]))
        _rename(r, f"{tag}:")
        at = len(w.pages)
        w.append(r, outline_item=title(content, key), import_outline=True)
        labels = _labels(r)
        for i, (first, style, start) in enumerate(labels):
            last = labels[i + 1][0] - 1 if i + 1 < len(labels) else len(r.pages) - 1
            ranges.append((at + first, at + last, style, f"{tag}:", start))
    for first, last, style, prefix, start in ranges:
        w.set_page_label(first, last, style if style in ("/D", "/r", "/R", "/a", "/A") else None, prefix, start)
    w.page_mode = "/UseOutlines"
    w.add_metadata({"/Title": "The GRH Lean Handbook", "/Subject": f"All volumes, edition {version}"})
    w.compress_identical_objects()
    with open(out, "wb") as f:
        w.write(f)
    return {"volumes": [k for k, _ in found], "pages": len(w.pages), "bytes": os.path.getsize(out)}
