# Copyright (c) 2026 SymLean Team. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""The page sources of the SymLean site: TOML front matter and a small Markdown.

A page is a file under `Site/Pages/`:

    +++
    id = "derive"
    kind = "mode"
    title = "derive"
    summary = "..."
    +++

    Markdown body

The body is read into blocks:

* `## Heading` and `### Heading`, with an optional `{#anchor}` at the end;
* paragraphs, `- ` bullet lists (continuation lines indented by two spaces) and `1. ` lists;
* fenced code: `lean` cells, which the build compiles (`lean error`, `lean hidden`,
  `lean quote=FILE` change what is expected of them, and `lean expect="TEXT"` requires TEXT in
  the output), and `sh`/`text` blocks, which it does not;
* `$$ ... $$` display math;
* `---`, which separates examples;
* directives `::: name #anchor key="value"` ... `:::`, which may nest.

Inline markup is read by `sitehtml`.
"""

from __future__ import annotations

import re
import shlex
import tomllib
from dataclasses import dataclass, field
from pathlib import Path


class SourceError(ValueError):
    """A page source the generator cannot read, with its file and line."""


@dataclass
class Block:
    kind: str  # heading, para, list, code, math, rule, directive
    line: int
    text: str = ""
    level: int = 0
    anchor: str = ""
    ordered: bool = False
    items: list[str] = field(default_factory=list)
    lang: str = ""
    attrs: dict[str, str] = field(default_factory=dict)
    name: str = ""
    children: list["Block"] = field(default_factory=list)


@dataclass
class Page:
    path: Path
    meta: dict
    blocks: list[Block]

    @property
    def id(self) -> str:
        return self.meta["id"]

    @property
    def kind(self) -> str:
        return self.meta["kind"]

    @property
    def title(self) -> str:
        return self.meta["title"]

    @property
    def summary(self) -> str:
        return self.meta.get("summary", "")


_HEADING_RE = re.compile(r"^(#{2,3})\s+(.*?)\s*(?:\{#([A-Za-z0-9_-]+)\})?\s*$")
_FENCE_RE = re.compile(r"^```(\S*)\s*(.*)$")
_DIRECTIVE_RE = re.compile(r"^:::\s*([a-z][a-z-]*)\s*(.*)$")
_BULLET_RE = re.compile(r"^- (.*)$")
_ORDERED_RE = re.compile(r"^\d+\. (.*)$")


def _attrs(text: str, where: str) -> dict[str, str]:
    """`#anchor key="value" flag` as a dictionary; the anchor is under `id`."""
    out: dict[str, str] = {}
    try:
        words = shlex.split(text)
    except ValueError as err:
        raise SourceError(f"{where}: cannot read the attributes {text!r}: {err}") from err
    for word in words:
        if word.startswith("#"):
            out["id"] = word[1:]
        elif "=" in word:
            key, value = word.split("=", 1)
            out[key] = value
        else:
            out[word] = "true"
    return out


def parse_blocks(lines: list[str], first_line: int, where: str) -> list[Block]:
    """The blocks of `lines`, whose first line is line `first_line` of the file `where`."""
    blocks: list[Block] = []
    i = 0
    n = len(lines)

    def loc(k: int) -> str:
        return f"{where}:{first_line + k}"

    while i < n:
        line = lines[i]
        stripped = line.strip()
        if not stripped:
            i += 1
            continue
        # Directives, closed by a line ':::' at the same depth.
        m = _DIRECTIVE_RE.match(stripped)
        if m and line.startswith(":::"):
            name, rest = m.group(1), m.group(2)
            depth, j = 1, i + 1
            in_fence = False
            while j < n:
                s = lines[j].strip()
                if s.startswith("```"):
                    in_fence = not in_fence
                elif not in_fence:
                    if _DIRECTIVE_RE.match(s) and lines[j].startswith(":::"):
                        depth += 1
                    elif s == ":::":
                        depth -= 1
                        if depth == 0:
                            break
                j += 1
            if j >= n:
                raise SourceError(f"{loc(i)}: the directive '{name}' is not closed")
            body = lines[i + 1 : j]
            block = Block("directive", first_line + i, name=name, attrs=_attrs(rest, loc(i)))
            block.text = "\n".join(body)
            block.children = parse_blocks(body, first_line + i + 1, where)
            blocks.append(block)
            i = j + 1
            continue
        if stripped == ":::":
            raise SourceError(f"{loc(i)}: ':::' closes no directive")
        # Fenced code.
        m = _FENCE_RE.match(line)
        if m:
            lang, rest = m.group(1), m.group(2)
            j = i + 1
            while j < n and not lines[j].startswith("```"):
                j += 1
            if j >= n:
                raise SourceError(f"{loc(i)}: the code block is not closed")
            code = "\n".join(lines[i + 1 : j])
            blocks.append(Block("code", first_line + i, text=code, lang=lang or "text",
                                attrs=_attrs(rest, loc(i))))
            i = j + 1
            continue
        # Display math.
        if stripped.startswith("$$"):
            body = stripped[2:]
            j = i
            if body.endswith("$$") and len(body) >= 2:
                tex = body[:-2]
            else:
                parts = [body]
                j = i + 1
                while j < n and not lines[j].strip().endswith("$$"):
                    parts.append(lines[j])
                    j += 1
                if j >= n:
                    raise SourceError(f"{loc(i)}: the display formula is not closed")
                parts.append(lines[j].strip()[:-2])
                tex = "\n".join(parts)
            blocks.append(Block("math", first_line + i, text=tex.strip()))
            i = j + 1
            continue
        if stripped == "---":
            blocks.append(Block("rule", first_line + i))
            i += 1
            continue
        m = _HEADING_RE.match(line)
        if m:
            blocks.append(Block("heading", first_line + i, text=m.group(2), level=len(m.group(1)),
                                anchor=m.group(3) or ""))
            i += 1
            continue
        if line.startswith("# "):
            raise SourceError(f"{loc(i)}: the page title comes from the front matter; use ##")
        # Lists.
        if _BULLET_RE.match(line) or _ORDERED_RE.match(line):
            ordered = bool(_ORDERED_RE.match(line))
            item_re = _ORDERED_RE if ordered else _BULLET_RE
            items: list[str] = []
            j = i
            while j < n:
                cur = lines[j]
                mm = item_re.match(cur)
                if mm:
                    items.append(mm.group(1))
                elif cur.startswith("  ") and cur.strip() and items:
                    items[-1] += "\n" + cur.strip()
                elif not cur.strip():
                    # A blank line ends the list unless the next line is another item.
                    if j + 1 < n and item_re.match(lines[j + 1]):
                        j += 1
                        continue
                    break
                else:
                    break
                j += 1
            blocks.append(Block("list", first_line + i, ordered=ordered, items=items))
            i = j
            continue
        # A paragraph runs to the next blank line or block start.
        j = i
        para: list[str] = []
        while j < n:
            cur = lines[j]
            s = cur.strip()
            if not s or cur.startswith("```") or s.startswith("$$") or s == "---" or \
                    _HEADING_RE.match(cur) or (cur.startswith(":::")) or \
                    (j > i and (_BULLET_RE.match(cur) or _ORDERED_RE.match(cur))):
                break
            para.append(s)
            j += 1
        blocks.append(Block("para", first_line + i, text="\n".join(para)))
        i = j
    return blocks


_REQUIRED = {"id", "kind", "title"}
KINDS = {"home", "docs", "index", "guide", "tutorial", "mode", "command", "tactic", "call",
         "option", "oracle"}


def read_page(path: Path) -> Page:
    text = path.read_text(encoding="utf-8")
    lines = text.split("\n")
    if not lines or lines[0].strip() != "+++":
        raise SourceError(f"{path}:1: a page starts with front matter between '+++' lines")
    try:
        end = lines.index("+++", 1)
    except ValueError as err:
        raise SourceError(f"{path}: the front matter is not closed") from err
    try:
        meta = tomllib.loads("\n".join(lines[1:end]))
    except tomllib.TOMLDecodeError as err:
        raise SourceError(f"{path}: front matter: {err}") from err
    missing = _REQUIRED - meta.keys()
    if missing:
        raise SourceError(f"{path}: front matter lacks {', '.join(sorted(missing))}")
    if meta["kind"] not in KINDS:
        raise SourceError(f"{path}: unknown kind {meta['kind']!r}")
    blocks = parse_blocks(lines[end + 1 :], end + 2, str(path))
    return Page(path, meta, blocks)


def read_pages(root: Path) -> list[Page]:
    pages = [read_page(p) for p in sorted(root.rglob("*.md"))]
    seen: dict[str, Path] = {}
    for page in pages:
        if page.id in seen:
            raise SourceError(f"{page.path}: the id {page.id!r} is also used by {seen[page.id]}")
        seen[page.id] = page.path
    return pages


def walk(blocks: list[Block]):
    """Every block, directives' children included, in document order."""
    for block in blocks:
        yield block
        if block.kind == "directive":
            yield from walk(block.children)
