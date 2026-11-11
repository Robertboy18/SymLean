# Copyright (c) 2026 SymLean Team. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""HTML of the SymLean site: the page shell, the navigation, inline markup, math and cells."""

from __future__ import annotations

import html
import re
from dataclasses import dataclass, field
from pathlib import Path

import sitelean
import sitemath
from sitelean import Cell
from siteparse import Block, Page

GITHUB = "https://github.com/Robertboy18/SymLean"
SITE_URL = "https://robertboy18.github.io/SymLean/"

KIND_LABELS = {
    "mode": "Mode of #cas",
    "command": "Command",
    "tactic": "Tactic",
    "call": "Function of #cas",
    "option": "Options",
    "oracle": "Option of #cas and cas",
    "guide": "Guide",
    "tutorial": "Tutorial",
}
DOT = ' <span class="dot">·</span> '
REF_KINDS = {"mode", "command", "tactic", "call", "option", "oracle"}
EXAMPLE_SECTIONS = ["Basic Examples", "Scope", "Options", "Applications",
                    "Properties and Relations", "Possible Issues", "Neat Examples"]


class RenderError(ValueError):
    """A page that cannot be rendered, with its source position."""


@dataclass
class Site:
    pages: dict[str, Page]
    paths: dict[str, str]
    guide_order: list[str]
    guide_members: dict[str, list[tuple[str, list[str]]]]  # guide -> [(group, [page ids])]
    tutorial_order: list[str]
    cell_of: dict[int, Cell]
    figures_dir: Path
    footer_note: str = ""
    problems: list[str] = field(default_factory=list)

    def guides_of(self, page_id: str) -> list[str]:
        return [g for g in self.guide_order
                if any(page_id in ids for _, ids in self.guide_members.get(g, []))]


def slug(text: str) -> str:
    text = re.sub(r"<[^>]+>", "", text)
    text = re.sub(r"[`*$\\]", "", text)
    return re.sub(r"[^a-z0-9]+", "-", text.lower()).strip("-") or "section"


# ---------------------------------------------------------------------------
# Inline markup

_INLINE_RE = re.compile(
    r"""
    (?P<code>`+)(?P<codetext>.+?)(?P=code)
  | (?<![\\\w])\$(?P<math>(?:\\.|[^$\\])+?)\$
  | \[\[(?P<wiki>[^\]|]+)(?:\|(?P<wikitext>(?:`[^`]*`|[^\]`])+))?\]\]
  | \[(?P<ltext>[^\]]+)\]\((?P<href>[^)\s]+)\)
  | \*\*(?P<bold>.+?)\*\*
  | (?<![\w*])\*(?P<ital>[^*\s](?:[^*]*?[^*\s])?)\*(?!\w)
  | \\(?P<esc>[$*`\[\]\\])
    """,
    re.X | re.S,
)


def smart(text: str) -> str:
    """Typographic apostrophes and quotes in escaped prose."""
    text = re.sub(r"(?<=\w)'(?=\w)", "\u2019", text)
    text = re.sub(r"(?<=\w)'(?=\s|$|[.,;:!?)])", "\u2019", text)
    text = re.sub(r"&quot;(.+?)&quot;", "\u201c\\1\u201d", text)
    text = re.sub(r"(^|[\s(])'(\S.*?)'(?=[\s.,;:!?)]|$)", "\\1\u2018\\2\u2019", text)
    return re.sub(r"\u2039([^\u203a\s]+)\u203a", r"<var>\1</var>", text)


def code_html(text: str) -> str:
    """Inline Lean code: highlighted, with ‹placeholders› in italic."""
    return f'<code class="lean">{sitelean.highlight(text)}</code>'


class Inline:
    """Inline markup of one page."""

    def __init__(self, renderer: "PageRenderer") -> None:
        self.r = renderer

    def __call__(self, text: str) -> str:
        out: list[str] = []
        pos = 0
        for m in _INLINE_RE.finditer(text):
            out.append(smart(html.escape(text[pos:m.start()])))
            pos = m.end()
            if m.group("code"):
                out.append(code_html(m.group("codetext").strip() if m.group("code") == "``"
                                     else m.group("codetext")))
            elif m.group("math") is not None:
                out.append(self.r.math(m.group("math"), display=False))
            elif m.group("wiki"):
                out.append(self.r.symbol_link(m.group("wiki").strip(), m.group("wikitext")))
            elif m.group("ltext"):
                out.append(self.r.link(m.group("href"), self(m.group("ltext"))))
            elif m.group("bold"):
                out.append(f"<strong>{self(m.group('bold'))}</strong>")
            elif m.group("ital"):
                out.append(f"<em>{self(m.group('ital'))}</em>")
            elif m.group("esc"):
                out.append(html.escape(m.group("esc")))
        out.append(smart(html.escape(text[pos:])))
        return "".join(out).replace("\n", " ")


# ---------------------------------------------------------------------------
# Pages


class PageRenderer:
    def __init__(self, site: Site, page: Page) -> None:
        self.site = site
        self.page = page
        self.path = site.paths[page.id]
        self.depth = self.path.count("/")
        self.inline = Inline(self)
        self.figure_number = 0
        self.anchors: set[str] = set()

    # Links -----------------------------------------------------------------

    def rel(self, target: str) -> str:
        """A link from this page to `target`, a path from the site root."""
        here = self.path.split("/")[:-1]
        there = target.split("/")
        k = 0
        while k < len(here) and k < len(there) - 1 and here[k] == there[k]:
            k += 1
        return "/".join([".."] * (len(here) - k) + there[k:])

    def fail(self, where: str, message: str) -> None:
        self.site.problems.append(f"{self.page.path}: {where}: {message}")

    def page_href(self, page_id: str, anchor: str = "") -> str | None:
        if page_id not in self.site.paths:
            return None
        href = self.rel(self.site.paths[page_id])
        return href + (f"#{anchor}" if anchor else "")

    def link(self, href: str, text_html: str) -> str:
        if re.match(r"https?://", href):
            return f'<a class="ext" href="{html.escape(href)}">{text_html}</a>'
        if href.startswith("#"):
            return f'<a href="{html.escape(href)}">{text_html}</a>'
        if href.startswith("src:"):
            path = href[4:]
            return f'<a class="src" href="{GITHUB}/blob/main/{html.escape(path)}">{text_html}</a>'
        m = re.fullmatch(r"(ref|guide|tutorial|page):([A-Za-z0-9_.?-]+)(?:#([A-Za-z0-9_-]+))?", href)
        if m:
            target = self.page_href(m.group(2), m.group(3) or "")
            if target is None:
                self.fail("link", f"no page {m.group(2)!r}")
                return text_html
            return f'<a href="{html.escape(target)}">{text_html}</a>'
        if href in ("docs:index", "docs:all", "home"):
            target = {"docs:index": "docs/index.html", "docs:all": "docs/all.html",
                      "home": "index.html"}[href]
            return f'<a href="{self.rel(target)}">{text_html}</a>'
        self.fail("link", f"unknown link target {href!r}")
        return text_html

    def symbol_link(self, page_id: str, text: str | None = None) -> str:
        anchor = ""
        if "#" in page_id:
            page_id, anchor = page_id.split("#", 1)
        page = self.site.pages.get(page_id)
        if page is None:
            self.fail("link", f"no page {page_id!r} for [[{page_id}]]")
            return html.escape(text or page_id)
        label = self.inline(text) if text else code_html(page.title)
        return f'<a class="sym" href="{self.page_href(page_id, anchor)}">{label}</a>'

    # Math ------------------------------------------------------------------

    def math(self, tex: str, display: bool) -> str:
        try:
            rendered = sitemath.tex_to_mathml(tex, display=display)
            return rendered if display else f'<span class="inline-math">{rendered}</span>'
        except sitemath.MathError as err:
            self.fail("math", str(err))
            return f"<code>{html.escape(tex)}</code>"

    # Blocks ----------------------------------------------------------------

    def heading(self, block: Block, level: int | None = None, extra: str = "") -> str:
        level = level or block.level
        anchor = block.anchor or slug(block.text)
        base, k = anchor, 2
        while anchor in self.anchors:
            anchor = f"{base}-{k}"
            k += 1
        self.anchors.add(anchor)
        return (f'<h{level} id="{anchor}">{self.inline(block.text)}{extra}'
                f'<a class="anchor" href="#{anchor}" aria-label="Link to this section">#</a>'
                f"</h{level}>")

    def blocks(self, blocks: list[Block]) -> str:
        return "\n".join(self.block(b) for b in blocks)

    def list_item(self, item: str) -> str:
        """An item, with its indented `- ` lines as a nested list."""
        head: list[str] = []
        subs: list[str] = []
        for line in item.split("\n"):
            if line.startswith("- ") and head:
                subs.append(line[2:])
            elif subs:
                subs[-1] += "\n" + line
            else:
                head.append(line)
        inner = self.inline("\n".join(head))
        if subs:
            inner += "<ul>" + "".join(f"<li>{self.inline(s)}</li>" for s in subs) + "</ul>"
        return inner

    def block(self, b: Block) -> str:
        if b.kind == "heading":
            return self.heading(b)
        if b.kind == "para":
            return f"<p>{self.inline(b.text)}</p>"
        if b.kind == "list":
            tag = "ol" if b.ordered else "ul"
            items = "".join(f"<li>{self.list_item(item)}</li>" for item in b.items)
            return f"<{tag}>{items}</{tag}>"
        if b.kind == "math":
            return f'<div class="display-math">{self.math(b.text, display=True)}</div>'
        if b.kind == "rule":
            return '<hr class="sep">'
        if b.kind == "code":
            return self.code(b)
        if b.kind == "directive":
            return self.directive(b)
        raise RenderError(f"{self.page.path}:{b.line}: unknown block {b.kind}")

    def code(self, b: Block) -> str:
        if b.lang != "lean":
            return f'<pre class="shell">{html.escape(b.text)}</pre>'
        cell = self.site.cell_of.get(id(b))
        if cell is None:
            raise RenderError(f"{self.page.path}:{b.line}: a Lean block without a cell")
        return render_cell(self, cell)

    # Directives --------------------------------------------------------------

    def directive(self, b: Block) -> str:
        handler = getattr(self, "d_" + b.name.replace("-", "_"), None)
        if handler is None:
            raise RenderError(f"{self.page.path}:{b.line}: unknown directive {b.name!r}")
        return handler(b)

    def d_note(self, b: Block) -> str:
        return f'<aside class="note">{self.blocks(b.children)}</aside>'

    def d_figure(self, b: Block) -> str:
        self.figure_number += 1
        number = self.figure_number
        anchor = b.attrs.get("id", f"figure-{number}")
        self.anchors.add(anchor)
        caption = b.attrs.get("caption", "")
        children = list(b.children)
        if not caption and children and children[-1].kind == "para" and \
                children[-1].text.startswith("Caption:"):
            caption = children.pop().text[len("Caption:"):].strip()
        body = ""
        if "svg" in b.attrs:
            svg_path = self.site.figures_dir / b.attrs["svg"]
            if not svg_path.exists():
                self.fail("figure", f"no figure file {svg_path}")
            else:
                svg = svg_path.read_text(encoding="utf-8")
                svg = re.sub(r"<\?xml[^>]*>\s*", "", svg)
                body += f'<div class="svg">{svg}</div>'
        body += self.blocks(children)
        cls = "figure " + b.attrs.get("class", "")
        return (f'<figure class="{cls.strip()}" id="{anchor}"><div class="figure-body">{body}</div>'
                f'<figcaption><a class="fig-number" href="#{anchor}">Figure {number}.</a> '
                f"{self.inline(caption)}</figcaption></figure>")

    def d_usage(self, b: Block) -> str:
        """`code form` lines, each followed by `: meaning` lines."""
        rows: list[tuple[str, list[str]]] = []
        for line in b.text.split("\n"):
            s = line.strip()
            if not s:
                continue
            if s.startswith(": "):
                if not rows:
                    raise RenderError(f"{self.page.path}:{b.line}: usage meaning before a form")
                rows[-1][1].append(s[2:])
            else:
                rows.append((s, []))
        out = []
        for form, meaning in rows:
            form_html = self.inline(form)
            out.append(f'<div class="usage-row"><div class="usage-form">{form_html}</div>'
                       f'<div class="usage-meaning">{self.inline(" ".join(meaning))}</div></div>')
        return f'<section class="usage" aria-label="Usage">{"".join(out)}</section>'

    def d_commands(self, b: Block) -> str:
        """A guide's list of reference pages, in groups."""
        out = []
        groups = command_groups(b)
        for group, ids in groups:
            rows = []
            for page_id in ids:
                page = self.site.pages.get(page_id)
                if page is None:
                    self.fail("commands", f"no page {page_id!r}")
                    continue
                rows.append(f'<li><a class="sym" href="{self.page_href(page_id)}">'
                            f"{code_html(page.title)}</a>"
                            f'<span class="cmd-summary">{self.inline(page.summary)}</span></li>')
            head = f"<h3 id=\"{slug(group)}\">{self.inline(group)}</h3>" if group else ""
            if group:
                self.anchors.add(slug(group))
            out.append(f'<section class="cmd-group">{head}<ul class="cmd-list">{"".join(rows)}</ul>'
                       "</section>")
        return "".join(out)

    def d_guides(self, b: Block) -> str:
        """Every guide with its summary and its commands, for the documentation center."""
        cards = []
        for gid in self.site.guide_order:
            g = self.site.pages[gid]
            names = []
            for _, ids in self.site.guide_members.get(gid, []):
                for pid in ids:
                    if pid in self.site.pages and len(names) < 8:
                        names.append(f'<a href="{self.page_href(pid)}">'
                                     f"{code_html(self.site.pages[pid].title)}</a>")
            count = sum(len(ids) for _, ids in self.site.guide_members.get(gid, []))
            more = "" if count <= len(names) else \
                f' <a class="more" href="{self.page_href(gid)}">and {count - len(names)} more</a>'
            cards.append(f'<li class="guide-card"><h3><a href="{self.page_href(gid)}">'
                         f"{self.inline(g.title)}</a></h3><p>{self.inline(g.summary)}</p>"
                         f'<p class="guide-cmds">{" ".join(names)}{more}</p></li>')
        return f'<ul class="guide-grid">{"".join(cards)}</ul>'

    def d_tutorials(self, b: Block) -> str:
        items = []
        for tid in self.site.tutorial_order:
            t = self.site.pages[tid]
            items.append(f'<li><a href="{self.page_href(tid)}">{self.inline(t.title)}</a>'
                         f'<span class="cmd-summary">{self.inline(t.summary)}</span></li>')
        return f'<ul class="tutorial-list">{"".join(items)}</ul>'

    def d_az(self, b: Block) -> str:
        """Every reference page, by its first letter."""
        refs = [p for p in self.site.pages.values() if p.kind in REF_KINDS]
        refs.sort(key=lambda p: (p.title.lstrip("#").lower(), p.title))
        groups: dict[str, list[Page]] = {}
        for p in refs:
            groups.setdefault(p.title.lstrip("#")[:1].upper(), []).append(p)
        letters = " ".join(f'<a href="#letter-{k}">{k}</a>' for k in groups)
        sections = []
        for k, ps in groups.items():
            self.anchors.add(f"letter-{k}")
            rows = "".join(f'<li><a class="sym" href="{self.page_href(p.id)}">{code_html(p.title)}</a>'
                           f'<span class="cmd-summary">{self.inline(p.summary)}</span></li>' for p in ps)
            sections.append(f'<section class="az-group" id="letter-{k}"><h2>{k}</h2>'
                            f'<ul class="cmd-list">{rows}</ul></section>')
        return f'<p class="az-letters">{letters}</p>' + "".join(sections)

    def d_grid(self, b: Block) -> str:
        """A grid of small examples, each a `###` label and its cells."""
        cards: list[tuple[Block, list[Block]]] = []
        for child in b.children:
            if child.kind == "heading":
                cards.append((child, []))
            elif cards:
                cards[-1][1].append(child)
            else:
                raise RenderError(f"{self.page.path}:{b.line}: a grid starts with a ### label")
        out = []
        for head, body in cards:
            inner = []
            for blk in body:
                if blk.kind == "code" and blk.lang == "lean":
                    inner.append(render_cell(self, self.site.cell_of[id(blk)], compact=True))
                else:
                    inner.append(self.block(blk))
            out.append(f'<div class="grid-card"><h3>{self.inline(head.text)}</h3>{"".join(inner)}</div>')
        return f'<div class="grid">{"".join(out)}</div>'

    def d_teaser(self, b: Block) -> str:
        return f'<div class="teaser">{self.blocks(b.children)}</div>'

    def d_columns(self, b: Block) -> str:
        return f'<div class="columns">{self.blocks(b.children)}</div>'

    def d_aside(self, b: Block) -> str:
        return f'<aside class="aside">{self.blocks(b.children)}</aside>'

    def d_table(self, b: Block) -> str:
        """Rows of cells split at ` | `; the first row is the header."""
        rows = [[c.strip() for c in line.split(" | ")] for line in b.text.split("\n") if line.strip()]
        if len(rows) < 2:
            raise RenderError(f"{self.page.path}:{b.line}: a table needs a header and a row")
        if any(len(row) != len(rows[0]) for row in rows):
            raise RenderError(f"{self.page.path}:{b.line}: the rows of a table differ in length")
        head = "".join(f"<th>{self.inline(c)}</th>" for c in rows[0])
        body = "".join("<tr>" + "".join(f"<td>{self.inline(c)}</td>" for c in row) + "</tr>"
                       for row in rows[1:])
        return f'<table class="opts"><thead><tr>{head}</tr></thead><tbody>{body}</tbody></table>'


def command_groups(b: Block) -> list[tuple[str, list[str]]]:
    groups: list[tuple[str, list[str]]] = [("", [])]
    for line in b.text.split("\n"):
        s = line.strip()
        if not s:
            continue
        if s.startswith("### "):
            groups.append((s[4:].strip(), []))
        elif s.startswith("- "):
            groups[-1][1].append(s[2:].strip())
        else:
            raise RenderError(f"commands directive: cannot read {s!r}")
    return [(g, ids) for g, ids in groups if ids]


# ---------------------------------------------------------------------------
# Cells


_VALIDATION = {
    "proof term checked by the kernel against this proposition": ("kernel", "Checked by Lean’s kernel"),
    "completed proof checked by the elaborator; kernel check occurs when the declaration is accepted":
        ("elab", "Checked by the elaborator"),
}


def lean_pre(text: str, cls: str = "", hovers: list[dict] | None = None) -> str:
    classes = f"lean {cls}".strip()
    return f'<pre class="{classes}">{sitelean.highlight(text, hovers)}</pre>'


def render_value(value: str, big: bool = True) -> str:
    """A value of a report: typeset when it is an expression, with the plain form beside it."""
    tex = sitemath.cas_to_tex(value) if "\n" not in value else None
    plain = f'<code class="plain">{html.escape(value)}</code>'
    if tex and sitemath.is_worth_typesetting(tex):
        try:
            mathml = sitemath.tex_to_mathml(r"\displaystyle " + tex if big else tex, display=big)
        except sitemath.MathError:
            return plain
        return f'<div class="tf">{mathml}</div>{plain}'
    if "\n" in value:
        return f'<pre class="plain">{html.escape(value)}</pre>'
    return f'<code class="plain only">{html.escape(value)}</code>'


_PLAIN_QUALIFIERS = {"scalar ℝ", "scalar map ℝ → ℝ"}
_REAL_DOMAIN_RE = re.compile(r"^(?:[\w\u0370-\u03ff]+|\([\w\u0370-\u03ff, ]+\)) ∈ ℝ(?:\^\d+)?$|^ℝ$")


def qualifier_text(qualifier: str) -> str:
    """A qualifier without the parts that hold for almost every report, such as `scalar ℝ`."""
    parts = [q for q in qualifier.split("; ") if q.strip() not in _PLAIN_QUALIFIERS]
    return "; ".join(parts)


def shown_field(f: sitelean.Field) -> bool:
    """Whether a report field says more than the input cell already does."""
    if f.label == "Input":
        return qualifier_text(f.qualifier) != ""
    if f.label == "Domain":
        return not _REAL_DOMAIN_RE.match(f.value.strip())
    return True


def ticks_html(text: str) -> str:
    """Escaped text with its `backtick` spans as code."""
    return re.sub(r"`([^`]+)`", lambda m: code_html(html.unescape(m.group(1))), html.escape(text))


def conditions_html(value: str) -> str:
    """The conditions of a report, typeset when every one of them parses."""
    plain = f"<code>{html.escape(value)}</code>"
    parts = [c.strip() for c in value.split(";") if c.strip()]
    texs = [sitemath.cas_to_tex(c) for c in parts]
    if not parts or any(t is None for t in texs):
        return plain
    try:
        maths = [sitemath.tex_to_mathml(t, display=False) for t in texs]
    except sitemath.MathError:
        return plain
    return '<span class="conds">' + ", ".join(maths) + "</span>"


def _same_statement(a: str, b: str) -> bool:
    return " ".join(a.split()) == " ".join(b.split())


def render_report(r: PageRenderer, report: sitelean.Report, compact: bool = False) -> str:
    out = ['<div class="report">']
    steps = sitelean.find(report.nodes, "CAS.explanation.checkedStep")
    first = sitelean.step_parts(steps[0]).get("Proposition", "") if steps else ""
    outputs = [f for f in report.fields if f.label == "Output"]
    # A `Theorem` field that states the first checked step again is left to the theorem box.
    others = [f for f in report.fields if f.label != "Output" and shown_field(f)
              and not (f.label == "Theorem" and _same_statement(f.value, first))]
    for f in outputs:
        q = qualifier_text(f.qualifier)
        qual = f'<p class="qual">{html.escape(q)}</p>' if q else ""
        out.append(f'<div class="result">{qual}{render_value(f.value)}</div>')
    if others and not compact:
        rows = []
        for f in others:
            q = qualifier_text(f.qualifier)
            q = f' <span class="qual-inline">({html.escape(q)})</span>' if q else ""
            value = conditions_html(f.value) if f.label == "Conditions" else f"<code>{html.escape(f.value)}</code>"
            rows.append(f"<dt>{html.escape(f.label)}{q}</dt><dd>{value}</dd>")
        out.append(f'<dl class="fields">{"".join(rows)}</dl>')
    if steps:
        head = sitelean.step_parts(steps[0])
        prop = sitelean.dedent_continuation(head.get("Proposition", ""))
        level, badge = _VALIDATION.get(head.get("Validation", "").strip(), ("other", head.get("Validation", "")))
        thm = head.get("Theorem", "").strip()
        by = f'<p class="by">from <code>{html.escape(thm)}</code></p>' if thm and not compact else ""
        # A card joins Lean's lines of the statement and wraps it at its own width.
        statement = lean_pre(" ".join(prop.split()) if compact else prop)
        out.append(f'<div class="theorem"><p class="badge {level}"><span class="tick" aria-hidden="true">✓</span> '
                   f'{html.escape(badge)}: {ticks_html(steps[0].text)}</p>'
                   f"{statement}{by}</div>")
        if not compact:
            items = []
            for s in steps:
                parts = sitelean.step_parts(s)
                lv, bd = _VALIDATION.get(parts.get("Validation", "").strip(), ("other", parts.get("Validation", "")))
                t = parts.get("Theorem", "").strip()
                t_html = f' · <code>{html.escape(t)}</code>' if t else ""
                items.append(f'<li><p class="step-title">{ticks_html(s.text)}</p>'
                             f'{lean_pre(sitelean.dedent_continuation(parts.get("Proposition", "")))}'
                             f'<p class="step-meta"><span class="badge {lv}">{html.escape(bd)}</span>{t_html}</p></li>')
            out.append(f'<details class="cert"><summary>The certificate: {len(steps)} checked '
                       f'step{"s" if len(steps) != 1 else ""}</summary><ol class="steps">{"".join(items)}</ol>'
                       "</details>")
    comps = [n for n in report.nodes if n.tag == "CAS.Command.details"]
    comp_nodes = []
    for d in comps:
        comp_nodes.extend(c for c in d.children if c.tag == "CAS.Command.computation")
        comp_body = [line for line in d.body if line.strip()]
        if comp_body:
            comp_nodes.insert(0, sitelean.Node("", "", comp_body))
    if comp_nodes and not compact:
        out.append(f'<details class="comp"><summary>The computation</summary>'
                   f'{render_tree(comp_nodes)}</details>')
    if report.rest and not compact:
        out.append(f'<pre class="msg-rest">{html.escape(report.rest)}</pre>')
    out.append("</div>")
    return "".join(out)


def render_tree(nodes: list[sitelean.Node]) -> str:
    items = []
    for n in nodes:
        body = "\n".join(n.body)
        title = f'<p class="node-title">{html.escape(n.text)}</p>' if n.text else ""
        body_html = f'<pre class="node-body">{html.escape(body)}</pre>' if body.strip() else ""
        kids = render_tree(n.children) if n.children else ""
        items.append(f"<li>{title}{body_html}{kids}</li>")
    return f'<ul class="tree">{"".join(items)}</ul>'


_AXIOMS_RE = re.compile(r"^'(.+)' depends on axioms: \[(.*)\]\s*$", re.S)
_NO_AXIOMS_RE = re.compile(r"^'(.+)' does not depend on any axioms\s*$")


def render_message(r: PageRenderer, msg: dict, compact: bool = False) -> str:
    sev = msg["severity"]
    text = msg["data"].rstrip("\n")
    if sev == "information":
        report = sitelean.parse_report(text)
        if report is not None:
            return render_report(r, report, compact)
        m = _AXIOMS_RE.match(text)
        if m:
            axioms = [a.strip() for a in m.group(2).replace("\n", " ").split(",") if a.strip()]
            names = ", ".join(f"<code>{html.escape(a)}</code>" for a in axioms)
            return (f'<div class="msg axioms"><p><code>{html.escape(m.group(1))}</code> depends on the '
                    f"axioms {names}.</p></div>")
        m = _NO_AXIOMS_RE.match(text)
        if m:
            return (f'<div class="msg axioms"><p><code>{html.escape(m.group(1))}</code> depends on no '
                    "axioms.</p></div>")
        if text.startswith("Try this:"):
            suggestion = text[len("Try this:"):].strip()
            suggestion = re.sub(r"^\[apply\]\s*", "", suggestion)
            return (f'<div class="msg try"><p class="try-label">Try this</p>{lean_pre(suggestion)}</div>')
        return f'<pre class="msg info">{html.escape(text)}</pre>'
    label = "Error" if sev == "error" else "Warning"
    head, rest = sitelean.split_error(text)
    more = (f'<details class="more"><summary>The rest of the message</summary>'
            f"<pre>{html.escape(rest)}</pre></details>") if rest.strip() else ""
    return (f'<div class="msg {sev}"><p class="sev">{label}</p><pre>{html.escape(head)}</pre>{more}</div>')


def _proves_something(code: str) -> bool:
    return bool(re.search(r"^\s*(theorem|lemma|example)\b", code, re.M))


def render_cell(r: PageRenderer, cell: Cell, compact: bool = False) -> str:
    if cell.mode == "hidden":
        return ""
    n = cell.number
    in_label = f'<a class="label" href="#in-{n}">In[{n}]:=</a>' if not compact else \
        '<span class="label">In</span>'
    r.anchors.add(f"in-{n}")
    r.anchors.add(f"out-{n}")
    quote_note = ""
    if cell.mode == "quote":
        where = ("where <code>#guard_msgs</code> pins the output"
                 f'{" (the part shown)" if cell.pinned_substring else ""}') if cell.pinned \
            else "which Lean compiles"
        quote_note = (f'<p class="quote-note">Quoted from <a class="src" href="{GITHUB}/blob/main/'
                      f'{html.escape(cell.quote_file)}"><code>{html.escape(cell.quote_file)}</code></a>, '
                      f"{where}.</p>")
    parts = [f'<div class="cell in" id="in-{n}">{in_label}<div class="cell-body">'
             f"{lean_pre(cell.code.rstrip(chr(10)), hovers=cell.hovers)}{quote_note}</div></div>"]
    outs: list[str] = []
    if cell.mode == "quote":
        for sev, text in cell.pinned:
            if sev == "info" and cell.suggestion:
                shown = text + (" …" if cell.suggestion == "start" else "")
                outs.append(f'<div class="msg try"><p class="try-label">Try this</p>{lean_pre(shown)}</div>')
                continue
            msg = {"severity": "information" if sev == "info" else sev, "data": text}
            report = _pinned_report(text) if sev == "info" else None
            outs.append(render_report(r, report, compact) if report else render_message(r, msg, compact))
    else:
        for msg in cell.messages:
            outs.append(render_message(r, msg, compact))
    if not outs and _proves_something(cell.code) and cell.mode != "error":
        outs.append('<div class="msg ok"><p><span class="tick" aria-hidden="true">✓</span> '
                    "Lean accepts the proof.</p></div>")
    if outs:
        out_label = f'<span class="label">Out[{n}]=</span>' if not compact else \
            '<span class="label">Out</span>'
        parts.append(f'<div class="cell out" id="out-{n}">{out_label}<div class="cell-body">'
                     f'{"".join(outs)}</div></div>')
    cls = "cells compact" if compact else "cells"
    return f'<div class="{cls}">{"".join(parts)}</div>'


def _pinned_report(text: str) -> sitelean.Report | None:
    fields = []
    for line in text.split("\n"):
        f = sitelean._parse_field(line.strip())
        if f is None:
            return None
        fields.append(f)
    if not any(f.label == "Output" for f in fields):
        return None
    return sitelean.Report("#cas", fields, [], "")


# ---------------------------------------------------------------------------
# The page shell


def nav_tree(r: PageRenderer) -> str:
    site = r.site
    current = r.page.id
    # A page listed in several guides opens one of them, the one of its breadcrumb.
    guides = site.guides_of(current)
    home = r.page.meta.get("guide")
    open_guides = {home} if home in guides else set(guides[:1])
    if r.page.kind == "guide":
        open_guides.add(current)
    home_cur = ' aria-current="page"' if r.page.kind == "docs" else ""
    parts = [f'<p class="nav-home"><a href="{r.rel("docs/index.html")}"{home_cur}>Documentation</a></p>']
    parts.append('<p class="nav-heading">Guides</p>')
    for gid in site.guide_order:
        g = site.pages[gid]
        items = []
        for _, ids in site.guide_members.get(gid, []):
            for pid in ids:
                if pid not in site.pages:
                    continue
                cur = ' aria-current="page"' if pid == current else ""
                items.append(f'<li><a href="{r.page_href(pid)}"{cur}>{code_html(site.pages[pid].title)}</a></li>')
        is_open = " open" if gid in open_guides else ""
        cur = ' aria-current="page"' if gid == current else ""
        parts.append(f'<details{is_open}><summary><a href="{r.page_href(gid)}"{cur}>'
                     f"{r.inline(g.title)}</a></summary><ul>{''.join(items)}</ul></details>")
    parts.append('<p class="nav-heading">Tutorials</p><ul class="nav-flat">')
    for tid in site.tutorial_order:
        cur = ' aria-current="page"' if tid == current else ""
        parts.append(f'<li><a href="{r.page_href(tid)}"{cur}>{r.inline(site.pages[tid].title)}</a></li>')
    parts.append("</ul>")
    cur = ' aria-current="page"' if r.page.kind == "index" else ""
    parts.append(f'<p class="nav-heading"><a href="{r.rel("docs/all.html")}"{cur}>Index A to Z</a></p>')
    return f'<nav class="sidebar" aria-label="Documentation">{"".join(parts)}</nav>'


def breadcrumb(r: PageRenderer) -> str:
    page = r.page
    crumbs = [f'<a href="{r.rel("docs/index.html")}">Documentation</a>']
    if page.kind in REF_KINDS:
        guides = r.site.guides_of(page.id)
        home = page.meta.get("guide")
        if home in guides:
            guides = [home]
        if guides:
            crumbs.append(f'<a href="{r.page_href(guides[0])}">{r.inline(r.site.pages[guides[0]].title)}</a>')
    elif page.kind == "tutorial":
        crumbs.append(f'<a href="{r.rel("docs/index.html")}#tutorials">Tutorials</a>')
    if page.kind != "docs":
        crumbs.append(f'<span aria-current="page">{r.inline(page.title) if page.kind not in REF_KINDS else code_html(page.title)}</span>')
    sep = ' <span class="sep">›</span> '
    return f'<nav class="crumbs" aria-label="Breadcrumb">{sep.join(crumbs)}</nav>'


def topbar(r: PageRenderer) -> str:
    def item(path: str, label: str, active: bool) -> str:
        cur = ' aria-current="page"' if active else ""
        return f'<a href="{r.rel(path)}"{cur}>{label}</a>'
    kind = r.page.kind
    return ('<header class="topbar"><div class="topbar-inner">'
            f'<a class="brand" href="{r.rel("index.html")}">{logo(r, "brand-logo")}</a><nav class="top-nav">'
            + item("docs/index.html", "Docs", kind not in ("home", "index") and r.page.id != "first-hour")
            + item("docs/tutorial/first-hour.html", "Getting started", r.page.id == "first-hour")
            + item("docs/all.html", "Index", kind == "index")
            + f'<a class="code-button" href="{GITHUB}">Code</a></nav></div></header>')


def logo(r: PageRenderer, cls: str) -> str:
    """The SymLean logo, with the light version for a dark color scheme."""
    return (f'<picture class="{cls}"><source media="(prefers-color-scheme: dark)" '
            f'srcset="{r.rel("static/brand/symlean-logo-dark.png")}">'
            f'<img src="{r.rel("static/brand/symlean-logo.png")}" alt="SymLean" width="960" height="252">'
            '</picture>')


def shell(r: PageRenderer, body: str, with_nav: bool) -> str:
    page = r.page
    title = page.meta.get("html_title") or (f"{page.title} · SymLean" if page.kind != "home" else "SymLean")
    title = re.sub(r"[`*$]", "", re.sub(r"<[^>]+>", "", title))
    desc = html.escape(re.sub(r"[`$*]", "", page.summary), quote=True)
    layout = (f'<div class="docs">{nav_tree(r)}<main class="doc" id="main">{body}</main></div>'
              if with_nav else f'<main class="home" id="main">{body}</main>')
    footer = (f'<footer class="footer"><p>{r.inline(r.site.footer_note)}</p>'
              f'<p><a href="{GITHUB}">SymLean on GitHub</a> · Apache License 2.0</p></footer>')
    return ("<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n"
            '<meta name="viewport" content="width=device-width, initial-scale=1">\n'
            f"<title>{html.escape(title)}</title>\n"
            f'<meta name="description" content="{desc}">\n'
            f'<link rel="stylesheet" href="{r.rel("static/site.css")}">\n'
            f'<link rel="icon" type="image/png" href="{r.rel("static/brand/favicon.png")}">\n'
            f'<link rel="apple-touch-icon" href="{r.rel("static/brand/apple-touch-icon.png")}">\n'
            f'<meta property="og:title" content="{html.escape(title, quote=True)}">\n'
            f'<meta property="og:description" content="{desc}">\n'
            f'<meta property="og:image" content="{SITE_URL}static/brand/social-preview.png">\n'
            '<meta name="twitter:card" content="summary_large_image">\n'
            f"</head>\n<body class=\"kind-{page.kind}\">\n"
            '<a class="skip" href="#main">Skip to the content</a>\n'
            f"{topbar(r)}\n{layout}\n{footer}\n"
            f'<script defer src="{r.rel("static/site.js")}"></script>\n</body>\n</html>\n')


def page_head(r: PageRenderer) -> str:
    page = r.page
    label = KIND_LABELS.get(page.kind, "")
    label_html = f'<p class="kind">{html.escape(label)}</p>' if label else ""
    title_html = code_html(page.title) if page.kind in REF_KINDS else r.inline(page.title)
    summary = f'<p class="summary">{r.inline(page.summary)}</p>' if page.summary else ""
    return f'<header class="page-head">{label_html}<h1>{title_html}</h1>{summary}</header>'


def ref_sections(r: PageRenderer) -> str:
    """The body of a reference page: Details and Options and the Examples as sections."""
    blocks = r.page.blocks
    out: list[str] = []
    k = 0
    n = len(blocks)
    while k < n:
        b = blocks[k]
        if b.kind == "heading" and b.level == 2 and b.text == "Details and Options":
            j = k + 1
            while j < n and not (blocks[j].kind == "heading" and blocks[j].level == 2):
                j += 1
            r.anchors.add("details")
            out.append('<details class="section details-options" id="details" open>'
                       '<summary><h2>Details and Options</h2></summary>'
                       f"{r.blocks(blocks[k + 1:j])}</details>")
            k = j
            continue
        if b.kind == "heading" and b.level == 2 and b.text == "Examples":
            j = k + 1
            while j < n and not (blocks[j].kind == "heading" and blocks[j].level == 2):
                j += 1
            out.append(examples(r, blocks[k + 1:j], b))
            k = j
            continue
        out.append(r.block(b))
        k += 1
    return "\n".join(out)


def _count_examples(blocks: list[Block]) -> int:
    count, has = 0, False
    for b in blocks:
        if b.kind == "rule":
            count += has
            has = False
        elif b.kind in ("code", "para", "list", "math", "directive"):
            has = True
    return count + has


def examples(r: PageRenderer, blocks: list[Block], head: Block) -> str:
    sections: list[tuple[Block, list[Block]]] = []
    lead: list[Block] = []
    for b in blocks:
        if b.kind == "heading" and b.level == 3:
            sections.append((b, []))
        elif sections:
            sections[-1][1].append(b)
        else:
            lead.append(b)
    total = sum(_count_examples(body) for _, body in sections)
    parts = [f'<section class="examples" id="examples"><h2>Examples <span class="count">({total})</span>'
             '<a class="anchor" href="#examples" aria-label="Link to this section">#</a></h2>']
    r.anchors.add("examples")
    parts.append(r.blocks(lead))
    for sec_head, body in sections:
        if sec_head.text not in EXAMPLE_SECTIONS:
            r.fail("examples", f"unknown examples section {sec_head.text!r}")
        anchor = slug(sec_head.text)
        r.anchors.add(anchor)
        is_open = " open" if sec_head.text == "Basic Examples" else ""
        parts.append(f'<details class="ex-section" id="{anchor}"{is_open}><summary><h3>{html.escape(sec_head.text)} '
                     f'<span class="count">({_count_examples(body)})</span></h3></summary>'
                     f'<div class="ex-body">{r.blocks(body)}</div></details>')
    parts.append("</section>")
    return "".join(parts)


def see_also(r: PageRenderer) -> str:
    page = r.page
    out = []
    ids = page.meta.get("see_also", [])
    if ids:
        links = []
        for pid in ids:
            if pid not in r.site.pages:
                r.fail("see_also", f"no page {pid!r}")
                continue
            links.append(f'<a class="sym" href="{r.page_href(pid)}">{code_html(r.site.pages[pid].title)}</a>')
        r.anchors.add("see-also")
        out.append(f'<section class="see-also" id="see-also"><h2>See Also</h2>'
                   f'<p class="sym-row">{DOT.join(links)}</p></section>')
    guides = r.site.guides_of(page.id) if page.kind in REF_KINDS else page.meta.get("related_guides", [])
    if guides:
        r.anchors.add("related-guides")
        items = "".join(f'<li><a href="{r.page_href(g)}">{r.inline(r.site.pages[g].title)}</a></li>'
                        for g in guides if g in r.site.pages)
        out.append(f'<section class="related" id="related-guides"><h2>Related Guides</h2><ul>{items}</ul></section>')
    tutorials = page.meta.get("tutorials", [])
    if tutorials:
        r.anchors.add("tutorials")
        items = []
        for t in tutorials:
            if t not in r.site.pages:
                r.fail("tutorials", f"no page {t!r}")
                continue
            items.append(f'<li><a href="{r.page_href(t)}">{r.inline(r.site.pages[t].title)}</a></li>')
        out.append(f'<section class="related" id="tutorials"><h2>Tutorials</h2><ul>{"".join(items)}</ul></section>')
    return "".join(out)


def render_home(r: PageRenderer) -> str:
    m = r.page.meta
    authors = " · ".join(html.escape(a) for a in m.get("authors", []))
    buttons = [f'<a class="button primary" href="{GITHUB}">Code</a>',
               f'<a class="button" href="{r.rel("docs/index.html")}">Documentation</a>',
               f'<a class="button" href="{r.rel("docs/tutorial/first-hour.html")}">Getting started</a>']
    hero = (f'<header class="hero"><h1>{logo(r, "hero-logo")}</h1>'
            f'<p class="tagline">{r.inline(m.get("tagline", ""))}</p>'
            f'<p class="authors">{authors}</p>'
            f'<p class="affiliation">{html.escape(m.get("affiliation", ""))}</p>'
            f'<p class="buttons">{"".join(buttons)}</p></header>')
    return hero + r.blocks(r.page.blocks)


def render_page(site: Site, page: Page) -> tuple[str, set[str]]:
    r = PageRenderer(site, page)
    if page.kind == "home":
        body = render_home(r)
        return shell(r, body, with_nav=False), r.anchors
    head = breadcrumb(r) + page_head(r)
    if page.kind in REF_KINDS:
        body = head + ref_sections(r) + see_also(r)
    else:
        body = head + r.blocks(page.blocks) + see_also(r)
    return shell(r, body, with_nav=True), r.anchors
