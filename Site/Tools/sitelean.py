# Copyright (c) 2026 SymLean Team. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""The Lean side of the SymLean site: checked sessions and compiler-exported hovers.

Each page is one Lean file, a notebook session: `import CAS`, the page's own imports, then its
cells in order. `run_pages` compiles the files (in parallel, with a cache keyed on the file, the
toolchain and the build of the imported modules) and gives each cell the messages Lean reported
on its lines. `check_cells` holds each cell to what its fence says: a `lean` cell compiles without
errors or warnings, a `lean error` cell reports an error, a `lean quote=FILE` cell appears
verbatim in FILE, which the library's tests compile, and shows the output pinned there, and a cell
with `expect="TEXT"` prints TEXT in one of its messages.

`parse_report` reads the message of a `#cas` command into its header and its trace tree, and
`highlight` marks up Lean source.
"""

from __future__ import annotations

import concurrent.futures
import hashlib
import html
import json
import os
import re
import resource
import subprocess
from dataclasses import dataclass, field
from pathlib import Path

PREAMBLE = ["import CAS"]
OPTIONS = [
    "-Dpp.unicode.fun=true",
    "-DautoImplicit=false",
    "-DrelaxedAutoImplicit=false",
    "-Dweak.cega.nativeCertificates=false",
]


@dataclass
class Cell:
    page: str
    source: str  # file:line of the fence
    code: str
    mode: str  # run, error, hidden, quote
    number: int = 0  # In[n]/Out[n]; 0 for hidden cells
    quote_file: str = ""
    start: int = 0  # lines of the cell in the page's Lean file
    end: int = 0
    messages: list[dict] = field(default_factory=list)
    pinned: list[tuple[str, str]] = field(default_factory=list)  # quote cells: (severity, text)
    pinned_substring: bool = False
    suggestion: str = ""  # quote cells: "true" when the pinned information is a suggestion, "start" for its start
    expect: str = ""  # text that one of the cell's messages must contain
    hovers: list[dict] = field(default_factory=list)


class CellError(Exception):
    """A cell whose messages do not fit its fence."""


def lean_file(imports: list[str], cells: list[Cell]) -> str:
    """The Lean file of a page; sets the line range of each compiled cell."""
    lines = PREAMBLE + [f"import {m}" for m in imports] + ["", "set_option linter.hashCommand false", ""]
    for cell in cells:
        if cell.mode == "quote":
            continue
        code = cell.code.rstrip("\n").split("\n")
        cell.start = len(lines) + 1
        lines.extend(code)
        cell.end = len(lines)
        lines.append("")
    return "\n".join(lines) + "\n"


def module_traces(repo: Path, imports: list[str]) -> str:
    """The Lake traces of the imported modules, which change when their build changes."""
    roots = [repo / ".lake/build/lib/lean"] + sorted(repo.glob(".lake/packages/*/.lake/build/lib/lean"))
    out = []
    for module in ["CAS"] + imports:
        rel = module.replace(".", "/") + ".trace"
        trace = next((root / rel for root in roots if (root / rel).exists()), None)
        out.append(trace.read_text(encoding="utf-8") if trace else f"missing {module}")
    return "\n".join(out)


@dataclass
class LeanRunner:
    repo: Path
    lean: str
    lean_path: str
    cache: Path
    work: Path
    jobs: int = 4
    threads: int = 2
    timeout: int = 1800
    mem_gb: int = 0
    version: str = ""

    def __post_init__(self) -> None:
        self.cache.mkdir(parents=True, exist_ok=True)
        self.work.mkdir(parents=True, exist_ok=True)
        if not self.version:
            self.version = subprocess.run([self.lean, "--version"], capture_output=True, text=True,
                                          check=True).stdout.strip()

    def _limit(self) -> None:
        if self.mem_gb:
            limit = self.mem_gb * 1024 ** 3
            resource.setrlimit(resource.RLIMIT_AS, (limit, limit))

    def key(self, text: str, imports: list[str]) -> str:
        h = hashlib.sha256()
        driver = (self.repo / "Site/Tools/CheckPage.lean").read_text(encoding="utf-8")
        for part in (text, self.version, " ".join(OPTIONS), module_traces(self.repo, imports), driver):
            h.update(part.encode("utf-8"))
            h.update(b"\0")
        return h.hexdigest()

    def run_one(self, name: str, text: str, imports: list[str], cells: list[Cell]) -> tuple[dict, bool]:
        """The messages of one Lean file, and whether they came from the cache."""
        boundaries = [{"start": c.start, "end": c.end, "mode": c.mode}
                      for c in cells if c.mode != "quote"]
        key = self.key(text + json.dumps(boundaries), imports)
        cached = self.cache / f"{key}.json"
        if cached.exists():
            return json.loads(cached.read_text(encoding="utf-8")), True
        path = self.work / f"{name}.lean"
        path.write_text(text, encoding="utf-8")
        cells_path = self.work / f"{name}.cells.json"
        output_path = self.work / f"{name}.info.json"
        cells_path.write_text(json.dumps(boundaries), encoding="utf-8")
        env = dict(os.environ, LEAN_PATH=self.lean_path)
        cmd = [self.lean, f"-j{self.threads}", "--run", str(self.repo / "Site/Tools/CheckPage.lean"),
               str(path), str(cells_path), str(output_path)]
        try:
            proc = subprocess.run(cmd, cwd=self.repo, env=env, capture_output=True, text=True,
                                  timeout=self.timeout, preexec_fn=self._limit)
        except subprocess.TimeoutExpired as err:
            raise CellError(f"{name}: lean did not finish within {self.timeout} s") from err
        if proc.returncode != 0:
            raise CellError(f"{name}: lean exited with {proc.returncode}: "
                            f"{proc.stderr[-2000:]}\n{proc.stdout[-2000:]}")
        result = json.loads(output_path.read_text(encoding="utf-8"))
        cached.write_text(json.dumps(result, ensure_ascii=False), encoding="utf-8")
        return result, False

    def run_pages(self, jobs: dict[str, tuple[str, list[str], list[Cell]]], log) -> dict[str, dict]:
        """The messages of each page's file; `jobs` maps a page id to its file and imports."""
        results: dict[str, dict] = {}
        errors: list[str] = []
        with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, self.jobs)) as pool:
            futures = {pool.submit(self.run_one, name, text, imports, cells): name
                       for name, (text, imports, cells) in jobs.items()}
            for future in concurrent.futures.as_completed(futures):
                name = futures[future]
                try:
                    messages, hit = future.result()
                except CellError as err:
                    errors.append(str(err))
                    continue
                results[name] = messages
                log(f"{'cached' if hit else 'compiled'} {name}")
        if errors:
            raise CellError("\n".join(errors))
        return results


def assign_messages(name: str, cells: list[Cell], messages: list[dict]) -> list[str]:
    """Give each cell the messages on its lines; the problems of messages outside every cell."""
    problems = []
    for msg in messages:
        line = msg["pos"]["line"]
        for cell in cells:
            if cell.mode != "quote" and cell.start <= line <= cell.end:
                cell.messages.append(msg)
                break
        else:
            problems.append(f"{name}.lean:{line}: {msg['severity']}: {msg['data'][:400]}")
    return problems


def check_cells(cells: list[Cell]) -> list[str]:
    """The problems of cells whose messages do not fit their fences."""
    problems = []
    for cell in cells:
        severities = [m["severity"] for m in cell.messages]
        if cell.mode in ("run", "hidden"):
            bad = [m for m in cell.messages if m["severity"] in ("error", "warning")]
            for m in bad:
                problems.append(f"{cell.source}: {m['severity']} in a cell that must compile "
                                f"cleanly:\n{m['data'][:1500]}")
        elif cell.mode == "error":
            if "error" not in severities:
                problems.append(f"{cell.source}: a 'lean error' cell compiled without an error")
        if cell.expect and not any(cell.expect in m["data"] for m in cell.messages):
            problems.append(f"{cell.source}: the output does not contain {cell.expect!r}")
    return problems


def assign_hovers(cells: list[Cell], source: str, hovers: list[dict]) -> None:
    """Keep compiler byte ranges relative to each visible cell, including Unicode identifiers."""
    offsets = [0]
    for line in source.splitlines(keepends=True):
        offsets.append(offsets[-1] + len(line.encode("utf-8")))
    for cell in cells:
        if cell.mode == "quote":
            continue
        start = offsets[cell.start - 1]
        end = start + len(cell.code.rstrip("\n").encode("utf-8"))
        unique = {}
        for item in hovers:
            if start <= item["start"] < item["end"] <= end:
                relative = dict(item, start=item["start"] - start, end=item["end"] - start)
                unique[(relative["start"], relative["end"], relative["kind"], relative["text"])] = relative
        cell.hovers = list(unique.values())


# ---------------------------------------------------------------------------
# Quoted cells


_GUARD_RE = re.compile(r"#guard_msgs\b([^\n]*?)\bin\s*\Z")


def read_quote(repo: Path, cell: Cell) -> str | None:
    """Fill in the pinned output of a quoted cell; the problem if the quote is not in its file."""
    path = repo / cell.quote_file
    if not path.exists():
        return f"{cell.source}: the quoted file {cell.quote_file} does not exist"
    text = path.read_text(encoding="utf-8")
    code = cell.code.strip("\n")
    # The quote is whole lines of code: not a prefix of a longer line, and not inside a comment
    # or a docstring, where `#guard_msgs` pins repeat the commands.
    found = []
    pos = text.find(code)
    while pos >= 0:
        end = pos + len(code)
        whole = (pos == 0 or text[pos - 1] == "\n") and (end == len(text) or text[end] == "\n")
        if whole and text.rfind("/-", 0, pos) <= text.rfind("-/", 0, pos):
            found.append(pos)
        pos = text.find(code, pos + 1)
    if not found:
        return f"{cell.source}: the cell does not appear verbatim in {cell.quote_file}"
    if len(found) > 1 and not re.match(r"\s*(theorem|example|#cas)", code):
        return f"{cell.source}: the cell appears more than once in {cell.quote_file}"
    # A `#guard_msgs ... in` right before the quote pins its messages, in the docstring before it.
    # A command quoted more than once takes its first pinned occurrence.
    cell.pinned = []
    for pos in found:
        before = text[:pos].rstrip()
        m = _GUARD_RE.search(before)
        if not m:
            continue
        doc = before[:m.start()].rstrip()
        start = doc.rfind("/--")
        if doc.endswith("-/") and start >= 0:
            cell.pinned_substring = "substring := true" in m.group(1)
            cell.pinned = _guard_messages(doc[start + 3:-2])
            break
    return None


def _guard_messages(body: str) -> list[tuple[str, str]]:
    body = body.strip("\n")
    out = []
    for chunk in re.split(r"\n---\n", body):
        chunk = chunk.strip()
        m = re.match(r"(info|warning|error|trace):\s?(.*)", chunk, re.S)
        if m:
            out.append((m.group(1), m.group(2).strip()))
        elif chunk:
            out.append(("info", chunk))
    return out


# ---------------------------------------------------------------------------
# Reports of `#cas`


@dataclass
class Field:
    label: str
    qualifier: str
    value: str


@dataclass
class Node:
    tag: str
    text: str
    body: list[str] = field(default_factory=list)
    children: list["Node"] = field(default_factory=list)


@dataclass
class Report:
    command: str
    fields: list[Field]
    nodes: list[Node]
    rest: str  # text after the header that is not a trace tree


_FIELD_START_RE = re.compile(r"^([A-Za-zρσλμ][A-Za-z0-9ρσλμ₀-₉' ]{0,40}?)(?=: | \(|:$)")


def _parse_field(line: str) -> Field | None:
    m = _FIELD_START_RE.match(line)
    if not m:
        return None
    label = m.group(1)
    rest = line[len(label):]
    qualifier = ""
    if rest.startswith(" ("):
        depth, k = 0, 1
        while k < len(rest):
            if rest[k] == "(":
                depth += 1
            elif rest[k] == ")":
                depth -= 1
                if depth == 0:
                    break
            k += 1
        if depth != 0:
            return None
        qualifier = rest[2:k]
        rest = rest[k + 1:]
    if not rest.startswith(":"):
        return None
    return Field(label, qualifier, rest[1:].strip())


def _indent(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


_TAG_RE = re.compile(r"^\[([A-Za-z0-9_.]+)\]\s?(.*)$")


def _parse_tree(lines: list[str]) -> list[Node]:
    roots: list[Node] = []
    stack: list[tuple[int, Node]] = []
    for line in lines:
        if not line.strip():
            continue
        ind = _indent(line)
        m = _TAG_RE.match(line.strip())
        if m:
            node = Node(m.group(1), m.group(2))
            while stack and stack[-1][0] >= ind:
                stack.pop()
            (stack[-1][1].children if stack else roots).append(node)
            stack.append((ind, node))
        else:
            while stack and stack[-1][0] >= ind:
                stack.pop()
            if stack:
                stack[-1][1].body.append(line[stack[-1][0] + 2:] if ind >= stack[-1][0] + 2 else line.strip())
            else:
                roots.append(Node("", line.strip()))
    return roots


def parse_report(text: str) -> Report | None:
    """The parts of a `#cas` report, or None if `text` is not one."""
    lines = text.split("\n")
    if not lines or not lines[0].startswith("#cas"):
        return None
    fields: list[Field] = []
    k = 1
    while k < len(lines) and lines[k].strip():
        line = lines[k]
        f = _parse_field(line)
        if f is None:
            if fields and line.startswith(" "):
                fields[-1].value += "\n" + line.strip()
            elif fields:
                # An unlabelled line continues the last field (a wrapped value).
                fields[-1].value += "\n" + line
            else:
                return None
        else:
            fields.append(f)
        k += 1
    if not any(f.label == "Output" for f in fields):
        return None
    tail = lines[k + 1:]
    nodes = _parse_tree(tail) if any(_TAG_RE.match(t.strip()) for t in tail) else []
    rest = "" if nodes else "\n".join(tail).strip()
    return Report(lines[0], fields, nodes, rest)


def find(nodes: list[Node], tag: str) -> list[Node]:
    out = []
    for node in nodes:
        if node.tag == tag:
            out.append(node)
        out.extend(find(node.children, tag))
    return out


def step_parts(node: Node) -> dict[str, str]:
    """`Proposition`, `Validation` and `Theorem` of a checked step, continuation lines joined."""
    parts: dict[str, str] = {}
    key = ""
    for line in node.body:
        m = re.match(r"^(Proposition|Validation|Theorem|Statement|Proof|Lemma): ?(.*)$", line)
        if m and not line.startswith(" "):
            key = m.group(1)
            parts[key] = m.group(2)
        elif key:
            parts[key] += "\n" + line
        else:
            parts.setdefault("Note", "")
            parts["Note"] += line + "\n"
    return parts


def dedent_continuation(text: str) -> str:
    """A multi-line proposition with its continuation lines dedented by the label's indent."""
    lines = text.split("\n")
    if len(lines) == 1:
        return text
    rest = lines[1:]
    common = min((_indent(x) for x in rest if x.strip()), default=0)
    shift = max(0, common - 2)
    return "\n".join([lines[0]] + [x[shift:] for x in rest])


# ---------------------------------------------------------------------------
# Errors


def split_error(text: str) -> tuple[str, str]:
    """The first paragraph of an error message and the rest, which the page folds."""
    lines = text.split("\n")
    if len(lines) <= 8:
        return text, ""
    for k in range(1, len(lines) - 1):
        line, nxt = lines[k], lines[k + 1]
        if not line.startswith(" ") and line.rstrip().endswith(":") and nxt.startswith(" "):
            return "\n".join(lines[:k]), "\n".join(lines[k:])
        if not line.strip():
            return "\n".join(lines[:k]), "\n".join(lines[k + 1:])
    return "\n".join(lines[:6]), "\n".join(lines[6:])


# ---------------------------------------------------------------------------
# Highlighting

_KEYWORDS = set("""theorem lemma example def abbrev variable open namespace section end by fun
have show from at with in if then else let set_option import noncomputable instance where calc
do return match universe local private public protected attribute""".split())
_TACTICS = set("""cas cas? cas_nf cega cega? simp simp_all norm_num ring ring_nf linarith nlinarith
positivity exact intro intros rw rewrite apply refine constructor decide field_simp grind using
exact? apply? rfl use obtain rcases cases induction unfold conv norm_cast push_cast gcongr
filter_upwards""".split())
_TYPES = set("ℝ ℂ ℕ ℤ ℚ Prop Type Sort".split())

_LEAN_TOKEN_RE = re.compile(
    r"""
    (?P<comment>--[^\n]*|/-.*?-/)
  | (?P<string>"(?:\\.|[^"\\])*")
  | (?P<placeholder>‹[^›\n]*›)
  | (?P<command>\#[a-z_]+)
  | (?P<name>[A-Za-z_Ͱ-Ͽἀ-῿℀-⅏\U0001d400-\U0001d7ff]
       [A-Za-z0-9_'!?.Ͱ-Ͽἀ-῿₀-ₜᵢⱼ℀-⅏\U0001d400-\U0001d7ff]*)
  | (?P<number>\d+(?:\.\d+)?)
  | (?P<other>.)
    """,
    re.S | re.VERBOSE,
)


_MODE_RE = re.compile(r"#cas\s*\[\s*([A-Za-z]+)")


def highlight(code: str, hovers: list[dict] | None = None) -> str:
    """HTML for Lean source: keywords, tactics, commands, modes, numbers and comments marked."""
    modes = {m.start(1) for m in _MODE_RE.finditer(code)}
    out: list[str] = []
    for m in _LEAN_TOKEN_RE.finditer(code):
        kind = m.lastgroup
        text = m.group(0)
        esc = html.escape(text, quote=False)
        if kind == "comment":
            rendered = f'<span class="c">{esc}</span>'
        elif kind == "string":
            rendered = f'<span class="s">{esc}</span>'
        elif kind == "placeholder":
            rendered = f"<var>{html.escape(text[1:-1], quote=False)}</var>"
        elif kind == "command":
            rendered = f'<span class="k">{esc}</span>'
        elif kind == "name" and m.start() in modes:
            rendered = f'<span class="m">{esc}</span>'
        elif kind == "name" and text in _KEYWORDS:
            rendered = f'<span class="k">{esc}</span>'
        elif kind == "name" and (text in _TACTICS or text.rstrip("?") in ("cas", "cega")):
            rendered = f'<span class="t">{esc}</span>'
        elif kind == "name" and text in _TYPES:
            rendered = f'<span class="ty">{esc}</span>'
        elif kind == "number":
            rendered = f'<span class="n">{esc}</span>'
        elif kind == "other" and text in "ℝℂℕℤℚ":
            rendered = f'<span class="ty">{esc}</span>'
        else:
            rendered = esc
        if hovers and kind not in ("comment", "string", "other"):
            start = len(code[:m.start()].encode("utf-8"))
            stop = start + len(text.encode("utf-8"))
            matches = [h for h in hovers if h["start"] <= start and stop <= h["end"]
                       and (h["kind"] != "command" or kind == "command")]
            if matches:
                item = min(matches, key=lambda h: (h["kind"] != "term", h["end"] - h["start"]))
                tip = html.escape(item["text"], quote=True)
                rendered = (f'<span class="lean-hover" tabindex="0" data-lean-hover="{tip}" '
                            f'title="{tip}">{rendered}</span>')
        out.append(rendered)
    return "".join(out)
