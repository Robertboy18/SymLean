# Copyright (c) 2026 SymLean Team. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Build the SymLean website from `Site/Pages`: compile every example, render static HTML, check it.

    python3 Site/Tools/sitegen.py --out _out/site [--registry _out/CommandRegistry.json]

Every Lean cell of a page is compiled against the built library when the site is built, and the
page shows what Lean printed. MathML and compiler-exported hovers work offline; the only script
displays those hovers. The build fails on a cell whose messages do not fit its fence (an
`expect="TEXT"` cell must print TEXT), a broken link or anchor, an unexpected script, or a
reference page that names a form the registry does not have (and a registry form that no page
documents).

`Site/Tools/build.sh` builds the library and the registry first and then runs this program; see
`--help` for the settings.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path
from urllib.parse import unquote, urlsplit

sys.path.insert(0, str(Path(__file__).resolve().parent))

import sitehtml  # noqa: E402
import sitelean  # noqa: E402
import siteparse  # noqa: E402

TOOLS = Path(__file__).resolve().parent
REPO = TOOLS.parent.parent


def out_path(page: siteparse.Page) -> str:
    kind = page.kind
    if kind == "home":
        return "index.html"
    if kind == "docs":
        return "docs/index.html"
    if kind == "index":
        return "docs/all.html"
    if kind == "guide":
        return f"docs/guide/{page.id}.html"
    if kind == "tutorial":
        return f"docs/tutorial/{page.id}.html"
    return f"docs/ref/{page.id}.html"


def collect_cells(pages: list[siteparse.Page]) -> tuple[dict[str, list[sitelean.Cell]], dict[int, sitelean.Cell]]:
    cells: dict[str, list[sitelean.Cell]] = {}
    cell_of: dict[int, sitelean.Cell] = {}
    for page in pages:
        number = 0
        page_cells = []
        for block in siteparse.walk(page.blocks):
            if block.kind != "code" or block.lang != "lean":
                continue
            attrs = block.attrs
            if "quote" in attrs:
                mode = "quote"
            elif "error" in attrs:
                mode = "error"
            elif "hidden" in attrs:
                mode = "hidden"
            else:
                mode = "run"
            unknown = set(attrs) - {"quote", "error", "hidden", "suggestion", "expect"}
            if unknown:
                raise siteparse.SourceError(f"{page.path}:{block.line}: unknown cell attributes {sorted(unknown)}")
            if "expect" in attrs and (mode == "quote" or not attrs["expect"]):
                raise siteparse.SourceError(f"{page.path}:{block.line}: `expect=TEXT` needs a text "
                                            "and goes on a compiled cell")
            if "suggestion" in attrs and (mode != "quote" or attrs["suggestion"] not in ("true", "start")):
                raise siteparse.SourceError(f"{page.path}:{block.line}: `suggestion` or `suggestion=start` "
                                            "goes on a quoted cell")
            if mode != "hidden":
                number += 1
            cell = sitelean.Cell(page.id, f"{page.path}:{block.line}", block.text, mode,
                                 number if mode != "hidden" else 0, attrs.get("quote", ""),
                                 suggestion=attrs.get("suggestion", ""), expect=attrs.get("expect", ""))
            page_cells.append(cell)
            cell_of[id(block)] = cell
        cells[page.id] = page_cells
    return cells, cell_of


def guide_structure(pages: dict[str, siteparse.Page]) -> tuple[list[str], dict, list[str]]:
    docs = [p for p in pages.values() if p.kind == "docs"]
    guide_order = list(docs[0].meta.get("guides", [])) if docs else []
    tutorial_order = list(docs[0].meta.get("tutorials", [])) if docs else []
    guide_order += sorted(p.id for p in pages.values() if p.kind == "guide" and p.id not in guide_order)
    tutorial_order += sorted(p.id for p in pages.values() if p.kind == "tutorial" and p.id not in tutorial_order)
    members: dict[str, list[tuple[str, list[str]]]] = {}
    for gid in guide_order:
        if gid not in pages:
            continue
        groups: list[tuple[str, list[str]]] = []
        for block in siteparse.walk(pages[gid].blocks):
            if block.kind == "directive" and block.name == "commands":
                groups.extend(sitehtml.command_groups(block))
        members[gid] = groups
    return [g for g in guide_order if g in pages], members, [t for t in tutorial_order if t in pages]


def lean_environment(repo: Path) -> tuple[str, str]:
    lean = os.environ.get("SYMLEAN_SITE_LEAN")
    lean_path = os.environ.get("SYMLEAN_SITE_LEAN_PATH")
    if not lean:
        lean = subprocess.run(["lake", "env", "which", "lean"], cwd=repo, capture_output=True,
                              text=True, check=True).stdout.strip()
    if not lean_path:
        lean_path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=repo,
                                   capture_output=True, text=True, check=True).stdout.strip()
    return lean, lean_path


# ---------------------------------------------------------------------------
# Checks over the output

_HREF_RE = re.compile(r'\s(?:href|src)="([^"]*)"')
_ID_RE = re.compile(r'\sid="([^"]+)"')


def check_output(out: Path) -> list[str]:
    problems = []
    files = sorted(p for p in out.rglob("*") if p.is_file())
    ids: dict[Path, set[str]] = {}
    for f in files:
        if f.suffix in (".js", ".mjs", ".cjs", ".ts") and f.relative_to(out).as_posix() != "static/site.js":
            problems.append(f"{f}: a script file in the output")
    htmls = [f for f in files if f.suffix == ".html"]
    for f in htmls:
        ids[f.resolve()] = set(_ID_RE.findall(f.read_text(encoding="utf-8")))
    for f in htmls:
        text = f.read_text(encoding="utf-8")
        safe = re.sub(r'<script defer src="(?:\.\./)*static/site\.js"></script>', '', text)
        if re.search(r"<script\b", safe, re.I) or re.search(r"\son[a-z]+=\"", safe):
            problems.append(f"{f}: a script in the page")
        for href in _HREF_RE.findall(text):
            href = html_unescape(href)
            parts = urlsplit(href)
            if parts.scheme in ("http", "https", "mailto"):
                continue
            if parts.scheme:
                problems.append(f"{f}: link with scheme {parts.scheme!r}: {href}")
                continue
            target = (f.parent / unquote(parts.path)).resolve() if parts.path else f.resolve()
            if not target.exists():
                problems.append(f"{f.relative_to(out)}: broken link {href}")
                continue
            if parts.fragment and target.suffix == ".html":
                if parts.fragment not in ids.get(target, set()):
                    problems.append(f"{f.relative_to(out)}: no anchor #{parts.fragment} in "
                                    f"{target.relative_to(out.resolve())}")
    return problems


def html_unescape(s: str) -> str:
    return s.replace("&amp;", "&").replace("&quot;", '"').replace("&#x27;", "'").replace("&lt;", "<").replace("&gt;", ">")


def check_prose(pages: list[siteparse.Page]) -> list[str]:
    """The house style of the page sources: no em dashes in prose."""
    problems = []
    for page in pages:
        in_fence = False
        for k, line in enumerate(page.path.read_text(encoding="utf-8").split("\n"), 1):
            if line.startswith("```"):
                in_fence = not in_fence
                continue
            if not in_fence and "—" in line:
                problems.append(f"{page.path}:{k}: an em dash in prose")
    return problems


def check_registry(registry: Path, pages: list[siteparse.Page]) -> list[str]:
    data = json.loads(registry.read_text(encoding="utf-8"))
    kinds = {f["kind"] for f in data["forms"]}
    calls = {c["decl"] for c in data["calls"]} | {c["name"] for c in data["calls"]}
    covered_forms: set[str] = set()
    covered_calls: set[str] = set()
    problems = []
    for page in pages:
        for kind in page.meta.get("forms", []):
            if kind not in kinds:
                problems.append(f"{page.path}: the registry has no form {kind!r}")
            covered_forms.add(kind)
        for call in page.meta.get("calls", []):
            if call not in calls:
                problems.append(f"{page.path}: the registry has no call {call!r}")
            covered_calls.add(call)
    for f in data["forms"]:
        if f["kind"] not in covered_forms:
            problems.append(f"no reference page documents the form {f['kind']} "
                            f"({f['module']}:{f['line']})")
    for c in data["calls"]:
        if c["decl"] not in covered_calls and c["name"] not in covered_calls:
            problems.append(f"no reference page documents the call {c['name']} ({c['decl']})")
    return problems


# ---------------------------------------------------------------------------


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out", required=True, help="output directory (its contents are replaced)")
    ap.add_argument("--pages", default=str(REPO / "Site/Pages"), help="page sources")
    ap.add_argument("--registry", help="CommandRegistry.json for the coverage check")
    ap.add_argument("--cache", default=str(REPO / "_out/site-cache"), help="message cache")
    ap.add_argument("--work", default=str(REPO / "_out/site-work"), help="generated Lean files")
    ap.add_argument("--jobs", type=int, default=int(os.environ.get("SYMLEAN_SITE_JOBS", "4")),
                    help="Lean files compiled at once (SYMLEAN_SITE_JOBS)")
    ap.add_argument("--threads", type=int, default=int(os.environ.get("SYMLEAN_SITE_LEAN_THREADS", "2")),
                    help="threads of each Lean process (SYMLEAN_SITE_LEAN_THREADS)")
    ap.add_argument("--timeout", type=int, default=int(os.environ.get("SYMLEAN_SITE_TIMEOUT", "1800")),
                    help="seconds allowed for one page (SYMLEAN_SITE_TIMEOUT)")
    ap.add_argument("--mem-gb", type=int, default=int(os.environ.get("SYMLEAN_SITE_MEM_GB", "0")),
                    help="address-space limit of each Lean process in GB, 0 for none (SYMLEAN_SITE_MEM_GB)")
    ap.add_argument("--draft", action="store_true",
                    help="report problems without failing (for a partial set of pages)")
    ap.add_argument("--no-lean", action="store_true",
                    help="check and render the pages without compiling their cells (no outputs)")
    args = ap.parse_args()

    started = time.time()

    def log(msg: str) -> None:
        print(f"[{time.time() - started:7.1f}s] {msg}", flush=True)

    out = Path(args.out).resolve()
    pages_list = siteparse.read_pages(Path(args.pages))
    pages = {p.id: p for p in pages_list}
    paths = {p.id: out_path(p) for p in pages_list}
    guide_order, members, tutorial_order = guide_structure(pages)
    cells, cell_of = collect_cells(pages_list)
    log(f"{len(pages_list)} pages, {sum(len(c) for c in cells.values())} cells")

    problems: list[str] = []
    problems += check_prose(pages_list)

    # Compile.
    jobs = {}
    for page in pages_list:
        page_cells = cells[page.id]
        for cell in page_cells:
            if cell.mode == "quote":
                problem = sitelean.read_quote(REPO, cell)
                if problem:
                    problems.append(problem)
        if any(c.mode != "quote" for c in page_cells):
            imports = list(page.meta.get("imports", []))
            jobs[page.id] = (sitelean.lean_file(imports, page_cells), imports, page_cells)
    version = None
    if not args.no_lean:
        lean, lean_path = lean_environment(REPO)
        runner = sitelean.LeanRunner(REPO, lean, lean_path, Path(args.cache), Path(args.work),
                                     jobs=args.jobs, threads=args.threads, timeout=args.timeout,
                                     mem_gb=args.mem_gb)
        try:
            results = runner.run_pages(jobs, log)
        except sitelean.CellError as err:
            print(f"error: {err}", file=sys.stderr)
            return 1
        for page_id, result in results.items():
            problems += sitelean.assign_messages(page_id, cells[page_id], result["messages"])
            sitelean.assign_hovers(cells[page_id], jobs[page_id][0], result["hovers"])
            problems += sitelean.check_cells(cells[page_id])
        version = re.search(r"version ([0-9.]+)", runner.version)

    # Render.
    footer = (f"Examples built with Lean {version.group(1) if version else ''}. "
              "Quoted examples link to their source.")
    site = sitehtml.Site(pages, paths, guide_order, members, tutorial_order, cell_of,
                         REPO / "Site/Static/figures", footer)
    if out.exists():
        shutil.rmtree(out)
    out.mkdir(parents=True)
    for page in pages_list:
        try:
            text, _ = sitehtml.render_page(site, page)
        except sitehtml.RenderError as err:
            problems.append(str(err))
            continue
        target = out / paths[page.id]
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text, encoding="utf-8")
    problems += site.problems
    static = REPO / "Site/Static"
    (out / "static").mkdir(parents=True, exist_ok=True)
    shutil.copy2(static / "site.css", out / "static/site.css")
    shutil.copy2(static / "site.js", out / "static/site.js")
    shutil.copytree(static / "fonts", out / "static/fonts")
    shutil.copytree(static / "brand", out / "static/brand")
    log(f"rendered {len(pages_list)} pages into {out}")

    # Check.
    problems += check_output(out)
    if args.registry:
        problems += check_registry(Path(args.registry), pages_list)
    for p in problems:
        print(f"problem: {p}", file=sys.stderr)
    log(f"{len(problems)} problems")
    if problems and not args.draft:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
