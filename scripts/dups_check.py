"""Compare the duplicate gate's output with its baseline.

Usage: python3 -I dups_check.py OUT BASELINE [--update]

Both files hold the five count lines (`DUPDEF n`, `DUPTHM n`, `RESTATE n`, `UNUSED n`, `EQUIV n`)
and one `TAG: item` line per listed item. The check fails when a count exceeds the baseline's and
prints the items that the baseline does not list. `--update` copies OUT to BASELINE.
"""
import shutil, sys

TAGS = ("DUPDEF", "DUPTHM", "RESTATE", "UNUSED", "EQUIV")


def read(path):
    counts, items = {}, set()
    for line in open(path, encoding="utf-8"):
        line = line.rstrip("\n")
        head = line.split(" ", 1)
        if len(head) == 2 and head[0] in TAGS and head[1].isdigit():
            counts[head[0]] = int(head[1])
        elif line.split(":", 1)[0] in TAGS:
            items.add(line)
    return counts, items


out, base = sys.argv[1], sys.argv[2]
counts, items = read(out)
if set(counts) != set(TAGS):
    sys.exit(f"dups: {out} lacks some counts (the Lean run failed?)")
if "--update" in sys.argv:
    shutil.copy(out, base)
    print("dups: baseline updated: " + ", ".join(f"{t} {counts[t]}" for t in TAGS))
    sys.exit(0)
bcounts, bitems = read(base)
status = 0
for tag in TAGS:
    mark = "ok  " if counts[tag] <= bcounts.get(tag, 0) else "FAIL"
    if mark == "FAIL":
        status = 1
    print(f"{mark} {tag} {counts[tag]} (baseline {bcounts.get(tag, 0)})")
for line in sorted(items - bitems):
    print(f"new  {line}")
sys.exit(status)
