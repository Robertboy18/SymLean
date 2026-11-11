#!/usr/bin/env bash
# Copyright (c) 2026 SymLean Team. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Build the SymLean website: the library, the command registry, then the pages
# of `Site/Pages`, whose Lean cells are compiled against the library, rendered
# to static HTML with MathML and checked. Everything runs offline, with Lean
# and Python; the output opens from disk, including the compiled Lean hovers.
#
#   bash Site/Tools/build.sh                writes _out/site
#   bash Site/Tools/build.sh _out/other     writes _out/other (inside _out/)
#
# It needs Python 3.11 or later with latex2mathml; SYMLEAN_SITE_PYTHON names
# the interpreter (python3 by default). SYMLEAN_SITE_JOBS,
# SYMLEAN_SITE_LEAN_THREADS, SYMLEAN_SITE_TIMEOUT and SYMLEAN_SITE_MEM_GB set
# the Lean processes of the pages, as `Site/Tools/sitegen.py --help` explains.

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
tools_root="$repo_root/Site/Tools"
output_root="$repo_root/_out"
requested_output="${1:-$output_root/site}"
python="${SYMLEAN_SITE_PYTHON:-python3}"

for command in realpath lake "$python"; do
  if ! command -v "$command" >/dev/null 2>&1; then
    printf 'The site build requires %s.\n' "$command" >&2
    exit 127
  fi
done
if ! "$python" -c 'import sys, latex2mathml; sys.exit(sys.version_info < (3, 11))' 2>/dev/null; then
  printf 'The site build requires Python 3.11 or later with latex2mathml; %s is not.\n' "$python" >&2
  exit 127
fi

if [[ -L "$output_root" ]]; then
  printf 'Site output root must not be a symbolic link: %s\n' "$output_root" >&2
  exit 1
fi
mkdir -p "$output_root"
output_root="$(realpath -e -- "$output_root")"
if [[ "$requested_output" != /* ]]; then
  requested_output="$repo_root/$requested_output"
fi
output_dir="$(realpath -m -- "$requested_output")"
case "$output_dir" in
  "$output_root"/*) ;;
  *)
    printf 'Site output must be a strict subdirectory of %s.\n' "$output_root" >&2
    exit 1
    ;;
esac

cd "$repo_root"

# The library, with every proof checked by the kernel. Lake caches the
# certificate profile, so the pages below compile against this build.
lake -R -Kcertificates=kernel build CAS

# The command registry: every form of `#cas`, `cas`, `cas?`, `cas_nf`, `cega`
# and `cega?` and every call of `#cas e`, read from Lean's parser tables.
registry="$output_root/CommandRegistry.json"
lake env lean --run Site/Tools/CommandRegistry.lean > "$registry.tmp"
mv "$registry.tmp" "$registry"

# The pages: compile every cell, render, and check the links, the anchors and
# the registry.
"$python" "$tools_root/sitegen.py" --out "$output_dir" --registry "$registry"

printf 'Site generated at %s\n' "$output_dir"
