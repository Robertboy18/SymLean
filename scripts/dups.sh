#!/bin/bash
# Copyright (c) 2026 SymLean Team. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# The duplicate gate. Counts the duplicate definitions and theorems, the restatements of theorems
# outside SymLean, the unused declarations and the equivalence pairs of the library (the modules
# under CAS/ except CAS/Examples, see scripts/Dups.lean), writes the lists to .lake/dups.out, and
# fails when a count exceeds its value in scripts/dups.baseline. Run it from the repository root
# after `lake build`. `--update` writes the current lists to the baseline instead.
set -euo pipefail
cd "$(dirname "$0")/.."
(git ls-files 'CAS/*.lean' | sed 's|/|.|g; s|\.lean$||; s|^|import |'; cat scripts/Dups.lean) |
  lake env lean --stdin > .lake/dups.out
python3 -I scripts/dups_check.py .lake/dups.out scripts/dups.baseline "$@"
