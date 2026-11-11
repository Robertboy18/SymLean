#!/bin/bash
# Copyright (c) 2026 SymLean Team. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Tests of the optional oracle library `CASOracle`. They call external programs, so they are
# elaborated here against the built library instead of being part of `lake build`. Run from any
# directory, with the oracles configured as in the manual (SYMLEAN_ORACLE_PYTHON or the per-oracle
# Python variables, SYMLEAN_SAGE_PATH, SYMLEAN_MAXIMA_PATH, SYMLEAN_GAPPA_PATH).
# `Oracles.lean` calls the real oracles, one positive per oracle and task; `EdgeCases.lean` the
# edge cases of the numerical searches, with SymPy and FLINT only; `Refusals.lean` runs with the
# deliberately wrong programs of `drivers/` and a missing Sage. `#guard_msgs` turns every
# mismatch into an error, so the exit status is the result.
set -u
cd "$(dirname "$0")/../.."
if ! grep -q '"name": "DSLean"' lake-manifest.json; then
  echo "lake-manifest.json has no entry for DSLean, which CASOracle needs: run" \
    "lake -R -Koracle=on update DSLean (an update without -Koracle=on drops the entry)"
  exit 1
fi
lake -R -Koracle=on build CASOracle || exit 1
status=0
run() {
  local file=$1
  shift
  if env "$@" lake -Koracle=on env lean -DwarningAsError=true "$file"; then
    echo "ok   $file"
  else
    echo "FAIL $file"
    status=1
  fi
}
run tests/oracle/Oracles.lean
run tests/oracle/EdgeCases.lean
drivers="$PWD/tests/oracle/drivers"
pidfile=$(mktemp)
run tests/oracle/Refusals.lean SYMLEAN_SYMPY_PYTHON="$drivers/python" \
  SYMLEAN_PARI_PYTHON="$drivers/python" SYMLEAN_FLINT_PYTHON="$drivers/python" \
  SYMLEAN_MAXIMA_PATH="$drivers/maxima" SYMLEAN_GAPPA_PATH="$drivers/gappa" \
  SYMLEAN_SAGE_PATH=/nonexistent/sage SYMLEAN_TEST_PIDFILE="$pidfile"
rm -f "$pidfile"
python_bin=${SYMLEAN_ORACLE_PYTHON:-${SYMLEAN_SYMPY_PYTHON:-python3}}
# With pytest-xdist installed, the pytest-rerunfailures plugin opens a localhost socket;
# -p no:rerunfailures keeps the run from listening.
if "$python_bin" -m pytest -q -p no:rerunfailures -p no:cacheprovider oracle; then
  echo "ok   oracle (pytest)"
else
  echo "FAIL oracle (pytest)"
  status=1
fi
exit $status
