#!/bin/bash
# Copyright (c) 2026 SymLean Team. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Native-certificate regression tests for `cega`. They need `cega.nativeCertificates`, which would
# put native axioms into the library, so they are elaborated here against the built library
# instead of being part of `lake build`. Run from the repository root after `lake build`.
# Each file is elaborated with `Elab.async` false and with the default; `#guard_msgs` turns every
# mismatch into an error, so the exit status is the result.
set -u
cd "$(dirname "$0")/../.."
status=0
for file in tests/cega/*.lean; do
  for async in false true; do
    if lake env lean -DElab.async=$async -DwarningAsError=true "$file"; then
      echo "ok   $file (Elab.async=$async)"
    else
      echo "FAIL $file (Elab.async=$async)"
      status=1
    fi
  done
done
exit $status
