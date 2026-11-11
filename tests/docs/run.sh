#!/bin/bash
# Copyright (c) 2026 SymLean Team. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Documentation and route tests. A module elaborated by `lean` does not load the docstrings of its
# imports, and the routes that a test registers with `@[cas_route]` must stay out of the library,
# so these files are not modules, and they are elaborated here against the built library instead
# of being part of `lake build`. Run from the repository root after `lake build`; `#guard_msgs`
# turns every mismatch into an error, so the exit status is the result.
set -u
cd "$(dirname "$0")/../.."
status=0
for file in tests/docs/*.lean; do
  if lake env lean -DwarningAsError=true "$file"; then
    echo "ok   $file"
  else
    echo "FAIL $file"
    status=1
  fi
done
exit $status
