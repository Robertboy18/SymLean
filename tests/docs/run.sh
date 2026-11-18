#!/bin/bash
# Copyright (c) 2026 SymLean Team. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Documentation and route tests, the test of the compatibility import `CAS.Irreducible`, a
# registered derivative backend, a grid table read from a file, and the compiled reading of a
# large literal. A module elaborated by `lean` does not load the docstrings of its imports, the
# routes and the backend that a test registers with `@[cas_route]` and
# `@[cas_derivative_backend]` must stay out of the library, as must a data file, which every
# module of the library would be rebuilt for, and a literal with a compiled implementation,
# which `scripts/audit.sh` lists; only a file outside the module system loads the bodies that
# `CAS.Irreducible` is about, and the library has no `#eval`. So these files are not modules, and
# they are elaborated here against the built library instead of being part of `lake build`. Run
# from the repository root after `lake build`; `#guard_msgs` turns every mismatch into an error,
# so the exit status is the result.
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
