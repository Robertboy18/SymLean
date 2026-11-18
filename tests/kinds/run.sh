#!/bin/bash
# Copyright (c) 2026 SymLean Team. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Tests that must give the same result in a file outside the module system and in a `module`.
# Each `tests/kinds/*.lean` is elaborated against the built library as it is written, an ordinary
# file, and once more as a module: `module` goes in front, `import CAS` becomes
# `public import CAS` and every other `import CAS.…` becomes `meta import CAS.…`. A file outside
# the module system loads the bodies that a module cannot see, so the frontends are checked in
# both. Run from the repository root after `lake build`; `#guard_msgs` turns every mismatch into
# an error, so the exit status is the result.
set -u
cd "$(dirname "$0")/../.."
status=0
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
for file in tests/kinds/*.lean; do
  if lake env lean -DwarningAsError=true "$file"; then
    echo "ok   $file (ordinary file)"
  else
    echo "FAIL $file (ordinary file)"
    status=1
  fi
  module="$work/$(basename "$file")"
  sed -e '0,/^import CAS$/s//module\n\npublic import CAS/' \
    -e 's/^import \(CAS\.[A-Za-z.]*\)$/meta import \1/' "$file" > "$module"
  if ! grep -q '^module$' "$module"; then
    echo "FAIL $file (module): no line \`import CAS\` to turn into a module header"
    status=1
  elif lake env lean -DwarningAsError=true "$module"; then
    echo "ok   $file (module)"
  else
    echo "FAIL $file (module)"
    status=1
  fi
done
exit $status
