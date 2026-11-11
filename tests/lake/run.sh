#!/bin/bash
# Copyright (c) 2026 SymLean Team. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Tests of SymLean's Lake configuration: the certificate profiles, the tracking of the files that
# modules embed with `include_str`, in modules that no glob lists as well, the uses of
# `include_str` that the check of `CAS/IncludeStr.lean` or the facet refuses, in a module or
# through the macros and elaborators of another, the time that the search takes, and a consumer's
# own module setup facet and library facet. Each run copies the configuration (`lakefile.lean`,
# `lake-manifest.json`, `lean-toolchain`) and `CAS/IncludeStr.lean` next to the stand-in library
# of `symlean/`, the consumer package of `consumer/` and the package `top/` that requires the
# consumer, in a scratch directory under `TMPDIR`, so that it neither rebuilds the library nor
# changes the options, such as the certificate profile, that Lake caches with the repository's
# configuration. The dependencies come from the repository's `.lake/packages`, so run it after
# `lake build`; it needs no network. The exit status is the result.
set -u
repo="$(cd "$(dirname "$0")/../.." && pwd)"
if [[ ! -d "$repo/.lake/packages/mathlib" ]]; then
  echo "$repo/.lake/packages has no dependencies: run lake build first"
  exit 1
fi
scratch="$(mktemp -d "${TMPDIR:-/tmp}/symlean-lake.XXXXXX")"
trap 'rm -rf "$scratch"' EXIT
status=0
ok() { echo "ok   $1"; }
fail() { echo "FAIL $1"; grep -v '^trace:' "$log" | tail -n 12 | sed 's/^/     /'; status=1; }

cp -R "$repo/tests/lake/symlean" "$repo/tests/lake/consumer" "$repo/tests/lake/top" "$scratch/"
cp "$repo/lakefile.lean" "$repo/lake-manifest.json" "$repo/lean-toolchain" "$scratch/symlean/"
cp "$repo/CAS/IncludeStr.lean" "$scratch/symlean/CAS/"
for package in symlean consumer top; do
  cp "$repo/lean-toolchain" "$scratch/$package/"
  mkdir -p "$scratch/$package/.lake"
  ln -s "$repo/.lake/packages" "$scratch/$package/.lake/packages"
done
# The manifests of the consumer and of `top` pin SymLean's dependencies, so that Lake resolves
# them offline.
python3 - "$repo/lake-manifest.json" "$scratch" <<'EOF'
import json, sys
manifest = json.load(open(sys.argv[1]))
inherited = [dict(entry, inherited=True) for entry in manifest["packages"]
             if entry["name"] != "DSLean"]
def path(name, directory, inherited):
    return {"type": "path", "scope": "", "name": name, "manifestFile": "lake-manifest.json",
            "inherited": inherited, "dir": directory, "configFile": "lakefile.lean"}
for name, packages in [("consumer", [path("SymLean", "../symlean", False)]),
                       ("top", [path("consumer", "../consumer", False),
                                path("SymLean", "../symlean", True)])]:
    json.dump({"version": manifest["version"], "packagesDir": ".lake/packages",
               "packages": packages + inherited, "name": name, "lakeDir": ".lake"},
              open(f"{sys.argv[2]}/{name}/lake-manifest.json", "w"), indent=1)
EOF
symlean="$scratch/symlean"
consumer="$scratch/consumer"
top="$scratch/top"
log="$scratch/lake.log"
: > "$log"
# `lake_in dir args` runs `lake args` in `dir`; `shows_file dir file line` checks that `file` of
# `dir`, elaborated against the build, prints `line`, and `shows dir line` does so for `Show.lean`.
lake_in() { (cd "$1" && shift && lake "$@") > "$log" 2>&1; }
shows() { shows_file "$1" Show.lean "$2"; }
shows_file() { (cd "$1" && lake env lean "$2") > "$log" 2>&1 && grep -qx "$3" "$log"; }
# `embed value` writes `value` to each embedded file of the runs below.
embed() {
  for file in "$symlean/CAS/data.txt" "$consumer/Probe/single.txt" "$consumer/Probe/multi.txt" \
      "$consumer/Probe/plusminus.txt" "$consumer/Probe/coerced" "$consumer/Sparse/hidden.txt" \
      "$top/Top/top.txt"; do
    printf '%s' "$1" > "$file"
  done
}
embed before
printf decoy > "$consumer/Probe/decoy.txt"

# An unknown profile stops Lake before it builds anything, as the root and as a dependency.
for value in not-a-profile Kernel ""; do
  if ! lake_in "$symlean" -R "-Kcertificates=$value" build CAS &&
      grep -q "unknown certificates profile '$value'" "$log" &&
      [[ ! -d "$symlean/.lake/build" ]]; then
    ok "root profile '$value' is refused"
  else
    fail "root profile '$value' is refused"
  fi
  if ! lake_in "$consumer" -R "-Kcertificates=$value" build Plain &&
      grep -q "unknown certificates profile '$value'" "$log"; then
    ok "forwarded profile '$value' is refused"
  else
    fail "forwarded profile '$value' is refused"
  fi
done
for value in kernel fast native; do
  directory=$([[ $value == kernel ]] && echo build || echo build-fast)
  if lake_in "$symlean" -R "-Kcertificates=$value" build CAS &&
      [[ -f "$symlean/.lake/$directory/lib/lean/CAS/Embedded.olean" ]]; then
    ok "root profile '$value' builds into .lake/$directory"
  else
    fail "root profile '$value' builds into .lake/$directory"
  fi
  if lake_in "$consumer" -R "-Kcertificates=$value" build Plain; then
    ok "forwarded profile '$value' builds"
  else
    fail "forwarded profile '$value' builds"
  fi
done

# The consumer's own module setup facet, and its own library facet named like the last part of
# SymLean's, run with SymLean as a dependency.
rm -f "$consumer/presetup-ran.txt" "$consumer/consumer-facet-ran.txt"
if lake_in "$consumer" -R build Plain && [[ -f "$consumer/presetup-ran.txt" ]]; then
  ok "the consumer's module setup facet runs"
else
  fail "the consumer's module setup facet runs"
fi
if [[ -f "$consumer/consumer-facet-ran.txt" ]]; then
  ok "the consumer's library facet embeddedInputs runs"
else
  fail "the consumer's library facet embeddedInputs runs"
fi

# Editing an embedded file rebuilds the module that reads it: in the library as the root package,
# in the library and the consumer when SymLean is a dependency, and in all three packages two
# levels above SymLean. The consumer's modules include a user token `+/-` before the path and a
# coercion that would turn the path into `decoy.txt`.
if lake_in "$symlean" -R build CAS && shows "$symlean" "cas=before"; then
  embed after
  if lake_in "$symlean" build CAS && shows "$symlean" "cas=after"; then
    ok "the library tracks its embedded file"
  else
    fail "the library tracks its embedded file"
  fi
else
  fail "the library builds with its embedded file"
fi
embed before
probe="single=VALUE multi=VALUE plusminus=VALUE coerced=VALUE cas=VALUE"
if lake_in "$consumer" build Probe @SymLean/CAS && shows "$consumer" "${probe//VALUE/before}"
then
  embed after
  if lake_in "$consumer" build Probe @SymLean/CAS && shows "$consumer" "${probe//VALUE/after}"
  then
    ok "the consumer and its dependency track their embedded files"
  else
    fail "the consumer and its dependency track their embedded files"
  fi
else
  fail "the consumer builds with its embedded files"
fi
embed before
if lake_in "$top" build Top @consumer/Probe @SymLean/CAS &&
    shows "$top" "top=before single=before cas=before"; then
  embed after
  if lake_in "$top" build Top @consumer/Probe @SymLean/CAS &&
      shows "$top" "top=after single=after cas=after"; then
    ok "two levels above SymLean, each package tracks its embedded files"
  else
    fail "two levels above SymLean, each package tracks its embedded files"
  fi
else
  fail "two levels above SymLean, the packages build with their embedded files"
fi

# A module under the root of a library that no glob lists, and that the library's root does not
# import, is tracked too: Lake builds `Sparse.Hidden` as part of `Sparse` when `SparseUser` imports
# it.
embed before
if lake_in "$consumer" build SparseUser && shows_file "$consumer" ShowSparse.lean "hidden=before"
then
  embed after
  if lake_in "$consumer" build SparseUser && shows_file "$consumer" ShowSparse.lean "hidden=after"
  then
    ok "a module under the root of a library that no glob lists is tracked"
  else
    fail "a module under the root of a library that no glob lists is tracked"
  fi
else
  fail "a module under the root of a library that no glob lists builds"
fi

# The search finds each path that Lean reads, and one more for each mention outside code, here
# `comment.txt` and `line-comment.txt`. Only the paths that `lake query` prints count, not what
# Lake reports on the way.
spellings="after-desync.txt after-infix.txt after-macro.txt after-notation.txt alias.txt \
between.txt chars.txt comment.txt commented.txt custom-command.txt deep.txt do-block.txt \
do-next.txt docslash.txt elab.txt escaped-quote.txt escaped.txt fields.txt gap.txt \
line-comment.txt nested.txt next-line.txt parenthesized.txt payload.txt quote.txt raw-plain.txt \
raw.txt slashdash.txt struct-x.txt struct-y.txt via-public.txt where-a.txt where-b.txt "
query="$scratch/query.txt"
if lake_in "$consumer" build Spellings &&
    (cd "$consumer" && lake query Spellings:SymLean.embeddedInputs) > "$query" 2> "$log" &&
    [[ "$(grep '\.txt$' "$query" | sed 's|.*/||' | LC_ALL=C sort | tr '\n' ' ')" == "$spellings" ]]
then
  ok "each spelling of a path is tracked"
else
  cat "$query" >> "$log"
  fail "each spelling of a path is tracked"
fi

# Every other use of `include_str` stops the build: the check refuses it at the use, with a message
# that says what to write, and the facet refuses a module that breaks one of its rules. The
# modules of `Refused/` and `Foreign/` go into their library one at a time, each with the modules
# that it imports, since the build stops at the first refusal; `Refused/Private.lean`, which embeds
# nothing, stays. `Foreign/` loads the modules of `Macros/`, a library without the facet, among them
# commands whose expansion is a declaration that uses `include_str`, by a macro, by `macro_rules`
# and by a command elaborator.
macro="this include_str comes from a macro or notation, so the build cannot track its file"
literal="the path of include_str must be a plain string literal right after the keyword"
runtime="this include_str is elaborated against a text other than the file"
unchecked="this module contains include_str but does not load CAS.IncludeStr through its public \
imports"
producer="whose text has include_str in a string, a syntax quotation or a command other than a \
declaration"
# `refusals lib`: for each input line `module others…|expected`, builds `lib` with `module` and the
# others, and checks that the build fails with a message `lib/module` followed by `expected`, or,
# for an empty `expected`, that it succeeds.
refusals() {
  local lib=$1 modules expected module m
  mv "$consumer/$lib" "$scratch/$lib"
  mkdir "$consumer/$lib"
  cp "$scratch/$lib/"*.txt "$consumer/$lib/"
  if [[ $lib == Refused ]]; then cp "$scratch/$lib/Private.lean" "$consumer/$lib/"; fi
  while IFS='|' read -r modules expected; do
    module=${modules%% *}
    for m in $modules; do cp "$scratch/$lib/$m" "$consumer/$lib/"; done
    expected="${expected//MACRO/$macro}"
    expected="${expected//LITERAL/$literal}"
    expected="${expected//RUNTIME/$runtime}"
    expected="${expected//UNCHECKED/$unchecked}"
    expected="${expected//PRODUCER/$producer}"
    if [[ -z $expected ]]; then
      if lake_in "$consumer" build "$lib"; then
        ok "$lib/$module builds"
      else
        fail "$lib/$module builds"
      fi
    elif ! lake_in "$consumer" build "$lib" && grep -qF "$lib/$module$expected" "$log"; then
      ok "$lib/$module is refused"
    else
      fail "$lib/$module is refused"
    fi
    for m in $modules; do rm "$consumer/$lib/$m"; done
  done
}
refusals Refused <<'EOF'
Macro.lean|:8:32: MACRO
Notation.lean|:8:35: MACRO
CoeFun.lean|:10:31: LITERAL
Then.lean|:11:36: LITERAL
NextLine.lean|:13:2: LITERAL
Operator.lean|:11:32: LITERAL
Parenthesized.lean|:6:37: LITERAL
Joined.lean|:6:30: LITERAL
Interpolated.lean|:6:36: LITERAL
MacroUse.lean MacroDef.lean|:6:32: MACRO
NotationUse.lean NotationDef.lean|:6:35: MACRO
ElabUse.lean ElabDef.lean|:6:31: MACRO
Runtime.lean|:1:31: RUNTIME
Gap.lean|:11:4: LITERAL
NoCheck.lean|: UNCHECKED
PrivateChain.lean|: UNCHECKED
PrivateDef.lean|: UNCHECKED
Elaborated.lean|: this module names includeStr, the syntax kind or an elaborator of include_str
Override.lean|: this module names includeStr, the syntax kind or an elaborator of include_str
Erase.lean|: this module names checkIncludeStr, the syntax kind or an elaborator of include_str
EOF
refusals Foreign <<'EOF'
Plain.lean|
Use.lean|: this module loads Macros.Embed, PRODUCER
UseDef.lean|: this module loads Macros.EmbedDef, PRODUCER
UseDefRules.lean|: this module loads Macros.EmbedDefRules, PRODUCER
UseDefElab.lean|: this module loads Macros.EmbedDefElab, PRODUCER
Checked.lean|:7:38: MACRO
Restored.lean|: this module loads Macros.Restore, which names includeStr
EOF

# The search takes time linear in the module: 3,000 strings that each hold a brace take well
# under 20 seconds of CPU time.
mkdir -p "$consumer/Big"
printf big > "$consumer/Big/data.txt"
python3 - "$consumer/Big/Strings.lean" <<'EOF'
import sys
lines = ["module", "", "public import CAS.IncludeStr", ""]
lines += [f'def s{n} : String := "{{"' for n in range(3000)]
lines.append('def big : String := include_str "data.txt"')
open(sys.argv[1], "w").write("\n".join(lines) + "\n")
EOF
seconds=$(cd "$consumer" && python3 - 2> "$log" <<'EOF'
import resource, subprocess
query = subprocess.run(["lake", "query", "Big:SymLean.embeddedInputs"], capture_output=True,
                       text=True)
usage = resource.getrusage(resource.RUSAGE_CHILDREN)
if query.returncode == 0 and query.stdout.strip().endswith("/Big/data.txt"):
    print(f"{usage.ru_utime + usage.ru_stime:.1f}")
EOF
)
if [[ -n "$seconds" ]] && python3 -c "import sys; sys.exit(float(sys.argv[1]) >= 20)" "$seconds"
then
  ok "the search of 3,000 strings takes $seconds s of CPU time"
else
  fail "the search of 3,000 strings takes under 20 s of CPU time (${seconds:-no result})"
fi
exit $status
