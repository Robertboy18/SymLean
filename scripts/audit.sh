#!/bin/bash
# Lists every constant of SymLean's library (the modules under CAS/) that uses an axiom beyond
# propext, Classical.choice and Quot.sound, or that is extern, implemented_by, csimp or unsafe,
# and counts the opaque and partial constants. Run it from the repository root after `lake build`.
set -euo pipefail
cd "$(dirname "$0")/.."
(find CAS -name '*.lean' | sed 's|/|.|g; s|\.lean$||; s|^|import |'; cat <<'EOF'
open Lean Compiler in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut found := #[]
  let mut opaques := 0
  let mut partials := 0
  for (n, c) in env.constants.map₁.toList do
    unless (env.getModuleIdxFor? n).any (env.header.moduleNames[·.toNat]!.getRoot == `CAS) do
      continue
    let extra := (← collectAxioms n).filter
      fun a => !#[``propext, ``Classical.choice, ``Quot.sound].contains a
    let tags := extra.toList.map (s!"uses {·}")
      ++ (if isExtern env n then ["extern"] else [])
      ++ (getImplementedBy? env n).toList.map (s!"implemented_by {privateToUserName ·}")
      ++ (if hasCSimpAttribute env n then ["csimp"] else [])
      ++ (if c.isUnsafe then ["unsafe"] else [])
    unless tags.isEmpty do found := found.push s!"{privateToUserName n}: {tags}"
    if c matches .opaqueInfo _ then opaques := opaques + 1
    if c.isPartial then partials := partials + 1
  for line in found.qsort (· < ·) do IO.println line
  IO.println s!"{opaques} opaque constants, {partials} partial ones"
EOF
) | lake env lean --stdin
