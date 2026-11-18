#!/bin/bash
# Lists every constant of SymLean's library (the modules under CAS/) that uses an axiom beyond
# propext, Classical.choice and Quot.sound, or that is extern, implemented_by, csimp or unsafe,
# and counts the opaque and partial constants. Run it from the repository root after `lake build`.
#
# Lean itself replaces the constructor index `T.ctorIdx` of every inductive type `T` with several
# constructors by a generated unsafe definition `T.ctorIdx._impl` that reads the constructor tag
# of its argument. Such a pair is counted, not listed, after a check of its name, its type and its
# body; a replacement of a constructor index that fails the check is listed like any other.
set -euo pipefail
cd "$(dirname "$0")/.."
(echo 'import Lean.Meta.Constructions.CtorIdx'
find CAS -name '*.lean' | sed 's|/|.|g; s|\.lean$||; s|^|import |'; cat <<'EOF'
open Lean Compiler

/-- Whether `value` is `fun x₁ … xₙ ↦ getObjTagNat _ xₙ`, the tag read of its last argument. -/
def isTagRead : Expr → Bool
  | .lam _ _ body@(.lam ..) _ => isTagRead body
  | .lam _ _ body _ => body.isAppOfArity ``getObjTagNat 2 && body.appArg! == .bvar 0
  | _ => false

/-- Whether `index` is the constructor index `T.ctorIdx` of an inductive type and `impl` the
implementation `T.ctorIdx._impl` that Lean generates for it: `impl` implements `index`, has its
type, and its body is the tag read of its last argument. -/
def isGeneratedCtorIdx (env : Environment) (index impl : Name) : Bool :=
  (isCtorIdxCore? env index).isSome && impl == index ++ `_impl &&
    getImplementedBy? env index == some impl &&
    match env.find? index, env.find? impl with
    | some logical, some (.defnInfo generated) =>
        generated.type == logical.type && isTagRead generated.value
    | _, _ => false

#eval show CoreM Unit from do
  let env ← getEnv
  let mut found := #[]
  let mut indices := 0
  let mut opaques := 0
  let mut partials := 0
  for (n, c) in env.constants.map₁.toList do
    unless (env.getModuleIdxFor? n).any (env.header.moduleNames[·.toNat]!.getRoot == `CAS) do
      continue
    if c matches .opaqueInfo _ then opaques := opaques + 1
    if c.isPartial then partials := partials + 1
    if (getImplementedBy? env n).any (isGeneratedCtorIdx env n) then
      indices := indices + 1
      continue
    if isGeneratedCtorIdx env n.getPrefix n then continue
    let extra := (← collectAxioms n).filter
      fun a => !#[``propext, ``Classical.choice, ``Quot.sound].contains a
    let tags := extra.toList.map (s!"uses {·}")
      ++ (if isExtern env n then ["extern"] else [])
      ++ (getImplementedBy? env n).toList.map (s!"implemented_by {privateToUserName ·}")
      ++ (if hasCSimpAttribute env n then ["csimp"] else [])
      ++ (if c.isUnsafe then ["unsafe"] else [])
    unless tags.isEmpty do found := found.push s!"{privateToUserName n}: {tags}"
  for line in found.qsort (· < ·) do IO.println line
  IO.println s!"{indices} constructor indices implemented by the tag read that Lean generates"
  IO.println s!"{opaques} opaque constants, {partials} partial ones"
EOF
) | lake env lean --stdin
