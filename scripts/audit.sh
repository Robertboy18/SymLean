#!/bin/bash
# Check the axioms of CAS after `lake build`. Pass CASOracle or CASHex to include a separately
# built optional library. The report lists compiler hooks and unsafe definitions as well.
# Use --inventory to print the same report without enforcing the axiom check.
#
# Lean itself replaces the constructor index `T.ctorIdx` of every inductive type `T` with several
# constructors by a generated unsafe definition `T.ctorIdx._impl` that reads the constructor tag
# of its argument. Such a pair is counted, not listed, after a check of its name, its type and its
# body; a replacement of a constructor index that fails the check is listed like any other.
set -euo pipefail
cd "$(dirname "$0")/.."
libraries=()
check=true
for arg in "$@"; do
  case "$arg" in
    --inventory) check=false ;;
    CAS|CASOracle|CASHex) libraries+=("$arg") ;;
    *) printf 'Usage: %s [--inventory] [CAS|CASOracle|CASHex ...]\n' "$0" >&2; exit 2 ;;
  esac
done
if (( ${#libraries[@]} == 0 )); then libraries=(CAS); fi

roots=()
for library in "${libraries[@]}"; do roots+=("\`$library"); done
(
  printf 'import Lean.Meta.Constructions.CtorIdx\n'
  for library in "${libraries[@]}"; do
    if [[ -f "$library.lean" ]]; then printf 'import %s\n' "$library"; fi
    find "$library" -name '*.lean' | LC_ALL=C sort | sed 's|/|.|g; s|\.lean$||; s|^|import |'
  done
  printf 'def auditRoots : List Lean.Name := [%s]\n' "$(IFS=,; printf '%s' "${roots[*]}")"
  printf 'def checkAudit : Bool := %s\n' "$check"
  cat <<'EOF'
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
  let mut unexpected : Array String := #[]
  let mut indices := 0
  let mut opaques := 0
  let mut partials := 0
  for (n, c) in env.constants.map₁.toList do
    unless (env.getModuleIdxFor? n).any (auditRoots.contains env.header.moduleNames[·.toNat]!.getRoot) do
      continue
    if c matches .opaqueInfo _ then opaques := opaques + 1
    if c.isPartial then partials := partials + 1
    if (getImplementedBy? env n).any (isGeneratedCtorIdx env n) then
      indices := indices + 1
      continue
    if isGeneratedCtorIdx env n.getPrefix n then continue
    let extra := (← collectAxioms n).filter
      fun a => !#[``propext, ``Classical.choice, ``Quot.sound].contains a
    for ax in extra do
      -- The compact-literal elaborator calls unsafeBaseIO. Its own implementation may use
      -- lcProof, but a proof or another declaration that reaches it still fails this check.
      unless n == `CAS.Numerics.natCompactImpl && c.isUnsafe && ax == ``lcProof do
        unexpected := unexpected.push s!"{privateToUserName n} uses {ax}"
    let tags := extra.toList.map (s!"uses {·}")
      ++ (if isExtern env n then ["extern"] else [])
      ++ (getImplementedBy? env n).toList.map (s!"implemented_by {privateToUserName ·}")
      ++ (if hasCSimpAttribute env n then ["csimp"] else [])
      ++ (if c.isUnsafe then ["unsafe"] else [])
    unless tags.isEmpty do found := found.push s!"{privateToUserName n}: {tags}"
  for line in found.qsort (· < ·) do IO.println line
  IO.println s!"{indices} constructor indices implemented by the tag read that Lean generates"
  IO.println s!"{opaques} opaque constants, {partials} partial ones"
  if checkAudit && !unexpected.isEmpty then
    throwError "unexpected axiom dependencies:\n{String.intercalate "\n" (unexpected.qsort (· < ·)).toList}"
EOF
) | lake env lean --stdin
