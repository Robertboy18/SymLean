/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Algebra.Basic
public import CAS.Command.Arguments
public import CAS.NumberTheory.ModularPower
public meta import Mathlib.Tactic.NormNum.PowMod

/-!
# Shared helpers of the number theory commands

The number theory modes and the Hex backends read their natural arguments with `parseNat`,
which evaluates closed integer expressions such as `2 ^ 64 + 1` by
`CAS.Command.Arguments.evalInteger`, as the calls do. Raw literals and the proofs of modular
powers by `Mathlib.Meta.NormNum.evalNatPowMod` (repeated squaring) are shared here too.

## Implementation notes

Primality and integer factorization are Hex's: `primeQ`, `moebiusMu` and `factorInteger` take
Hex's primality and factorization certificates when `CASHex.NumberTheory` is imported, and
refuse without it. With that import `eulerPhi` takes Hex's factorization for every `n ≥ 2`;
without it the kernel counts the residues coprime to `n` for `n ≤ totientCountBound`
(`logTotient`).
-/

public meta section

namespace CAS.Command.NumberTheory

open Lean Elab Command Meta Term

/-- `n` as a raw natural literal expression. -/
def raw (n : Nat) : Lean.Expr := mkRawNatLit n

/-- The proof `Nat.mod (Nat.pow a b) m = c` of `evalNatPowMod`, with `c`. -/
def powModProof (a b m : Nat) : Nat × Lean.Expr :=
  let ⟨c, proof⟩ := Mathlib.Meta.NormNum.evalNatPowMod (raw a) (raw b) (raw m)
  (c.rawNatLit?.getD 0, proof)

/-- Read a natural number argument of `operation` by `Arguments.evalInteger`, as `10`,
`2 ^ 5 * 3` or `20 / 4`. A negative value is refused with `{operation}: expected a natural
number`. -/
def parseNat (operation : String) (stx : Syntax) : CommandElabM Nat := do
  let v ← Arguments.evalInteger operation ⟨stx⟩
  unless 0 ≤ v do throwErrorAt stx "{operation}: expected a natural number"
  return v.toNat

/-- Read a tuple `(a, b, …)` of natural numbers. -/
def parseNatTuple (operation : String) (stx : Syntax) : CommandElabM (Array Nat) := do
  match stx with
  | `(($a, $rest,*)) => (#[a] ++ rest.getElems).mapM (parseNat operation ·)
  | _ => return #[← parseNat operation stx]

end CAS.Command.NumberTheory
