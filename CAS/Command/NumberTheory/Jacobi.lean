/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.NumberTheory.Modular
public import CAS.NumberTheory.Jacobi
public meta import CAS.NumberTheory.Jacobi

/-!
# The Jacobi symbol: `#cas (jacobiSymbol a n)`

The call `jacobiSymbol a n` proves `jacobiSym a n = j`, as Mathematica's `JacobiSymbol`, for an
integer `a` and an odd natural number `n`. The kernel checks the value by running the
reciprocity loop `CAS.NumberTheory.Jacobi.loop` once.

## Main definitions

* `CAS.Command.NumberTheory.logJacobi`: the report of the call, which `CAS.Command.Calls` runs on
  evaluated arguments.

## Implementation notes

The proof does not use Mathlib's `norm_num` extension for Jacobi symbols: its module declares a
root namespace `Tactic`, which makes `open … Tactic` ambiguous wherever it is imported, so
`import CAS` cannot include it. The loop of `CAS/NumberTheory/Jacobi.lean` needs only Mathlib's
`jacobiSym` and its reciprocity lemmas. The proof is
`CAS.NumberTheory.Jacobi.jacobiSym_eq_of_loop`, whose two hypotheses, `n % 2 = 1` and that the
loop on `a % n` and `n` returns `j`, the kernel decides by `decide +kernel`.
-/

public meta section

namespace CAS.Command.NumberTheory

open Lean Elab Command Meta Term
open CAS.Command.Algebra (natTerm proveStatement)

/-- Run the call `jacobiSymbol a n` on its evaluated arguments; `input` is the call. The fuel
`2 (log₂ (a % n) + log₂ n) + 4` is more than the loop uses. -/
def logJacobi (ref : Syntax) (a : Int) (n : Nat) (input : Syntax) : CommandElabM Unit := do
  unless n % 2 = 1 do throwErrorAt input "jacobiSymbol: expected an odd natural number"
  let residue := (a % n).toNat
  let fuel := 2 * (Nat.log2 residue + Nat.log2 n) + 4
  let some j := CAS.NumberTheory.Jacobi.loop fuel residue n
    | throwErrorAt input "jacobiSymbol: internal error"
  let (proposition, proof) ← liftTermElabM <| proveStatement "jacobiSymbol"
    (← `(jacobiSym $(← intTerm a) $(natTerm n) = $(← intTerm j)))
    (← `(tactic| exact CAS.NumberTheory.Jacobi.jacobiSym_eq_of_loop $(natTerm fuel)
      (by decide +kernel) (by decide +kernel)))
  logNumber ref "jacobiSymbol" s!"({a} / {n})" s!"{j}" "Jacobi symbol" proposition proof
    (domain := "ℤ × ℕ") (inputType := "an integer and an odd natural number")

end CAS.Command.NumberTheory
