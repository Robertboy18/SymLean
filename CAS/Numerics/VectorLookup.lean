/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Data.Fin.VecNotation

/-!
# Direct compiled lookups in vector notation

`vecConsLookup x u i` reads entry `i` of `Matrix.vecCons x u` by testing the index directly,
and the `csimp` lemma `vecCons_eq_vecConsLookup` makes compiled code use it in place of
`Matrix.vecCons`, so that a compiled lookup `![a₀, …, aₙ] i` costs one comparison per
position. Proofs and kernel reduction still use `Matrix.vecCons`.

## Implementation notes

`Matrix.vecCons` is `Fin.cons`, that is `Fin.cases`, which Lean defines through
`Fin.induction`; compiled `Fin.cases` evaluates its induction hypotheses, so a compiled lookup
in `![...]` doubles in cost with each index. We prove `vecCons_eq_vecConsLookup` by cases on
the index. The compiler trusts only this kernel-checked equation when it substitutes the
lookup, so the lemma changes what native certificate checks cost and nothing they prove. It
applies to code compiled in modules that import this one.
-/

@[expose] public section

namespace CAS.Numerics

universe u

/-- `Matrix.vecCons` with a direct test of the index. -/
def vecConsLookup {α : Type u} {n : ℕ} (x : α) (u : Fin n → α) (i : Fin n.succ) : α :=
  if h : i.val = 0 then x else u ⟨i.val - 1, by omega⟩

/-- Compiled code may replace `Matrix.vecCons` by the direct lookup. -/
@[csimp] theorem vecCons_eq_vecConsLookup : @Matrix.vecCons.{u} = @vecConsLookup.{u} := by
  funext α n x u i
  cases i using Fin.cases <;> simp [vecConsLookup, Fin.succ]

end CAS.Numerics
