/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Data.Fin.VecNotation
public import CAS.Numerics.VectorLookup

/-!
# Direct compiled case analysis for finite indices

`finCasesDirect` is case analysis on `Fin (n + 1)` by a direct match on the index, and the
`@[csimp]` lemma `fin_cases_eq_direct` makes the compiler use it for `Fin.cases`.
`fin_cons_eq_direct` does the same for `Fin.cons`, through `finConsDirect`. For
`Matrix.vecCons` the module imports `CAS.Numerics.VectorLookup`, whose `@[csimp]` lemma
`vecCons_eq_vecConsLookup` replaces it, so that every importer compiles `Matrix.vecCons` the
same way and each constant has one `@[csimp]` lemma. The logical definitions stay the same.

## Implementation notes

Lean's `Fin.cases` uses induction with an unused recursive argument. In strict compiled
evaluation, that argument can repeat earlier lookups in nested finite vectors. We replace
the compiled implementation by a direct case split, with a kernel proof of equality: each
`@[csimp]` lemma is proved by `rfl` on the two cases of the index. `Fin.cons` and
`Matrix.vecCons`, which Mathlib defines through `Fin.cases` and compiles in its own modules,
need their own replacements. Two `@[csimp]` lemmas for one constant would make the compiled code
depend on the order of the imports, since the one imported last wins without a warning.
-/

@[expose] public section

namespace CAS.Continuum

universe u

/-- Case analysis on a finite index without computing earlier successor branches. -/
@[inline] def finCasesDirect {n : Nat} {motive : Fin (n + 1) → Sort u}
    (zero : motive 0) (succ : ∀ i : Fin n, motive i.succ) : ∀ i, motive i
  | ⟨0, _⟩ => zero
  | ⟨i + 1, hi⟩ => succ ⟨i, Nat.lt_of_succ_lt_succ hi⟩

/-- The compiler may use direct case analysis for every application of `Fin.cases`. -/
@[csimp] theorem fin_cases_eq_direct : @Fin.cases = @finCasesDirect := by
  funext n motive zero succ i
  obtain ⟨_ | i, hi⟩ := i <;> rfl

/-- Prepend to a dependent finite tuple using direct case analysis. -/
@[inline] def finConsDirect {n : Nat} {α : Fin (n + 1) → Sort u}
    (head : α 0) (tail : ∀ i : Fin n, α i.succ) : ∀ i, α i :=
  finCasesDirect head tail

/-- Rewrite tuple construction before the compiler unfolds the imported `Fin.cons`. -/
@[csimp] theorem fin_cons_eq_direct : @Fin.cons = @finConsDirect := by
  funext n α head tail i
  obtain ⟨_ | i, hi⟩ := i <;> rfl

end CAS.Continuum
