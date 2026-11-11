/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Data.Nat.ModEq

/-!
# The Chinese remainder theorem for explicit congruences

A system `y ≡ rᵢ (mod mᵢ)` is stated as a list of pairs `(mᵢ, rᵢ)`, with residues that need
not be reduced. `modEq_iff_of_lcm` characterizes all its solutions by one solution `x` modulo the
lcm of the moduli, and `not_exists_of_incompatible` proves that there is no solution when two
congruences disagree modulo the gcd of their moduli. A system is solvable exactly when its
congruences agree pairwise in this sense, so the two theorems decide every system.

## Main results

* `CAS.NumberTheory.modEq_iff_of_lcm`: the solutions of a solvable system are one residue class
  modulo the lcm.
* `CAS.NumberTheory.not_exists_of_incompatible`: a system with two incompatible congruences has
  no solution.

## Implementation notes

We state the solutions modulo the lcm rather than modulo the product of pairwise coprime moduli
(`Nat.modEq_list_prod_iff`): the lcm form covers every solvable system and has a shorter proof by
`Nat.mod_lcm`. `#cas [chineseRemainder]` finds the solution `x` outside the kernel, by
merging the congruences one at a time with the extended Euclidean algorithm. The lcm is a
`List.foldr` of `Nat.lcm`, which the kernel evaluates on literals, so the command proves the
hypotheses `hM` and `hx` by `decide +kernel`.

## References

* The mathlib Community, "The Lean Mathematical Library", in *Proceedings of the 9th ACM SIGPLAN
  International Conference on Certified Programs and Proofs (CPP 2020)*, ACM, 2020, pp. 367-381,
  <https://doi.org/10.1145/3372885.3373824>.
  We use its `Nat.ModEq` with the lemmas `Nat.mod_lcm` and `Nat.ModEq.of_dvd`.
-/

@[expose] public section

namespace CAS.NumberTheory

/-- The modulus `p.1` of a pair `p` of `pairs` divides the lcm of all the moduli. -/
theorem dvd_foldr_lcm {pairs : List (ℕ × ℕ)} {p : ℕ × ℕ} (hp : p ∈ pairs) :
    p.1 ∣ pairs.foldr (fun q acc ↦ Nat.lcm q.1 acc) 1 := by
  induction pairs with
  | nil => simp at hp
  | cons q qs ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Nat.dvd_lcm_left _ _
    · exact (ih hp).trans (Nat.dvd_lcm_right _ _)

/-- When `x` solves every congruence `y ≡ rᵢ (mod mᵢ)` of `pairs` and `M` is the lcm of the
moduli, `y` solves them all exactly when `y ≡ x (mod M)`. -/
theorem modEq_iff_of_lcm (pairs : List (ℕ × ℕ)) (x M : ℕ)
    (hM : pairs.foldr (fun q acc ↦ Nat.lcm q.1 acc) 1 = M)
    (hx : ∀ p ∈ pairs, x ≡ p.2 [MOD p.1]) (y : ℕ) :
    (∀ p ∈ pairs, y ≡ p.2 [MOD p.1]) ↔ y ≡ x [MOD M] := by
  subst hM
  constructor
  · intro h
    induction pairs with
    | nil => exact Nat.modEq_one
    | cons q qs ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at h hx
      exact Nat.mod_lcm (h.1.trans hx.1.symm) (ih hx.2 h.2)
  · intro h p hp
    exact (h.of_dvd (dvd_foldr_lcm hp)).trans (hx p hp)

/-- No `y` solves every congruence of `pairs` when two of them, `y ≡ r₁ (mod m₁)` and
`y ≡ r₂ (mod m₂)`, give different residues modulo `gcd m₁ m₂`. -/
theorem not_exists_of_incompatible {pairs : List (ℕ × ℕ)} {m₁ r₁ m₂ r₂ : ℕ}
    (h₁ : (m₁, r₁) ∈ pairs) (h₂ : (m₂, r₂) ∈ pairs)
    (h : r₁ % Nat.gcd m₁ m₂ ≠ r₂ % Nat.gcd m₁ m₂) :
    ¬ ∃ y : ℕ, ∀ p ∈ pairs, y ≡ p.2 [MOD p.1] := by
  rintro ⟨y, hy⟩
  exact h (((hy _ h₁).of_dvd (Nat.gcd_dvd_left m₁ m₂)).symm.trans
    ((hy _ h₂).of_dvd (Nat.gcd_dvd_right m₁ m₂)))

end CAS.NumberTheory
