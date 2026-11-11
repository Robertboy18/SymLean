/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# The Jacobi symbol by quadratic reciprocity

`CAS.NumberTheory.Jacobi.loop` computes `J(a | b)` for odd `b` the way Euclid's algorithm
computes a gcd: it takes out the factors `2` of `a` with the value of `J(2 | b)`, and otherwise
swaps `a` and `b` by quadratic reciprocity and reduces `b` modulo `a`. `jacobiSym_eq_of_loop`
turns one run of the loop into `jacobiSym a b = j`, so the kernel checks a value by evaluating
the loop once.

## Main definitions

* `CAS.NumberTheory.Jacobi.loop`: the reciprocity loop, with fuel.

## Main results

* `CAS.NumberTheory.Jacobi.loop_sound`: a value returned by the loop is the Jacobi symbol.
* `CAS.NumberTheory.Jacobi.jacobiSym_eq_of_loop`: `jacobiSym a b = j` for an integer `a`.

## Implementation notes

Mathlib's `norm_num` extension for Jacobi symbols lives in a module that also declares a root
namespace `Tactic`, which makes `open … Tactic` ambiguous in every module that imports it, so it
cannot be part of `import CAS`. We prove each step of the loop from Mathlib's lemmas instead:
`jacobiSym.at_two` with `ZMod.χ₈_nat_eq_if_mod_eight` for a factor `2`,
`jacobiSym.quadratic_reciprocity_if` for the swap and `jacobiSym.mod_left` for the reduction.
The fuel only makes the recursion structural. For `a < b` each step keeps `a < b` and lowers
`log₂ a + log₂ b` by at least one; the command starts from `a % b`, so its fuel
`2 (log₂ (a % b) + log₂ b) + 4` is never used up.

## References

* The mathlib Community, "The Lean Mathematical Library", in *Proceedings of the 9th ACM SIGPLAN
  International Conference on Certified Programs and Proofs (CPP 2020)*, ACM, 2020, pp. 367-381,
  <https://doi.org/10.1145/3372885.3373824>.
  We use its Jacobi symbol `jacobiSym` and the lemmas named above.
-/

@[expose] public section

namespace CAS.NumberTheory.Jacobi

/-- `χ₈ b` for odd `b`: `1` when `b % 8` is `1` or `7`, else `-1`. -/
def twoSign (b : ℕ) : ℤ := if b % 8 = 1 ∨ b % 8 = 7 then 1 else -1

/-- The sign in quadratic reciprocity for odd `a` and `b`: `-1` when both are `3` modulo `4`. -/
def recSign (a b : ℕ) : ℤ := if a % 4 = 3 ∧ b % 4 = 3 then -1 else 1

/-- The Jacobi symbol `J(a | b)` for odd `b` by reciprocity and the value at `2`, or `none` when
`fuel` runs out. -/
def loop : ℕ → ℕ → ℕ → Option ℤ
  | 0, _, _ => none
  | fuel + 1, a, b =>
    if b = 1 then some 1
    else if a = 0 then some 0
    else if a % 2 = 0 then (loop fuel (a / 2) b).map (twoSign b * ·)
    else (loop fuel (b % a) a).map (recSign a b * ·)

/-- A value `j` returned by `loop fuel a b` for odd `b` is the Jacobi symbol `J(a | b)`. -/
theorem loop_sound : ∀ (fuel a b : ℕ) (j : ℤ), b % 2 = 1 → loop fuel a b = some j →
    jacobiSym a b = j
  | 0, _, _, _, _, h => by simp [loop] at h
  | fuel + 1, a, b, j, hb, h => by
    unfold loop at h
    split_ifs at h with h1 h2 h3
    · subst h1
      simpa using h
    · subst h2
      simp only [Option.some.injEq] at h
      subst h
      exact_mod_cast jacobiSym.zero_left (by omega)
    · obtain ⟨j', hj', rfl⟩ := Option.map_eq_some_iff.mp h
      have ha : (a : ℤ) = 2 * ((a / 2 : ℕ) : ℤ) := by omega
      rw [ha, jacobiSym.mul_left, jacobiSym.at_two (Nat.odd_iff.mpr hb),
        ZMod.χ₈_nat_eq_if_mod_eight, loop_sound fuel (a / 2) b j' hb hj', twoSign]
      split_ifs <;> omega
    · obtain ⟨j', hj', rfl⟩ := Option.map_eq_some_iff.mp h
      have ha : a % 2 = 1 := by omega
      rw [← jacobiSym.quadratic_reciprocity_if ha hb, jacobiSym.mod_left,
        ← Int.natCast_mod, loop_sound fuel (b % a) a j' ha hj', recSign]
      split_ifs <;> simp

/-- `J(a | b) = j` for an integer `a` and an odd natural `b` when the loop, run on `a % b`,
returns `j`. -/
theorem jacobiSym_eq_of_loop {a : ℤ} {b : ℕ} {j : ℤ} (fuel : ℕ) (hb : b % 2 = 1)
    (h : loop fuel (a % b).toNat b = some j) : jacobiSym a b = j := by
  rw [jacobiSym.mod_left, ← Int.toNat_of_nonneg (Int.emod_nonneg a (by omega))]
  exact loop_sound fuel _ b j hb h

end CAS.NumberTheory.Jacobi
