/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Analysis.SpecialFunctions.Legendre.Coefficients
public import Mathlib.NumberTheory.Bernoulli

/-!
# Bernoulli numbers that the kernel evaluates

Mathlib defines the Bernoulli numbers `bernoulli' n` by well-founded recursion over `Fin n`, and
`bernoulli n = (-1) ^ n * bernoulli' n`. The calls `#cas (BernoulliB n)`, `#cas (zeta s)` and
`#cas (BernoulliB n x)` evaluate `bernoulliNumerators n` instead: the integers `Bⱼ (n + 1)!` for
`j ≤ n` (Mathlib's `bernoulli`, `B₁ = -1/2`). `bernoulli_eq_numerators` identifies its entries
with Mathlib's numbers.

## Main results

* `bernoulli_eq_numerators`: `bernoulli n` is entry `n` of `bernoulliNumerators n` over
  `(n + 1)!`.

## Implementation notes

We compute by the classical recurrence `(m + 1) Bₘ = -∑ j < m, C(m + 1, j) Bⱼ` for `m ≥ 1`,
which is Mathlib's `sum_bernoulli`. There is no rational arithmetic and no gcd: the entries are
scaled to the common denominator `(n + 1)!`, and the binomial coefficients are updated by exact
divisions of natural numbers. The recursion is written with the primitive operations of `ℕ` and
`ℤ`, which the kernel reduces in fewer steps than instance arithmetic. The commands run the same
function to state the numbers, and the kernel evaluates it again when it checks the statement.

## References

* NIST Digital Library of Mathematical Functions, §24.2 Definitions and Generating Functions,
  Version 1.2.8 (2026-09-15), <https://dlmf.nist.gov/24.2>. Equation (24.2.1) defines `Bₙ` by
  its generating function, with `B₁ = -1/2`.
* NIST Digital Library of Mathematical Functions, §24.5 Recurrence Relations, Version 1.2.8
  (2026-09-15), <https://dlmf.nist.gov/24.5>. The recurrence is (24.5.3).
-/

@[expose] public section

namespace CAS.Analysis.SpecialFunctions

open Finset

/-! ### Integer numerators for the kernel -/

/-- `∑ i < l.length, C(n, j + i) l[i]`, given `c = C(n, j)`: the next coefficient is
`C(n, j + 1) = C(n, j) (n - j) / (j + 1)`. -/
def binomialDot (n : ℕ) : List ℤ → ℕ → ℕ → ℤ
  | [], _, _ => 0
  | x :: l, j, c => Int.add (Int.mul (Int.ofNat c) x)
      (binomialDot n l (Nat.add j 1) (Nat.div (Nat.mul c (Nat.sub n j)) (Nat.add j 1)))

/-- `l.map (· * m) ++ [a]`. -/
def scaleConcat (m a : ℤ) : List ℤ → List ℤ
  | [] => [a]
  | x :: l => Int.mul x m :: scaleConcat m a l

/-- The integers `Bⱼ (n + 1)!` for `j ≤ n` (Mathlib's `bernoulli`). Step `k + 1` multiplies the
entries `Bⱼ (k + 1)!` by `k + 2` and appends
`B_{k+1} (k + 2)! = -∑ j ≤ k, C(k + 2, j) Bⱼ (k + 1)!`. -/
def bernoulliNumerators : ℕ → List ℤ
  | 0 => [1]
  | k + 1 =>
    let l := bernoulliNumerators k
    scaleConcat (Int.ofNat (Nat.add k 2)) (Int.neg (binomialDot (Nat.add k 2) l 0 1)) l

/-- The cons step of `binomialDot`, with the primitive operations written as `+`, `*`, `-` and `/`:
`binomialDot n (x :: l) j c = c x + binomialDot n l (j + 1) (c (n - j) / (j + 1))`, where the
coefficient update uses truncated subtraction and floor division in `ℕ`. It holds by definition. -/
theorem binomialDot_cons (n j c : ℕ) (x : ℤ) (l : List ℤ) :
    binomialDot n (x :: l) j c = c * x + binomialDot n l (j + 1) (c * (n - j) / (j + 1)) := rfl

/-- Started at the coefficient `C(n, j)`, `binomialDot n l j` computes
`∑ i < l.length, C(n, j + i) l[i]` (written with `l.getD i 0`), for every `n`, `j` and list `l`. -/
theorem binomialDot_eq (n : ℕ) (l : List ℤ) (j : ℕ) :
    binomialDot n l j (n.choose j) =
      ∑ i ∈ range l.length, ((n.choose (j + i) : ℕ) : ℤ) * l.getD i 0 := by
  induction l generalizing j with
  | nil => simp [binomialDot]
  | cons x l ih =>
    rw [binomialDot_cons, ← Nat.choose_succ_right_eq, Nat.mul_div_cancel _ (Nat.succ_pos j), ih,
      List.length_cons, sum_range_succ']
    simp [add_comm, add_left_comm]

/-- `scaleConcat m a l` multiplies every entry of `l` by `m` and appends `a`: it equals
`l.map (· * m) ++ [a]`. -/
theorem scaleConcat_eq (m a : ℤ) (l : List ℤ) : scaleConcat m a l = l.map (· * m) ++ [a] := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [scaleConcat, ih]; rfl

/-- The recursion step of `bernoulliNumerators` in list form: the list for `k + 1` is the list for
`k` with every entry multiplied by `k + 2`, followed by
`-binomialDot (k + 2) (bernoulliNumerators k) 0 1`. -/
theorem bernoulliNumerators_succ (k : ℕ) :
    bernoulliNumerators (k + 1) = (bernoulliNumerators k).map (· * ((k + 2 : ℕ) : ℤ)) ++
      [-binomialDot (k + 2) (bernoulliNumerators k) 0 1] := by
  rw [bernoulliNumerators, scaleConcat_eq]
  rfl

/-- `bernoulliNumerators n` has `n + 1` entries, one for each index `j ≤ n`. -/
theorem length_bernoulliNumerators (n : ℕ) : (bernoulliNumerators n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bernoulliNumerators_succ, ih]

/-- Entry `j ≤ n` of `bernoulliNumerators n` is `bernoulli j (n + 1)!`. -/
theorem bernoulliNumerators_getD (n : ℕ) :
    ∀ j ≤ n, ((bernoulliNumerators n).getD j 0 : ℚ) / (n + 1).factorial = bernoulli j := by
  induction n with
  | zero =>
    intro j hj
    obtain rfl : j = 0 := by omega
    simp [bernoulliNumerators]
  | succ k ih =>
    intro j hj
    have hlen := length_bernoulliNumerators k
    rw [bernoulliNumerators_succ]
    rcases Nat.lt_or_eq_of_le hj with hj | rfl
    · rw [List.getD_append _ _ _ _ (by simp [hlen]; omega),
        List.getD_eq_getElem _ _ (by simp [hlen]; omega), List.getElem_map, ← ih j (by omega),
        List.getD_eq_getElem _ _ (by omega), Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · have hd := binomialDot_eq (k + 2) (bernoulliNumerators k) 0
      rw [Nat.choose_zero_right] at hd
      rw [List.getD_append_right _ _ _ _ (by simp [hlen]), List.length_map, hlen, Nat.sub_self,
        List.getD_cons_zero, hd, hlen]
      -- `∑ j ≤ k + 1, C(k + 2, j) Bⱼ = 0`, the last term being `(k + 2) B_{k+1}`.
      have hsum := sum_bernoulli (k + 2)
      have hterm : ∀ i ∈ range (k + 1), ((k + 2).choose i : ℚ) * bernoulli i =
          ((k + 2).choose i : ℚ) * ((bernoulliNumerators k).getD i 0 : ℚ) / (k + 1).factorial := by
        intro i hi
        rw [← ih i (by simpa [Nat.lt_succ_iff] using hi)]
        ring
      rw [ite_eq_right (by omega), sum_range_succ, sum_congr rfl hterm, ← sum_div,
        Nat.choose_succ_self_right] at hsum
      have hf : ((k + 1).factorial : ℚ) ≠ 0 := by positivity
      rw [Nat.factorial_succ, div_eq_iff (by positivity)]
      rw [div_add' _ _ _ hf, div_eq_zero_iff, or_iff_left hf] at hsum
      simp only [zero_add] at hsum ⊢
      push_cast at hsum ⊢
      linear_combination -hsum

/-- `bernoulli n` is entry `n` of `bernoulliNumerators n` over `(n + 1)!`; the kernel evaluates
the right side. -/
theorem bernoulli_eq_numerators (n : ℕ) :
    bernoulli n = ((bernoulliNumerators n).getD n 0 : ℚ) / (n + 1).factorial :=
  (bernoulliNumerators_getD n n le_rfl).symm

end CAS.Analysis.SpecialFunctions
