/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.GridBall
import Mathlib.Tactic.Positivity.Finset

/-!
# Fixed-point series loops on natural numbers

A power series `∑ i < n, X i / w i` whose terms satisfy `X (i + 1) = X i * r i` is evaluated in
units of `2 ^ -P` by a loop over natural numbers: the current term is a pair `zp - zn`, multiplied
at each step by the pair `cp - cn` and divided by `d i` (so `r i = (cp - cn) / d i`), and its
quotient by `w i` is added to the partial sum `sp - sn` (`seriesLoop`). Each step rounds twice,
so the computed term stays within a bound `B i` of the exact term whenever
`B (i + 1) ≥ |r i| B i + 1` (`seriesLoop_spec`), and the whole sum carries the single error
bound `∑ i < n, (B i / w i + 1)`. For nonnegative terms the loop `nonnegLoop` keeps one natural
per quantity (`nonnegLoop_spec`).

## Implementation notes

We carry the a priori bound `B` through the loop instead of a ball per term, so no ball product
is formed per term: a step costs four natural multiplications, four divisions and four additions,
about 30 us in the kernel at `P = 160`, and a step of `nonnegLoop` about 17 us.
-/

@[expose] public section

namespace CAS.Numerics

/-- The state of a fixed-point series loop: the current term `zp - zn` and the partial sum
`sp - sn`. -/
structure SeriesState where
  /-- Positive part of the current term. -/
  zp : ℕ
  /-- Negative part of the current term. -/
  zn : ℕ
  /-- Positive part of the partial sum. -/
  sp : ℕ
  /-- Negative part of the partial sum. -/
  sn : ℕ

namespace SeriesState

/-- The current term as an integer. -/
def term (s : SeriesState) : ℤ := (s.zp : ℤ) - s.zn

/-- The partial sum as an integer. -/
def sum (s : SeriesState) : ℤ := (s.sp : ℤ) - s.sn

/-- One step: add the quotient of the term by `w`, then multiply the term by `(cp - cn) / d`. -/
def step (cp cn d w : ℕ) (s : SeriesState) : SeriesState :=
  ⟨Nat.div (Nat.add (Nat.mul s.zp cp) (Nat.mul s.zn cn)) d,
    Nat.div (Nat.add (Nat.mul s.zp cn) (Nat.mul s.zn cp)) d,
    Nat.add s.sp (Nat.div s.zp w), Nat.add s.sn (Nat.div s.zn w)⟩

end SeriesState

/-- `n` steps of the signed series loop from `init`. -/
def seriesLoop (cp cn : ℕ) (d w : ℕ → ℕ) (init : SeriesState) (n : ℕ) : SeriesState :=
  Nat.rec (motive := fun _ ↦ SeriesState) init (fun i s ↦ SeriesState.step cp cn (d i) (w i) s) n

/-- The state of a fixed-point loop with nonnegative terms: the term `z` and the sum `s`. -/
structure NonnegState where
  /-- The current term. -/
  z : ℕ
  /-- The partial sum. -/
  s : ℕ

/-- `n` steps of the loop with nonnegative terms: add `z / w i`, then multiply `z` by
`c / d i`. -/
def nonnegLoop (c : ℕ) (d w : ℕ → ℕ) (z₀ : ℕ) (n : ℕ) : NonnegState :=
  Nat.rec (motive := fun _ ↦ NonnegState) ⟨z₀, 0⟩
    (fun i st ↦ ⟨Nat.div (Nat.mul st.z c) (d i), Nat.add st.s (Nat.div st.z (w i))⟩) n

/-- The recursion equation of `nonnegLoop` at `n + 1`: the term becomes `z * c / d n` and the sum
gains `z / w n`, with `z` the term after `n` steps. -/
theorem nonnegLoop_succ (c : ℕ) (d w : ℕ → ℕ) (z₀ n : ℕ) :
    nonnegLoop c d w z₀ (n + 1) =
      ⟨Nat.div (Nat.mul (nonnegLoop c d w z₀ n).z c) (d n),
        Nat.add (nonnegLoop c d w z₀ n).s (Nat.div (nonnegLoop c d w z₀ n).z (w n))⟩ := rfl

namespace SeriesState

/-- The term after `step cp cn d w s` is `(zp * cp + zn * cn) / d - (zp * cn + zn * cp) / d`,
with natural quotients. -/
theorem term_step (cp cn d w : ℕ) (s : SeriesState) :
    (step cp cn d w s).term =
      (((s.zp * cp + s.zn * cn) / d : ℕ) : ℤ) - (((s.zp * cn + s.zn * cp) / d : ℕ) : ℤ) := rfl

/-- The sum after `step cp cn d w s` is the old sum plus `zp / w - zn / w`, with natural
quotients. -/
theorem sum_step (cp cn d w : ℕ) (s : SeriesState) :
    (step cp cn d w s).sum = s.sum + ((((s.zp / w : ℕ) : ℤ)) - ((s.zn / w : ℕ) : ℤ)) := by
  simp only [step, sum, Nat.add_eq, GridBall.natDiv_eq_div]
  push_cast; ring

end SeriesState

/-- The recursion equation of `seriesLoop` at `n + 1`: one `SeriesState.step` with `d n` and `w n`
after `n` steps. -/
theorem seriesLoop_succ (cp cn : ℕ) (d w : ℕ → ℕ) (init : SeriesState) (n : ℕ) :
    seriesLoop cp cn d w init (n + 1) =
      SeriesState.step cp cn (d n) (w n) (seriesLoop cp cn d w init n) := rfl

/-- One rounded multiplication of a pair moves it by less than one from the exact product. -/
theorem abs_step_term_sub_lt (cp cn d w : ℕ) (s : SeriesState) :
    |((s.term : ℚ) * (((cp : ℚ) - cn) / d)) - ((SeriesState.step cp cn d w s).term : ℚ)| < 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [SeriesState.term_step]
  have h := GridBall.abs_sub_natDiv_sub_lt (s.zp * cp + s.zn * cn) (s.zp * cn + s.zn * cp) d hd
  rw [SeriesState.term_step]
  have hq : (s.term : ℚ) * (((cp : ℚ) - cn) / d) =
      (((s.zp * cp + s.zn * cn : ℕ) : ℚ) - ((s.zp * cn + s.zn * cp : ℕ) : ℚ)) / d := by
    simp only [SeriesState.term]; push_cast; ring
  rw [hq]
  push_cast at h ⊢
  exact h

/-- The fixed-point series loop: if the exact terms satisfy `X (i + 1) = X i r i` with
`r i = (cp - cn) / d i`, and the bounds satisfy `|X 0 - term₀| ≤ B 0` and
`|r i| B i + 1 ≤ B (i + 1)`, then after `n` steps the term is within `B n` of `X n` and the sum
is within `∑ i < n, (B i / w i + 1)` of `∑ i < n, X i / w i`. -/
theorem seriesLoop_spec {cp cn : ℕ} {d w : ℕ → ℕ} {init : SeriesState} {X B : ℕ → ℚ}
    (hX : ∀ i, X (i + 1) = X i * (((cp : ℚ) - cn) / d i))
    (hB : ∀ i, |((cp : ℚ) - cn) / d i| * B i + 1 ≤ B (i + 1))
    (h0 : |X 0 - init.term| ≤ B 0) (hs0 : init.sp = 0 ∧ init.sn = 0) (n : ℕ) :
    |X n - (seriesLoop cp cn d w init n).term| ≤ B n ∧
      |(∑ i ∈ Finset.range n, X i / w i) - (seriesLoop cp cn d w init n).sum| ≤
        ∑ i ∈ Finset.range n, (B i / w i + 1) := by
  induction n with
  | zero =>
    refine ⟨h0, ?_⟩
    simp [seriesLoop, SeriesState.sum, hs0.1, hs0.2]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    set s := seriesLoop cp cn d w init n
    rw [seriesLoop_succ]
    set r : ℚ := ((cp : ℚ) - cn) / d n
    have hstep := abs_step_term_sub_lt cp cn (d n) (w n) s
    refine ⟨?_, ?_⟩
    · rw [hX n]
      have h2 := abs_sub_le (X n * r) ((s.term : ℚ) * r)
        ((SeriesState.step cp cn (d n) (w n) s).term : ℚ)
      rw [← sub_mul, abs_mul] at h2
      linarith [hB n, mul_le_mul_of_nonneg_left ih1 (abs_nonneg r)]
    · have hterm : |X n / w n - (((s.zp / w n : ℕ) : ℚ) - ((s.zn / w n : ℕ) : ℚ))| <
          B n / w n + 1 := by
        rcases Nat.eq_zero_or_pos (w n) with hw0 | hw
        · simp [hw0]
        have hwq : (0 : ℚ) < w n := by exact_mod_cast hw
        have h1 : |X n / w n - ((s.zp : ℚ) - s.zn) / w n| ≤ B n / w n := by
          rw [← sub_div, abs_div, abs_of_pos hwq]
          exact div_le_div_of_nonneg_right (by simpa [SeriesState.term] using ih1) hwq.le
        exact GridBall.abs_sub_natDiv_lt hw h1
      obtain ⟨h1, h1'⟩ := abs_le.mp ih2
      obtain ⟨h2, h2'⟩ := abs_lt.mp hterm
      rw [SeriesState.sum_step, Finset.sum_range_succ, Finset.sum_range_succ, abs_le]
      simp only [Int.cast_add, Int.cast_sub, Int.cast_natCast]
      constructor <;> linarith

/-- The loop with nonnegative terms computes the signed loop with zero negative parts. -/
theorem nonnegLoop_eq (c : ℕ) (d w : ℕ → ℕ) (z₀ n : ℕ) :
    seriesLoop c 0 d w ⟨z₀, 0, 0, 0⟩ n =
      ⟨(nonnegLoop c d w z₀ n).z, 0, (nonnegLoop c d w z₀ n).s, 0⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [seriesLoop_succ, ih]
    simp [SeriesState.step, nonnegLoop, GridBall.natDiv_eq_div]

/-- `seriesLoop_spec` for the loop with nonnegative terms. -/
theorem nonnegLoop_spec {c : ℕ} {d w : ℕ → ℕ} {z₀ : ℕ} {X B : ℕ → ℚ}
    (hX : ∀ i, X (i + 1) = X i * ((c : ℚ) / d i))
    (hB : ∀ i, |(c : ℚ) / d i| * B i + 1 ≤ B (i + 1))
    (h0 : |X 0 - z₀| ≤ B 0) (n : ℕ) :
    |X n - (nonnegLoop c d w z₀ n).z| ≤ B n ∧
      |(∑ i ∈ Finset.range n, X i / w i) - (nonnegLoop c d w z₀ n).s| ≤
        ∑ i ∈ Finset.range n, (B i / w i + 1) := by
  have h := seriesLoop_spec (cp := c) (cn := 0) (d := d) (w := w) (init := ⟨z₀, 0, 0, 0⟩)
    (X := X) (B := B) (by simpa using hX) (by simpa using hB)
    (by simpa [SeriesState.term] using h0) ⟨rfl, rfl⟩ n
  rw [nonnegLoop_eq] at h
  simpa [SeriesState.term, SeriesState.sum] using h

/-- A geometric sum with ratio in `[0, 1 / 2]` is at most two. -/
theorem geom_sum_le_two {q : ℚ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (m : ℕ) :
    ∑ k ∈ Finset.range m, q ^ k ≤ 2 := by
  have h := geom_sum_mul q m
  have hqm : 0 ≤ q ^ m := pow_nonneg hq0 m
  have hS : 0 ≤ ∑ k ∈ Finset.range m, q ^ k :=
    Finset.sum_nonneg fun k _ ↦ pow_nonneg hq0 k
  nlinarith

end CAS.Numerics
