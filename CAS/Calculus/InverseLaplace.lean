/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.Laplace
public import CAS.Calculus.LinearODERoots

/-!
# Terms of inverse Laplace transforms

For a denominator factor `(s - a) ² + β`, the terms of an inverse Laplace transform are
`tⁿ e^{a t}` times `cosQ β t` or `sinQ β t`, where `cosQ β t` is `cos (√β t)` for `β > 0`,
`cosh (√(-β) t)` for `β < 0` and `1` for `β = 0`, and `sinQ β t` is `sin (√β t) / √β`,
`sinh (√(-β) t) / √(-β)` and `t`. Their transforms are rational functions of `s` without square
roots (`QuadTerm.transform_eq`). For a monic squarefree factor `R` whose roots are known only by
enclosures, and `W` with `W R' = B + T R` and `B` of fewer coefficients than `R`, the transforms
of the terms `enclosedTerms R D W` add up to `B / R` for `s` beyond the real parts of the roots
(`Enclosures.laplace`). `#cas [inverseLaplace s t]` proves its results with
`integral_exp_mul_quadSum` and `integral_exp_mul_quadSum_enclosed`.

## Main definitions

* `quadPQ`: the polynomials `P`, `Q` with `(u + b i) ^ m = P + b Q i` when `b ² = β` and
  `(u + b) ^ m = P + b Q` when `b ² = -β`.
* `QuadTerm`: a term `c tⁿ e^{a t} cosQ β t` or `c tⁿ e^{a t} sinQ β t`, with
  `QuadTerm.toLaplace`, its convergence bound `QuadTerm.bound` (`a + √(max (-β) 0)`) and its
  transform `QuadTerm.transform`.
* `enclosedTerms`: the terms `W(r) e^{r t}` for the real roots `r` of `R` and
  `2 Re (W(z) e^{z t})` for the pairs `z, z̄`.

## Main results

* `QuadTerm.transform_eq`: the transform of a term, without square roots.
* `integral_exp_mul_quadSum`: the transform of a finite sum of `QuadTerm`s.
* `Enclosures.laplace`: when `D.check R` holds, `W R' = B + T R` and `B` has fewer coefficients
  than `R`, the transforms of `enclosedTerms R D W` add up to `B / R` for `s` beyond the real
  parts of the roots.
* `Enclosures.re_lt`: a rational bound `σ` of those real parts, read off the enclosures.
* `integral_exp_mul_quadSum_enclosed`: the two kinds of terms together.

## Implementation notes

`QuadTerm.toLaplace` writes a term as a `LaplaceTerm`, with frequency `√β` or `√(-β)` (none for
`β = 0`) and the factor `1 / √|β|` of `sinQ β t` in the coefficient, so that the transforms and the
linearity `integral_exp_mul_sum` of `CAS.Calculus.Laplace` apply. `QuadTerm.transform_eq` then
removes the square roots: with `u = s - a` the transforms are `n! P / (u ² + β) ^ (n + 1)` and
`n! Q / (u ² + β) ^ (n + 1)` for `(P, Q) = quadPQ u β (n + 1)` (`laplacePQ_eq_quadPQ`,
`add_pow_eq_quadPQ`). For rational `c`, `a` and `β` the transform is thus a rational function of
`s` with rational coefficients, even when `√β` is irrational. `le_add_sqrt` and `add_sqrt_le`
compare bounds `a + √c` with rational numbers.

Over the enclosed roots, untrusted code proposes the enclosures `D` (`LinearODE.Enclosures`) and
the polynomials `W` and `T`; the kernel checks `D` (`Enclosures.check`) and `W R' = B + T R`
over `ℚ` (`coeffEq`). The partial fractions `Enclosures.partial_fraction` of
`CAS.Calculus.LinearODERoots` give `B / R = ∑ W(μ) / (s - μ)` over the roots. A real root `r`
contributes the term `W(r) e^{r t}`, and a pair `z, z̄` the two real terms of
`2 Re (W(z) e^{z t})`, whose transforms add up to `W(z) / (s - z) + W(z̄) / (s - z̄)`
(`pair_transform`). This is the classical expansion over simple poles, with
`W(μ) = B(μ) / R'(μ)`. `Enclosures.re_lt` gives the convergence bound from the check
`enclosedBelow D σ`. Only the forward direction is proved, that the terms have the given
transform; uniqueness of the inverse transform up to null sets (Lerch's theorem) is not.

## References

* NIST Digital Library of Mathematical Functions, §1.14 Integral Transforms, Version 1.2.8
  (2026-09-15), <https://dlmf.nist.gov/1.14>. §1.14(iii): the definition (1.14.17).
-/

@[expose] public section

open MeasureTheory Set Real

namespace CAS.Calculus.Laplace

/-- `(P, Q)` with `P₀ = 1`, `Q₀ = 0`, `Pₘ₊₁ = Pₘ u - Qₘ β`, `Qₘ₊₁ = Qₘ u + Pₘ`. -/
def quadPQ (u β : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | m + 1 => ((quadPQ u β m).1 * u - (quadPQ u β m).2 * β,
      (quadPQ u β m).2 * u + (quadPQ u β m).1)

/-- `laplacePQ u b m = (P, b Q)` for `(P, Q) = quadPQ u (b ^ 2) m`. -/
theorem laplacePQ_eq_quadPQ (u b : ℝ) (m : ℕ) :
    laplacePQ u b m = ((quadPQ u (b ^ 2) m).1, b * (quadPQ u (b ^ 2) m).2) := by
  induction m with
  | zero => simp [laplacePQ, quadPQ]
  | succ m ih =>
    simp only [laplacePQ, quadPQ, ih, Prod.mk.injEq]
    constructor <;> ring

/-- `(u + b) ^ m = P + b Q` and `(u - b) ^ m = P - b Q` for `(P, Q) = quadPQ u (-(b ^ 2)) m`. -/
theorem add_pow_eq_quadPQ (u b : ℝ) (m : ℕ) :
    (u + b) ^ m = (quadPQ u (-(b ^ 2)) m).1 + b * (quadPQ u (-(b ^ 2)) m).2 ∧
      (u - b) ^ m = (quadPQ u (-(b ^ 2)) m).1 - b * (quadPQ u (-(b ^ 2)) m).2 := by
  induction m with
  | zero => simp [quadPQ]
  | succ m ih =>
    simp only [quadPQ, pow_succ, ih.1, ih.2]
    constructor <;> ring

/-- `quadPQ u 0 m = (u ^ m, m u ^ (m - 1))`. -/
theorem quadPQ_zero (u : ℝ) (m : ℕ) : quadPQ u 0 (m + 1) = (u ^ (m + 1), (m + 1) * u ^ m) := by
  induction m with
  | zero => simp [quadPQ]
  | succ m ih =>
    rw [quadPQ, ih]
    simp only [mul_zero, sub_zero, Prod.mk.injEq]
    push_cast
    constructor <;> ring

/-- `LaplaceTerm.transform` unfolded (by `rfl`, so that its equation lemma is not realized here,
in the module of `CAS.Calculus.Laplace`'s own users). -/
theorem LaplaceTerm.transform_def (T : LaplaceTerm) (s : ℝ) :
    T.transform s = match T.kind with
      | .exp => T.c * (T.n.factorial / (s - T.a) ^ (T.n + 1))
      | .cos => T.c * (T.n.factorial * (laplacePQ (s - T.a) T.b (T.n + 1)).1 /
          ((s - T.a) ^ 2 + T.b ^ 2) ^ (T.n + 1))
      | .sin => T.c * (T.n.factorial * (laplacePQ (s - T.a) T.b (T.n + 1)).2 /
          ((s - T.a) ^ 2 + T.b ^ 2) ^ (T.n + 1))
      | .cosh => T.c * (T.n.factorial / 2 *
          (1 / (s - (T.a + T.b)) ^ (T.n + 1) + 1 / (s - (T.a - T.b)) ^ (T.n + 1)))
      | .sinh => T.c * (T.n.factorial / 2 *
          (1 / (s - (T.a + T.b)) ^ (T.n + 1) - 1 / (s - (T.a - T.b)) ^ (T.n + 1))) := rfl

/-- `LaplaceTerm.eval` unfolded (by `rfl`). -/
theorem LaplaceTerm.eval_def (T : LaplaceTerm) (t : ℝ) :
    T.eval t = match T.kind with
      | .exp => T.c * (t ^ T.n * Real.exp (T.a * t))
      | .cos => T.c * (t ^ T.n * Real.exp (T.a * t) * Real.cos (T.b * t))
      | .sin => T.c * (t ^ T.n * Real.exp (T.a * t) * Real.sin (T.b * t))
      | .cosh => T.c * (t ^ T.n * Real.exp (T.a * t) * Real.cosh (T.b * t))
      | .sinh => T.c * (t ^ T.n * Real.exp (T.a * t) * Real.sinh (T.b * t)) := rfl

/-- `LaplaceTerm.Admissible` unfolded (by `rfl`). -/
theorem LaplaceTerm.admissible_def (T : LaplaceTerm) (s : ℝ) :
    T.Admissible s = match T.kind with
      | .exp | .cos | .sin => T.a < s
      | .cosh | .sinh => T.a + T.b < s ∧ T.a - T.b < s := rfl

/-- A term `c tⁿ e^{a t} cosQ β t` (`odd = false`) or `c tⁿ e^{a t} sinQ β t` (`odd = true`). -/
structure QuadTerm where
  /-- The coefficient. -/
  c : ℝ
  /-- The power of `t`. -/
  n : ℕ
  /-- The rate. -/
  a : ℝ
  /-- The constant of the factor `(s - a) ² + β`. -/
  β : ℝ
  /-- `sinQ` instead of `cosQ`. -/
  odd : Bool

/-- The term as a `LaplaceTerm`: `cos`, `sin` with frequency `√β` for `β > 0`, `cosh`, `sinh`
with `√(-β)` for `β < 0`, `tⁿ e^{a t}` and `t^(n+1) e^{a t}` for `β = 0`; the factor `1 / √|β|`
of `sinQ` is in the coefficient. -/
noncomputable def QuadTerm.toLaplace (T : QuadTerm) : LaplaceTerm :=
  if 0 < T.β then
    if T.odd then ⟨T.c / √T.β, T.n, T.a, √T.β, .sin⟩ else ⟨T.c, T.n, T.a, √T.β, .cos⟩
  else if T.β < 0 then
    if T.odd then ⟨T.c / √(-T.β), T.n, T.a, √(-T.β), .sinh⟩ else ⟨T.c, T.n, T.a, √(-T.β), .cosh⟩
  else
    if T.odd then ⟨T.c, T.n + 1, T.a, 0, .exp⟩ else ⟨T.c, T.n, T.a, 0, .exp⟩

/-- The convergence bound `a + √(max (-β) 0)`: `a` for `β ≥ 0`, `a + √(-β)` for `β < 0`. -/
noncomputable def QuadTerm.bound (T : QuadTerm) : ℝ := T.a + √(max (-T.β) 0)

/-- The transform of a term, without square roots. -/
noncomputable def QuadTerm.transform (T : QuadTerm) (s : ℝ) : ℝ :=
  T.c * T.n.factorial *
    (if T.odd then (quadPQ (s - T.a) T.β (T.n + 1)).2 else (quadPQ (s - T.a) T.β (T.n + 1)).1) /
    ((s - T.a) ^ 2 + T.β) ^ (T.n + 1)

/-- If `T.bound < s`, the term `T.toLaplace` is admissible at `s` (`LaplaceTerm.Admissible`), the
condition under which its transform is proved. -/
theorem QuadTerm.admissible (T : QuadTerm) {s : ℝ} (h : T.bound < s) :
    T.toLaplace.Admissible s := by
  unfold QuadTerm.bound at h
  unfold QuadTerm.toLaplace
  have hb0 := Real.sqrt_nonneg (max (-T.β) 0)
  split_ifs with h1 h2 h3 h4 h5 <;> simp only [LaplaceTerm.admissible_def]
  all_goals first
    | linarith
    | (rw [max_eq_left (by linarith)] at h
       constructor <;> linarith [Real.sqrt_nonneg (-T.β)])

/-- The transform of a term in the form without square roots. -/
theorem QuadTerm.transform_eq (T : QuadTerm) {s : ℝ} (h : T.bound < s) :
    T.toLaplace.transform s = T.transform s := by
  obtain ⟨c, n, a, β, odd⟩ := T
  unfold QuadTerm.bound at h
  simp only at h
  unfold QuadTerm.toLaplace QuadTerm.transform
  simp only
  rcases lt_trichotomy β 0 with hβ | hβ | hβ
  · -- `cosh`, `sinh` with `b = √(-β)`.
    have hneg : ¬ 0 < β := by linarith
    rw [max_eq_left (by linarith)] at h
    set b := √(-β) with hb
    have hb0 : 0 ≤ b := Real.sqrt_nonneg _
    have hbb : b ^ 2 = -β := Real.sq_sqrt (by linarith)
    have hβb : β = -(b ^ 2) := by linarith
    have hX : s - (a + b) ≠ 0 := by intro h0; linarith
    have hY : s - (a - b) ≠ 0 := by intro h0; linarith
    have hX' : s - (a + b) = (s - a) - b := by ring
    have hY' : s - (a - b) = (s - a) + b := by ring
    have hpq := add_pow_eq_quadPQ (s - a) b (n + 1)
    rw [← hβb] at hpq
    have hD : (s - a) ^ 2 + β = ((s - a) - b) * ((s - a) + b) := by rw [hβb]; ring
    have hXne : (s - a) - b ≠ 0 := hX' ▸ hX
    have hYne : (s - a) + b ≠ 0 := hY' ▸ hY
    cases odd
    · simp only [hneg, hβ, ↓reduceIte, LaplaceTerm.transform_def, Bool.false_eq_true]
      rw [hX', hY', hD, mul_pow]
      rw [div_add_div _ _ (pow_ne_zero _ hXne) (pow_ne_zero _ hYne), hpq.1, hpq.2]
      field_simp
      ring
    · simp only [hneg, hβ, ↓reduceIte, LaplaceTerm.transform_def]
      have hbpos : 0 < b := by rw [hb]; exact Real.sqrt_pos.2 (by linarith)
      rw [hX', hY', hD, mul_pow]
      rw [div_sub_div _ _ (pow_ne_zero _ hXne) (pow_ne_zero _ hYne), hpq.1, hpq.2]
      field_simp
      ring
  · -- `β = 0`: `tⁿ e^{a t}` and `t^(n+1) e^{a t}`.
    subst hβ
    simp only [lt_irrefl, ↓reduceIte, neg_zero, max_self, Real.sqrt_zero, add_zero] at h ⊢
    have hu0 : s - a ≠ 0 := by intro h0; linarith
    rw [quadPQ_zero]
    cases odd
    · simp only [Bool.false_eq_true, ↓reduceIte, LaplaceTerm.transform_def]
      rw [← pow_mul]
      generalize s - a = u at hu0 ⊢
      rw [show 2 * (n + 1) = (n + 1) + (n + 1) by ring, pow_add]
      field_simp
      ring
    · simp only [↓reduceIte, LaplaceTerm.transform_def, Nat.factorial_succ]
      push_cast
      rw [← pow_mul]
      generalize s - a = u at hu0 ⊢
      rw [show 2 * (n + 1) = (n + 1) + 1 + n by ring, pow_add, pow_add]
      field_simp
      ring
  · -- `cos`, `sin` with `b = √β`.
    have hb0 : 0 < √β := Real.sqrt_pos.2 hβ
    have hbb : √β ^ 2 = β := Real.sq_sqrt hβ.le
    cases odd
    · simp only [hβ, ↓reduceIte, LaplaceTerm.transform_def, Bool.false_eq_true]
      rw [laplacePQ_eq_quadPQ, hbb]
      ring
    · simp only [hβ, ↓reduceIte, LaplaceTerm.transform_def]
      rw [laplacePQ_eq_quadPQ, hbb]
      field_simp

/-- `x ≤ a + √c` when `x ≤ a`, or when `0 ≤ x - a` and `(x - a) ² ≤ c`. -/
theorem le_add_sqrt {x a c : ℝ} (h : x - a ≤ 0 ∨ (0 ≤ x - a ∧ (x - a) ^ 2 ≤ c)) :
    x ≤ a + √c := by
  rcases h with h | ⟨h0, h1⟩
  · linarith [Real.sqrt_nonneg c]
  · have := (Real.le_sqrt h0 (le_trans (sq_nonneg _) h1)).2 h1
    linarith

/-- `a + √c ≤ y` when `0 ≤ y - a` and `c ≤ (y - a) ²`. -/
theorem add_sqrt_le {y a c : ℝ} (h0 : 0 ≤ y - a) (h1 : c ≤ (y - a) ^ 2) : a + √c ≤ y := by
  have := (Real.sqrt_le_left h0).2 h1
  linarith

/-- For `0 ≤ T.β`, the convergence bound `T.bound` is `T.a`. -/
theorem QuadTerm.bound_of_nonneg (T : QuadTerm) (h : 0 ≤ T.β) : T.bound = T.a := by
  simp [QuadTerm.bound, max_eq_right (neg_nonpos.2 h)]

/-- `T.bound = T.a + √(-T.β)` for every term `T`, with no sign condition on `T.β`: for `0 ≤ T.β`
both sides are `T.a`, as `Real.sqrt` is `0` on nonpositive arguments. -/
theorem QuadTerm.bound_eq_add_sqrt (T : QuadTerm) : T.bound = T.a + √(-T.β) := by
  rw [QuadTerm.bound]
  rcases le_total 0 (-T.β) with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, Real.sqrt_zero, Real.sqrt_eq_zero_of_nonpos h]

/-- `(s - a) ² - c > 0` when `a + √c < s`. -/
theorem sub_sq_sub_pos {s a c : ℝ} (h : a + √c < s) : 0 < (s - a) ^ 2 - c := by
  rcases lt_or_ge c 0 with hc | hc
  · nlinarith [sq_nonneg (s - a)]
  have h0 : √c < s - a := by linarith
  have h1 : (√c) ^ 2 < (s - a) ^ 2 := by
    have := Real.sqrt_nonneg c
    nlinarith
  rw [Real.sq_sqrt hc] at h1
  linarith

/-- Linearity over a list of quadratic-factor terms. -/
theorem integral_exp_mul_quadSum (Ts : List QuadTerm) {s : ℝ} (h : ∀ T ∈ Ts, T.bound < s) :
    IntegrableOn (fun t ↦ Real.exp (-(s * t)) * (Ts.map fun T ↦ T.toLaplace.eval t).sum)
        (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * (Ts.map fun T ↦ T.toLaplace.eval t).sum =
        (Ts.map fun T ↦ T.transform s).sum := by
  have key := integral_exp_mul_sum (Ts.map QuadTerm.toLaplace) (s := s) (by
    intro L hL
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hL
    exact T.admissible (h T hT))
  simp only [List.map_map, Function.comp_def] at key
  refine ⟨key.1, key.2.trans ?_⟩
  congr 1
  exact List.map_congr_left fun T hT ↦ T.transform_eq (h T hT)

/-! ## Terms over the enclosed roots of a squarefree factor -/

section Enclosed

open Complex _root_.Polynomial CAS.LinearODE CAS.AlgRoot
open CAS.Polynomial (coeffEval coeffAdd coeffMul coeffDeriv coeffEq)

/-- A conjugate pair of terms `2 Re (w e^{z t})`: its transform. -/
theorem pair_transform (w z : ℂ) (s : ℝ) :
    (⟨((2 : ℂ) * w).re, 0, z.re, z.im, .cos⟩ : LaplaceTerm).transform s +
      (⟨-((2 : ℂ) * w).im, 0, z.re, z.im, .sin⟩ : LaplaceTerm).transform s =
    (w / ((s : ℂ) - z) + (starRingEnd ℂ) w / ((s : ℂ) - (starRingEnd ℂ) z)).re := by
  have hc : (starRingEnd ℂ) w / ((s : ℂ) - (starRingEnd ℂ) z) =
      (starRingEnd ℂ) (w / ((s : ℂ) - z)) := by
    rw [map_div₀, map_sub, Complex.conj_ofReal]
  rw [hc, Complex.add_conj, Complex.ofReal_re, Complex.div_re, LaplaceTerm.transform_def,
    LaplaceTerm.transform_def]
  simp only [laplacePQ, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one,
    Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- The terms of the inverse transform of `B / R` over the enclosed roots of `R`: `W(r) e^{r t}`
for a real root `r`, `2 Re (W(z) e^{z t})` for a pair `z, z̄`. -/
noncomputable def enclosedTerms (R : List ℚ) (D : Enclosures) (W : List ℚ) : List LaplaceTerm :=
  (D.reals.map fun I ↦ (⟨coeffEval W (CAS.AlgRoot.real R I.1 I.2), 0,
      CAS.AlgRoot.real R I.1 I.2, 0, .exp⟩ : LaplaceTerm)) ++
  D.discs.flatMap fun d ↦
    [⟨((2 : ℂ) * (polyC W).eval (CAS.AlgRoot.complex R d.1 d.2.1 d.2.2.1)).re, 0,
        (CAS.AlgRoot.complex R d.1 d.2.1 d.2.2.1).re,
        (CAS.AlgRoot.complex R d.1 d.2.1 d.2.2.1).im, .cos⟩,
      ⟨-((2 : ℂ) * (polyC W).eval (CAS.AlgRoot.complex R d.1 d.2.1 d.2.2.1)).im, 0,
        (CAS.AlgRoot.complex R d.1 d.2.1 d.2.2.1).re,
        (CAS.AlgRoot.complex R d.1 d.2.1 d.2.2.1).im, .sin⟩]

/-- For real points `r = f I` over a list `l`, the sum in `ℂ` of `W(r) / (s - r)`, with `W(r)` the
value of `polyC W`, is the cast of the sum of the transforms at `s` of the terms `W(r) e^{r t}`, for
every real `s`. -/
theorem sum_reals_transform (l : List (ℚ × ℚ)) (f : ℚ × ℚ → ℝ) (W : List ℚ) (s : ℝ) :
    ((l.map fun I ↦ ((f I : ℝ) : ℂ)).map fun μ ↦ (polyC W).eval μ / ((s : ℂ) - μ)).sum =
      (((l.map fun I ↦ (⟨coeffEval W (f I), 0, f I, 0, .exp⟩ : LaplaceTerm)).map
        fun T ↦ T.transform s).sum : ℝ) := by
  induction l with
  | nil => simp
  | cons I l ih =>
    simp only [List.map_cons, List.sum_cons, ih, eval_polyC_ofReal, Complex.ofReal_add,
      LaplaceTerm.transform_def, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    push_cast
    ring

/-- For complex points `z = g d` over a list `l`, the sum in `ℂ` of `W(μ) / (s - μ)` over the points
`z` and their conjugates `z̄` is the cast of the sum of the transforms at `s` of the terms
`2 Re (W(z) e^{z t})`, one `cos` and one `sin` term for each `d`, for every real `s`. -/
theorem sum_discs_transform {δ : Type*} (l : List δ) (g : δ → ℂ) (W : List ℚ) (s : ℝ) :
    ((l.flatMap fun d ↦ [g d, (starRingEnd ℂ) (g d)]).map
        fun μ ↦ (polyC W).eval μ / ((s : ℂ) - μ)).sum =
      (((l.flatMap fun d ↦
          [(⟨((2 : ℂ) * (polyC W).eval (g d)).re, 0, (g d).re, (g d).im, .cos⟩ : LaplaceTerm),
            ⟨-((2 : ℂ) * (polyC W).eval (g d)).im, 0, (g d).re, (g d).im, .sin⟩]).map
        fun T ↦ T.transform s).sum : ℝ) := by
  induction l with
  | nil => simp
  | cons d l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append, List.sum_append, ih,
      List.map_append, List.sum_append, Complex.ofReal_add]
    congr 1
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      eval_conj_polyC]
    have hc : (starRingEnd ℂ) ((polyC W).eval (g d)) / ((s : ℂ) - (starRingEnd ℂ) (g d)) =
        (starRingEnd ℂ) ((polyC W).eval (g d) / ((s : ℂ) - g d)) := by
      rw [map_div₀, map_sub, Complex.conj_ofReal]
    rw [pair_transform, hc, Complex.add_conj, Complex.ofReal_re]

/-- `R` has no zero at `s` when every root of `R` has real part below `s`. -/
theorem Enclosures.eval_ne_zero (R : List ℚ) (D : Enclosures) (hD : D.check R = true) {s : ℝ}
    (hs : ∀ μ ∈ rrAll (D.rroots R), μ.re < s) : coeffEval R s ≠ 0 := by
  intro h0
  have h1 : (polyC R).eval (s : ℂ) = 0 := by rw [eval_polyC_ofReal, h0, Complex.ofReal_zero]
  rw [← Enclosures.prod_eq' R D hD, eval_list_prod, List.prod_eq_zero_iff] at h1
  simp only [List.map_map, List.mem_map, Function.comp_apply, eval_sub, eval_X, eval_C] at h1
  obtain ⟨μ, hμ, h2⟩ := h1
  have h3 := congrArg Complex.re h2
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at h3
  linarith [hs μ hμ]

/-- The transforms of `enclosedTerms R D W` add up to `B / R` when `W R' = B + T R`. -/
theorem Enclosures.transform_sum (R : List ℚ) (D : Enclosures) (hD : D.check R = true)
    (B W T : List ℚ) (hB : B.length < R.length)
    (hW : coeffEq (coeffMul W (coeffDeriv R)) (coeffAdd B (coeffMul T R)) = true) {s : ℝ}
    (hs : ∀ μ ∈ rrAll (D.rroots R), μ.re < s) :
    ((enclosedTerms R D W).map fun T ↦ T.transform s).sum = coeffEval B s / coeffEval R s := by
  have hR := Enclosures.eval_ne_zero R D hD hs
  have hR' : (polyC R).eval (s : ℂ) ≠ 0 := by
    rw [eval_polyC_ofReal]; exact_mod_cast hR
  have hpf := Enclosures.partial_fraction R D hD B W T hB hW s hR'
  rw [eval_polyC_ofReal, eval_polyC_ofReal] at hpf
  apply Complex.ofReal_injective
  rw [Complex.ofReal_div, hpf, Enclosures.rrAll_eq, List.map_append, List.sum_append,
    sum_reals_transform _ (fun I ↦ CAS.AlgRoot.real R I.1 I.2),
    sum_discs_transform _
      (fun d : ℚ × ℚ × ℚ × ℚ × ℚ × ℚ ↦ CAS.AlgRoot.complex R d.1 d.2.1 d.2.2.1),
    enclosedTerms, List.map_append, List.sum_append, Complex.ofReal_add]

/-- If every enclosed root of `R` has real part below `s`, every term of `enclosedTerms R D W` is
admissible at `s` (`LaplaceTerm.Admissible`). No check of `D` is assumed. -/
theorem Enclosures.admissible (R : List ℚ) (D : Enclosures) (W : List ℚ) {s : ℝ}
    (hs : ∀ μ ∈ rrAll (D.rroots R), μ.re < s) : ∀ T ∈ enclosedTerms R D W, T.Admissible s := by
  intro T hT
  simp only [Enclosures.rrAll_eq, List.mem_append, List.mem_map, List.mem_flatMap,
    List.mem_cons, List.not_mem_nil, or_false] at hs
  simp only [enclosedTerms, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false] at hT
  rcases hT with ⟨I, hI, rfl⟩ | ⟨d, hd, rfl | rfl⟩
  · simpa [LaplaceTerm.admissible_def] using hs _ (Or.inl ⟨I, hI, rfl⟩)
  · simpa [LaplaceTerm.admissible_def] using hs _ (Or.inr ⟨d, hd, Or.inl rfl⟩)
  · simpa [LaplaceTerm.admissible_def] using hs _ (Or.inr ⟨d, hd, Or.inl rfl⟩)

/-- The inverse transform of `B / R` over the enclosed roots of `R`. -/
theorem Enclosures.laplace (R : List ℚ) (D : Enclosures) (hD : D.check R = true)
    (B W T : List ℚ) (hB : B.length < R.length)
    (hW : coeffEq (coeffMul W (coeffDeriv R)) (coeffAdd B (coeffMul T R)) = true) {s : ℝ}
    (hs : ∀ μ ∈ rrAll (D.rroots R), μ.re < s) :
    IntegrableOn (fun t ↦ Real.exp (-(s * t)) * ((enclosedTerms R D W).map
        fun T ↦ T.eval t).sum) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * ((enclosedTerms R D W).map
        fun T ↦ T.eval t).sum = coeffEval B s / coeffEval R s := by
  have h := integral_exp_mul_sum (enclosedTerms R D W) (Enclosures.admissible R D W hs)
  exact ⟨h.1, h.2.trans (Enclosures.transform_sum R D hD B W T hB hW hs)⟩

/-- Every interval of `D` ends at `σ` or below, and every disc `(u, v, ρ, …)` has `u + ρ ≤ σ`. -/
def enclosedBelow (D : Enclosures) (σ : ℚ) : Bool :=
  (D.reals.all fun I ↦ decide (I.2 ≤ σ)) && D.discs.all fun d ↦ decide (d.1 + d.2.2.1 ≤ σ)

/-- The enclosed roots of `R` have real part below `s` when `enclosedBelow D σ` and `σ < s`. -/
theorem Enclosures.re_lt (R : List ℚ) (D : Enclosures) (hD : D.check R = true) {σ : ℚ}
    (hσ : enclosedBelow D σ = true) {s : ℝ} (hs : (σ : ℝ) < s) :
    ∀ μ ∈ rrAll (D.rroots R), μ.re < s := by
  simp only [Enclosures.check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hD
  simp only [enclosedBelow, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hσ
  obtain ⟨⟨⟨⟨⟨hreal, -⟩, hdisc⟩, -⟩, -⟩, -⟩ := hD
  intro μ hμ
  rw [Enclosures.rrAll_eq, List.mem_append] at hμ
  rcases hμ with hμ | hμ
  · obtain ⟨I, hI, rfl⟩ := List.mem_map.mp hμ
    have h1 := (AlgRoot.real_spec R (hreal I hI).1 (hreal I hI).2).1.2
    have h2 : (I.2 : ℝ) ≤ σ := by exact_mod_cast hσ.1 I hI
    rw [Complex.ofReal_re]
    linarith
  · obtain ⟨d, hd, hμ⟩ := List.mem_flatMap.mp hμ
    have h1 := (re_mem_of_mem_closedBall (AlgRoot.complex_spec R (hdisc d hd).1).1).1.2
    have h2 : (d.1 : ℝ) + d.2.2.1 ≤ σ := by exact_mod_cast hσ.2 d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hμ
    rcases hμ with rfl | rfl
    · linarith
    · rw [Complex.conj_re]
      linarith

/-- Linearity over quadratic-factor terms together with the enclosed terms of `B / R`. -/
theorem integral_exp_mul_quadSum_enclosed (Ts : List QuadTerm) (R : List ℚ) (D : Enclosures)
    (hD : D.check R = true) (B W T : List ℚ) (hB : B.length < R.length)
    (hW : coeffEq (coeffMul W (coeffDeriv R)) (coeffAdd B (coeffMul T R)) = true) {s : ℝ}
    (h : ∀ T ∈ Ts, T.bound < s) (hs : ∀ μ ∈ rrAll (D.rroots R), μ.re < s) :
    IntegrableOn (fun t ↦ Real.exp (-(s * t)) * ((Ts.map fun T ↦ T.toLaplace.eval t).sum +
        ((enclosedTerms R D W).map fun T ↦ T.eval t).sum)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-(s * t)) * ((Ts.map fun T ↦ T.toLaplace.eval t).sum +
          ((enclosedTerms R D W).map fun T ↦ T.eval t).sum) =
        (Ts.map fun T ↦ T.transform s).sum + coeffEval B s / coeffEval R s := by
  have h1 := integral_exp_mul_quadSum Ts h
  have h2 := Enclosures.laplace R D hD B W T hB hW hs
  have hf : (fun t ↦ Real.exp (-(s * t)) * ((Ts.map fun T ↦ T.toLaplace.eval t).sum +
      ((enclosedTerms R D W).map fun T ↦ T.eval t).sum)) =
      fun t ↦ Real.exp (-(s * t)) * (Ts.map fun T ↦ T.toLaplace.eval t).sum +
        Real.exp (-(s * t)) * ((enclosedTerms R D W).map fun T ↦ T.eval t).sum := by
    funext t
    rw [mul_add]
  rw [hf]
  refine ⟨Integrable.add h1.1 h2.1, ?_⟩
  rw [integral_add h1.1 h2.1, h1.2, h2.2]

end Enclosed

end CAS.Calculus.Laplace
