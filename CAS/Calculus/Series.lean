/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.IteratedDifferentiation
public import Mathlib.Analysis.Calculus.Taylor

/-!
# Taylor expansions and limits of one-variable expressions

`exactValue? ρ e` evaluates an expression exactly at a rational point when every
transcendental subterm is taken at a point where its value is rational: `sin 0`, `cos 0`,
`exp 0`, `log 1`, `atan 0`, `asin 0`, `acos 1`, and `sqrt` of a rational square.
`seriesCheck e n a cs` checks that the `k`-th symbolic derivative at `a` equals `k! cs_k` for
`k ≤ n`, and `series_of_check` turns the check and validity of the derivatives at `a` into
the Taylor expansion

`e (x) = ∑ k ≤ n, cs_k (x - a) ^ k + o ((x - a) ^ n)` as `x → a`.

`leading_of_check` is the case of a single leading term `c (x - a) ^ m`, and
`tendsto_div_of_check` gives the limit `c / d` of a quotient whose numerator and denominator
have leading terms `c (x - a) ^ m` and `d (x - a) ^ m` with `d ≠ 0`.

## Main definitions

* `exactValue?`: exact rational evaluation with the special values above.
* `seriesCheck`, `leadingCheck`: the Boolean checks of Taylor coefficients at a rational point.

## Main results

* `exactValue?_sound`: an exact value is the real value.
* `eventually_validIterates`, `exists_validIteratesOn_Ioo`: validity at a point holds near it.
* `series_of_check`, `leading_of_check`: certified Taylor expansions.
* `tendsto_div_of_isLittleO`, `tendsto_div_of_check`: limits of quotients.
* `tendsto_of_validIteratesOn`: continuity at a point of validity.

## Implementation notes

The search of `#cas [series x a n]` (`CAS.Command.Series`) proposes the coefficients by
evaluating the symbolic derivatives `iteratedDiff` at `a` with `exactValue?` and dividing by
`k!`. The kernel then evaluates `seriesCheck` itself, so it recomputes the same derivatives and
values and trusts nothing from the search. Validity of the derivatives is asked at the point
only: the CEGA domain checker (`CertifiedEvalRegistry.validIteratesOn?`), evaluated by the
kernel on the interval `[a, a]`, proves it there, and `eventually_validIterates` and
`exists_validIteratesOn_Ioo` widen it to an open interval by continuity. On that interval
`contDiffOn_univariateEval` gives the smoothness and `iteratedDerivWithin_univariateEval_eq`
the derivatives that Mathlib's `taylor_isLittleO` needs. Taylor's theorem is Mathlib's.

For limits we divide the two leading-term expansions by `(x - a) ^ m`
(`tendsto_div_of_isLittleO`) instead of going through Mathlib's `HasDerivAt.lhopital_zero_nhds`.
That theorem takes the limit of the quotient of the first derivatives as a hypothesis, which for
`m > 1` is a limit of the same kind again, while one decided `leadingCheck` per side settles
every order at once.
-/

@[expose] public section

namespace CAS.Verified.Expr

open Filter Asymptotics Topology Set

/-- The rational square root of `q`, when `q` is the square of a nonnegative rational. -/
def ratSqrt? (q : ℚ) : Option ℚ :=
  if 0 ≤ q then
    let s : ℚ := (Nat.sqrt q.num.toNat : ℚ) / Nat.sqrt q.den
    if s * s = q then some s else none
  else none

/-- When `ratSqrt? q` returns `some s`, `s` is a nonnegative rational with `s * s = q`. -/
theorem ratSqrt?_spec {q s : ℚ} (h : ratSqrt? q = some s) : 0 ≤ s ∧ s * s = q := by
  simp only [ratSqrt?] at h
  split_ifs at h with hq hs
  cases h
  exact ⟨by positivity, hs⟩

/-- Exact rational evaluation at a rational point, with the special values of the elementary
functions at `0` and `1`. -/
def exactValue? {ι : Type*} (ρ : ι → ℚ) : Verified.Expr ι → Option ℚ
  | .nat n => some n
  | .int n => some n
  | .rat p q => some ((p : ℚ) / q)
  | .pi => none
  | .e => none
  | .var i => some (ρ i)
  | .add a b => do return (← exactValue? ρ a) + (← exactValue? ρ b)
  | .sub a b => do return (← exactValue? ρ a) - (← exactValue? ρ b)
  | .mul a b => do return (← exactValue? ρ a) * (← exactValue? ρ b)
  | .div a b => do return (← exactValue? ρ a) / (← exactValue? ρ b)
  | .neg a => do return -(← exactValue? ρ a)
  | .pow a k => do return (← exactValue? ρ a) ^ k
  | .sin a => do if (← exactValue? ρ a) = 0 then some 0 else none
  | .cos a => do if (← exactValue? ρ a) = 0 then some 1 else none
  | .atan a => do if (← exactValue? ρ a) = 0 then some 0 else none
  | .asin a => do if (← exactValue? ρ a) = 0 then some 0 else none
  | .acos a => do if (← exactValue? ρ a) = 1 then some 0 else none
  | .exp a => do if (← exactValue? ρ a) = 0 then some 1 else none
  | .log a => do if (← exactValue? ρ a) = 1 then some 0 else none
  | .sqrt a => do ratSqrt? (← exactValue? ρ a)
  | .rpow _ _ => none

/-- An exact value is the real value. -/
theorem exactValue?_sound {ι : Type*} (ρ : ι → ℚ) :
    ∀ (expr : Verified.Expr ι) (q : ℚ), exactValue? ρ expr = some q →
      expr.eval (fun i ↦ (ρ i : ℝ)) = q := by
  intro expr
  induction expr with
  | nat | int | rat | var =>
    rintro q ⟨⟩
    simp
  | pi | e | rpow => rintro q ⟨⟩
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb | div a b iha ihb =>
    intro q h
    simp only [exactValue?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    simp [iha x hx, ihb y hy]
  | neg a ih | pow a k ih =>
    intro q h
    simp only [exactValue?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨x, hx, rfl⟩ := h
    simp [ih x hx]
  | sin a ih | cos a ih | atan a ih | asin a ih | acos a ih | exp a ih | log a ih =>
    intro q h
    simp only [exactValue?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨x, hx, rfl, rfl⟩ := h
    simp [ih _ hx]
  | sqrt a ih =>
    intro q h
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hs0, rfl⟩ := ratSqrt?_spec h
    simp [ih _ hx, Real.sqrt_mul_self (Rat.cast_nonneg.mpr hs0)]

/-- The point `!₂[a]` as the function `fun _ ↦ a`. -/
theorem euclideanSingle_eq_const (a : ℝ) : (⇑(!₂[a] : EuclideanSpace ℝ (Fin 1))) = fun _ ↦ a := by
  funext i
  fin_cases i
  simp

/-- The `k`-th symbolic derivatives at `a` equal `k! cs_k` for `k ≤ n`. -/
def seriesCheck (expr : Verified.Expr (Fin 1)) (n : ℕ) (a : ℚ) (cs : List ℚ) : Bool :=
  (List.range (n + 1)).all fun k ↦
    exactValue? (fun _ ↦ a) (expr.iteratedDiff (0 : Fin 1) k) == some (cs.getD k 0 * k.factorial)

private theorem coefficient_of_seriesCheck {expr : Verified.Expr (Fin 1)} {n : ℕ} {a : ℚ}
    {cs : List ℚ} (h : seriesCheck expr n a cs = true) {k : ℕ} (hk : k ≤ n) :
    (expr.iteratedDiff (0 : Fin 1) k).eval (!₂[(a : ℝ)]) = (cs.getD k 0 : ℝ) * k.factorial := by
  have hk' := List.all_eq_true.mp h k (List.mem_range.mpr (Nat.lt_succ_of_le hk))
  rw [euclideanSingle_eq_const, exactValue?_sound _ _ _ (beq_iff_eq.mp hk')]
  push_cast
  ring

/-- The point `!₂[x]` depends continuously on `x`. -/
theorem continuous_euclideanSingle : Continuous fun x : ℝ ↦ (!₂[x] : ℝ^1) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ by fin_cases i; exact continuous_id)

/-- Validity of the first `n` derivatives at a point persists near it. -/
theorem eventually_validIterates {expr : Verified.Expr (Fin 1)} {n : ℕ} {a : ℝ}
    (h : expr.ValidIteratesOn n {a}) :
    ∀ᶠ x in 𝓝 a, ∀ k < n, (expr.iteratedDiff (0 : Fin 1) k).ValidAt !₂[x] :=
  (Filter.eventually_all_finite (Set.finite_Iio n)).2 fun k hk ↦
    (continuous_euclideanSingle.tendsto a).eventually (eventually_validAt _ _ (h k hk a rfl))

/-- Validity of the first `n` derivatives at a point holds on an open interval around it. -/
theorem exists_validIteratesOn_Ioo {expr : Verified.Expr (Fin 1)} {n : ℕ} {a : ℝ}
    (h : expr.ValidIteratesOn n {a}) :
    ∃ ε > 0, expr.ValidIteratesOn n (Ioo (a - ε) (a + ε)) := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_validIterates h)
  refine ⟨ε, hε, fun k hk x hx ↦ hball ?_ k hk⟩
  rwa [← Real.ball_eq_Ioo] at hx

/-- **Certified Taylor expansion.** -/
theorem series_of_check (expr : Verified.Expr (Fin 1)) (n : ℕ) (a : ℚ)
    (hvalid : expr.ValidIteratesOn (n + 1) {(a : ℝ)})
    (cs : List ℚ) (h : seriesCheck expr n a cs = true) :
    (fun x ↦ expr.univariateEval x -
        ∑ k ∈ Finset.range (n + 1), (cs.getD k 0 : ℝ) * (x - a) ^ k) =o[𝓝 (a : ℝ)]
      fun x ↦ (x - a) ^ n := by
  obtain ⟨ε, hε, hvalid'⟩ := exists_validIteratesOn_Ioo hvalid
  have has : (a : ℝ) ∈ Ioo ((a : ℝ) - ε) (a + ε) := ⟨by linarith, by linarith⟩
  have ho := taylor_isLittleO (convex_Ioo _ _) has
    (contDiffOn_univariateEval expr n isOpen_Ioo.uniqueDiffOn hvalid')
  rw [isOpen_Ioo.nhdsWithin_eq has] at ho
  refine ho.congr_left fun x ↦ ?_
  rw [taylor_within_apply]
  congr 1
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hkn : k ≤ n := Finset.mem_range_succ_iff.mp hk
  rw [iteratedDerivWithin_univariateEval_eq expr k isOpen_Ioo.uniqueDiffOn
    (hvalid'.mono (by omega)) has, coefficient_of_seriesCheck h hkn, smul_eq_mul]
  field_simp

/-- The derivatives at `a` of order below `m` vanish and the `m`-th is `m! c`. -/
def leadingCheck (expr : Verified.Expr (Fin 1)) (m : ℕ) (a c : ℚ) : Bool :=
  seriesCheck expr m a (List.replicate m 0 ++ [c])

/-- A single leading term: `expr (x) = c (x - a) ^ m + o ((x - a) ^ m)`. -/
theorem leading_of_check (expr : Verified.Expr (Fin 1)) (m : ℕ) (a : ℚ)
    (hvalid : expr.ValidIteratesOn (m + 1) {(a : ℝ)})
    (c : ℚ) (h : leadingCheck expr m a c = true) :
    (fun x ↦ expr.univariateEval x - (c : ℝ) * (x - a) ^ m) =o[𝓝 (a : ℝ)]
      fun x ↦ (x - a) ^ m := by
  refine (series_of_check expr m a hvalid _ h).congr_left fun x ↦ ?_
  rw [Finset.sum_range_succ, Finset.sum_eq_zero fun k hk ↦ ?_]
  · simp [List.getD_eq_getElem?_getD]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append, Finset.mem_range.mp hk]

/-- **Limits from leading terms.** If `g (x) = c (x - a) ^ m + o ((x - a) ^ m)` and
`h (x) = d (x - a) ^ m + o ((x - a) ^ m)` with `d ≠ 0`, then `g / h → c / d` as `x → a`,
`x ≠ a`. -/
theorem tendsto_div_of_isLittleO {g h : ℝ → ℝ} {a c d : ℝ} {m : ℕ}
    (hg : (fun x ↦ g x - c * (x - a) ^ m) =o[𝓝 a] fun x ↦ (x - a) ^ m)
    (hh : (fun x ↦ h x - d * (x - a) ^ m) =o[𝓝 a] fun x ↦ (x - a) ^ m) (hd : d ≠ 0) :
    Tendsto (fun x ↦ g x / h x) (𝓝[≠] a) (𝓝 (c / d)) := by
  have hne : ∀ᶠ x in 𝓝[≠] a, (x - a) ^ m ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact pow_ne_zero _ (sub_ne_zero.mpr hx)
  have key {f : ℝ → ℝ} {b : ℝ} (hf : (fun x ↦ f x - b * (x - a) ^ m) =o[𝓝 a] fun x ↦ (x - a) ^ m) :
      Tendsto (fun x ↦ f x / (x - a) ^ m) (𝓝[≠] a) (𝓝 b) := by
    have := (hf.mono (nhdsWithin_le_nhds (s := {a}ᶜ))).tendsto_div_nhds_zero.add_const b
    rw [zero_add] at this
    refine this.congr' ?_
    filter_upwards [hne] with x hx
    field_simp
    ring
  refine ((key hg).div (key hh) hd).congr' ?_
  filter_upwards [hne] with x hx
  exact div_div_div_cancel_right₀ hx _ _

/-- The limit `L = c / d` of a quotient of two expressions from their leading terms at `a`. -/
theorem tendsto_div_of_check (num den : Verified.Expr (Fin 1)) (m : ℕ) (a : ℚ)
    (hnum : num.ValidIteratesOn (m + 1) {(a : ℝ)}) (hden : den.ValidIteratesOn (m + 1) {(a : ℝ)})
    (c d L : ℚ)
    (h : (leadingCheck num m a c && leadingCheck den m a d && decide (d ≠ 0) &&
      decide (L = c / d)) = true) :
    Tendsto (fun x ↦ num.univariateEval x / den.univariateEval x) (𝓝[≠] (a : ℝ))
      (𝓝 (L : ℝ)) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hc, hd⟩, hd0⟩, rfl⟩ := h
  rw [Rat.cast_div]
  exact tendsto_div_of_isLittleO (leading_of_check num m a hnum c hc)
    (leading_of_check den m a hden d hd) (by exact_mod_cast hd0)

/-- An expression is continuous at every point where it is valid. -/
theorem tendsto_of_validIteratesOn (expr : Verified.Expr (Fin 1)) (a : ℚ)
    (hvalid : expr.ValidIteratesOn 1 {(a : ℝ)}) :
    Tendsto (fun x ↦ expr.univariateEval x) (𝓝 (a : ℝ)) (𝓝 (expr.univariateEval a)) :=
  (hasDerivAt_univariateEval expr a (hvalid 0 one_pos a rfl)).continuousAt.tendsto

end CAS.Verified.Expr
