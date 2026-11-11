/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.AsymptoticScale

/-!
# Second terms at infinity

The rules of `CAS.Calculus.AsymptoticScale` keep the dominant term of a sum; when the dominant
terms cancel, `#cas [limit x → ∞]` (`CAS.Command.AsymptoticLimits`) takes the equivalent from the
next term. Three ways to reach it:

* the conjugate, `√p - q = (p - q ^ 2) / (√p + q)` when `p ≥ 0` and `q > 0`
  (`sqrt_sub_eq`, `sub_sqrt_eq`, `sqrt_sub_sqrt_eq`, and `sqrt_add_eq`, `add_sqrt_eq` for
  `q < 0`), so that the cancellation moves into the polynomial `p - q ^ 2`, where it is exact;
* the first-order expansions `e ^ u - 1 ~ u` and `log P ~ P - 1` for `u → 0` and `P → 1`
  (`asym_exp_sub_one`, `asym_log_of_sub_one`), from the derivatives of `exp` at `0` and of
  `log` at `1`, next to `e ^ u ~ 1` for `u → 0` (`asym_exp_of_tendsto_zero`);
* eventual equality (`asym_congr`) and eventual positivity of a function with a positive
  equivalent (`asym_eventually_pos`), which justify the rewriting.
-/

@[expose] public section

namespace CAS.Asymptotic

open Filter Asymptotics Topology Real

/-- If `f = g` eventually at `+∞` and `g ~ c · scale a b k`, then `f ~ c · scale a b k`. This is
`IsEquivalent.congr_left` for `Asym`; `#cas [limit x → ∞]` builds it by name with `mkAppM`. -/
theorem asym_congr {f g : ℝ → ℝ} {c a b k : ℝ} (h : ∀ᶠ x in atTop, f x = g x)
    (hg : Asym g c a b k) : Asym f c a b k :=
  IsEquivalent.congr_left hg (h.mono fun _ hx ↦ hx.symm)

/-- A function with a positive equivalent is eventually positive. -/
theorem asym_eventually_pos {f : ℝ → ℝ} {c a b k : ℝ} (hf : Asym f c a b k) (hc : 0 < c) :
    ∀ᶠ x in atTop, 0 < f x := by
  filter_upwards [hf.isLittleO.def (by norm_num : (0 : ℝ) < 1 / 2), eventually_gt_atTop 1]
    with x hx h1
  have hs : 0 < c * scale a b k x := mul_pos hc (scale_pos h1)
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_pos hs] at hx
  linarith [neg_abs_le (f x - c * scale a b k x)]

/-- `√(q · 1) = r · 1` for `q = r ^ 2`, `r ≥ 0`: the root of a rational square stays rational. -/
theorem sqrt_mul_one_eq {q r : ℝ} (hr : 0 ≤ r) (h : q = r ^ 2) : √(q * 1) = r * 1 := by
  rw [mul_one, mul_one, h, Real.sqrt_sq hr]

/-! ## Conjugates -/

/-- For `0 ≤ p` and `0 < q`, `√p - q = (p - q ^ 2) / (√p + q)`. It is kept for `#cas [limit x → ∞]`,
which closes its eventual rewriting goals with `exact sqrt_sub_eq hp.le hq`; Mathlib has no
conjugate lemma of this form. -/
theorem sqrt_sub_eq {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    √p - q = (p - q ^ 2) / (√p + q) := by
  rw [eq_div_iff (by positivity)]
  linear_combination Real.sq_sqrt hp

/-- For `0 ≤ p` and `0 < q`, `q - √p = (q ^ 2 - p) / (q + √p)`. It is kept for `#cas [limit x → ∞]`,
which closes its eventual rewriting goals with `exact sub_sqrt_eq hp.le hq`; Mathlib has no
conjugate lemma of this form. -/
theorem sub_sqrt_eq {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    q - √p = (q ^ 2 - p) / (q + √p) := by
  rw [eq_div_iff (by positivity)]
  linear_combination -Real.sq_sqrt hp

/-- For `0 ≤ p` and `0 < q`, `√p - √q = (p - q) / (√p + √q)`. It is kept for `#cas [limit x → ∞]`,
which closes its eventual rewriting goals with `exact sqrt_sub_sqrt_eq hp.le hq`; Mathlib has no
conjugate lemma of this form. -/
theorem sqrt_sub_sqrt_eq {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    √p - √q = (p - q) / (√p + √q) := by
  rw [eq_div_iff (by positivity)]
  linear_combination Real.sq_sqrt hp - Real.sq_sqrt hq.le

/-- For `0 ≤ p` and `q < 0`, `√p + q = (p - q ^ 2) / (√p - q)`. It is kept for `#cas [limit x → ∞]`,
which closes its eventual rewriting goals with `exact sqrt_add_eq hp.le hq`; Mathlib has no
conjugate lemma of this form. -/
theorem sqrt_add_eq {p q : ℝ} (hp : 0 ≤ p) (hq : q < 0) :
    √p + q = (p - q ^ 2) / (√p - q) := by
  rw [eq_div_iff (sub_pos.2 (hq.trans_le (Real.sqrt_nonneg p))).ne']
  linear_combination Real.sq_sqrt hp

/-- For `0 ≤ p` and `q < 0`, `q + √p = (p - q ^ 2) / (√p - q)`, the commuted form of `sqrt_add_eq`.
It is kept for `#cas [limit x → ∞]`, which closes the goal for a sum written `q + √p` with
`exact add_sqrt_eq hp.le hq`; Mathlib has no conjugate lemma of this form. -/
theorem add_sqrt_eq {p q : ℝ} (hp : 0 ≤ p) (hq : q < 0) :
    q + √p = (p - q ^ 2) / (√p - q) :=
  (add_comm q √p).trans (sqrt_add_eq hp hq)

/-! ## First-order expansions at `0` and `1` -/

/-- If `u x → 0` as `x → +∞`, then `e ^ (u x) - 1` is asymptotically equivalent to `u x` at `+∞`. -/
theorem isEquivalent_exp_sub_one {u : ℝ → ℝ} (hu : Tendsto u atTop (𝓝 0)) :
    (fun x ↦ exp (u x) - 1) ~[atTop] u := by
  have h : (fun h : ℝ ↦ exp h - 1 - h) =o[𝓝 0] fun h ↦ h := by
    simpa using (Real.hasDerivAt_exp 0).hasFDerivAt.isLittleO
  exact h.comp_tendsto hu

/-- If `u ~ c · scale a b k` at `+∞` with `(b, a, k)` lexicographically negative (so `u → 0`), then
`e ^ u - 1 ~ c · scale a b k`. -/
theorem asym_exp_sub_one {u : ℝ → ℝ} {c a b k : ℝ} (hu : Asym u c a b k) (h : NegTriple a b k) :
    Asym (fun x ↦ exp (u x) - 1) c a b k :=
  (isEquivalent_exp_sub_one (tendsto_of_asym_zero hu h)).trans hu

/-- If `P x - 1 → 0` as `x → +∞`, then `log (P x)` is asymptotically equivalent to `P x - 1` at
`+∞`. -/
theorem isEquivalent_log_of_sub_one {P : ℝ → ℝ} (hP : Tendsto (fun x ↦ P x - 1) atTop (𝓝 0)) :
    (fun x ↦ log (P x)) ~[atTop] fun x ↦ P x - 1 := by
  have h : (fun y : ℝ ↦ log y - (y - 1)) =o[𝓝 1] fun y ↦ y - 1 := by
    simpa using (Real.hasDerivAt_log one_ne_zero).hasFDerivAt.isLittleO
  have hP1 : Tendsto P atTop (𝓝 1) := by simpa using hP.add_const 1
  exact h.comp_tendsto hP1

/-- If `P - 1 ~ c · scale a b k` at `+∞` with `(b, a, k)` lexicographically negative (so `P → 1`),
then `log P ~ c · scale a b k`. -/
theorem asym_log_of_sub_one {P : ℝ → ℝ} {c a b k : ℝ} (hP : Asym (fun x ↦ P x - 1) c a b k)
    (h : NegTriple a b k) : Asym (fun x ↦ log (P x)) c a b k :=
  (isEquivalent_log_of_sub_one (tendsto_of_asym_zero hP h)).trans hP

/-- A function tending to `0` makes `e ^ u` equivalent to `1`. -/
theorem asym_exp_of_tendsto_zero {u : ℝ → ℝ} (hu : Tendsto u atTop (𝓝 0)) :
    Asym (fun x ↦ exp (u x)) 1 0 0 0 := by
  have h1 : (fun x : ℝ ↦ (1 : ℝ) * scale 0 0 0 x) = fun _ ↦ 1 := funext fun x ↦ by simp [scale]
  unfold Asym
  rw [h1]
  refine (isEquivalent_const_iff_tendsto one_ne_zero).mpr ?_
  simpa [Function.comp_def] using (Real.continuous_exp.tendsto 0).comp hu

end CAS.Asymptotic
