/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Asymptotic comparison at infinity in the scale `xᵃ eᵇˣ (log x)ᵏ`

`scale a b k x = x ^ a e ^ (b x) (log x) ^ k`. Two scale functions compare lexicographically in
`(b, a, k)`: if the difference of the exponents is lexicographically negative (`NegTriple`), the
quotient tends to `0` (`tendsto_scale_zero`), from `xˢ e ^ (-b x) → 0` and `(log x)ʳ = o (xˢ)`;
the reverse gives `+∞` (`tendsto_scale_atTop`).

`Asym f c a b k` says `f ~ c · scale a b k` at `+∞`. The rules propagate it through products,
quotients and powers (exact on the exponents), sums (the dominant term wins, equal exponents add
their constants), `exp` of an affine function, `log` (`log f ~ a log x` or `~ b x`), square
roots, and `arctan` (`→ ± π / 2` when the argument tends to `± ∞`). The limit of `f` is then that
of `c · scale a b k`: `0`, `c`, `+∞` or `-∞` (`tendsto_of_asym_zero`, `tendsto_of_asym_const`,
`tendsto_of_asym_atTop`, `tendsto_of_asym_atBot`).

## Main definitions

* `scale`: the scale function `x ^ a e ^ (b x) (log x) ^ k`.
* `NegTriple`: lexicographic negativity of `(b, a, k)`.
* `Asym`: `f ~ c · scale a b k` at `+∞`, with Mathlib's `IsEquivalent`.

## Main results

* `tendsto_scale_zero`, `tendsto_scale_atTop`, `isLittleO_scale`: comparison in the scale.
* `asym_mul`, `asym_div`, `asym_pow`, `asym_add_left`, `asym_add_same`, `asym_exp_affine`,
  `asym_log_rpow`, `asym_sqrt`, `asym_arctan_atTop` and the other rules for `Asym`.
* `tendsto_of_asym_zero`, `tendsto_of_asym_const`, `tendsto_of_asym_atTop`,
  `tendsto_of_asym_atBot`: the limit from an equivalent.

## Implementation notes

`#cas [limit x → ∞]` (`CAS.Command.AsymptoticLimits`) computes, in untrusted meta code, an
equivalent `c xᵃ eᵇˣ (log x)ᵏ` of every subexpression and assembles a proof of `Asym` from the
rules, one rule for each node. The side conditions, `NegTriple` of the exponent differences and
the sign or nonvanishing of the constants, are proved by `norm_num`, `ring` and `positivity`,
and the kernel checks the whole term. At `-∞` we substitute `x ↦ -x` and conclude with
Mathlib's `Filter.tendsto_comp_neg_atTop_iff`.

The scale is fixed: every equivalent has this three-parameter form, so comparing two terms is
comparing two triples, and each rule is a short lemma about `IsEquivalent`. The price is that a
sum whose dominant terms cancel needs a rewriting first (`CAS.Calculus.AsymptoticExpansion`),
and that `exp` takes only affine arguments and arguments that tend to `0`, so `exp (x ^ 2)` and
`exp (exp x)` are out of reach. The growth facts are Mathlib's (`isLittleO_log_rpow_rpow_atTop`,
`tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`, `tendsto_rpow_neg_atTop`).
-/

@[expose] public section

namespace CAS.Asymptotic

open Real Filter Asymptotics Topology

/-- `x ^ a e ^ (b x) (log x) ^ k`. -/
noncomputable def scale (a b k x : ℝ) : ℝ := x ^ a * exp (b * x) * log x ^ k

/-- The triple `(b, a, k)` is lexicographically negative. -/
def NegTriple (a b k : ℝ) : Prop := b < 0 ∨ (b = 0 ∧ a < 0) ∨ (b = 0 ∧ a = 0 ∧ k < 0)

/-- For `1 < x`, `scale a b k x` is positive. -/
theorem scale_pos {a b k x : ℝ} (hx : 1 < x) : 0 < scale a b k x :=
  mul_pos (mul_pos (rpow_pos_of_pos (by linarith) _) (exp_pos _)) (rpow_pos_of_pos (log_pos hx) _)

/-- For `1 < x`, the product of two scale functions at `x` adds the exponents:
`scale a₁ b₁ k₁ x * scale a₂ b₂ k₂ x = scale (a₁ + a₂) (b₁ + b₂) (k₁ + k₂) x`. -/
theorem scale_mul {a₁ b₁ k₁ a₂ b₂ k₂ x : ℝ} (hx : 1 < x) :
    scale a₁ b₁ k₁ x * scale a₂ b₂ k₂ x = scale (a₁ + a₂) (b₁ + b₂) (k₁ + k₂) x := by
  unfold scale
  rw [rpow_add (by linarith), rpow_add (log_pos hx), add_mul, exp_add]
  ring

/-- For `1 < x`, the inverse negates the exponents: `(scale a b k x)⁻¹ = scale (-a) (-b) (-k) x`. -/
theorem scale_inv {a b k x : ℝ} (hx : 1 < x) : (scale a b k x)⁻¹ = scale (-a) (-b) (-k) x := by
  unfold scale
  rw [rpow_neg (by linarith), rpow_neg (log_pos hx).le, neg_mul, exp_neg]
  field_simp

/-- For `1 < x`, the quotient of two scale functions at `x` subtracts the exponents:
`scale a₁ b₁ k₁ x / scale a₂ b₂ k₂ x = scale (a₁ - a₂) (b₁ - b₂) (k₁ - k₂) x`. -/
theorem scale_div {a₁ b₁ k₁ a₂ b₂ k₂ x : ℝ} (hx : 1 < x) :
    scale a₁ b₁ k₁ x / scale a₂ b₂ k₂ x = scale (a₁ - a₂) (b₁ - b₂) (k₁ - k₂) x := by
  rw [div_eq_mul_inv, scale_inv hx, scale_mul hx]
  ring_nf

/-- For `1 < x` and a natural `n`, `scale a b k x ^ n = scale (n * a) (n * b) (n * k) x`. -/
theorem scale_pow {a b k x : ℝ} (hx : 1 < x) (n : ℕ) :
    scale a b k x ^ n = scale (n * a) (n * b) (n * k) x := by
  induction n with
  | zero =>
      simp [scale]
  | succ n ih =>
      rw [pow_succ, ih, scale_mul hx]
      congr 1 <;> push_cast <;> ring

/-- `scale 0 0 0 x = 1` for every real `x`. -/
theorem scale_zero (x : ℝ) : scale 0 0 0 x = 1 := by simp [scale]

/-- `scale 1 0 0 x = x` for every real `x`. -/
theorem scale_one_zero_zero (x : ℝ) : scale 1 0 0 x = x := by simp [scale]

/-- `scale 0 0 1 x = log x` for every real `x`. -/
theorem scale_zero_zero_one (x : ℝ) : scale 0 0 1 x = log x := by simp [scale]

/-- `scale 0 b 0 x = exp (b * x)` for every real `x`. -/
theorem scale_zero_b_zero (b x : ℝ) : scale 0 b 0 x = exp (b * x) := by simp [scale]

/-! ## Comparison of scale functions -/

/-- **A negative triple tends to zero.** -/
theorem tendsto_scale_zero {a b k : ℝ} (h : NegTriple a b k) :
    Tendsto (scale a b k) atTop (𝓝 0) := by
  rcases h with hb | ⟨hb, ha⟩ | ⟨hb, ha, hk⟩
  · -- `(log x) ^ k = o (x)`, and `x ^ (a + 1) e ^ (b x) → 0`.
    have hlog := isLittleO_log_rpow_rpow_atTop k (zero_lt_one : (0 : ℝ) < 1)
    have hprod := (isBigO_refl (fun x : ℝ ↦ x ^ a * exp (b * x)) atTop).mul_isLittleO hlog
    have hlim := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a + 1) (-b) (by linarith)
    refine (hprod.trans_tendsto (hlim.congr' ?_))
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [rpow_add hx, rpow_one, neg_neg]
    ring
  · have hs : 0 < -a / 2 := by linarith
    have hlog := isLittleO_log_rpow_rpow_atTop k hs
    have hprod := (isBigO_refl (fun x : ℝ ↦ x ^ a) atTop).mul_isLittleO hlog
    have hlim := tendsto_rpow_neg_atTop (show 0 < -a / 2 by linarith)
    refine ((hprod.trans_tendsto (hlim.congr' ?_)).congr' ?_)
    · filter_upwards [eventually_gt_atTop 0] with x hx
      rw [← rpow_add hx]
      ring_nf
    · filter_upwards with x
      simp [scale, hb]
  · have hlim := (tendsto_rpow_neg_atTop (show 0 < -k by linarith)).comp tendsto_log_atTop
    refine hlim.congr' ?_
    filter_upwards with x
    simp [scale, hb, ha]

/-- **A positive triple tends to infinity.** -/
theorem tendsto_scale_atTop {a b k : ℝ} (h : NegTriple (-a) (-b) (-k)) :
    Tendsto (scale a b k) atTop atTop := by
  have hpos : Tendsto (scale (-a) (-b) (-k)) atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_scale_zero h, (eventually_gt_atTop 1).mono fun x hx ↦ scale_pos hx⟩
  refine hpos.inv_tendsto_nhdsGT_zero.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  simp [scale_inv hx]

/-- The smaller of two scale functions is negligible. -/
theorem isLittleO_scale {a₁ b₁ k₁ a₂ b₂ k₂ : ℝ}
    (h : NegTriple (a₂ - a₁) (b₂ - b₁) (k₂ - k₁)) :
    scale a₂ b₂ k₂ =o[atTop] scale a₁ b₁ k₁ := by
  have hD := (isLittleO_one_iff ℝ).mpr (tendsto_scale_zero h)
  have hprod := (isBigO_refl (scale a₁ b₁ k₁) atTop).mul_isLittleO hD
  refine hprod.congr' ?_ (.of_forall fun x ↦ mul_one _)
  filter_upwards [eventually_gt_atTop 1] with x hx
  rw [scale_mul hx]
  congr 1 <;> ring

/-! ## Asymptotic equivalents -/

/-- `f ~ c · scale a b k` at `+∞`. -/
def Asym (f : ℝ → ℝ) (c a b k : ℝ) : Prop := f ~[atTop] fun x ↦ c * scale a b k x

/-- `x ~ 1 · scale 1 0 0` at `+∞`: `Asym (fun x ↦ x) 1 1 0 0`. -/
theorem asym_id : Asym (fun x ↦ x) 1 1 0 0 := by
  unfold Asym
  simp only [one_mul, scale_one_zero_zero]
  exact IsEquivalent.refl

/-- A constant is its own equivalent: `Asym (fun _ ↦ c) c 0 0 0` for every real `c`. -/
theorem asym_const (c : ℝ) : Asym (fun _ ↦ c) c 0 0 0 := by
  unfold Asym
  simp only [scale_zero, mul_one]
  exact IsEquivalent.refl

/-- A function with `f x = c` at every `x` satisfies `Asym f c 0 0 0`. -/
theorem asym_of_eq_const {f : ℝ → ℝ} {c : ℝ} (h : ∀ x, f x = c) : Asym f c 0 0 0 :=
  (funext h : f = fun _ ↦ c) ▸ asym_const c

/-- Products: if `f ~ c₁ · scale a₁ b₁ k₁` and `g ~ c₂ · scale a₂ b₂ k₂` at `+∞`, then
`f g ~ c₁ c₂ · scale (a₁ + a₂) (b₁ + b₂) (k₁ + k₂)`. -/
theorem asym_mul {f g : ℝ → ℝ} {c₁ a₁ b₁ k₁ c₂ a₂ b₂ k₂ : ℝ} (hf : Asym f c₁ a₁ b₁ k₁)
    (hg : Asym g c₂ a₂ b₂ k₂) :
    Asym (fun x ↦ f x * g x) (c₁ * c₂) (a₁ + a₂) (b₁ + b₂) (k₁ + k₂) := by
  refine (hf.mul hg).trans_eventuallyEq ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  simp only [Pi.mul_apply, ← scale_mul hx]
  ring

/-- Quotients: if `f ~ c₁ · scale a₁ b₁ k₁` and `g ~ c₂ · scale a₂ b₂ k₂` at `+∞`, then
`f / g ~ (c₁ / c₂) · scale (a₁ - a₂) (b₁ - b₂) (k₁ - k₂)`. -/
theorem asym_div {f g : ℝ → ℝ} {c₁ a₁ b₁ k₁ c₂ a₂ b₂ k₂ : ℝ} (hf : Asym f c₁ a₁ b₁ k₁)
    (hg : Asym g c₂ a₂ b₂ k₂) :
    Asym (fun x ↦ f x / g x) (c₁ / c₂) (a₁ - a₂) (b₁ - b₂) (k₁ - k₂) := by
  refine (hf.div hg).trans_eventuallyEq ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  simp only [Pi.div_apply, ← scale_div hx]
  ring

/-- Natural powers: if `f ~ c · scale a b k` at `+∞`, then
`f ^ n ~ c ^ n · scale (n a) (n b) (n k)`. -/
theorem asym_pow {f : ℝ → ℝ} {c a b k : ℝ} (hf : Asym f c a b k) (n : ℕ) :
    Asym (fun x ↦ f x ^ n) (c ^ n) (n * a) (n * b) (n * k) := by
  refine (hf.pow n).trans_eventuallyEq ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  simp only [Pi.pow_apply, ← scale_pow hx]
  ring

/-- Negation: if `f ~ c · scale a b k` at `+∞`, then `-f ~ -c · scale a b k`. -/
theorem asym_neg {f : ℝ → ℝ} {c a b k : ℝ} (hf : Asym f c a b k) :
    Asym (fun x ↦ -f x) (-c) a b k := by
  refine hf.neg.trans_eventuallyEq ?_
  filter_upwards with x
  ring

private theorem isLittleO_of_asym {f : ℝ → ℝ} {c₁ a₁ b₁ k₁ c₂ a₂ b₂ k₂ : ℝ}
    (hf : Asym f c₂ a₂ b₂ k₂) (hc₁ : c₁ ≠ 0) (h : NegTriple (a₂ - a₁) (b₂ - b₁) (k₂ - k₁)) :
    f =o[atTop] fun x ↦ c₁ * scale a₁ b₁ k₁ x := by
  have h₁ : f =O[atTop] fun x ↦ c₂ * scale a₂ b₂ k₂ x := hf.isBigO
  have h₂ : (fun x ↦ c₂ * scale a₂ b₂ k₂ x) =O[atTop] scale a₂ b₂ k₂ :=
    (isBigO_refl (scale a₂ b₂ k₂) atTop).const_mul_left c₂
  refine (h₁.trans h₂).trans_isLittleO ?_
  exact (isLittleO_scale h).trans_isBigO (isBigO_self_const_mul hc₁ _ _)

/-- **The dominant term of a sum.** -/
theorem asym_add_left {f g : ℝ → ℝ} {c₁ a₁ b₁ k₁ c₂ a₂ b₂ k₂ : ℝ} (hf : Asym f c₁ a₁ b₁ k₁)
    (hg : Asym g c₂ a₂ b₂ k₂) (hc₁ : c₁ ≠ 0) (h : NegTriple (a₂ - a₁) (b₂ - b₁) (k₂ - k₁)) :
    Asym (fun x ↦ f x + g x) c₁ a₁ b₁ k₁ :=
  hf.add_isLittleO (isLittleO_of_asym hg hc₁ h)

/-- The dominant term of a sum, on the right: if `f ~ c₁ · scale a₁ b₁ k₁`,
`g ~ c₂ · scale a₂ b₂ k₂`, `c₂ ≠ 0` and `NegTriple (a₁ - a₂) (b₁ - b₂) (k₁ - k₂)`, then
`f + g ~ c₂ · scale a₂ b₂ k₂` at `+∞`. -/
theorem asym_add_right {f g : ℝ → ℝ} {c₁ a₁ b₁ k₁ c₂ a₂ b₂ k₂ : ℝ} (hf : Asym f c₁ a₁ b₁ k₁)
    (hg : Asym g c₂ a₂ b₂ k₂) (hc₂ : c₂ ≠ 0) (h : NegTriple (a₁ - a₂) (b₁ - b₂) (k₁ - k₂)) :
    Asym (fun x ↦ f x + g x) c₂ a₂ b₂ k₂ :=
  (hg.add_isLittleO (isLittleO_of_asym hf hc₂ h)).congr_left (.of_forall fun _ ↦ add_comm _ _)

/-- **Equal exponents add their constants.** -/
theorem asym_add_same {f g : ℝ → ℝ} {c₁ c₂ a b k : ℝ} (hf : Asym f c₁ a b k)
    (hg : Asym g c₂ a b k) (hc : c₁ + c₂ ≠ 0) :
    Asym (fun x ↦ f x + g x) (c₁ + c₂) a b k := by
  unfold Asym at *
  have hS : scale a b k =O[atTop] fun x ↦ (c₁ + c₂) * scale a b k x :=
    isBigO_self_const_mul hc _ _
  have hf' : (fun x ↦ f x - c₁ * scale a b k x) =o[atTop] scale a b k :=
    hf.isLittleO.trans_isBigO ((isBigO_refl _ _).const_mul_left c₁)
  have hg' : (fun x ↦ g x - c₂ * scale a b k x) =o[atTop] scale a b k :=
    hg.isLittleO.trans_isBigO ((isBigO_refl _ _).const_mul_left c₂)
  refine ((hf'.add hg').trans_isBigO hS).congr_left ?_
  intro x
  simp only [Pi.sub_apply]
  ring

/-- The dominant term of a difference, on the left: if `f ~ c₁ · scale a₁ b₁ k₁`,
`g ~ c₂ · scale a₂ b₂ k₂`, `c₁ ≠ 0` and `NegTriple (a₂ - a₁) (b₂ - b₁) (k₂ - k₁)`, then
`f - g ~ c₁ · scale a₁ b₁ k₁` at `+∞`. -/
theorem asym_sub_left {f g : ℝ → ℝ} {c₁ a₁ b₁ k₁ c₂ a₂ b₂ k₂ : ℝ} (hf : Asym f c₁ a₁ b₁ k₁)
    (hg : Asym g c₂ a₂ b₂ k₂) (hc₁ : c₁ ≠ 0) (h : NegTriple (a₂ - a₁) (b₂ - b₁) (k₂ - k₁)) :
    Asym (fun x ↦ f x - g x) c₁ a₁ b₁ k₁ :=
  (asym_add_left hf (asym_neg hg) hc₁ h).congr_left (.of_forall fun _ ↦ (sub_eq_add_neg _ _).symm)

/-- The dominant term of a difference, on the right: if `f ~ c₁ · scale a₁ b₁ k₁`,
`g ~ c₂ · scale a₂ b₂ k₂`, `c₂ ≠ 0` and `NegTriple (a₁ - a₂) (b₁ - b₂) (k₁ - k₂)`, then
`f - g ~ -c₂ · scale a₂ b₂ k₂` at `+∞`. -/
theorem asym_sub_right {f g : ℝ → ℝ} {c₁ a₁ b₁ k₁ c₂ a₂ b₂ k₂ : ℝ} (hf : Asym f c₁ a₁ b₁ k₁)
    (hg : Asym g c₂ a₂ b₂ k₂) (hc₂ : c₂ ≠ 0) (h : NegTriple (a₁ - a₂) (b₁ - b₂) (k₁ - k₂)) :
    Asym (fun x ↦ f x - g x) (-c₂) a₂ b₂ k₂ :=
  (asym_add_right hf (asym_neg hg) (neg_ne_zero.mpr hc₂) h).congr_left
    (.of_forall fun _ ↦ (sub_eq_add_neg _ _).symm)

/-- Equal exponents subtract their constants: if `f ~ c₁ · scale a b k`, `g ~ c₂ · scale a b k` and
`c₁ - c₂ ≠ 0`, then `f - g ~ (c₁ - c₂) · scale a b k` at `+∞`. -/
theorem asym_sub_same {f g : ℝ → ℝ} {c₁ c₂ a b k : ℝ} (hf : Asym f c₁ a b k)
    (hg : Asym g c₂ a b k) (hc : c₁ - c₂ ≠ 0) :
    Asym (fun x ↦ f x - g x) (c₁ - c₂) a b k := by
  simpa only [← sub_eq_add_neg] using asym_add_same hf (asym_neg hg) (by rwa [← sub_eq_add_neg])

/-- `exp (b x + d) = e ^ d e ^ (b x)`. -/
theorem asym_exp_affine {g : ℝ → ℝ} {b d : ℝ} (hg : ∀ x, g x = b * x + d) :
    Asym (fun x ↦ exp (g x)) (exp d) 0 b 0 := by
  unfold Asym
  simp only [scale_zero_b_zero]
  refine IsEquivalent.refl.congr_left ?_
  filter_upwards with x
  rw [hg, exp_add]
  ring

/-- `log f ~ a log x` when `f ~ c xᵃ`, `c > 0`, `a ≠ 0`. -/
theorem asym_log_rpow {f : ℝ → ℝ} {c a : ℝ} (hf : Asym f c a 0 0) (hc : 0 < c) (ha : a ≠ 0) :
    Asym (fun x ↦ log (f x)) a 0 0 1 := by
  unfold Asym at *
  simp only [scale_zero_zero_one]
  have hv : ∀ᶠ x in atTop, c * scale a 0 0 x ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact (mul_pos hc (scale_pos hx)).ne'
  have hratio := (isEquivalent_iff_tendsto_one hv).mp hf
  have hlog : Tendsto (fun x ↦ log (f x / (c * scale a 0 0 x))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (continuousAt_log one_ne_zero).tendsto.comp hratio
  have hfpos : ∀ᶠ x in atTop, 0 < f x / (c * scale a 0 0 x) :=
    hratio.eventually (lt_mem_nhds one_pos)
  -- `log f - a log x = log (f / (c xᵃ)) + log c → log c`.
  have hrest : (fun x ↦ log (f x) - a * log x) =o[atTop] fun x ↦ a * log x := by
    have hbig := (hlog.add_const (log c)).isBigO_one ℝ
    have hone : (fun _ ↦ (1 : ℝ)) =o[atTop] fun x ↦ a * log x := by
      refine (isLittleO_one_left_iff ℝ).mpr ?_
      have := tendsto_log_atTop.const_mul_atTop (abs_pos.mpr ha)
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 1] with x hx
      simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (log_pos hx)]
    refine (hbig.trans_isLittleO hone).congr' ?_ .rfl
    filter_upwards [hfpos, eventually_gt_atTop 1] with x hx hx1
    have hS : 0 < scale a 0 0 x := scale_pos hx1
    have hfx : 0 < f x := (div_pos_iff_of_pos_right (mul_pos hc hS)).mp hx
    rw [log_div hfx.ne' (mul_pos hc hS).ne', log_mul hc.ne' hS.ne']
    simp only [scale, zero_mul, exp_zero, mul_one, rpow_zero]
    rw [log_rpow (by linarith)]
    ring
  exact (IsEquivalent.refl.add_isLittleO hrest).congr_left (.of_forall fun _ ↦ add_sub_cancel _ _)

/-- `√f ~ √c · scale (a / 2) (b / 2) (k / 2)`. For `c ≤ 0` both sides are eventually `0`. -/
theorem asym_sqrt {f : ℝ → ℝ} {c a b k : ℝ} (hf : Asym f c a b k) :
    Asym (fun x ↦ √(f x)) (√c) (a / 2) (b / 2) (k / 2) := by
  unfold Asym at *
  rcases lt_or_ge 0 c with hc | hc
  swap
  · -- `f` is eventually nonpositive, so `√f` is eventually `0`, and so is `√c = 0`.
    have hle : ∀ᶠ x in atTop, f x ≤ 0 := by
      rcases hc.lt_or_eq with hc | rfl
      · have hv : ∀ᶠ x in atTop, c * scale a b k x ≠ 0 := by
          filter_upwards [eventually_gt_atTop 1] with x hx
          exact (mul_neg_of_neg_of_pos hc (scale_pos hx)).ne
        have hratio := (isEquivalent_iff_tendsto_one hv).mp hf
        filter_upwards [hratio.eventually (lt_mem_nhds one_pos), eventually_gt_atTop 1]
          with x hx hx1
        have hneg : c * scale a b k x < 0 := mul_neg_of_neg_of_pos hc (scale_pos hx1)
        rcases div_pos_iff.mp hx with ⟨_, h⟩ | ⟨h, _⟩
        · exact absurd h (not_lt.mpr hneg.le)
        · exact h.le
      · have hf0 : f ~[atTop] (0 : ℝ → ℝ) := by
          convert hf using 1
          funext x
          simp
        filter_upwards [isEquivalent_zero_iff_eventually_zero.mp hf0] with x hx
        simp [hx]
    have h0 : (fun x ↦ √c * scale (a / 2) (b / 2) (k / 2) x) = (0 : ℝ → ℝ) := by
      funext x
      simp [sqrt_eq_zero'.mpr hc]
    rw [h0]
    exact isEquivalent_zero_iff_eventually_zero.mpr
      (by filter_upwards [hle] with x hx; simp [sqrt_eq_zero'.mpr hx])
  have hv : ∀ᶠ x in atTop, c * scale a b k x ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact (mul_pos hc (scale_pos hx)).ne'
  have hratio := (isEquivalent_iff_tendsto_one hv).mp hf
  have hsqrt : Tendsto (fun x ↦ √(f x / (c * scale a b k x))) atTop (𝓝 1) := by
    simpa [Function.comp_def] using (continuous_sqrt.tendsto 1).comp hratio
  have hv' : ∀ᶠ x in atTop, √c * scale (a / 2) (b / 2) (k / 2) x ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact (mul_pos (sqrt_pos.mpr hc) (scale_pos hx)).ne'
  refine (isEquivalent_iff_tendsto_one hv').mpr (hsqrt.congr' ?_)
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hS : 0 < scale a b k x := scale_pos hx
  have hhalf : √(scale a b k x) = scale (a / 2) (b / 2) (k / 2) x := by
    have h0 : 0 < x := by linarith
    have hl : 0 < log x := log_pos hx
    unfold scale
    rw [sqrt_eq_rpow, mul_rpow (by positivity) (by positivity),
      mul_rpow (by positivity) (by positivity), ← rpow_mul h0.le, ← rpow_mul hl.le,
      ← exp_one_rpow, ← rpow_mul (exp_pos 1).le, exp_one_rpow]
    ring_nf
  simp only [Pi.div_apply]
  rw [sqrt_div' _ (mul_pos hc hS).le, sqrt_mul hc.le, hhalf]

/-- `arctan f → π / 2` when `f → +∞`. -/
theorem asym_arctan_atTop {f : ℝ → ℝ} {c a b k : ℝ} (hf : Asym f c a b k) (hc : 0 < c)
    (h : NegTriple (-a) (-b) (-k)) : Asym (fun x ↦ arctan (f x)) (π / 2) 0 0 0 := by
  unfold Asym at *
  simp only [scale_zero, mul_one]
  have hto : Tendsto f atTop atTop :=
    hf.symm.tendsto_atTop ((tendsto_scale_atTop h).const_mul_atTop hc)
  have := (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hto
  exact (isEquivalent_const_iff_tendsto (by positivity)).mpr this

/-- `arctan f → -π / 2` when `f → -∞`. -/
theorem asym_arctan_atBot {f : ℝ → ℝ} {c a b k : ℝ} (hf : Asym f c a b k) (hc : c < 0)
    (h : NegTriple (-a) (-b) (-k)) : Asym (fun x ↦ arctan (f x)) (-(π / 2)) 0 0 0 := by
  unfold Asym at *
  simp only [scale_zero, mul_one]
  have hto : Tendsto f atTop atBot :=
    hf.symm.tendsto_atBot ((tendsto_scale_atTop h).const_mul_atTop_of_neg hc)
  have := (tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp hto
  exact (isEquivalent_const_iff_tendsto (by have := pi_pos; linarith)).mpr this

/-! ## Limits -/

/-- If `f ~ c · scale a b k` at `+∞` and `NegTriple a b k`, then `f → 0` at `+∞`, for every `c`. -/
theorem tendsto_of_asym_zero {f : ℝ → ℝ} {c a b k : ℝ} (hf : Asym f c a b k)
    (h : NegTriple a b k) : Tendsto f atTop (𝓝 0) := by
  exact hf.symm.tendsto_nhds (by simpa using (tendsto_scale_zero h).const_mul c)

/-- If `Asym f c 0 0 0`, that is `f ~ c` at `+∞`, then `f → c` at `+∞`. -/
theorem tendsto_of_asym_const {f : ℝ → ℝ} {c : ℝ} (hf : Asym f c 0 0 0) :
    Tendsto f atTop (𝓝 c) := by
  unfold Asym at hf
  simp only [scale_zero, mul_one] at hf
  exact hf.symm.tendsto_nhds tendsto_const_nhds

/-- If `f ~ c · scale a b k` at `+∞` with `0 < c` and `NegTriple (-a) (-b) (-k)`, then `f → +∞` at
`+∞`. -/
theorem tendsto_of_asym_atTop {f : ℝ → ℝ} {c a b k : ℝ} (hf : Asym f c a b k) (hc : 0 < c)
    (h : NegTriple (-a) (-b) (-k)) : Tendsto f atTop atTop :=
  hf.symm.tendsto_atTop ((tendsto_scale_atTop h).const_mul_atTop hc)

/-- If `f ~ c · scale a b k` at `+∞` with `c < 0` and `NegTriple (-a) (-b) (-k)`, then `f → -∞` at
`+∞`. -/
theorem tendsto_of_asym_atBot {f : ℝ → ℝ} {c a b k : ℝ} (hf : Asym f c a b k) (hc : c < 0)
    (h : NegTriple (-a) (-b) (-k)) : Tendsto f atTop atBot :=
  hf.symm.tendsto_atBot ((tendsto_scale_atTop h).const_mul_atTop_of_neg hc)

end CAS.Asymptotic
