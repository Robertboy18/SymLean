/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.LinearODEComplex
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.Algebra.Polynomial
public import CAS.Polynomial.OfCoeffList

/-!
# Roots of rational polynomials with certified enclosures

A polynomial `∑ aₖ Xᵏ` is given by its list of rational coefficients, lowest degree first
(`polyC`, Mathlib's `Polynomial.ofCoeffList` mapped to `ℂ`); the list arithmetic is that of
`CAS.Polynomial.CoefficientList`, which `CAS.Polynomial.OfCoeffList` connects to polynomials. We
name each root by an enclosure, where Mathematica's `Root[f, k]` uses the index `k` of the root:

* `AlgRoot.real a lo hi`, a real root in `(lo, hi)`, which exists when `a` changes sign between
  the rational endpoints (`real_spec`, the intermediate value theorem, in
  `CAS.Polynomial.CoefficientEval`);
* `AlgRoot.complex a u v ρ`, a complex root at distance at most `ρ` from `u + v i`, which exists
  when `cCheck` accepts rational bounds for the Newton map `z ↦ z - p (z) / p' (u + v i)`
  (`complex_spec`).

When a list of distinct roots has as many elements as the degree of a monic polynomial, the
polynomial is the product of the factors `X - μ` (`prod_eq_polyC`), and `charC_eq_coeff` gives
its coefficients in the form `CAS.LinearODE.charC` uses.

## Main definitions

* `polyC`: the complex polynomial of a list of rational coefficients.
* `gEval`, `absH`, `deltaH`: the value at `u + v i` in rational arithmetic, and bounds for
  `|p (z)|` and `|p (z) - p (z₀)|` on discs.
* `cCheck`: the disc test for a complex root.
* `complex`: a root in an accepted disc, chosen with `Classical.epsilon`.

## Main results

* `eval_eq_zero_iff_of_radical`: `p` and `s` have the same roots when `s g = p` and `p h = sᵐ`.
* `prod_eq_polyC`: a monic polynomial with as many distinct roots as its degree is the product of
  its linear factors.
* `exists_complex_root`, `complex_spec`: a disc accepted by `cCheck` contains a root.

## Implementation notes

With `z₀ = u + v i`, `cCheck a u v ρ κ R L` asks in rational arithmetic for `0 < ρ`, `0 < L`,
`0 ≤ κ < 1`, `|u| + |v| ≤ R` (so `|z₀| ≤ R`), `L ≤ |p' (z₀)|`, `|p (z₀)| ≤ (1 - κ) ρ L` and
`deltaH (coeffDeriv a) R ρ ≤ κ L`, a bound for `|p' (z) - p' (z₀)|` on the disc `|z - z₀| ≤ ρ`.
Moduli are compared through their squares, so no square root is taken. Then
`g z = z - p (z) / p' (z₀)` maps the disc into itself and is `κ`-Lipschitz on it, and Mathlib's
`ContractingWith.exists_fixedPoint'` gives a fixed point, which is a root of `p`. This is the test
of Rump's Theorem 13.3, his modification of Krawczyk's operator, in one complex variable, with a
disc in place of the interval vector and `1 / p' (z₀)` for his matrix `R` (not the bound `R` of
`cCheck`). Rump proves existence with Brouwer's fixed point theorem; we ask for a contraction
factor `κ < 1` instead, so that Banach's theorem, which Mathlib has, suffices. Uniqueness is not
part of `cCheck`: `CAS.Calculus.LinearODERoots` gets distinct roots from disjoint discs.

The search (`CAS.Command.RootSplit`) proposes all the numbers: Durand-Kerner centres refined by
exact Newton steps and rounded to `10 ^ -d`, the radius `2 · 10 ^ -d`, `κ = 1 / 2`,
`R = |u| + |v|` and a rational `L` below `|p' (z₀)|`, with `d` doubled from 8 up to a
root-separation bound. The kernel decides `cCheck` on them.

## References

* Siegfried M. Rump, "Verification methods: Rigorous results using floating-point arithmetic",
  *Acta Numerica* 19 (2010), pp. 287-449, <https://doi.org/10.1017/S096249291000005X>.
  Theorem 13.3 for the test that `cCheck` specializes.
* R. Krawczyk, "Newton-Algorithmen zur Bestimmung von Nullstellen mit Fehlerschranken",
  *Computing* 4 (1969), pp. 187-201, <https://doi.org/10.1007/BF02234767>. The origin of the
  Krawczyk operator.
-/

@[expose] public section

namespace CAS.AlgRoot

open _root_.Polynomial Complex Metric
open CAS.Polynomial (coeffEval coeffEvalRat coeffEval_ratCast continuous_coeffEval coeffAdd
  coeffMul coeffPow coeffDeriv coeffEq)

/-! ## Polynomials from coefficient lists -/

/-- `∑ aₖ Xᵏ` over `ℂ` for the rational coefficients `a`, lowest degree first: Mathlib's
`Polynomial.ofCoeffList a`, mapped to `ℂ`. -/
noncomputable def polyC (a : List ℚ) : ℂ[X] := (ofCoeffList a).map (algebraMap ℚ ℂ)

/-- The empty coefficient list is the zero polynomial. -/
@[simp] theorem polyC_nil : polyC [] = 0 := by simp [polyC]

/-- Horner's rule: `polyC (c :: cs) = c + X · polyC cs`. -/
@[simp] theorem polyC_cons (c : ℚ) (cs : List ℚ) :
    polyC (c :: cs) = C (c : ℂ) + X * polyC cs := by
  simp [polyC, ofCoeffList_cons]

/-- At a real point `x`, `polyC a` takes the value `coeffEval a x`. -/
theorem eval_polyC_ofReal (a : List ℚ) (x : ℝ) :
    (polyC a).eval (x : ℂ) = (coeffEval a x : ℂ) := by
  induction a with
  | nil => simp
  | cons c cs ih => simp [ih]

/-- The `k`th coefficient of `polyC a` is the `k`th entry of `a`, and `0` past its end. -/
theorem coeff_polyC (a : List ℚ) (k : ℕ) : (polyC a).coeff k = (a.getD k 0 : ℂ) := by
  simp [polyC]

/-- `polyC` turns the sum `coeffAdd` of two coefficient lists into the sum of polynomials. -/
theorem polyC_coeffAdd (a b : List ℚ) : polyC (coeffAdd a b) = polyC a + polyC b := by
  simp only [polyC, CAS.Polynomial.ofCoeffList_coeffAdd, Polynomial.map_add]

/-- `polyC` turns the product `coeffMul` of two coefficient lists into the product of
polynomials. -/
theorem polyC_coeffMul (a b : List ℚ) : polyC (coeffMul a b) = polyC a * polyC b := by
  simp only [polyC, CAS.Polynomial.ofCoeffList_coeffMul, Polynomial.map_mul]

/-- `polyC` turns the power `coeffPow a m` into the `m`th power of `polyC a`. -/
theorem polyC_coeffPow (a : List ℚ) (m : ℕ) : polyC (coeffPow a m) = polyC a ^ m := by
  simp only [polyC, CAS.Polynomial.ofCoeffList_coeffPow, Polynomial.map_pow]

/-- The derivative of `polyC a` is `polyC` of the derivative list `coeffDeriv a`. -/
theorem derivative_polyC (a : List ℚ) : derivative (polyC a) = polyC (coeffDeriv a) := by
  simp only [polyC, CAS.Polynomial.ofCoeffList_coeffDeriv, Polynomial.derivative_map]

/-- Two coefficient lists that `coeffEq` accepts, equal up to trailing zeros, give the same
polynomial. -/
theorem polyC_eq_of_coeffEq {a b : List ℚ} (h : coeffEq a b = true) : polyC a = polyC b := by
  simp only [polyC, CAS.Polynomial.ofCoeffList_eq_of_coeffEq h]

/-- `p` and its radical `s` have the same complex roots when `s g = p` and `p h = sᵐ` as
coefficient lists, for any lists `g`, `h` and exponent `m`. -/
theorem eval_eq_zero_iff_of_radical {p s g h : List ℚ} {m : ℕ} (hg : coeffMul s g = p)
    (hh : coeffMul p h = coeffPow s m) (z : ℂ) :
    (polyC p).eval z = 0 ↔ (polyC s).eval z = 0 := by
  refine ⟨fun hp ↦ ?_, fun hs ↦ by rw [← hg, polyC_coeffMul, eval_mul, hs, zero_mul]⟩
  have := congrArg (Polynomial.eval z) (congrArg polyC hh)
  rw [polyC_coeffMul, polyC_coeffPow, eval_mul, eval_pow, hp, zero_mul] at this
  exact eq_zero_of_pow_eq_zero this.symm

/-! ## Products of linear factors -/

/-- For every list `L` of complex numbers, `LinearODE.charC L k` is the `k`th coefficient of
`∏ μ ∈ L, (X - μ)`. -/
theorem charC_eq_coeff : ∀ (L : List ℂ) (k : ℕ),
    LinearODE.charC L k = ((L.map fun μ ↦ X - C μ).prod).coeff k
  | [], k => by
    simp only [LinearODE.charC, List.map_nil, List.prod_nil, coeff_one]
  | μ :: L, k => by
    cases k with
    | zero =>
      simp only [LinearODE.charC, LinearODE.mulRoot, List.map_cons, List.prod_cons,
        charC_eq_coeff L 0, sub_mul, coeff_sub, mul_coeff_zero, coeff_X_zero, coeff_C_zero,
        zero_mul, zero_sub, neg_mul]
    | succ k =>
      simp only [LinearODE.charC, LinearODE.mulRoot, List.map_cons, List.prod_cons,
        charC_eq_coeff L k, charC_eq_coeff L (k + 1), sub_mul, coeff_sub, coeff_X_mul,
        coeff_C_mul]

/-- A list of `d + 1` coefficients gives a polynomial of degree at most `d`. -/
theorem natDegree_polyC_le (a : List ℚ) {d : ℕ} (hlen : a.length = d + 1) :
    (polyC a).natDegree ≤ d := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_polyC, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  simp

/-- A list of `d + 1` coefficients whose entry at index `d` is `1` gives a monic polynomial. -/
theorem monic_polyC (a : List ℚ) {d : ℕ} (hlen : a.length = d + 1) (hlast : a.getD d 0 = 1) :
    (polyC a).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one d (natDegree_polyC_le a hlen)
    (by rw [coeff_polyC, hlast]; simp)

/-- A monic polynomial of degree `d` with `d` distinct roots `μᵢ` is `∏ (X - μᵢ)`. -/
theorem prod_eq_polyC (a : List ℚ) {d : ℕ} (hlen : a.length = d + 1) (hlast : a.getD d 0 = 1)
    (L : List ℂ) (hL : L.length = d) (hnd : L.Nodup)
    (hroot : ∀ μ ∈ L, (polyC a).eval μ = 0) :
    (L.map fun μ ↦ X - C μ).prod = polyC a := by
  have hmonic := monic_polyC a hlen hlast
  have hne : polyC a ≠ 0 := hmonic.ne_zero
  have hle : (L : Multiset ℂ) ≤ (polyC a).roots :=
    (Multiset.le_iff_subset (Multiset.coe_nodup.mpr hnd)).mpr fun μ hμ ↦
      (mem_roots hne).mpr (hroot μ hμ)
  have hdvd := (Multiset.prod_X_sub_C_dvd_iff_le_roots hne (L : Multiset ℂ)).mpr hle
  have hP : ((L : Multiset ℂ).map fun μ ↦ X - C μ).prod.Monic :=
    monic_multiset_prod_of_monic _ _ fun μ _ ↦ monic_X_sub_C μ
  have hdeg : ((L : Multiset ℂ).map fun μ ↦ X - C μ).prod.natDegree = d := by
    rw [natDegree_multiset_prod_X_sub_C_eq_card]
    simp [hL]
  have := (eq_of_monic_of_dvd_of_natDegree_le hP hmonic hdvd
    (by rw [hdeg]; exact natDegree_polyC_le a hlen)).symm
  rwa [Multiset.map_coe, Multiset.prod_coe] at this

/-! ## Complex roots -/

/-- `(re, im)` of `∑ aₖ (u + v i)ᵏ`. -/
def gEval : List ℚ → ℚ → ℚ → ℚ × ℚ
  | [], _, _ => (0, 0)
  | c :: cs, u, v =>
    (c + (u * (gEval cs u v).1 - v * (gEval cs u v).2),
      u * (gEval cs u v).2 + v * (gEval cs u v).1)

/-- `polyC a` at `u + v i` is `x + y i` for `(x, y) = gEval a u v`, the value in rational
arithmetic. -/
theorem eval_polyC_gauss (a : List ℚ) (u v : ℚ) :
    (polyC a).eval ((u : ℂ) + (v : ℂ) * I) =
      ((gEval a u v).1 : ℂ) + ((gEval a u v).2 : ℂ) * I := by
  induction a with
  | nil => simp [gEval]
  | cons c cs ih =>
    simp only [polyC_cons, eval_add, eval_C, eval_mul, eval_X, ih, gEval]
    apply Complex.ext <;> simp

/-- `∑ |aₖ| Rᵏ`, a bound for `|∑ aₖ wᵏ|` on `|w| ≤ R`. -/
def absH : List ℚ → ℚ → ℚ
  | [], _ => 0
  | c :: cs, R => |c| + R * absH cs R

/-- A bound for `|p (z) - p (z₀)|` on `|z - z₀| ≤ ρ` when `|z₀| ≤ R`. -/
def deltaH : List ℚ → ℚ → ℚ → ℚ
  | [], _, _ => 0
  | _ :: cs, R, ρ => (R + ρ) * deltaH cs R ρ + ρ * absH cs R

/-- For `|w| ≤ R`, the value of `polyC a` at `w` has modulus at most `absH a R`. -/
theorem norm_eval_le {R : ℚ} {w : ℂ} (hw : ‖w‖ ≤ R) :
    ∀ a : List ℚ, ‖(polyC a).eval w‖ ≤ absH a R
  | [] => by simp [absH]
  | c :: cs => by
    have hR : 0 ≤ R := by exact_mod_cast (norm_nonneg w).trans hw
    simp only [polyC_cons, eval_add, eval_C, eval_mul, eval_X, absH, Rat.cast_add, Rat.cast_mul,
      Rat.cast_abs]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_ratCast]
    gcongr
    exact_mod_cast norm_eval_le hw cs

/-- For `|z₀| ≤ R` and `|z - z₀| ≤ ρ`, the values of `polyC a` at `z` and `z₀` differ in modulus
by at most `deltaH a R ρ`. -/
theorem norm_eval_sub_le {R ρ : ℚ} {z₀ z : ℂ} (h₀ : ‖z₀‖ ≤ R) (hz : ‖z - z₀‖ ≤ ρ) :
    ∀ a : List ℚ, ‖(polyC a).eval z - (polyC a).eval z₀‖ ≤ deltaH a R ρ
  | [] => by simp [deltaH]
  | c :: cs => by
    have hR : 0 ≤ R := by exact_mod_cast (norm_nonneg z₀).trans h₀
    have hρ : 0 ≤ ρ := by exact_mod_cast (norm_nonneg _).trans hz
    have hzR : ‖z‖ ≤ R + ρ := (norm_le_norm_add_norm_sub' z z₀).trans (add_le_add h₀ hz)
    have ih := norm_eval_sub_le h₀ hz cs
    have hb := norm_eval_le h₀ cs
    have hd : (0 : ℝ) ≤ deltaH cs R ρ := (norm_nonneg _).trans ih
    have e : (polyC (c :: cs)).eval z - (polyC (c :: cs)).eval z₀ =
        z * ((polyC cs).eval z - (polyC cs).eval z₀) + (z - z₀) * (polyC cs).eval z₀ := by
      simp only [polyC_cons, eval_add, eval_C, eval_mul, eval_X]
      ring
    simp only [e, deltaH, Rat.cast_add, Rat.cast_mul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    gcongr

/-- Rational bounds for the Newton map of `a` around `u + v i` on the disc of radius `ρ`:
`|p' (z₀)| ≥ L`, `|p (z₀)| ≤ (1 - κ) ρ L`, `|z₀| ≤ R` and `|p' (z) - p' (z₀)| ≤ κ L`. -/
def cCheck (a : List ℚ) (u v ρ κ R L : ℚ) : Bool :=
  decide (0 < ρ) && decide (0 < L) && decide (0 ≤ κ) && decide (κ < 1) &&
    decide (|u| + |v| ≤ R) &&
    decide (L * L ≤ (gEval (coeffDeriv a) u v).1 ^ 2 + (gEval (coeffDeriv a) u v).2 ^ 2) &&
    decide ((gEval a u v).1 ^ 2 + (gEval a u v).2 ^ 2 ≤ ((1 - κ) * ρ * L) ^ 2) &&
    decide (deltaH (coeffDeriv a) R ρ ≤ κ * L)

/-- The squared modulus of `p + q i` for rationals `p` and `q` is `p² + q²`. -/
theorem norm_sq_gauss (p q : ℚ) : ‖((p : ℂ) + (q : ℂ) * I)‖ ^ 2 = ((p ^ 2 + q ^ 2 : ℚ) : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- When `cCheck a u v ρ κ R L` holds, `polyC a` has a root at distance at most `ρ` from
`u + v i`: the Newton map `z ↦ z - p (z) / p' (u + v i)` is a contraction of that closed disc. -/
theorem exists_complex_root (a : List ℚ) {u v ρ κ R L : ℚ}
    (h : cCheck a u v ρ κ R L = true) :
    ∃ z ∈ closedBall ((u : ℂ) + (v : ℂ) * I) ρ, (polyC a).eval z = 0 := by
  simp only [cCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hρ, hL⟩, hκ0⟩, hκ1⟩, hR⟩, hLd⟩, hp⟩, hΔ⟩ := h
  set z₀ : ℂ := (u : ℂ) + (v : ℂ) * I with hz₀
  set c : ℂ := (polyC (coeffDeriv a)).eval z₀ with hc
  have hρ' : (0 : ℝ) < ρ := by exact_mod_cast hρ
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hκ0' : (0 : ℝ) ≤ κ := by exact_mod_cast hκ0
  have hκ1' : (κ : ℝ) < 1 := by exact_mod_cast hκ1
  -- `|c| ≥ L`.
  have hnc : (L : ℝ) ≤ ‖c‖ := by
    refine (sq_le_sq₀ hL'.le (norm_nonneg c)).mp ?_
    rw [hc, hz₀, eval_polyC_gauss, norm_sq_gauss]
    exact_mod_cast (sq L).trans_le hLd
  have hcpos : 0 < ‖c‖ := lt_of_lt_of_le hL' hnc
  have hcne : c ≠ 0 := norm_pos_iff.mp hcpos
  -- `|p (z₀)| ≤ (1 - κ) ρ L`.
  have hpz : ‖(polyC a).eval z₀‖ ≤ (1 - κ) * ρ * L := by
    have hnn : (0 : ℚ) ≤ (1 - κ) * ρ * L := mul_nonneg (mul_nonneg (by linarith) hρ.le) hL.le
    refine (sq_le_sq₀ (norm_nonneg _) (by exact_mod_cast hnn)).mp ?_
    rw [hz₀, eval_polyC_gauss, norm_sq_gauss]
    exact_mod_cast hp
  have hz₀R : ‖z₀‖ ≤ R := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_ratCast, Complex.norm_ratCast]
    exact_mod_cast hR
  -- The Newton map.
  set g : ℂ → ℂ := fun z ↦ z - (polyC a).eval z / c with hg
  have hderiv (z : ℂ) : HasDerivAt g (1 - (polyC (coeffDeriv a)).eval z / c) z := by
    have := (polyC a).hasDerivAt z
    rw [derivative_polyC] at this
    exact (hasDerivAt_id z).sub (this.div_const c)
  have hbound : ∀ z ∈ closedBall z₀ ρ, ‖deriv g z‖ ≤ κ := by
    intro z hz
    rw [(hderiv z).deriv, ← div_self hcne, ← sub_div, norm_div, div_le_iff₀ hcpos, norm_sub_rev]
    calc ‖(polyC (coeffDeriv a)).eval z - c‖ ≤ deltaH (coeffDeriv a) R ρ :=
          norm_eval_sub_le hz₀R (mem_closedBall_iff_norm.mp hz) (coeffDeriv a)
      _ ≤ κ * L := by exact_mod_cast hΔ
      _ ≤ κ * ‖c‖ := mul_le_mul_of_nonneg_left hnc hκ0'
  have hlip : ∀ z ∈ closedBall z₀ ρ, ∀ w ∈ closedBall z₀ ρ, ‖g z - g w‖ ≤ κ * ‖z - w‖ :=
    fun z hz w hw ↦ (convex_closedBall z₀ ρ).norm_image_sub_le_of_norm_deriv_le
      (fun x _ ↦ (hderiv x).differentiableAt) hbound hw hz
  have hmaps : Set.MapsTo g (closedBall z₀ ρ) (closedBall z₀ ρ) := by
    intro z hz
    have h₁ := hlip z hz z₀ (mem_closedBall_self hρ'.le)
    rw [mem_closedBall_iff_norm] at hz ⊢
    have h₂ : ‖g z₀ - z₀‖ ≤ (1 - κ) * ρ := by
      simp only [hg]
      rw [sub_sub_cancel_left, norm_neg, norm_div, div_le_iff₀ hcpos]
      exact hpz.trans (mul_le_mul_of_nonneg_left hnc (mul_nonneg (by linarith) hρ'.le))
    calc ‖g z - z₀‖ ≤ ‖g z - g z₀‖ + ‖g z₀ - z₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ κ * ρ + (1 - κ) * ρ := by
          gcongr
          exact h₁.trans (mul_le_mul_of_nonneg_left hz hκ0')
      _ = ρ := by ring
  have hK : ContractingWith (Real.toNNReal κ) (hmaps.restrict g _ _) := by
    refine ⟨Real.toNNReal_lt_one.mpr hκ1', .of_dist_le_mul fun x y ↦ ?_⟩
    rw [Real.coe_toNNReal _ hκ0', Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    exact hlip x x.2 y y.2
  obtain ⟨y, hy, hfix, -⟩ := ContractingWith.exists_fixedPoint' isClosed_closedBall.isComplete
    hmaps hK (mem_closedBall_self hρ'.le) (edist_ne_top _ _)
  exact ⟨y, hy, by simpa [Function.IsFixedPt, hg, hcne] using hfix⟩

/-- A root of `polyC a` at distance at most `ρ` from `u + v i`, chosen by `Classical.epsilon`. One
exists when `cCheck a u v ρ κ R L` holds for some `κ`, `R`, `L` (`complex_spec`); otherwise the
value is unspecified, as is the choice among several roots in the disc. -/
noncomputable def complex (a : List ℚ) (u v ρ : ℚ) : ℂ :=
  Classical.epsilon fun z ↦ z ∈ closedBall ((u : ℂ) + (v : ℂ) * I) ρ ∧ (polyC a).eval z = 0

/-- When `cCheck a u v ρ κ R L` holds, `complex a u v ρ` lies at distance at most `ρ` from
`u + v i` and is a root of `polyC a`. -/
theorem complex_spec (a : List ℚ) {u v ρ κ R L : ℚ} (h : cCheck a u v ρ κ R L = true) :
    complex a u v ρ ∈ closedBall ((u : ℂ) + (v : ℂ) * I) ρ ∧
      (polyC a).eval (complex a u v ρ) = 0 :=
  Classical.epsilon_spec (exists_complex_root a h)

/-- A point at distance at most `ρ` from `u + v i` has real part in `[u - ρ, u + ρ]` and imaginary
part in `[v - ρ, v + ρ]`. -/
theorem re_mem_of_mem_closedBall {u v ρ : ℚ} {z : ℂ}
    (hz : z ∈ closedBall ((u : ℂ) + (v : ℂ) * I) ρ) :
    z.re ∈ Set.Icc ((u : ℝ) - ρ) (u + ρ) ∧ z.im ∈ Set.Icc ((v : ℝ) - ρ) (v + ρ) := by
  rw [mem_closedBall_iff_norm] at hz
  have h₁ := abs_le.mp ((Complex.abs_re_le_norm _).trans hz)
  have h₂ := abs_le.mp ((Complex.abs_im_le_norm _).trans hz)
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ratCast_re, Complex.ratCast_im, Complex.sub_im, Complex.add_im, Complex.mul_im,
    mul_zero, mul_one, sub_zero, add_zero, zero_add] at h₁ h₂
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- `polyC a` has rational coefficients, so its value at the conjugate `z̄` is the conjugate of its
value at `z`. -/
theorem eval_conj_polyC (a : List ℚ) (z : ℂ) :
    (polyC a).eval ((starRingEnd ℂ) z) = (starRingEnd ℂ) ((polyC a).eval z) := by
  induction a with
  | nil => simp
  | cons c cs ih =>
    simp only [polyC_cons, eval_add, eval_C, eval_mul, eval_X, ih, map_add, map_mul, map_ratCast]

end CAS.AlgRoot
