/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

public import CAS.Expr.Syntax
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import CAS.Notation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Euclidean analytic semantics for verified symbolic derivatives

The executable derivative `Verified.Expr.diff` of the expression language in `CAS.Expr.Syntax`
gives the Fréchet derivative of the evaluated function `ℝ^n → ℝ` at every point where the
expression is valid. Validity is the side-condition predicate `Verified.Expr.ValidAt`:
denominators and logarithm arguments are nonzero, arguments of `asin` and `acos` differ from
`±1`, and square-root arguments and the bases of real powers are positive.

## Main definitions

* `symbolicFDeriv`: the formal Fréchet derivative of an expression at a point, as a continuous
  linear map.

## Main results

* `hasFDerivAt_eval`, `fderiv_eval_eq`: at a valid point, `symbolicFDeriv` is the Fréchet
  derivative of evaluation.
* `continuousAt_eval`, `eventually_validAt`: evaluation is continuous at a valid point, and
  validity holds on a neighbourhood of it.
* `symbolicFDeriv_apply_single_eq_diff_eval`: on the `i`-th basis vector, `symbolicFDeriv` gives
  the value of `expr.diff i`, at every point.
* `hasDerivAt_eval_add_smul_single`, `deriv_eval_add_smul_single_eq_diff_eval`: at a point of
  the coordinate line through `x` in direction `i` where `expr` is valid, the derivative along
  the line is the value of `expr.diff i`.

## Implementation notes

`diff` returns an expression, while a Fréchet derivative is a linear map, so we go through
`symbolicFDeriv`, which reads each derivative rule as a continuous linear map, and split the
proof in two. `hasFDerivAt_eval` is the analysis: an induction on the expression in which each
case applies Mathlib's rules (`HasFDerivAt.mul`, `hasDerivAt_inv`, `Real.hasDerivAt_arcsin`,
`HasFDerivAt.rpow`, ...), and `ValidAt` supplies the hypotheses those rules ask for.
`symbolicFDeriv_apply_single_eq_diff_eval` is an identity of formulas. It needs no validity,
since both sides use the same formulas and the same convention `y / 0 = 0`. The derivative rules
are classical and Mathlib's.

The line form `hasDerivAt_eval_add_smul_single` is the one the theorem of `#cas [derive x]`
(`CAS.Command.Differential`), the antiderivative checks of `CAS.Calculus.Antiderivative` and the
monotonicity tests of `CAS.Continuum.IntervalEval.Registry.Monotonicity` use.
-/

@[expose] public section

namespace CAS

open scoped BigOperators
open scoped Topology

namespace Verified.Expr

/--
The formal Fréchet derivative of `expr` at `x`, represented as a continuous linear map.

Each constructor is interpreted by its usual derivative rule, with the subexpression values
evaluated at `x`. `hasFDerivAt_eval` proves that this map is the Fréchet derivative under
`expr.ValidAt x`.
-/
noncomputable def symbolicFDeriv {n : ℕ} (expr : Verified.Expr (Fin n))
    (x : ℝ^n) : ℝ^n →L[ℝ] ℝ :=
  match expr with
  | .nat _ | .int _ | .rat _ _ | .pi | .e => 0
  | .var i => EuclideanSpace.proj i
  | .add a b => symbolicFDeriv a x + symbolicFDeriv b x
  | .mul a b => (a.eval x) • symbolicFDeriv b x + (b.eval x) • symbolicFDeriv a x
  | .sub a b => symbolicFDeriv a x - symbolicFDeriv b x
  | .div a b =>
      (a.eval x) • ((-(b.eval x ^ (2 : Nat))⁻¹) • symbolicFDeriv b x) +
        (b.eval x)⁻¹ • symbolicFDeriv a x
  | .neg a => -(symbolicFDeriv a x)
  | .pow a k => (k • (a.eval x) ^ (k - 1)) • symbolicFDeriv a x
  | .sin a => Real.cos (a.eval x) • symbolicFDeriv a x
  | .cos a => -(Real.sin (a.eval x) • symbolicFDeriv a x)
  | .atan a => (1 / (1 + (a.eval x) ^ 2)) • symbolicFDeriv a x
  | .asin a => (1 / Real.sqrt (1 - (a.eval x) ^ 2)) • symbolicFDeriv a x
  | .acos a => -((1 / Real.sqrt (1 - (a.eval x) ^ 2)) • symbolicFDeriv a x)
  | .exp a => Real.exp (a.eval x) • symbolicFDeriv a x
  | .log a => (a.eval x)⁻¹ • symbolicFDeriv a x
  | .sqrt a => (1 / (2 * Real.sqrt (a.eval x))) • symbolicFDeriv a x
  | .rpow a b =>
      (b.eval x * a.eval x ^ (b.eval x - 1)) • symbolicFDeriv a x +
        (a.eval x ^ b.eval x * Real.log (a.eval x)) • symbolicFDeriv b x

/--
Evaluation of a valid verified expression has the formal continuous linear map
`symbolicFDeriv expr x` as its Fréchet derivative at `x`.
-/
theorem hasFDerivAt_eval {n : ℕ} (expr : Verified.Expr (Fin n))
    (x : ℝ^n) (h : expr.ValidAt x) :
    HasFDerivAt (fun y : ℝ^n ↦ expr.eval y) (symbolicFDeriv expr x) x := by
  induction expr generalizing x with
  | nat | int | rat | pi | e => exact hasFDerivAt_const _ x
  | var i => exact (EuclideanSpace.proj (𝕜 := ℝ) i : ℝ^n →L[ℝ] ℝ).hasFDerivAt
  | add a b ha hb => exact (ha _ h.1).add (hb _ h.2)
  | mul a b ha hb => exact (ha _ h.1).mul (hb _ h.2)
  | sub a b ha hb => exact (ha _ h.1).sub (hb _ h.2)
  | div a b ha hb =>
    rw [show (fun y : ℝ^n ↦ (a.div b).eval y) = fun y : ℝ^n ↦ a.eval y * (b.eval y)⁻¹ from
      funext fun _ ↦ div_eq_mul_inv _ _]
    exact (ha _ h.1).mul ((hasDerivAt_inv h.2.2).comp_hasFDerivAt x (hb _ h.2.1))
  | neg a ha => exact (ha _ h).neg
  | pow a k ha => simpa [symbolicFDeriv] using (ha _ h).pow k
  | sin a ha => exact (ha _ h).sin
  | cos a ha =>
    exact (ha _ h).cos.congr_fderiv (neg_smul (Real.sin (a.eval x)) (symbolicFDeriv a x))
  | atan a ha => exact (ha _ h).arctan
  | asin a ha => exact (Real.hasDerivAt_arcsin h.2.1 h.2.2).comp_hasFDerivAt x (ha _ h.1)
  | acos a ha =>
    simpa [symbolicFDeriv, Function.comp_def] using
      (Real.hasDerivAt_arccos h.2.1 h.2.2).comp_hasFDerivAt x (ha _ h.1)
  | exp a ha => exact (ha _ h).exp
  | log a ha => exact (ha _ h.1).log h.2
  | sqrt a ha => exact (ha _ h.1).sqrt h.2.ne'
  | rpow a b ha hb => exact (ha _ h.1).rpow (hb _ h.2.1) h.2.2

/--
At every valid point, Mathlib's `fderiv` of expression evaluation is the formal derivative
map computed by `symbolicFDeriv`.
-/
theorem fderiv_eval_eq {n : ℕ} (expr : Verified.Expr (Fin n))
    (x : ℝ^n) (h : expr.ValidAt x) :
    fderiv ℝ (fun y : ℝ^n ↦ expr.eval y) x = symbolicFDeriv expr x :=
  (hasFDerivAt_eval expr x h).fderiv

/-- Evaluation of a verified expression is continuous at every point where it is valid. -/
theorem continuousAt_eval {n : ℕ} (expr : Verified.Expr (Fin n))
    (x : ℝ^n) (h : expr.ValidAt x) :
    ContinuousAt (fun y : ℝ^n ↦ expr.eval y) x :=
  (hasFDerivAt_eval expr x h).continuousAt

/--
Validity of a verified expression persists on some neighborhood of a valid Euclidean point.

Continuity preserves the strict inequalities for positive-branch operations and the
nonvanishing condition for denominators.
-/
theorem eventually_validAt {n : ℕ} (expr : Verified.Expr (Fin n)) (x : ℝ^n)
    (h : expr.ValidAt fun i ↦ x i) :
    ∀ᶠ y : ℝ^n in 𝓝 x, expr.ValidAt fun i ↦ y i := by
  induction expr generalizing x with
  | nat | int | rat | pi | e | var => exact .of_forall fun _ ↦ h
  | add a b ha hb | mul a b ha hb | sub a b ha hb => exact (ha _ h.1).and (hb _ h.2)
  | div a b ha hb =>
    exact (ha _ h.1).and ((hb _ h.2.1).and ((continuousAt_eval b x h.2.1).eventually_ne h.2.2))
  | neg a ha | pow a _ ha | sin a ha | cos a ha | atan a ha | exp a ha => exact ha _ h
  | asin a ha | acos a ha =>
    have hc := continuousAt_eval a x h.1
    exact (ha _ h.1).and ((hc.eventually_ne h.2.1).and (hc.eventually_ne h.2.2))
  | log a ha => exact (ha _ h.1).and ((continuousAt_eval a x h.1).eventually_ne h.2)
  | sqrt a ha =>
    exact (ha _ h.1).and ((continuousAt_eval a x h.1).eventually (eventually_gt_nhds h.2))
  | rpow a b ha hb =>
    exact (ha _ h.1).and ((hb _ h.2.1).and
      ((continuousAt_eval a x h.1).eventually (eventually_gt_nhds h.2.2)))

/--
Applying the formal Fréchet derivative to the `i`-th coordinate basis vector agrees with
evaluating the executable symbolic partial derivative `expr.diff i`.
-/
theorem symbolicFDeriv_apply_single_eq_diff_eval {n : ℕ}
    (expr : Verified.Expr (Fin n)) (x : ℝ^n) (i : Fin n) :
    (symbolicFDeriv expr x) (EuclideanSpace.single i (1 : ℝ)) = (expr.diff i).eval x := by
  induction expr generalizing x with
  | nat | int | rat | pi | e => simp [symbolicFDeriv]
  | var j => by_cases hji : j = i <;> simp [symbolicFDeriv, hji]
  | add a b ha hb | sub a b ha hb => simp [symbolicFDeriv, ha, hb]
  | mul a b ha hb => simp [symbolicFDeriv, ha, hb, add_comm, mul_comm]
  | div a b ha hb =>
    simp [symbolicFDeriv, ha, hb]
    by_cases hb0 : b.eval x = 0
    · simp [hb0]
    · field_simp [hb0]
      ring
  | neg a ha | sin a ha | cos a ha | exp a ha => simp [symbolicFDeriv, ha]
  | pow a k ha => simp [symbolicFDeriv, ha, mul_assoc]
  | atan a ha => simp [symbolicFDeriv, ha, div_eq_mul_inv, mul_comm]
  | asin a ha | acos a ha | log a ha => simp [symbolicFDeriv, ha, div_eq_mul_inv, mul_comm]
  | sqrt a ha => simp [symbolicFDeriv, ha, div_eq_mul_inv, mul_assoc, mul_comm]
  | rpow a b ha hb =>
    simp only [Verified.Expr.diff, Verified.Expr.eval, symbolicFDeriv, add_apply, smul_apply,
      ha, hb, smul_eq_mul, Nat.cast_one]
    ring

/--
Differentiating expression evaluation along an affine coordinate line agrees with the
executable symbolic partial derivative.
-/
theorem hasDerivAt_eval_add_smul_single {n : ℕ}
    (expr : Verified.Expr (Fin n)) (x : ℝ^n) (i : Fin n) (t : ℝ)
    (h : expr.ValidAt (x + t • EuclideanSpace.single i (1 : ℝ))) :
    HasDerivAt
      (fun s : ℝ ↦ expr.eval
        (x + s • EuclideanSpace.single i (1 : ℝ)))
      ((expr.diff i).eval
        (x + t • EuclideanSpace.single i (1 : ℝ))) t := by
  have hline : HasDerivAt (fun s : ℝ ↦ x + s • EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ)) t := by
    simpa using ((hasDerivAt_id t).smul_const (EuclideanSpace.single i (1 : ℝ))).const_add x
  simpa [Function.comp_def, symbolicFDeriv_apply_single_eq_diff_eval expr _ i] using
    (hasFDerivAt_eval expr _ h).comp_hasDerivAt t hline

/--
The scalar derivative along an affine coordinate line is computed by the executable symbolic
partial derivative.
-/
theorem deriv_eval_add_smul_single_eq_diff_eval {n : ℕ}
    (expr : Verified.Expr (Fin n)) (x : ℝ^n) (i : Fin n) (t : ℝ)
    (h : expr.ValidAt (x + t • EuclideanSpace.single i (1 : ℝ))) :
    deriv
      (fun s : ℝ ↦ expr.eval
        (x + s • EuclideanSpace.single i (1 : ℝ))) t =
      (expr.diff i).eval
        (x + t • EuclideanSpace.single i (1 : ℝ)) :=
  (hasDerivAt_eval_add_smul_single expr x i t h).deriv


end Verified.Expr

end CAS
