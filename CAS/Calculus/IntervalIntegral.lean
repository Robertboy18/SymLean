/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import CAS.Expr.Syntax

/-!
# Checked interval-integral expressions

Finite interval integrals whose closed forms stay inside `Verified.Expr`: a constant body
(`intervalIntegralConst`), a monomial `coeff * x ^ k` (`intervalIntegralPowConstCoeff`) and a
finite polynomial (`intervalIntegralPolyConstCoeff`). Coefficients may depend on other
coordinates; the evaluation theorems assume that they do not mention the integration coordinate.

The evaluation theorems identify each symbolic closed form with Mathlib's interval integral, so
symbolic calculus can differentiate the closed form without integration machinery in the
expression syntax module.
-/

@[expose] public section

namespace CAS

namespace Verified.Expr

/-- Symbolic integral of a body independent of the selected integration coordinate. -/
def intervalIntegralConst {ι : Type*}
    (_v : ι) (lower upper body : Verified.Expr ι) : Verified.Expr ι :=
  .mul body (.sub upper lower)

/-- The constant-body constructor agrees with the corresponding Mathlib interval integral. -/
@[simp] theorem eval_intervalIntegralConst {ι : Type*} [DecidableEq ι]
    (ρ : ι → ℝ) (v : ι) (lower upper body : Verified.Expr ι)
    (hbody : containsVar v body = false) :
    (intervalIntegralConst v lower upper body).eval ρ =
      ∫ t in lower.eval ρ..upper.eval ρ, body.eval (Function.update ρ v t) := by
  simp [intervalIntegralConst, eval_eq_eval_update_of_not_containsVar ρ v body hbody, mul_comm]

/--
Symbolic integral of `coeff * x ^ k` when `coeff` is independent of the integration coordinate.
-/
def intervalIntegralPowConstCoeff {ι : Type*}
    (_v : ι) (lower upper coeff : Verified.Expr ι) (k : Nat) : Verified.Expr ι :=
  .mul coeff (.div (.sub (.pow upper (k + 1)) (.pow lower (k + 1))) (.nat (k + 1)))

/-- The monomial constructor agrees with the corresponding Mathlib interval integral. -/
@[simp] theorem eval_intervalIntegralPowConstCoeff {ι : Type*} [DecidableEq ι]
    (ρ : ι → ℝ) (v : ι) (lower upper coeff : Verified.Expr ι) (k : Nat)
    (hcoeff : containsVar v coeff = false) :
    (intervalIntegralPowConstCoeff v lower upper coeff k).eval ρ =
      ∫ t in lower.eval ρ..upper.eval ρ,
        coeff.eval (Function.update ρ v t) * t ^ k := by
  simp [intervalIntegralPowConstCoeff, eval_eq_eval_update_of_not_containsVar ρ v coeff hcoeff,
    integral_pow]

/--
Symbolic integral of a finite polynomial with coordinate-independent symbolic coefficients.
-/
def intervalIntegralPolyConstCoeff {ι : Type*} {m : Nat}
    (v : ι) (lower upper : Verified.Expr ι)
    (coeff : Fin m → Verified.Expr ι) : Verified.Expr ι :=
  addList ((List.finRange m).map fun i ↦
    intervalIntegralPowConstCoeff v lower upper (coeff i) i.val)

/--
The finite-polynomial constructor evaluates to the sum of its checked monomial integrals.

Writing the result as a finite sum keeps this theorem independent of a chosen interval-integral
linearity normal form.
-/
@[simp] theorem eval_intervalIntegralPolyConstCoeff {ι : Type*} [DecidableEq ι] {m : Nat}
    (ρ : ι → ℝ) (v : ι) (lower upper : Verified.Expr ι)
    (coeff : Fin m → Verified.Expr ι)
    (hcoeff : ∀ i : Fin m, containsVar v (coeff i) = false) :
    (intervalIntegralPolyConstCoeff v lower upper coeff).eval ρ =
      ((List.finRange m).map fun i ↦
        ∫ t in lower.eval ρ..upper.eval ρ,
          (coeff i).eval (Function.update ρ v t) * t ^ i.val).sum := by
  rw [intervalIntegralPolyConstCoeff, eval_addList, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun i _ ↦ by simp [hcoeff i])

end Verified.Expr

end CAS
