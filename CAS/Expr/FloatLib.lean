/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.Real
public import CAS.Expr.Syntax

/-!
# Translating symbolic expressions to FloatLib

`Expr.toFloatLib` translates the CAS syntax into FloatLib's expression language
`FloatLib.Numerics.Interval.Expr`, mapping variable labels to the caller's coordinate table.
The result can be evaluated directly by any sound FloatLib backend, with its own
endpoint representation and accuracy settings; numerical evaluation is left to those backends.
The denotation theorem `eval_toFloatLib` holds when every real-power base is positive.

## Main definitions

* `Expr.toFloatLib`: the translation.
* `Expr.RpowBasesPositive`: every real-power base of the expression is positive.

## Main results

* `Expr.eval_toFloatLib`: the translated expression has the value of the original one.

## Implementation notes

FloatLib's constants are rationals and its powers have natural exponents, so we write `π` as
`4 * atan(1)`, `e` as `exp(1)` and a real power `a ^ b` as `exp(log(a) * b)`. The last encoding
agrees with `Real.rpow` only at a positive base (`Real.rpow_def_of_pos`), which is why
`eval_toFloatLib` assumes `RpowBasesPositive`, a weaker restriction than the differentiation
conditions `ValidAt`. FloatLib's interval arcsine and arccosine (`asinBounds?`, `acosBounds?`)
accept only intervals inside `[-1, 1]`, so we clamp their argument with `max (-1) (min 1 _)`.
Mathlib's total `Real.arcsin` and `Real.arccos` are constant outside `[-1, 1]`, and
`Real.arcsin_projIcc` shows that the clamp keeps the value, constant tails included.

The translation and its proof by structural induction are ours; the interval arithmetic and its
soundness theorem `Expr.containsReal_eval?` are FloatLib's. Rewriting the conclusion of that
theorem with `eval_toFloatLib` gives an enclosure of the original CAS expression.

## References

* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, 2026, <https://github.com/lean-dojo/FloatLib>. We pin FloatLib 3.1.0
  (revision 0fe4f04).
-/

@[expose] public section

namespace CAS.Verified.Expr

/--
Translate a CAS expression into FloatLib's syntax using the supplied variable indices.

The translation preserves ordinary multiplication followed by addition. Clients that
require fused multiply-add construct FloatLib's explicit ternary FMA node.
-/
def toFloatLib {ι : Type*} (vars : ι → Nat) : Expr ι → FloatLib.Numerics.Interval.Expr
  | .nat n => .const n
  | .int n => .const n
  | .rat num den => .const (num / den)
  | .pi => .binary .mul (.const 4) (.unary .atan (.const 1))
  | .e => .unary .exp (.const 1)
  | .var i => .var (vars i)
  | .add a b => .binary .add (a.toFloatLib vars) (b.toFloatLib vars)
  | .mul a b => .binary .mul (a.toFloatLib vars) (b.toFloatLib vars)
  | .sub a b => .binary .sub (a.toFloatLib vars) (b.toFloatLib vars)
  | .div a b => .binary .div (a.toFloatLib vars) (b.toFloatLib vars)
  | .neg a => .unary .neg (a.toFloatLib vars)
  | .pow a n => .unary (.pow n) (a.toFloatLib vars)
  | .sin a => .unary .sin (a.toFloatLib vars)
  | .cos a => .unary .cos (a.toFloatLib vars)
  | .atan a => .unary .atan (a.toFloatLib vars)
  | .asin a =>
      .unary .asin (.binary .max (.const (-1)) (.binary .min (.const 1) (a.toFloatLib vars)))
  | .acos a =>
      .unary .acos (.binary .max (.const (-1)) (.binary .min (.const 1) (a.toFloatLib vars)))
  | .exp a => .unary .exp (a.toFloatLib vars)
  | .log a => .unary .log (a.toFloatLib vars)
  | .sqrt a => .unary .sqrt (a.toFloatLib vars)
  | .rpow a b =>
      .unary .exp (.binary .mul (.unary .log (a.toFloatLib vars)) (b.toFloatLib vars))

/--
Every real-power base occurring in the expression is positive in this environment.

Other total real operations impose no condition here. Their interval implementations
may still reject inputs outside the domains supported by the chosen backend.
-/
@[simp] def RpowBasesPositive {ι : Type*} (ρ : ι → ℝ) : Expr ι → Prop
  | .nat _ | .int _ | .rat _ _ | .pi | .e | .var _ => True
  | .add a b | .mul a b | .sub a b | .div a b =>
      a.RpowBasesPositive ρ ∧ b.RpowBasesPositive ρ
  | .neg a | .pow a _ | .sin a | .cos a | .atan a | .asin a | .acos a |
      .exp a | .log a | .sqrt a => a.RpowBasesPositive ρ
  | .rpow a b => a.RpowBasesPositive ρ ∧ b.RpowBasesPositive ρ ∧ 0 < a.eval ρ

private theorem arcsin_clamp (x : ℝ) :
    Real.arcsin (max (-1) (min 1 x)) = Real.arcsin x := by
  simpa [Set.coe_projIcc] using Real.arcsin_projIcc x

private theorem arccos_clamp (x : ℝ) :
    Real.arccos (max (-1) (min 1 x)) = Real.arccos x := by
  simp only [Real.arccos_eq_pi_div_two_sub_arcsin, arcsin_clamp]

/--
Translation preserves real evaluation when the coordinate table agrees with the
original environment and every real-power base is positive.

Apply this equality to the conclusion of FloatLib's `Expr.containsReal_eval?`
to obtain a certified bound for the original CAS expression.
-/
theorem eval_toFloatLib {ι : Type*} (expr : Expr ι)
    (vars : ι → Nat) (ρ : ι → ℝ) (values : Nat → ℝ)
    (hvars : ∀ i, values (vars i) = ρ i)
    (hpow : expr.RpowBasesPositive ρ) :
    (expr.toFloatLib vars).eval values = expr.eval ρ := by
  induction expr with
  | pi =>
      simp only [toFloatLib, FloatLib.Numerics.Interval.Expr.eval,
        FloatLib.Numerics.Interval.BinaryOp.eval, FloatLib.Numerics.Interval.UnaryOp.eval,
        Rat.cast_ofNat, Rat.cast_one, Real.arctan_one, eval]
      ring
  | rpow a b ha hb =>
      rcases hpow with ⟨hpa, hpb, hpos⟩
      simp only [toFloatLib, FloatLib.Numerics.Interval.Expr.eval,
        FloatLib.Numerics.Interval.BinaryOp.eval, FloatLib.Numerics.Interval.UnaryOp.eval,
        ha hpa, hb hpb, eval, Real.rpow_def_of_pos hpos]
  | _ =>
      simp_all [toFloatLib, FloatLib.Numerics.Interval.Expr.eval,
        FloatLib.Numerics.Interval.BinaryOp.eval, FloatLib.Numerics.Interval.UnaryOp.eval,
        arcsin_clamp, arccos_clamp]

end CAS.Verified.Expr
