/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import CAS.Tactic.KernelReadBack
public import CAS.Elaboration.RealExpression

/-!
# Limits at infinity of elementary primitives

`limitAtTopOfBody` computes the limit at `+∞` of a real function given by its body and proves
`Filter.Tendsto (fun t ↦ body) Filter.atTop (𝓝 limit)`. The improper-integral route of `cas`
needs the limits at `+∞` of the checked primitive `F`, and the limits at `-∞`, which it reads as
limits at `+∞` of `t ↦ F (-t)`, in order to apply Mathlib's
`MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'` and its variants. The command
`#cas [integrate x in [a, b]]` uses the same procedure for the value of the primitive at an
infinite endpoint. The limit is computed structurally for the decay shapes a planner primitive
takes:

* constants, sums, differences, negations, products and quotients by constants
  (`Filter.Tendsto.add`, `Filter.Tendsto.const_mul`, `Filter.Tendsto.div_const`, and friends);
* `Real.exp e` where `e` tends to `-∞`, such as an affine function of the variable with negative
  slope (`Real.tendsto_exp_atBot` composed with the divergence of `e`);
* real powers `t ^ (-s)` with `0 < s` (`tendsto_rpow_neg_atTop`), inverses and quotients by
  functions tending to `+∞` (`Filter.Tendsto.inv_tendsto_atTop`, `Filter.Tendsto.div_atTop`),
  such as natural powers of the variable and `1 + Real.exp t`;
* inverses and quotients by functions with a nonzero limit (`Filter.Tendsto.inv₀`,
  `Filter.Tendsto.div`);
* products of a natural or real power of the variable with a decaying exponential
  (`Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero`,
  `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`), and products of a decaying exponential with a
  polynomial in the variable, such as `exp (-t) * (-t - 1)`, which are multiplied out first;
* `Real.arctan e` where `e` tends to `+∞` or to `-∞`, whose limit is `π / 2` or `-(π / 2)`.

## Implementation notes

Every result is a proof term checked by Lean; the structural analysis is only a strategy for
choosing Mathlib lemmas. `limitAtTop` recurses through the term with its size as fuel, and the
mutual `divergesAtTop?` and `divergesAtBot?` prove the divergences that the rules for the
exponential, for inverses and quotients and for the arctangent need. A product that no rule
covers is multiplied out one step at a time by `distributeProduct?`, and `Filter.Tendsto.congr`
carries the limit of the expanded form back to the product. Side conditions on the constants,
such as `0 < c` or a nonzero limit, come from `proveNumericFact?`: an assumption, `norm_num`,
`positivity` or `linarith`. When no shape applies, `limitAtTop` returns `Outcome.unknown` with
the subterm it could not handle, and `limitAtTopOfBody` fails with a message that shows it, so
the caller can name the missing limit. We work on ordinary real syntax rather than on checked
expressions, so the limit routes of `CAS/Calculus/Limits.lean` play no part.
-/

public meta section

namespace CAS.Tactic.Integration.Limits

open Lean Elab Tactic Meta
open KernelReadBack
open CAS.Elaboration.RealExpression (realNumeral)

/-- The filter `Filter.atTop` on `ℝ`. -/
def atTopReal : MetaM Expr :=
  mkAppOptM ``Filter.atTop #[some (mkConst ``Real), none]

/-- The filter `Filter.atBot` on `ℝ`. -/
def atBotReal : MetaM Expr :=
  mkAppOptM ``Filter.atBot #[some (mkConst ``Real), none]

/-- The statement `Filter.Tendsto (fun t ↦ body) Filter.atTop target` for the variable `t`. -/
def tendstoStatement (binder body target : Expr) : MetaM Expr := do
  mkAppM ``Filter.Tendsto #[← mkLambdaFVars #[binder] body, ← atTopReal, target]

/-- Run `tactic` on a fresh goal for `statement`, returning the proof or `none` on failure. No
message reaches the user; the caller decides how to report. -/
def proveByTactic? (statement : Expr) (tactic : TSyntax `tactic) : MetaM (Option Expr) := do
  let goal ← mkFreshExprSyntheticOpaqueMVar statement
  let remaining ←
    try
      withSuppressedMessagesMeta <| runTacticOnGoal goal.mvarId! tactic
    catch _ =>
      return none
  unless remaining.isEmpty do
    return none
  let proof ← instantiateMVars goal
  if proof.hasMVar ∨ proof.hasSorry then
    return none
  return some proof

/-- Prove a numeric side fact such as `0 < c`, `c < 0`, or `n ≠ 0` about the constants of the
primitive from the local context and the numeral normalizers. -/
def proveNumericFact? (statement : Expr) : MetaM (Option Expr) := do
  proveByTactic? statement
    (← `(tactic| first | assumption | norm_num | positivity | linarith))

/-- Whether `expression` mentions the variable. -/
def dependsOn (binder expression : Expr) : Bool :=
  expression.containsFVar binder.fvarId!

/-- A proof that the constant `body` tends to itself along the variable. -/
def constantLimit (binder body : Expr) : MetaM Expr := do
  let statement ← tendstoStatement binder body (← mkAppM ``nhds #[body])
  let some proof ← proveByTactic? statement (← `(tactic| exact tendsto_const_nhds))
    | throwError "internal error: the constant limit of{indentExpr body}\nwas not proved"
  return proof

/-- The proof `Tendsto (Neg.neg : ℝ → ℝ) source target` given by the Mathlib lemma `name`
(`Filter.tendsto_neg_atTop_atBot` or `Filter.tendsto_neg_atBot_atTop`). -/
def negationLemma? (name : Name) (source target : MetaM Expr) : MetaM (Option Expr) := do
  let negation ← mkAppOptM ``Neg.neg #[some (mkConst ``Real), none]
  let statement ← mkAppM ``Filter.Tendsto #[negation, ← source, ← target]
  proveByTactic? statement (← `(tactic| exact $(mkIdent name)))

mutual

/-- A proof that `fun t ↦ body` tends to `+∞`, for the divergence shapes of a primitive:
the variable itself, a positive natural or real power, a positive constant multiple, a
constant shift, the negation of a function tending to `-∞`, and the exponential of a function
tending to `+∞`. -/
def divergesAtTop? (binder : Expr) : Nat → Expr → MetaM (Option Expr)
  | 0, _ => return none
  | fuel + 1, body => do
      let body := body.consumeMData
      if !dependsOn binder body then
        return none
      if body == binder then
        return some (← mkAppOptM ``Filter.tendsto_id #[some (mkConst ``Real), some (← atTopReal)])
      match body.getAppFnArgs with
      | (``HPow.hPow, #[_, exponentType, _, _, base, exponent]) =>
          if base == binder && !dependsOn binder exponent then
            if exponentType.isConstOf ``Nat then
              return ← proveByTactic? (← tendstoStatement binder body (← atTopReal))
                (← `(tactic| exact Filter.tendsto_pow_atTop (by norm_num)))
            else
              let positive ← mkAppM ``LT.lt #[← realNumeral 0, exponent]
              let some hpositive ← proveNumericFact? positive | return none
              return some (← mkAppM ``tendsto_rpow_atTop #[hpositive])
          return none
      | (``HMul.hMul, #[_, _, _, _, a, b]) =>
          if !dependsOn binder a then
            let positive ← mkAppM ``LT.lt #[← realNumeral 0, a]
            let some hpositive ← proveNumericFact? positive | return none
            let some hb ← divergesAtTop? binder fuel b | return none
            return some (← mkAppM ``Filter.Tendsto.const_mul_atTop #[hpositive, hb])
          if !dependsOn binder b then
            let positive ← mkAppM ``LT.lt #[← realNumeral 0, b]
            let some hpositive ← proveNumericFact? positive | return none
            let some ha ← divergesAtTop? binder fuel a | return none
            return some (← mkAppM ``Filter.Tendsto.atTop_mul_const #[hpositive, ha])
          return none
      | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
          if !dependsOn binder b then
            let some ha ← divergesAtTop? binder fuel a | return none
            return some (← mkAppM ``Filter.tendsto_atTop_add_const_right #[← atTopReal, b, ha])
          if !dependsOn binder a then
            let some hb ← divergesAtTop? binder fuel b | return none
            return some (← mkAppM ``Filter.tendsto_atTop_add_const_left #[← atTopReal, a, hb])
          return none
      | (``Neg.neg, #[_, _, a]) =>
          let some ha ← divergesAtBot? binder fuel a | return none
          let some negation ← negationLemma? ``Filter.tendsto_neg_atBot_atTop atBotReal atTopReal
            | return none
          return some (← mkAppM ``Filter.Tendsto.comp #[negation, ha])
      | (``Real.exp, #[argument]) =>
          let some hargument ← divergesAtTop? binder fuel argument | return none
          return some (← mkAppM ``Filter.Tendsto.comp
            #[mkConst ``Real.tendsto_exp_atTop, hargument])
      | _ => return none

/-- A proof that `fun t ↦ body` tends to `-∞`: the negation of a function tending to `+∞`, a
negative constant multiple of one, and constant shifts of such functions. -/
def divergesAtBot? (binder : Expr) : Nat → Expr → MetaM (Option Expr)
  | 0, _ => return none
  | fuel + 1, body => do
      let body := body.consumeMData
      if !dependsOn binder body then
        return none
      match body.getAppFnArgs with
      | (``Neg.neg, #[_, _, a]) =>
          let some ha ← divergesAtTop? binder fuel a | return none
          let some negation ← negationLemma? ``Filter.tendsto_neg_atTop_atBot atTopReal atBotReal
            | return none
          return some (← mkAppM ``Filter.Tendsto.comp #[negation, ha])
      | (``HMul.hMul, #[_, _, _, _, a, b]) =>
          if !dependsOn binder a then
            let negative ← mkAppM ``LT.lt #[a, ← realNumeral 0]
            let some hnegative ← proveNumericFact? negative | return none
            let some hb ← divergesAtTop? binder fuel b | return none
            return some (← mkAppM ``Filter.Tendsto.const_mul_atTop_of_neg #[hnegative, hb])
          if !dependsOn binder b then
            let negative ← mkAppM ``LT.lt #[b, ← realNumeral 0]
            let some hnegative ← proveNumericFact? negative | return none
            let some ha ← divergesAtTop? binder fuel a | return none
            return some (← mkAppM ``Filter.Tendsto.atTop_mul_const_of_neg #[hnegative, ha])
          return none
      | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
          if !dependsOn binder b then
            let some ha ← divergesAtBot? binder fuel a | return none
            return some (← mkAppM ``Filter.tendsto_atBot_add_const_right #[← atTopReal, b, ha])
          if !dependsOn binder a then
            let some hb ← divergesAtBot? binder fuel b | return none
            return some (← mkAppM ``Filter.tendsto_atBot_add_const_left #[← atTopReal, a, hb])
          return none
      | (``HSub.hSub, #[_, _, _, _, a, b]) =>
          if !dependsOn binder b then
            let some ha ← divergesAtBot? binder fuel a | return none
            return some (← mkAppM ``Filter.tendsto_atBot_add_const_right
              #[← atTopReal, ← mkAppM ``Neg.neg #[b], ha])
          return none
      | _ => return none

end

/-- The exponent `n` of the power factor of a product `t ^ n * exp e` (or `t * exp e`, read as
`n = 1`): a natural literal for a natural power, or a real term for a real power, together with
the exponential's argument. The factors may come in either order. -/
private def powerExponentialFactors? (binder a b : Expr) :
    Option (Expr × Bool × Expr) :=
  let power? (factor : Expr) : Option (Expr × Bool) :=
    if factor == binder then
      some (mkNatLit 1, true)
    else
      match factor.getAppFnArgs with
      | (``HPow.hPow, #[_, exponentType, _, _, base, exponent]) =>
          if base == binder && !exponent.containsFVar binder.fvarId! then
            some (exponent, exponentType.isConstOf ``Nat)
          else
            none
      | _ => none
  let exponential? (factor : Expr) : Option Expr :=
    match factor.getAppFnArgs with
    | (``Real.exp, #[argument]) => some argument
    | _ => none
  match power? a, exponential? b with
  | some (exponent, natural), some argument => some (exponent, natural, argument)
  | _, _ =>
      match power? b, exponential? a with
      | some (exponent, natural), some argument => some (exponent, natural, argument)
      | _, _ => none

/-- Prove that a product of a power of the variable and a decaying exponential tends to `0`:
`t ^ n * exp (-t)` through `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero`, and
`t ^ s * exp (-b * t)` (in any of the usual spellings of the exponent) through
`tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`, the exact shape being matched by `simp`. -/
private def powerExponentialLimit? (binder a b : Expr) : TermElabM (Option Expr) := do
  let some (exponent, natural, argument) := powerExponentialFactors? binder a b
    | return none
  let product ← mkAppM ``HMul.hMul #[a, b]
  let statement ← tendstoStatement binder product (← mkAppM ``nhds #[← realNumeral 0])
  -- The decay rate `r` of the exponent `-r * t`, `-(r * t)`, `r * t` with `r < 0`, or `-t`.
  let rate : Option Expr :=
    match argument.getAppFnArgs with
    | (``Neg.neg, #[_, _, inner]) =>
        if inner == binder then
          some (mkNatLit 1)
        else
          match inner.getAppFnArgs with
          | (``HMul.hMul, #[_, _, _, _, r, t]) => if t == binder then some r else none
          | _ => none
    | (``HMul.hMul, #[_, _, _, _, r, t]) =>
        if t == binder then
          match r.getAppFnArgs with
          | (``Neg.neg, #[_, _, positiveRate]) => some positiveRate
          | _ => none
        else
          none
    | _ => none
  let some rate := rate | return none
  let rateTerm ← Term.exprToSyntax rate
  let exponentTerm ← Term.exprToSyntax exponent
  let tactic ←
    if natural then
      `(tactic|
        first
          | simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero $exponentTerm
          | simpa [mul_comm] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero $exponentTerm
          | simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero $exponentTerm $rateTerm
              (by norm_num)
          | simpa [mul_comm] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero $exponentTerm
              $rateTerm (by norm_num))
    else
      `(tactic|
        first
          | simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero $exponentTerm $rateTerm
              (by norm_num)
          | simpa [mul_comm] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero $exponentTerm
              $rateTerm (by norm_num))
  proveByTactic? statement tactic

/-- Prove that a real power `t ^ e` of the variable with a negative constant exponent tends to
`0` (`tendsto_rpow_neg_atTop`). An exponent written `-s` is matched syntactically, so that the
unifier never unfolds real arithmetic; any other exponent `e` is first rewritten as `-(-e)`, and
`norm_num` (or the local context, for a symbolic exponent) proves the positivity of `-e`. -/
private def negativePowerLimit? (binder exponent : Expr) : TermElabM (Option Expr) := do
  let power ← mkAppM ``HPow.hPow #[binder, exponent]
  let statement ← tendstoStatement binder power (← mkAppM ``nhds #[← realNumeral 0])
  match exponent.getAppFnArgs with
  | (``Neg.neg, #[_, _, positive]) =>
      let positiveTerm ← Term.exprToSyntax positive
      proveByTactic? statement
        (← `(tactic|
          exact tendsto_rpow_neg_atTop (y := $positiveTerm)
            (by first | norm_num | positivity | assumption | linarith)))
  | _ =>
      let exponentTerm ← Term.exprToSyntax exponent
      proveByTactic? statement
        (← `(tactic|
          (rw [show $exponentTerm = -(-$exponentTerm) from (neg_neg _).symm]
           exact tendsto_rpow_neg_atTop
             (by first | norm_num | positivity | assumption | linarith))))

/-- Prove that a limit value is nonzero, as `Filter.Tendsto.inv₀` and `Filter.Tendsto.div`
require. -/
private def nonzeroFact? (value : Expr) : MetaM (Option Expr) := do
  proveNumericFact? (← mkAppM ``Ne #[value, ← realNumeral 0])

/-- Prove `Filter.Tendsto Real.arctan source (𝓝 limit)` by `tactic`, which weakens Mathlib's
one-sided limit `Real.tendsto_arctan_atTop` or `Real.tendsto_arctan_atBot` to the full
neighbourhood filter. -/
private def arctanLimit? (source : MetaM Expr) (limit : Expr) (tactic : TSyntax `tactic) :
    MetaM (Option Expr) := do
  proveByTactic?
    (← mkAppM ``Filter.Tendsto #[mkConst ``Real.arctan, ← source, ← mkAppM ``nhds #[limit]])
    tactic

/-- One step of multiplying out the product `a * b`, as the product `distributed` together with
the proof of `a * b = distributed`. A factor that is a sum, a difference or a negation is
distributed over, and a constant factor of a product, or a constant divisor, is moved out of
the product. Repeated, these steps turn an exponential times a polynomial into the products
`t ^ n * exp e` of `powerExponentialLimit?`. -/
private def distributeProduct? (binder a b : Expr) : MetaM (Option (Expr × Expr)) := do
  let constant (factor : Expr) : Bool := !dependsOn binder factor
  let product (left right : Expr) : MetaM Expr := mkAppM ``HMul.hMul #[left, right]
  match b.consumeMData.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, left, right]) =>
      return some (← mkAppM ``HAdd.hAdd #[← product a left, ← product a right],
        ← mkAppM ``mul_add #[a, left, right])
  | (``HSub.hSub, #[_, _, _, _, left, right]) =>
      return some (← mkAppM ``HSub.hSub #[← product a left, ← product a right],
        ← mkAppM ``mul_sub #[a, left, right])
  | (``Neg.neg, #[_, _, inner]) =>
      return some (← mkAppM ``Neg.neg #[← product a inner], ← mkAppM ``mul_neg #[a, inner])
  | (``HMul.hMul, #[_, _, _, _, left, right]) =>
      if constant left then
        return some (← product left (← product a right),
          ← mkAppM ``mul_left_comm #[a, left, right])
      if constant right then
        return some (← product (← product a left) right,
          ← mkEqSymm (← mkAppM ``mul_assoc #[a, left, right]))
  | (``HDiv.hDiv, #[_, _, _, _, numerator, denominator]) =>
      if constant denominator then
        return some (← mkAppM ``HDiv.hDiv #[← product a numerator, denominator],
          ← mkAppM ``mul_div_assoc' #[a, numerator, denominator])
  | _ => pure ()
  match a.consumeMData.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, left, right]) =>
      return some (← mkAppM ``HAdd.hAdd #[← product left b, ← product right b],
        ← mkAppM ``add_mul #[left, right, b])
  | (``HSub.hSub, #[_, _, _, _, left, right]) =>
      return some (← mkAppM ``HSub.hSub #[← product left b, ← product right b],
        ← mkAppM ``sub_mul #[left, right, b])
  | (``Neg.neg, #[_, _, inner]) =>
      return some (← mkAppM ``Neg.neg #[← product inner b], ← mkAppM ``neg_mul #[inner, b])
  | (``HMul.hMul, #[_, _, _, _, left, right]) =>
      if constant left then
        return some (← product left (← product right b), ← mkAppM ``mul_assoc #[left, right, b])
      if constant right then
        return some (← product (← product left b) right,
          ← mkAppM ``mul_right_comm #[left, right, b])
      return none
  | (``HDiv.hDiv, #[_, _, _, _, numerator, denominator]) =>
      if constant denominator then
        return some (← mkAppM ``HDiv.hDiv #[← product numerator b, denominator],
          ← mkAppM ``div_mul_eq_mul_div #[numerator, denominator, b])
      return none
  | _ => return none

/-- The outcome of the structural limit computation. -/
inductive Outcome where
  /-- The limit `limit` with a proof of `Tendsto (fun t ↦ body) atTop (𝓝 limit)`. -/
  | limit (limit proof : Expr)
  /-- No shape applied to the given subterm. -/
  | unknown (subterm : Expr)

/-- Compute the limit at `+∞` of `fun t ↦ body` structurally, returning the limit value and a
proof of `Filter.Tendsto (fun t ↦ body) Filter.atTop (𝓝 limit)`, or the first subterm whose
limit is not covered. The fuel bounds the recursion by the size of the term. -/
def limitAtTop (binder : Expr) : Nat → Expr → TermElabM Outcome
  | 0, body => return .unknown body
  | fuel + 1, body => do
      let body := body.consumeMData
      if !dependsOn binder body then
        return .limit body (← constantLimit binder body)
      let recurse := limitAtTop binder fuel
      match body.getAppFnArgs with
      | (``Neg.neg, #[_, _, a]) =>
          match ← recurse a with
          | .limit la pa =>
              return .limit (← mkAppM ``Neg.neg #[la]) (← mkAppM ``Filter.Tendsto.neg #[pa])
          | unknown => return unknown
      | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
          match ← recurse a, ← recurse b with
          | .limit la pa, .limit lb pb =>
              return .limit (← mkAppM ``HAdd.hAdd #[la, lb])
                (← mkAppM ``Filter.Tendsto.add #[pa, pb])
          | .unknown subterm, _ | _, .unknown subterm => return .unknown subterm
      | (``HSub.hSub, #[_, _, _, _, a, b]) =>
          match ← recurse a, ← recurse b with
          | .limit la pa, .limit lb pb =>
              return .limit (← mkAppM ``HSub.hSub #[la, lb])
                (← mkAppM ``Filter.Tendsto.sub #[pa, pb])
          | .unknown subterm, _ | _, .unknown subterm => return .unknown subterm
      | (``HMul.hMul, #[_, _, _, _, a, b]) =>
          if !dependsOn binder a then
            match ← recurse b with
            | .limit lb pb =>
                return .limit (← mkAppM ``HMul.hMul #[a, lb])
                  (← mkAppM ``Filter.Tendsto.const_mul #[a, pb])
            | unknown => return unknown
          if !dependsOn binder b then
            match ← recurse a with
            | .limit la pa =>
                return .limit (← mkAppM ``HMul.hMul #[la, b])
                  (← mkAppM ``Filter.Tendsto.mul_const #[b, pa])
            | unknown => return unknown
          match ← recurse a, ← recurse b with
          | .limit la pa, .limit lb pb =>
              return .limit (← mkAppM ``HMul.hMul #[la, lb])
                (← mkAppM ``Filter.Tendsto.mul #[pa, pb])
          | _, _ =>
              if let some proof ← powerExponentialLimit? binder a b then
                return .limit (← realNumeral 0) proof
              -- The product is multiplied out one step, and the two functions are identified
              -- pointwise by `Tendsto.congr (fun t ↦ distributed t = a t * b t)`.
              let some (distributed, equality) ← distributeProduct? binder a b
                | return .unknown body
              match ← recurse distributed with
              | .limit limit proof =>
                  let pointwise ← mkLambdaFVars #[binder] (← mkEqSymm equality)
                  return .limit limit (← mkAppM ``Filter.Tendsto.congr #[pointwise, proof])
              | .unknown _ => return .unknown body
      | (``HDiv.hDiv, #[_, _, _, _, a, b]) =>
          if !dependsOn binder b then
            match ← recurse a with
            | .limit la pa =>
                return .limit (← mkAppM ``HDiv.hDiv #[la, b])
                  (← mkAppM ``Filter.Tendsto.div_const #[pa, b])
            | unknown => return unknown
          match ← recurse a with
          | .limit la pa =>
              match ← divergesAtTop? binder fuel b with
              | some pb =>
                  return .limit (← realNumeral 0) (← mkAppM ``Filter.Tendsto.div_atTop #[pa, pb])
              | none =>
                  match ← recurse b with
                  | .limit lb pb =>
                      let some hlb ← nonzeroFact? lb | return .unknown body
                      return .limit (← mkAppM ``HDiv.hDiv #[la, lb])
                        (← mkAppM ``Filter.Tendsto.div #[pa, pb, hlb])
                  | .unknown _ => return .unknown body
          | unknown => return unknown
      | (``Inv.inv, #[_, _, a]) =>
          match ← divergesAtTop? binder fuel a with
          | some pa =>
              return .limit (← realNumeral 0) (← mkAppM ``Filter.Tendsto.inv_tendsto_atTop #[pa])
          | none =>
              match ← recurse a with
              | .limit la pa =>
                  let some hla ← nonzeroFact? la | return .unknown body
                  return .limit (← mkAppM ``Inv.inv #[la])
                    (← mkAppM ``Filter.Tendsto.inv₀ #[pa, hla])
              | .unknown _ => return .unknown body
      | (``Real.exp, #[argument]) =>
          match ← divergesAtBot? binder fuel argument with
          | some pargument =>
              return .limit (← realNumeral 0)
                (← mkAppM ``Filter.Tendsto.comp #[mkConst ``Real.tendsto_exp_atBot, pargument])
          | none => return .unknown body
      | (``HPow.hPow, #[_, exponentType, _, _, base, exponent]) =>
          if base == binder && !dependsOn binder exponent && !exponentType.isConstOf ``Nat then
            match ← negativePowerLimit? binder exponent with
            | some proof => return .limit (← realNumeral 0) proof
            | none => return .unknown body
          return .unknown body
      | (``Real.arctan, #[argument]) =>
          let halfPi ← mkAppM ``HDiv.hDiv
            #[mkConst ``Real.pi,
              ← mkAppOptM ``OfNat.ofNat #[some (mkConst ``Real), some (mkRawNatLit 2), none]]
          if let some hargument ← divergesAtTop? binder fuel argument then
            let some arctanLimit ← arctanLimit? atTopReal halfPi
                (← `(tactic| exact Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds))
              | return .unknown body
            return .limit halfPi (← mkAppM ``Filter.Tendsto.comp #[arctanLimit, hargument])
          if let some hargument ← divergesAtBot? binder fuel argument then
            let lowerLimit ← mkAppM ``Neg.neg #[halfPi]
            let some arctanLimit ← arctanLimit? atBotReal lowerLimit
                (← `(tactic| exact Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds))
              | return .unknown body
            return .limit lowerLimit (← mkAppM ``Filter.Tendsto.comp #[arctanLimit, hargument])
          return .unknown body
      | _ => return .unknown body

/--
The limit at `+∞` of the function `fun t ↦ body` given by `body` in terms of the local
variable `binder`, as the pair of the limit value and a proof of
`Filter.Tendsto (fun t ↦ body) Filter.atTop (𝓝 limit)` whose type is stated exactly in that
form. Fails, naming the subterm without a recognised limit, when the structural analysis does
not cover the primitive.
-/
def limitAtTopOfBody (operation : String) (binder body : Expr) : TermElabM (Expr × Expr) := do
  let body ← instantiateMVars body
  match ← limitAtTop binder (body.sizeWithoutSharing + 1) body with
  | .limit limit proof =>
      let statement ← tendstoStatement binder body (← mkAppM ``nhds #[limit])
      let proof ← mkExpectedTypeHint proof statement
      unless ← isTypeCorrect proof do
        throwError "{operation} internal error: the limit evidence for the primitive is ill-typed"
      return (limit, proof)
  | .unknown subterm =>
      throwError
        "{operation} could not determine the limit at +∞ of the primitive: no decay shape \
         applies to{indentExpr subterm}\nThe primitive is{indentExpr body}"

end CAS.Tactic.Integration.Limits
