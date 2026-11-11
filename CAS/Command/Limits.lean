/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.Limits
public import CAS.Command.Series
public meta import CAS.Calculus.Limits
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Limits at infinity, one-sided limits and poles

* `#cas [limit x → ∞] f` and `#cas [limit x → -∞] f` prove `Tendsto f atTop (𝓝 L)`,
  `Tendsto f atTop atTop` or `Tendsto f atTop atBot` (and the same at `atBot`), as
  Mathematica's `Limit[f, x -> Infinity]` returns `L`, `∞` or `-∞`.
* `#cas [limit x → a from above] f` and `from below` give one-sided limits at a rational point,
  finite or infinite.
* `#cas [limit x → a] (g / h)` at a pole, where the numerator vanishes to a lower order than
  the denominator, proves `Tendsto (g / h) (𝓝[≠] a) atTop` (or `atBot`) for a pole of even
  order and, for a pole of odd order, the two one-sided infinite limits of opposite signs:
  there is no two-sided limit, and Mathematica answers `Indeterminate`.

Other finite limits stay with `#cas [limit x → a]` of `CAS/Command/Series.lean`, and at infinity
an expression with `exp`, `log`, `sqrt`, `arctan`, `π` or `e` goes first to the asymptotic
comparison of `CAS/Command/AsymptoticLimits.lean`. The point is a closed expression of the
calculator with a rational value, such as `1/10000` or `-1/2`.

## Implementation notes

At infinity we write the expression as `N (t) / t ^ j` with `t = 1 / x` (`inversion` of
`CAS/Calculus/Limits.lean`), which handles rational functions by the comparison of degrees and
functions such as `x sin (1 / x)` or `x (exp (1 / x) - 1)` through the Taylor expansion of `N` at
`0`; `tendsto_of_inversion` carries the one-sided limit at `0` back to `x`. Finite limits are
exact rationals, from the leading Taylor coefficients of numerator and denominator
(`tendsto_div_of_check`, `tendsto_div_side_of_check`), and a one-sided limit at a point of
validity is the value there (`tendsto_side_of_validIteratesOn`). Infinite limits come from
`tendsto_div_pole_of_check` and `tendsto_div_pole_two_sided_of_check`, with the sign proposed by
`poleUp`. The leading terms are found in meta code from the exact values of the symbolic
derivatives (`leadingTerms`), and the kernel decides the check in the hypothesis of each theorem
(`withCheck`). The numerator and the denominator need to be valid at the point only, as the
domain checker certifies it on `[a, a]` (`Series.validityAt`) and the theorems extend it to a
neighbourhood.

The derivatives are computed with `y / 0 = 0` as in Lean, so they describe the function only where
it is valid. We certify the validity and the leading terms before a limit or a pole is stated: for
`1 / (x + x / x)` at `0` the derivatives suggest a pole of order `1`, but `x / x` is not valid at
`0`, and the domain checker refuses the denominator. Bare `cas` uses `quotientTheorem` and
`inversionTheorem` for `Tendsto` goals too (`CAS/Command/Goals.lean`).
-/

public meta section

namespace CAS.Command.Limits

open Lean Elab Command Meta
open CAS.Command.InfoView
open CAS.Command.SpecialFunctions
open CAS.Command.Series
open CAS.Verified.Expr

/-- The limit point. -/
inductive Point where
  | finite (a : ℚ) (above : Option Bool)
  | infinity (positive : Bool)

/-- A limit that a theorem proves: a rational number, a real constant, `atTop` or `atBot`. -/
inductive LimitValue where
  | finite (q : ℚ)
  | real (value : Lean.Expr)
  | top
  | bot

/-- The limit in messages, with the filter names of Lean for the infinite limits. -/
def LimitValue.describe : LimitValue → MessageData
  | .finite q => m!"{q}"
  | .real value => m!"{value}"
  | .top => "atTop"
  | .bot => "atBot"

/-- The limit as the reports print it. -/
def LimitValue.render : LimitValue → MetaM String
  | .finite q => pure (toString q)
  | .real value => return toString (← ppExpr value)
  | .top => pure "∞"
  | .bot => pure "-∞"

/-- The leading terms `c (x - a) ^ k` and `d (x - a) ^ m` of the numerator and the denominator of
a quotient at a zero `a` of the denominator: a pole of order `m - k` when `k < m`, and otherwise
the finite limit `c / d` from the terms of order `m`, where `c = 0` when the numerator vanishes
to a higher order. -/
inductive LeadingTerms where
  | pole (k m : Nat) (c d : ℚ)
  | finite (m : Nat) (c d : ℚ)

/-- The kind of limit as the reports print it. -/
def LeadingTerms.kind : LeadingTerms → String
  | .pole k m _ _ => s!"infinite limit at a pole of order {m - k}"
  | .finite m _ _ => s!"exact limit from the terms of order {m}"

/-- The leading terms of `num / den` at a zero `a` of `den`, from the exact values of the
symbolic derivatives. The first nonzero derivative of the denominator at `a` has order at most
`12`. -/
def leadingTerms (operation : String) (num den : Verified.Expr (Fin 1)) (a : ℚ) :
    MetaM LeadingTerms := do
  let some (m, denValue) := order? den a 12
    | throwError "{operation}: the denominator has no nonzero derivative of order at most 12 at \
        {a} that is an exact rational number"
  let d := denValue / m.factorial
  let numerator (k : Nat) : MetaM ℚ := do
    let some value := derivativeAt num k a
      | throwError "{operation}: the exact evaluator could not evaluate the symbolic derivative \
          of order {k} of the numerator at {a} to a rational number"
    return value
  for k in [0:m] do
    let value ← numerator k
    unless value == 0 do
      return .pole k m (value / k.factorial) d
  return .finite m ((← numerator m) / m.factorial) d

/-- `partialProof` applied to the kernel check of its first hypothesis, a decidable statement
such as `leadingCheck … = true`. -/
def withCheck (operation : String) (partialProof : Lean.Expr) : MetaM Lean.Expr := do
  let .forallE _ check _ _ ← whnfR (← inferType partialProof)
    | throwError "{operation}: unexpected certificate theorem shape"
  return mkApp partialProof (← CAS.Tactic.KernelReadBack.decideByKernel operation check)

/-- The limit of `num / den` at a zero `a` of `den` with the leading terms `leading`, on the side
`above` (`true` for `𝓝[>] a`) or on `𝓝[≠] a` when `above` is `none`: a finite limit, or `atTop`
or `atBot` at a pole. The validity at `a` and the leading terms are checked first. At a pole of
odd order with `above = none` it proves the two one-sided limits, `atTop` on one side and `atBot`
on the other, and then fails, as there is no limit on `𝓝[≠] a`. -/
def quotientTheorem (operation : String) (num den : Verified.Expr (Fin 1)) (a : ℚ)
    (leading : LeadingTerms) (above : Option Bool) : MetaM (Lean.Expr × LimitValue) := do
  let quotedNum ← quoteVerifiedExpr num
  let quotedDen ← quoteVerifiedExpr den
  match leading with
  | .pole k m c d =>
      let j := m - k
      let common := #[quotedNum, quotedDen, toExpr k, toExpr m, ← quoteRat a,
        ← requireValidityAt operation "numerator" quotedNum (k + 1) a,
        ← requireValidityAt operation "denominator" quotedDen (m + 1) a, ← quoteRat c,
        ← quoteRat d]
      let side (s : Bool) : MetaM (Lean.Expr × LimitValue) := do
        let up := poleUp (c / d) j s
        let proof ← withCheck operation
          (← mkAppM ``tendsto_div_pole_of_check (common ++ #[toExpr s, toExpr up]))
        return (proof, if up then .top else .bot)
      match above with
      | some s => side s
      | none =>
          if j % 2 == 1 then
            let (_, right) ← side true
            let (_, left) ← side false
            throwError "{operation}: {a} is a pole of odd order {j}; the route proves the limit \
              {right.describe} on `𝓝[>] {a}` and {left.describe} on `𝓝[<] {a}`, so there is no \
              limit on `𝓝[≠] {a}`"
          let up := decide (0 < c / d)
          let proof ← withCheck operation
            (← mkAppM ``tendsto_div_pole_two_sided_of_check (common.push (toExpr up)))
          return (proof, if up then .top else .bot)
  | .finite m c d =>
      let common := #[quotedNum, quotedDen, toExpr m, ← quoteRat a,
        ← requireValidityAt operation "numerator" quotedNum (m + 1) a,
        ← requireValidityAt operation "denominator" quotedDen (m + 1) a, ← quoteRat c,
        ← quoteRat d, ← quoteRat (c / d)]
      let partialProof ← match above with
        | some s => mkAppM ``tendsto_div_side_of_check (common.push (toExpr s))
        | none => mkAppM ``tendsto_div_of_check common
      return (← withCheck operation partialProof, .finite (c / d))

/-- The limit of `expr` at `+∞` (`positive`) or `-∞` by the substitution `x = 1 / t`, where
`name` is the variable: `inversion` writes `expr (1 / t)` as `N (t) / t ^ j`, whose limit as
`t → 0` from the side of `positive` is the limit of `expr` (`tendsto_of_inversion`). Returns the
theorem, the limit and the leading terms of `N (t) / t ^ j` at `0`. -/
def inversionTheorem (operation name : String) (expr : Verified.Expr (Fin 1)) (positive : Bool) :
    MetaM (Lean.Expr × LimitValue × LeadingTerms) := do
  let some (N, j) := inversion expr
    | throwError "{operation}: the expression is not built from {name} by field operations and \
        functions of arguments with a finite limit"
  let den : Verified.Expr (Fin 1) := .pow (.var 0) j
  let leading ← leadingTerms operation N den 0
  let (inner, value) ← quotientTheorem operation N den 0 leading (some positive)
  let partialProof ← mkAppM ``tendsto_of_inversion
    #[← quoteVerifiedExpr expr, ← quoteVerifiedExpr N, toExpr j]
  return (← mkAppM' (← withCheck operation partialProof) #[toExpr positive, inner], value,
    leading)

/-- The theorem for a quotient at a zero `a` of its denominator, on a side or from both sides when
`above` is `none`, with the rendered value and the kind of limit. At a pole of odd order the
theorem is the conjunction of the two one-sided limits; a finite limit from both sides is left to
`#cas [limit x → a]` of `CAS.Command.Series`. -/
def quotientLimit (input : Syntax) (num den : Verified.Expr (Fin 1)) (a : ℚ)
    (above : Option Bool) : CommandElabM (Lean.Expr × String × String) := withRef input do
  let leading ← liftTermElabM (leadingTerms "limit" num den a)
  match leading with
  | .pole k m _ _ =>
      if above.isNone && (m - k) % 2 == 1 then
        liftTermElabM do
          let (right, valueRight) ← quotientTheorem "limit" num den a leading (some true)
          let (left, valueLeft) ← quotientTheorem "limit" num den a leading (some false)
          return (← mkAppM ``And.intro #[right, left],
            s!"Indeterminate ({← valueRight.render} from above, {← valueLeft.render} from \
              below)", s!"no two-sided limit: a pole of order {m - k}")
      else
        liftTermElabM do
          let (proof, value) ← quotientTheorem "limit" num den a leading above
          return (proof, ← value.render, leading.kind)
  | .finite .. =>
      let some _ := above | throwUnsupportedSyntax
      liftTermElabM do
        let (proof, value) ← quotientTheorem "limit" num den a leading above
        return (proof, ← value.render, leading.kind)

/-- Restate a limit proof in ordinary notation, with closed numerals evaluated. -/
def clean (proof : Lean.Expr) : MetaM Lean.Expr := do
  let proof ← Digits.cleanProof proof (seriesCleanLemmas ++ [``Rat.cast_zero,
      ``Bool.false_eq_true, ``eq_self_iff_true])
    [``Verified.Expr.univariateEval, ``Verified.Expr.side] (simprocs := true)
  Digits.evaluateNumerals proof

/-- Run a limit command. -/
def logLimit (ref : Syntax) (coordinate : TSyntax `ident) (point : Point) (input : Syntax) :
    CommandElabM Unit := do
  let (reified, expr) ← parseUnivariate coordinate input
  let name := renderName coordinate.getId
  let (proof, value, kind, domain) ← match point with
    | .finite a above =>
        let sideText := match above with
          | some true => s!"{name} → {a}⁺"
          | some false => s!"{name} → {a}⁻"
          | none => s!"{name} → {a}, {name} ≠ {a}"
        match expr with
        | .div num den =>
            if derivativeAt den 0 a == some 0 then
              let (proof, value, kind) ← quotientLimit input num den a above
              pure (proof, value, kind, sideText)
            else continuity expr a above sideText reified
        | _ => continuity expr a above sideText reified
    | .infinity positive =>
        let (proof, value, leading) ← withRef input <| liftTermElabM <|
          inversionTheorem "limit" name expr positive
        pure (proof, ← liftTermElabM value.render, leading.kind,
          if positive then s!"{name} → ∞" else s!"{name} → -∞")
  let proof ← liftTermElabM (clean proof)
  let report ← liftTermElabM do
    evidenceReportMessage
      #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
        "Limit" proof]
  logReport ref {
    domain
    input := reified.render
    inputType := "scalar ℝ"
    output := value
    outputType := kind
  } #[report]
where
  /-- One-sided continuity at a point of validity. -/
  continuity (expr : Verified.Expr (Fin 1)) (a : ℚ) (above : Option Bool) (domain : String)
      (reified : ReifiedExpr) : CommandElabM (Lean.Expr × String × String × String) := do
    let some s := above | throwUnsupportedSyntax
    let proof ← liftTermElabM do
      let quoted ← quoteVerifiedExpr expr
      mkAppM ``tendsto_side_of_validIteratesOn
        #[quoted, ← quoteRat a, ← requireValidityAt "limit" "expression" quoted 1 a, toExpr s]
    let value := match derivativeAt expr 0 a with
      | some q => toString q
      | none =>
          let closed := expr.mapVars fun _ ↦ (.rat a.num a.den : Verified.Expr (Fin 1))
          (FullSimplify.Form.ofExpr reified.names closed).render
    return (proof, value, "limit, the value at the point", domain)

end CAS.Command.Limits

namespace CAS.Command

open Lean Elab Command

/-- `#cas [limit x → ∞] e` is the limit of `e` as `x` tends to `∞`, with the theorem
`Tendsto (fun x ↦ e) atTop (𝓝 L)`, or `atTop`, `atBot` in place of `𝓝 L` for an infinite limit;
see `#cas [limit x → a]`. The expression is written in `t = 1 / x` and expanded at `t = 0`.
-/
syntax (name := casLimitAtTopCommand) "#cas" "[" &"limit" ident " → " "∞" "]" term : command

/-- `#cas [limit x → -∞] e` is the limit of `e` as `x` tends to `-∞`, with the filter `atBot` in
place of `atTop`; see `#cas [limit x → ∞]` and `#cas [limit x → a]`.
-/
syntax (name := casLimitAtBotCommand) "#cas" "[" &"limit" ident " → " "-" "∞" "]" term :
  command

/-- `#cas [limit x → a from above] e` and `#cas [limit x → a from below] e` are the one-sided limits
at the rational point `a`, finite or infinite, with the filters `𝓝[>] a` and `𝓝[<] a`; see
`#cas [limit x → a]`.
-/
syntax (name := casLimitSideCommand)
  "#cas" "[" &"limit" ident " → " term " from " (&"above" <|> &"below") "]" term : command

elab_rules : command
  | `(#cas [limit $x:ident → ∞] $expr:term) =>
      Limits.logLimit expr x (.infinity true) expr
  | `(#cas [limit $x:ident → - ∞] $expr:term) =>
      Limits.logLimit expr x (.infinity false) expr
  | `(#cas [limit $x:ident → $a:term from above] $expr:term) => do
      Limits.logLimit expr x (.finite (← SpecialFunctions.parseRational "limit" a) (some true))
        expr
  | `(#cas [limit $x:ident → $a:term from below] $expr:term) => do
      Limits.logLimit expr x (.finite (← SpecialFunctions.parseRational "limit" a) (some false))
        expr
  | `(#cas [limit $x:ident → $a:term] $expr:term) => do
      Limits.logLimit expr x (.finite (← SpecialFunctions.parseRational "limit" a) none)
        expr

end CAS.Command
