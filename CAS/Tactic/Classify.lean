/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Certificate.Relations
public import CAS.Expr.Syntax

/-!
# Structural classification for symbolic tactics

An elaborated goal is classified before a theorem-producing tactic route is
selected. The classification depends only on the proposition's head symbol and
on broad expression features. It does not inspect theorem names or encode
identities for particular expressions.

## Main definitions

* `GoalKind`, `goalKind`: the class of a goal by its outer logical form.
* `arithmeticFeatures`: the operator features by which the arithmetic phase chooses a procedure.
* `rationalLiteral?`: numeral syntax read as a rational number, a heuristic whose
  proof-producing callers prove any value they use.
* `analyticSideConditionHint?`: a diagnostic for goals with analytic domain conditions.

## Implementation notes

Classification produces no proof. It decides which checked engine to invoke,
and only the proof returned by that engine can close the goal. `goalKind` reads the head
symbol: `Set.EqOn`, `ResidualBound` and `ApproxOn` give a semantic goal, an equality one of whose
sides is a `Verified.Expr.eval` gives a reflected equality, then come ordinary equalities,
disequalities and order relations, and everything else is `.other`. The stages of the `cas`
pipeline (`CAS.ExactTactic`) run only on the kinds they accept, and the arithmetic phase
(`CAS.Tactic.Arithmetic`) chooses its finisher by the kind and by `arithmeticFeatures`.
-/

public meta section

namespace CAS.Tactic.Classify

open Lean Meta

/-- The broad structural class of a goal accepted by the exact computer algebra frontend. -/
inductive GoalKind where
  /-- A certificate proposition such as `Set.EqOn` or `ResidualBound`. -/
  | semantic
  /-- An equality one of whose sides is an evaluation of the checked symbolic evaluator. -/
  | reflectedEquality
  /-- An ordinary Lean equality. -/
  | equality
  /-- An ordinary Lean disequality. -/
  | disequality
  /-- An ordinary strict or non-strict order relation. -/
  | order
  /-- A proposition outside the goal language of the exact computer algebra frontend. -/
  | other
  deriving BEq, Repr

/-- Coarse operator features used to choose a Mathlib arithmetic procedure. -/
structure ArithmeticFeatures where
  /-- The target contains a local variable. -/
  hasVariables : Bool
  /-- The target contains division or inversion. -/
  hasDivision : Bool
  /-- The target contains multiplication or a natural power. -/
  hasNonlinearSyntax : Bool
  /-- The target contains an operator handled naturally by `positivity`. -/
  hasPositivitySyntax : Bool
  deriving BEq, Repr

private def hasAnyConstant (expression : Expr) (names : Array Name) : Bool :=
  let constants := expression.getUsedConstants
  names.any constants.contains

private def signExpression? (target : Expr) : Option Expr := do
  let (_, lhs, rhs) ← target.le? <|> target.lt? <|> target.ne?'
  if lhs.zero? then
    some rhs
  else if rhs.zero? then
    some lhs
  else
    none

/-- Whether a term is the evaluation `Verified.Expr.eval ρ e` of a checked expression. -/
def isCheckedEvaluation (term : Expr) : Bool :=
  term.consumeMData.isAppOfArity ``Verified.Expr.eval 3

private def rationalLiteralAux? : Nat → Expr → MetaM (Option ℚ)
  | 0, _ => pure none
  | fuel + 1, term => do
      let term := term.consumeMData
      -- `Expr.nat?` reads an `OfNat.ofNat` numeral of any type; `getNatValue?` would accept only
      -- natural-number numerals.
      if let some value := term.rawNatLit? then
        return some value
      if let some value := term.nat? then
        return some value
      match_expr term with
      | Neg.neg _ _ argument =>
          return (← rationalLiteralAux? fuel argument).map (- ·)
      | Inv.inv _ _ argument =>
          let some value ← rationalLiteralAux? fuel argument | return none
          return if value = 0 then none else some value⁻¹
      | HAdd.hAdd _ _ _ _ lhs rhs =>
          let some a ← rationalLiteralAux? fuel lhs | return none
          let some b ← rationalLiteralAux? fuel rhs | return none
          return some (a + b)
      | HSub.hSub _ _ _ _ lhs rhs =>
          let some a ← rationalLiteralAux? fuel lhs | return none
          let some b ← rationalLiteralAux? fuel rhs | return none
          return some (a - b)
      | HMul.hMul _ _ _ _ lhs rhs =>
          let some a ← rationalLiteralAux? fuel lhs | return none
          let some b ← rationalLiteralAux? fuel rhs | return none
          return some (a * b)
      | HDiv.hDiv _ _ _ _ lhs rhs =>
          let some a ← rationalLiteralAux? fuel lhs | return none
          let some b ← rationalLiteralAux? fuel rhs | return none
          return if b = 0 then none else some (a / b)
      | Nat.cast _ _ natural =>
          return (natural.consumeMData.nat? <|>
          natural.consumeMData.rawNatLit?).map fun n ↦ (n : ℚ)
      | Int.cast _ _ integer =>
          return (← getIntValue? integer).map fun z ↦ (z : ℚ)
      | Rat.cast _ _ rational => rationalLiteralAux? fuel rational
      | OfScientific.ofScientific _ _ mantissa sign exponent =>
          let some m := mantissa.consumeMData.rawNatLit? <|> mantissa.consumeMData.nat?
          | return none
          let some e := exponent.consumeMData.rawNatLit? <|> exponent.consumeMData.nat?
          | return none
          let sign := sign.consumeMData
          if sign.isConstOf ``Bool.true then
            return some (Rat.ofScientific m true e)
          else if sign.isConstOf ``Bool.false then
            return some (Rat.ofScientific m false e)
          else
            return none
      | _ => return none


/--
Read numeral syntax as rational arithmetic: literals, negation, inversion,
sums, differences, products, quotients, and casts from `ℕ`, `ℤ`, and `ℚ`.
Unsupported syntax and a zero divisor give `none`. This heuristic ignores the
term's type and operation instances; it is not a semantic evaluator for natural
subtraction, integer division, or arbitrary overloaded arithmetic. Proof-producing
callers must separately prove the proposed value, for example with `norm_num`.
-/
def rationalLiteral? (term : Expr) : MetaM (Option ℚ) :=
  rationalLiteralAux? (term.sizeWithoutSharing + 1) term

/-- Heuristic for suppressing routine nonzero numeral conditions in diagnostics.
This syntax check supplies no proof that the term is nonzero. -/
def isNonzeroNumeral (term : Expr) : MetaM Bool := do
  if term.hasFVar ∨ term.hasMVar then
    return false
  return match ← rationalLiteral? term with
    | some value => value ≠ 0
    | none => false

/-- Classify a fully elaborated proposition by its outer logical form. An equality is
*reflected* when one of its sides is the evaluation of a checked expression; an ordinary
identity that merely mentions the evaluator inside a derivative or another operation is an
ordinary equality, whose derivative subterms the identity route rewrites first. -/
def goalKind (target : Expr) : GoalKind :=
  let target := target.consumeMData
  let head := target.getAppFn.consumeMData
  if head.isConstOf ``Set.EqOn ||
      head.isConstOf ``Certificate.ResidualBound ||
      head.isConstOf ``Certificate.ApproxOn then
    .semantic
  else if let some (_, lhs, rhs) := target.eq? then
    if isCheckedEvaluation lhs || isCheckedEvaluation rhs then
      .reflectedEquality
    else
      .equality
  else if target.ne?'.isSome then
    .disequality
  else if target.le?.isSome || target.lt?.isSome then
    .order
  else
    .other

/-- Collect the inexpensive syntactic features used by arithmetic dispatch. -/
def arithmeticFeatures (target : Expr) : ArithmeticFeatures :=
  {
    hasVariables := target.hasFVar
    hasDivision := hasAnyConstant target #[``HDiv.hDiv, ``Inv.inv]
    hasNonlinearSyntax :=
      hasAnyConstant target #[``HMul.hMul, ``HPow.hPow, ``Pow.pow]
    hasPositivitySyntax :=
      (signExpression? target).any fun expression ↦
        hasAnyConstant expression
          #[``abs, ``norm, ``Real.exp, ``Real.sqrt, ``HPow.hPow, ``Pow.pow]
  }

private structure AnalyticTerms where
  denominators : Array Expr := #[]
  expLogArguments : Array Expr := #[]
  squareRootArguments : Array Expr := #[]

private def pushUnique (values : Array Expr) (value : Expr) : Array Expr :=
  if values.contains value then values else values.push value

private def collectAnalyticTerms
    (target : Expr) (terms : AnalyticTerms := {}) : AnalyticTerms :=
  let stripped := target.consumeMData
  let head := stripped.getAppFn.consumeMData
  let arguments := stripped.getAppArgs
  let terms :=
    if head.isConstOf ``HDiv.hDiv && arguments.size == 6 then
      { terms with denominators := pushUnique terms.denominators arguments[arguments.size - 1]! }
    else if head.isConstOf ``Inv.inv && arguments.size == 3 then
      { terms with denominators := pushUnique terms.denominators arguments[arguments.size - 1]! }
    else
      terms
  let terms :=
    if head.isConstOf ``Real.exp && arguments.size == 1 then
      let argument := arguments[arguments.size - 1]!.consumeMData
      let logArguments := argument.getAppArgs
      if argument.getAppFn.consumeMData.isConstOf ``Real.log && logArguments.size == 1 then
        { terms with
          expLogArguments :=
            pushUnique terms.expLogArguments logArguments[logArguments.size - 1]! }
      else
        terms
    else
      terms
  let terms :=
    if head.isConstOf ``Real.sqrt && arguments.size == 1 then
      { terms with
        squareRootArguments :=
          pushUnique terms.squareRootArguments arguments[arguments.size - 1]! }
    else
      terms
  match target with
  | .app function argument =>
      collectAnalyticTerms argument (collectAnalyticTerms function terms)
  | .lam _ type body _
  | .forallE _ type body _ =>
      collectAnalyticTerms body (collectAnalyticTerms type terms)
  | .letE _ type value body _ =>
      collectAnalyticTerms body
        (collectAnalyticTerms value (collectAnalyticTerms type terms))
  | .proj _ _ body => collectAnalyticTerms body terms
  | .mdata _ body => collectAnalyticTerms body terms
  | _ => terms

private def renderExpressions
    (expressions : Array Expr) (render : String → String) : MetaM (List String) :=
  expressions.toList.mapM fun expression ↦ do
    return render (← ppExpr expression).pretty

private def squareBase? (expression : Expr) : MetaM (Option Expr) := do
  let expression := expression.consumeMData
  let head := expression.getAppFn.consumeMData
  unless head.isConstOf ``HPow.hPow || head.isConstOf ``Pow.pow do
    return none
  let arguments := expression.getAppArgs
  unless 2 ≤ arguments.size do
    return none
  let exponent := arguments[arguments.size - 1]!
  unless (← getNatValue? exponent) == some 2 do
    return none
  return some arguments[arguments.size - 2]!

private def renderSquareRootConditions
    (expressions : Array Expr) : MetaM (List String) :=
  expressions.toList.mapM fun expression ↦ do
    let candidate := (← squareBase? expression).getD expression
    return s!"0 ≤ {(← ppExpr candidate).pretty}"

/--
User-facing hint for ordinary goals containing operations with analytic domain
conditions.

This is diagnostic metadata only. It does not add assumptions or participate
in proof construction. The displayed candidates come from the actual
elaborated denominator and branch subterms rather than from variable names or
formula-specific templates.

Two caveats for readers of the hint. First, the ordinary arithmetic route that
prints it never reifies the goal, so the `#cas [simplify]` report it points to
describes the conditions the checked normalizer would generate for the reified
expression, not conditions that were actually computed for this goal. Second, the
square-root candidates are rendered as `0 ≤ a`, which is what Mathlib's
`Real.sqrt_sq`-style lemmas need, whereas the reflective engine's `ValidAt`
requires the stronger `0 < a` for `sqrt a`.
-/
def analyticSideConditionHint? (target : Expr) : MetaM (Option String) := do
  let constants := target.getUsedConstants
  let hasLogarithm := constants.contains ``Real.log
  let hasSquareRoot := constants.contains ``Real.sqrt
  let terms := collectAnalyticTerms target
  -- A literal denominator such as the `4` of `1/4` is proved nonzero by `norm_num`; naming it
  -- as a candidate condition would send the reader after a hypothesis that does not exist, so
  -- numeral denominators are dropped and a goal whose only denominators are numerals gets no
  -- branch hint at all.
  let denominators ← terms.denominators.filterM fun denominator ↦
    return !(← isNonzeroNumeral denominator)
  let hasDivision :=
    !denominators.isEmpty ∧
      (constants.contains ``HDiv.hDiv || constants.contains ``Inv.inv)
  let requirements :=
    (if hasDivision then ["nonzero denominator hypotheses"] else []) ++
    (if hasLogarithm then
      ["appropriate logarithm-branch hypotheses (`x ≠ 0` gives `exp (log x) = |x|`; \
        use `0 < x` to remove the absolute value)"]
    else []) ++
    (if hasSquareRoot then ["nonnegative or positive square-root hypotheses"] else [])
  if requirements.isEmpty then
    return none
  else
    let denominatorConditions ←
      renderExpressions denominators fun expression ↦ s!"{expression} ≠ 0"
    let logarithmConditions ←
      renderExpressions terms.expLogArguments fun expression ↦
        s!"{expression} ≠ 0 (or 0 < {expression} for the positive branch)"
    let squareRootConditions ← renderSquareRootConditions terms.squareRootArguments
    let candidates :=
      (denominatorConditions ++ logarithmConditions ++ squareRootConditions).eraseDups
    let candidateHint :=
      if candidates.isEmpty then
        ""
      else
        s!" Detected candidate conditions: {", ".intercalate candidates}."
    return some s!"This goal contains branch-sensitive operations and may need {
      "; ".intercalate requirements}. Put those facts in the local context; \
      pass one explicit fact as `cas using h` when needed. The corresponding \
      `#cas [simplify]` report shows the exact generated conditions.{candidateHint}"

end CAS.Tactic.Classify
