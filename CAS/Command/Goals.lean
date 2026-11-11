/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.AsymptoticLimits
public meta import CAS.Command.AsymptoticLimits
public import CAS.Command.Reduce
public meta import CAS.Command.Reduce
public import CAS.Polynomial.RealRoot.RootCount
public meta import CAS.Polynomial.RealRoot.RootCount
public meta import CAS.Tactic.RouteRegistry
public import CAS.Command.AlgebraGoals
public meta import CAS.Command.AlgebraGoals
public import CAS.Command.FindRoot
public meta import CAS.Command.FindRoot

/-!
# Closing goals with the theorems of the `#cas` commands

Some `#cas` commands prove theorems that are natural tactic goals. `route`, the `command` route
of bare `cas`, recognizes those goals, computes the certificate in compiled code exactly as the
command does, checks it in the kernel (`KernelReadBack.decideByKernel`), and transports the
command's theorem to the goal through proved identities between the checked expression and the
goal's own terms. The goals are limits, polynomial sign conditions, counts and existence of real
roots, and the goals of the algebra, matrix and number theory commands.

## Main definitions

* `CAS.Command.Goals.route`: the route of bare `cas` for these goals, registered under `command`.
* `CAS.Command.Goals.closeLimit`: a limit `Filter.Tendsto f l m` at a rational point or at
  infinity.
* `CAS.Command.Goals.closeSign`: a polynomial sign condition on `ℝ` or on `Set.Icc a b`.
* `CAS.Command.Goals.closeRootCount`: a count of distinct real roots.
* `CAS.Command.Goals.closeRootExistence`, `CAS.Command.Goals.closeFindRoot`: a root in stated
  bounds, from the root list or from the certificate of `#cas [findRoot]`.

## Implementation notes

The route closes these goals:

* limits `Filter.Tendsto f l m`, with `m` one of `𝓝 L`, `atTop` and `atBot`, as the limit
  commands compute them. At a rational point, with `l` the punctured neighbourhood `𝓝[≠] a`, a
  side `𝓝[>] a` or `𝓝[<] a`, or `𝓝 a`: from the leading Taylor coefficients of a quotient whose
  denominator vanishes at `a`, a finite limit or an infinite one at a pole
  (`Limits.quotientTheorem`), or by continuity at a point of validity
  (`tendsto_of_validIteratesOn`). At `l = atTop` or `atBot`: by asymptotic comparison
  (`AsymptoticLimits.asymptoticTheorem`) or by the substitution `x = 1 / t`
  (`Limits.inversionTheorem`). The stated limit must equal the computed one;
* sign conditions `∀ x : ℝ, p x ≤ q x` (or `<`, `≥`, `>`) for polynomials with rational
  coefficients, and the same relation in one free real variable, as `#cas [reduce x]` decides
  them: the complete root list with signs at cuts between the roots (`reduceCheck`), positive at
  every cut (`nonneg_of_reduceCheck`), and without roots for a strict relation
  (`pos_of_reduceCheck`); on an interval, `∀ x ∈ Set.Icc a b, p x ≤ q x` with rational numerals
  `a` and `b`, the root list has `a` and `b` as cell boundaries and only the gaps that meet
  `[a, b]` need a positive cut (`nonneg_on_Icc_of_reduceCheck`, `pos_on_Icc_of_reduceCheck`);
* counts of distinct real roots `Fintype.card (p.rootSet ℝ) = n` for a polynomial `p` over `ℚ` or
  `ℤ` written with `X`, numerals and ring operations, from the root list of `#cas [roots x]`
  (`card_rootSet_of_exprRootCheck`);
* existence of a root in an interval, `∃ x : ℝ, p x = q x ∧ c < x ∧ x ≤ d` (any conjunction of
  one polynomial equation with bounds of `x` by rational numerals), from an isolating interval or
  an exact rational root of the root list (`of_exprRootCheck`); for other one-variable
  equations, and for `∃! x, x ∈ Set.Icc a b ∧ f x = g x`, from the certificate of
  `#cas [findRoot]` (`Verified.Expr.existsUnique_root_of_rootCheck`);
* the goals of the algebra, matrix and number theory commands (polynomial gcds and divisions in
  `ℚ[X]`, inverses, ranks and characteristic polynomials of matrix literals, modular powers,
  inverses in `ZMod m`, Jacobi symbols, finite sums and products, Gamma values), by
  `CAS.Command.AlgebraGoals.close`.

Every proof is an ordinary term: the certificate checks are kernel evaluations, and the identity
between the checked expression and the goal's term is proved by the lowering bridge of
`CAS.Tactic.DerivativeBridge`, so a reification that does not denote the goal's function
fails instead of proving something else.

The limit, sign and root goals have one real variable, and their points, coefficients and
bounds are rational. Validity of a limit's expressions is certified at the point itself, since
it persists on a neighbourhood (`Verified.Expr.eventually_validIterates`). The searches are
bounded: a vanishing denominator needs a nonzero derivative of order at most 12 at the point,
and a root in stated bounds is looked for in the root list refined to 20 decimals. Only a
certified limit or root count that differs from the stated one is reported as wrong; every other
failure names the step that did not succeed and disproves nothing.
-/

public meta section

namespace CAS.Command.Goals

open Lean Elab Tactic Meta
open CAS.Polynomial CAS.Polynomial.RealRoot
open CAS.Command.SpecialFunctions (quoteRat)
open CAS.Tactic
open CAS.Tactic.KernelReadBack (decideByKernel)

/-! ## Reification in one variable -/

/-- Reflect `term`, a real expression in the variable `x` alone, as a checked expression over
`Fin 1`. Fails when the term mentions anything but `x`, numerals, and the operations of the
checked language. -/
def reifyIn (x term : Expr) : MetaM (Verified.Expr (Fin 1)) := do
  let config : Elaboration.RealExpression.Config := { operation := "cas", coordinates := #[x] }
  let reification ← Elaboration.RealExpression.reify config term
  unless reification.dimension == 1 do
    throwError "cas: the expression depends on more than the variable {x}"
  let some expression ← reification.toVerifiedExpr?
    | throwError "cas: an exponent of the expression is not a numeral"
  if h : reification.dimension = 1 then
    return cast (by rw [h]) expression
  throwError "cas: the expression depends on more than the variable {x}"

/-- Prove `∀ y : ℝ, quoted.eval ![y] = f y` with the lowering bridge. -/
def bridge (quoted f : Expr) : MetaM Expr := do
  let statement ← withLocalDeclD `y (mkConst ``Real) fun y ↦ do
    let environment ← Tactic.RealExpression.parameterVector #[y]
    let evaluation ← mkAppM ``Verified.Expr.eval #[environment, quoted]
    mkForallFVars #[y] (← mkEq evaluation (mkApp f y).headBeta)
  let goal ← mkFreshExprSyntheticOpaqueMVar statement
  let lowering ← Tactic.DerivativeBridge.loweringBridgeSyntax
  let remaining ←
    try
      KernelReadBack.withSuppressedMessagesMeta <|
        KernelReadBack.runTacticOnGoal goal.mvarId! (← `(tactic| (intro; $lowering:tactic)))
    catch _ =>
      throwError "cas could not identify the checked expression with the goal's function"
  unless remaining.isEmpty do
    throwError "cas could not identify the checked expression with the goal's function"
  -- A proof by `rfl` has type `e = e`; the hint keeps the statement, which `rw` reads.
  mkExpectedTypeHint (← instantiateMVars goal) statement

/-- Prove a closed proposition about numerals, or an equality of filters at a rational point,
with `norm_num` (unfolding the one-sided filter `Verified.Expr.side`). -/
def proveByNormNum (description : String) (proposition : Expr) : MetaM Expr := do
  let goal ← mkFreshExprSyntheticOpaqueMVar proposition
  let remaining ←
    try
      KernelReadBack.withSuppressedMessagesMeta <|
        KernelReadBack.runTacticOnGoal goal.mvarId!
          (← `(tactic| norm_num [Verified.Expr.side]))
    catch _ => throwError "cas could not prove {description}:{indentExpr proposition}"
  unless remaining.isEmpty do
    throwError "cas could not prove {description}:{indentExpr proposition}"
  mkExpectedTypeHint (← instantiateMVars goal) proposition

/-- Apply `partialProof` to kernel checks of its leading hypotheses, `count` of them, each a
decidable statement such as `reduceCheck … = true`. -/
def applyChecks (operation : String) (partialProof : Expr) (count : Nat) : MetaM Expr := do
  let mut proof := partialProof
  for _ in [:count] do
    let .forallE _ hypothesis _ _ ← whnfR (← inferType proof)
      | throwError "{operation}: unexpected certificate theorem shape"
    proof := mkApp proof (← decideByKernel operation hypothesis)
  return proof

/-- The real numeral of a rational. -/
def realOfRat (q : ℚ) : MetaM Expr := do
  let real := mkConst ``Real
  let numerator ← mkNumeral real q.num.natAbs
  let numerator ← if q.num < 0 then mkAppM ``Neg.neg #[numerator] else pure numerator
  if q.den = 1 then return numerator
  mkAppM ``HDiv.hDiv #[numerator, ← mkNumeral real q.den]

/-- A list of rationals as a term of type `List ℚ`. -/
def quoteRats (values : List ℚ) : MetaM Expr := do
  mkListLit (mkConst ``Rat) (← values.mapM quoteRat)

/-- The rational `((q : ℚ) : ℝ)`. -/
def ratCast (q : ℚ) : MetaM Expr := do
  mkAppOptM ``Rat.cast #[some (mkConst ``Real), none, some (← quoteRat q)]

/-! ## Limits -/

/-- The filter of a limit point: the neighbourhood, the punctured neighbourhood, or a side. -/
inductive Approach where
  | full
  | punctured
  | side (above : Bool)

/-- The point and approach of a filter `𝓝 a`, `𝓝[≠] a`, `𝓝[>] a`, or `𝓝[<] a`. -/
def approach? (filter : Expr) : MetaM (Option (Expr × Approach)) := do
  let filter := filter.consumeMData
  if filter.isAppOfArity ``nhds 3 then
    return some (filter.appArg!, .full)
  unless filter.isAppOfArity ``nhdsWithin 4 do
    return none
  let point := filter.getAppArgs[2]!
  let set := filter.getAppArgs[3]!.consumeMData
  let samePoint (e : Expr) : MetaM Bool := isDefEq e point
  if set.isAppOfArity ``Compl.compl 3 then
    let inner := set.appArg!.consumeMData
    if inner.isAppOfArity ``Singleton.singleton 4 && (← samePoint inner.appArg!) then
      return some (point, .punctured)
  if set.isAppOfArity ``Set.Ioi 3 && (← samePoint set.appArg!) then
    return some (point, .side true)
  if set.isAppOfArity ``Set.Iio 3 && (← samePoint set.appArg!) then
    return some (point, .side false)
  return none

/-- Why `norm_num` could not identify the certified limit `value` with the goal's filter `target`.
A different rational limit, or a different kind of limit, is wrong; another stated value may only
be unrecognized. -/
def limitMismatch (value : Limits.LimitValue) (target : Expr) : MetaM MessageData := do
  if target.isAppOfArity ``nhds 3 then
    let stated := target.appArg!
    match value, ← Tactic.Classify.rationalLiteral? stated with
    | .finite q, some L =>
        if q != L then return m!"cas limit route: the limit is {q}, not {L}"
    | .top, _ | .bot, _ =>
        return m!"cas limit route: the limit is {value.describe}, not {stated}"
    | _, _ => pure ()
    return m!"cas limit route: the limit is {value.describe}; norm_num could not identify it \
      with{indentExpr stated}"
  let top := target.isAppOfArity ``Filter.atTop 2
  match value with
  | .top | .bot =>
      if (value matches .top) == top then
        return m!"cas limit route: the limit is {value.describe}; norm_num could not identify \
          the filters"
  | _ => pure ()
  return m!"cas limit route: the limit is {value.describe}, not {if top then "atTop" else "atBot"}"

/-- Restate `limitProof : Tendsto F l m`, where `F` is the checked expression of the goal's
function (`hf`), or the quotient of its numerator and denominator when `quotient` is set, as the
goal `Tendsto f source target`. -/
def transport (limitProof : Expr) (value : Limits.LimitValue) (hf source target : Expr)
    (quotient : Bool) : MetaM Expr := do
  let #[_, _, _, l, m] := (← whnfR (← inferType limitProof)).getAppArgs
    | throwError "cas limit route: unexpected limit theorem shape"
  let hl ← proveByNormNum "the limit point" (← mkEq l source)
  let hm ← try proveByNormNum "the limit" (← mkEq m target)
    catch _ => throwError (← limitMismatch value target)
  mkAppM (if quotient then ``Verified.Expr.tendsto_div_of_univariateEval
    else ``Verified.Expr.tendsto_of_univariateEval) #[limitProof, hf, hl, hm]

/-- A theorem `Tendsto (fun x ↦ univariateEval expr x) l m` at `l = atTop` (`positive`) or
`atBot`, with its limit, as `#cas [limit x → ∞]` proves it: by asymptotic comparison when the
expression has `exp`, `log`, `sqrt`, `arctan`, `π` or `e`, and otherwise, or when the comparison
fails, by the substitution `x = 1 / t`. -/
def limitAtInfinity (expr : Verified.Expr (Fin 1)) (positive : Bool) :
    TermElabM (Expr × Limits.LimitValue) := do
  let substitution : TermElabM (Expr × Limits.LimitValue) := do
    let (proof, value, _) ←
      Limits.inversionTheorem "cas limit route" "the variable" expr positive
    return (proof, value)
  unless AsymptoticLimits.transcendental expr do return ← substitution
  let saved ← saveState
  try
    let (proof, value, _) ← AsymptoticLimits.asymptoticTheorem expr positive
    return (proof, value)
  catch asymptotic =>
    saved.restore
    try substitution
    catch inversion =>
      throwError "cas limit route: neither route proved the limit at \
        {if positive then "atTop" else "atBot"}.\nAsymptotic comparison:\
        {indentD asymptotic.toMessageData}\nSubstitution x = 1 / t:\
        {indentD inversion.toMessageData}"

/-- Close `Filter.Tendsto f l m` for a real function `f`, where `l` is `atTop`, `atBot` or a
filter at a rational point and `m` is `𝓝 L`, `atTop` or `atBot`. Returns the theorem that
restates the computed limit for the goal. -/
def closeLimit : TacticM Name := withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOfArity ``Filter.Tendsto 5 do
    throwError "cas limit route expected a `Filter.Tendsto` goal"
  let arguments := target.getAppArgs
  let real := mkConst ``Real
  unless (← isDefEq arguments[0]! real) && (← isDefEq arguments[1]! real) do
    throwError "cas limit route proves limits of real functions of a real variable"
  let function := arguments[2]!
  let source := arguments[3]!.consumeMData
  let limit := arguments[4]!.consumeMData
  unless limit.isAppOfArity ``nhds 3 || limit.isAppOfArity ``Filter.atTop 2 ||
      limit.isAppOfArity ``Filter.atBot 2 do
    throwError "cas limit route proves limits `𝓝 L`, `atTop` and `atBot`"
  let reify : TacticM (Verified.Expr (Fin 1) × Expr × Expr) := do
    let expr ← withLocalDeclD `x real fun x ↦ reifyIn x (mkApp function x).headBeta
    let quoted ← Command.quoteVerifiedExpr expr
    return (expr, quoted, ← bridge quoted function)
  let infinity? : Option Bool :=
    if source.isAppOfArity ``Filter.atTop 2 then some true
    else if source.isAppOfArity ``Filter.atBot 2 then some false else none
  if let some positive := infinity? then
    let (expr, _, hf) ← reify
    let (limitProof, value) ← limitAtInfinity expr positive
    goal.assign (← transport limitProof value hf source limit false)
    replaceMainGoal []
    return ``Verified.Expr.tendsto_of_univariateEval
  let some (point, approach) ← approach? source
    | throwError "cas limit route expected the filter `𝓝 a`, `𝓝[≠] a`, `𝓝[>] a`, `𝓝[<] a`, \
        `atTop` or `atBot`"
  let some a ← Tactic.Classify.rationalLiteral? point
    | throwError "cas limit route: the limit point{indentExpr point}\nis not a rational number"
  let (expr, quoted, hf) ← reify
  let quotient? : Option (Verified.Expr (Fin 1) × Verified.Expr (Fin 1)) :=
    match expr with
    | .div num den => if Series.derivativeAt den 0 a == some 0 then some (num, den) else none
    | _ => none
  let (proof, transfer) ← match quotient?, approach with
    | some (_, den), .full =>
        throwError "cas limit route: the denominator{indentExpr (← Command.quoteVerifiedExpr den)}\
          \nvanishes at {a}; the limit of the quotient is taken on `𝓝[≠] {a}`, where Lean's value \
          at the point does not count"
    | some (num, den), _ =>
        -- The leading terms come from the exact values of the symbolic derivatives, which
        -- describe the function only where it is valid; `quotientTheorem` certifies the
        -- validity and the leading terms before it states a limit or a pole.
        let above := match approach with
          | .side above => some above
          | _ => none
        let leading ← Limits.leadingTerms "cas limit route" num den a
        let (limitProof, value) ← Limits.quotientTheorem "cas limit route" num den a leading above
        pure (← transport limitProof value hf source limit true,
          ``Verified.Expr.tendsto_div_of_univariateEval)
    | none, _ =>
        let continuity ← mkAppM ``Verified.Expr.tendsto_of_validIteratesOn #[quoted,
          ← quoteRat a, ← Series.requireValidityAt "cas limit route" "function" quoted 1 a]
        unless limit.isAppOfArity ``nhds 3 do
          throwError "cas limit route: the function is continuous at {a}, so its limit there is \
            its value, not {if limit.isAppOfArity ``Filter.atTop 2 then "atTop" else "atBot"}"
        let stated := limit.appArg!
        -- The value: `expr` at `a`, through the bridge to the goal's function.
        let cast ← ratCast a
        let value ← mkAppM ``Verified.Expr.univariateEval #[quoted, cast]
        let valueGoal ← mkFreshExprSyntheticOpaqueMVar (← mkEq value stated)
        let hfSyntax ← Term.exprToSyntax hf
        let remaining ←
          try
            KernelReadBack.withSuppressedMessagesMeta <|
              KernelReadBack.runTacticOnGoal valueGoal.mvarId! (← `(tactic|
                (rw [Verified.Expr.univariateEval_eq_eval, $hfSyntax:term]; norm_num)))
          catch _ =>
            throwError "cas limit route: the function is continuous at {a}; norm_num could not \
              identify its value there with{indentExpr stated}"
        unless remaining.isEmpty do
          throwError "cas limit route: the function is continuous at {a}; norm_num could not \
            identify its value there with{indentExpr stated}"
        let hL ← mkCongrArg (← mkAppOptM ``nhds #[real, none]) (← instantiateMVars valueGoal)
        let nhdsCast ← mkAppM ``nhds #[cast]
        let hl ← proveByNormNum "the limit point" (← mkEq nhdsCast (← mkAppM ``nhds #[point]))
        let atPoint ← mkAppM ``Verified.Expr.tendsto_of_univariateEval #[continuity, hf, hl, hL]
        let proof ← match approach with
          | .full => pure atPoint
          | _ => mkAppM ``Filter.Tendsto.mono_left #[atPoint, ← mkAppOptM ``nhdsWithin_le_nhds
              #[none, none, some point, some source.getAppArgs[3]!]]
        pure (proof, ``Verified.Expr.tendsto_of_univariateEval)
  goal.assign proof
  replaceMainGoal []
  return transfer

/-! ## Sign conditions -/

/-- The relation `lhs ≤ rhs` or `lhs < rhs` of an order goal over `ℝ`, after unfolding `≥` and
`>`, with whether it is strict. -/
def relation? (target : Expr) : MetaM (Option (Expr × Expr × Bool)) := do
  let target ← whnfR target
  if let some (type, lhs, rhs) := target.le? then
    if ← isDefEq type (mkConst ``Real) then return some (lhs, rhs, false)
  if let some (type, lhs, rhs) := target.lt? then
    if ← isDefEq type (mkConst ``Real) then return some (lhs, rhs, true)
  return none

/-- The certificate terms `cert`, `locs`, `cuts`, `signs` of `reduceCheck`. -/
def quoteRootData (data : Reduce.RootData) : MetaM (Expr × Expr × Expr × Expr) := do
  return (← Roots.quoteCertificate 20 data.cert, ← Reduce.quoteLocs data.locs,
    ← quoteRats data.cuts,
    ← mkListLit (mkConst ``Bool) (data.signs.map toExpr))

/-- The checked expression and its root data for a polynomial `term` in the variable `x`. The
points of `marks` that are not roots stay outside the root intervals. -/
def polynomialData (x term : Expr) (marks : List ℚ := []) :
    MetaM (Verified.Expr (Fin 1) × Sparse.Univariate × Reduce.RootData) := do
  let expr ← reifyIn x term
  let some poly := Verified.Expr.Alg.mvPolyOf? expr
    | throwError "cas: the expression is not a polynomial with rational coefficients"
  match Reduce.rootData poly marks with
  | .ok data => return (expr, poly, data)
  | .error message => throwError "cas: {message}"

/-- The variable and the rational bounds of a membership `x ∈ Set.Icc a b`. -/
def iccBounds? (proposition : Expr) : MetaM (Option (Expr × ℚ × ℚ)) := do
  let proposition := proposition.consumeMData
  unless proposition.isAppOfArity ``Membership.mem 5 do return none
  let set := (proposition.getArg! 3).consumeMData
  unless set.isAppOfArity ``Set.Icc 4 do return none
  let some a ← Tactic.Classify.rationalLiteral? (set.getArg! 2) | return none
  let some b ← Tactic.Classify.rationalLiteral? (set.getArg! 3) | return none
  return some ((proposition.getArg! 4).consumeMData, a, b)

/-- Prove `statement`, a membership `x ∈ Set.Icc ↑a ↑b` with rational casts, from `membership`,
the same membership with the goal's real numerals. -/
def castMembership (statement membership : Expr) : TermElabM Expr := do
  let goal ← mkFreshExprSyntheticOpaqueMVar statement
  let membershipSyntax ← Term.exprToSyntax membership
  let remaining ←
    try
      KernelReadBack.withSuppressedMessagesMeta <|
        KernelReadBack.runTacticOnGoal goal.mvarId! (← `(tactic|
          (have h := $membershipSyntax:term
           simp only [Set.mem_Icc] at h ⊢
           push_cast at h ⊢
           constructor <;> linarith [h.1, h.2])))
    catch _ => throwError "cas sign route could not restate the bounds of the variable"
  unless remaining.isEmpty do
    throwError "cas sign route could not restate the bounds of the variable"
  mkExpectedTypeHint (← instantiateMVars goal) statement

/-- A rational of `[a, b]` at which `p` is negative: the middle of the part of `[a, b]` in a gap
of `data` whose cut is negative, or the middle of `[a, b]`. -/
def negativePointIn (p : Sparse.Univariate) (data : Reduce.RootData) (a b : ℚ) : ℚ :=
  let n := data.locs.length
  let candidates := (List.range (n + 1)).filterMap fun j ↦
    if data.signs.getD j true then none else
      let lo := if j = 0 then a else max a (data.locs.getD (j - 1) default).upper
      let hi := if j < n then min b (data.locs.getD j default).lower else b
      if lo ≤ hi then some ((lo + hi) / 2) else none
  (candidates.find? fun q ↦ Sparse.evalRat p q < 0).getD ((a + b) / 2)

/-- A root location in a message. -/
def locationText : RootLoc → MessageData
  | .exact r => m!"{r}"
  | .interval lo hi => m!"a point of ({lo}, {hi})"

/-- Close `lhs ≤ rhs` or `lhs < rhs` for polynomials in one real variable, for every value of
the variable or on an interval. A goal `∀ x : ℝ, …` is introduced first; after a hypothesis
`x ∈ Set.Icc a b` with rational numerals `a` and `b`, the root list has `a` and `b` as cell
boundaries, and only the gaps that meet `[a, b]` need a positive cut. -/
partial def closeSign (interval? : Option (Expr × ℚ × ℚ × Expr) := none) : TacticM Unit := do
  let goal ← getMainGoal
  let target ← goal.withContext do whnfR (← instantiateMVars (← goal.getType))
  if let .forallE _ domain _ _ := target then
    if let some (element, a, b) ← goal.withContext (iccBounds? domain) then
      let (membership, goal) ← goal.intro1P
      replaceMainGoal [goal]
      return ← closeSign (some (element, a, b, mkFVar membership))
    unless ← goal.withContext (isDefEq domain (mkConst ``Real)) do
      throwError "cas sign route expected a quantifier over ℝ"
    let (_, goal) ← goal.intro1P
    replaceMainGoal [goal]
    return ← closeSign interval?
  goal.withContext do
    let some (lhs, rhs, strict) ← relation? target
      | throwError "cas sign route expected a polynomial order relation over ℝ"
    let fvars := (collectFVars (collectFVars {} lhs) rhs).fvarIds
    let [variableId] := fvars.toList
      | throwError "cas sign route expected a relation in one real variable"
    let x := mkFVar variableId
    unless ← isDefEq (← inferType x) (mkConst ``Real) do
      throwError "cas sign route expected a relation in one real variable"
    let difference ← mkAppM ``HSub.hSub #[rhs, lhs]
    let marks := match interval? with
      | some (_, a, b, _) => [a, b]
      | none => []
    let (expr, poly, data) ← polynomialData x difference marks
    let quoted ← Command.quoteVerifiedExpr expr
    -- The reflection is identified with the difference first, so that the diagnosis below is
    -- about the stated difference; the value is exact rational arithmetic, not a proof.
    let hx := mkApp (← bridge quoted (← mkLambdaFVars #[x] difference)) x
    let transport := if strict then ``lt_of_eval_pos else ``le_of_eval_nonneg
    match interval? with
    | some (element, a, b, membership) =>
        unless element == x do
          throwError "cas sign route: the interval bounds another variable than the relation"
        unless gapSignsOn data.locs data.signs a b do
          let point := negativePointIn poly data a b
          throwError "cas sign route: the difference {← ppExpr difference} is \
            {Sparse.evalRat poly point} at {← ppExpr x} = {point} in [{a}, {b}] (exact rational \
            arithmetic, not a proof)"
        if strict then
          if let some l := data.locs.find? fun l ↦ !(l.before a || l.after b) then
            throwError "cas sign route: the root isolation finds a real root of the difference \
              {← ppExpr difference} at {locationText l} in [{a}, {b}], where the strict \
              relation would fail (not a proof)"
        let (cert, locs, cuts, signs) ← quoteRootData data
        let theoremName :=
          if strict then ``pos_on_Icc_of_reduceCheck else ``nonneg_on_Icc_of_reduceCheck
        let partialProof ← mkAppOptM theoremName
          #[some quoted, some cert, some locs, some cuts, some signs]
        let checked ← applyChecks "cas sign route" partialProof 1
        let signProof ← applyChecks "cas sign route"
          (mkApp2 checked (← quoteRat a) (← quoteRat b)) (if strict then 2 else 1)
        let .forallE _ membershipType _ _ ← whnfR (← inferType (mkApp signProof x))
          | throwError "cas sign route: unexpected interval theorem shape"
        let membershipProof ← castMembership membershipType membership
        goal.assign (← mkAppM transport #[mkApp2 signProof x membershipProof, hx])
    | none =>
        if let some (cut, _) := (data.cuts.zip data.signs).find? (fun pair ↦ !pair.2) then
          -- A simple point where the difference is negative, if one is near: halves first.
          let point := ((List.range 401).map fun k ↦ ((k : ℚ) - 200) / 2).find?
            (fun q ↦ Sparse.evalRat poly q < 0) |>.getD cut
          throwError "cas sign route: the difference {← ppExpr difference} is \
            {Sparse.evalRat poly point} at {← ppExpr x} = {point} (exact rational arithmetic, \
            not a proof)"
        if strict then
          if let some l := data.locs.head? then
            throwError "cas sign route: the root isolation finds a real root of the difference \
              {← ppExpr difference} at {locationText l}, where the strict relation would fail \
              (not a proof)"
        let (cert, locs, cuts, signs) ← quoteRootData data
        let partialProof ←
          if strict then
            mkAppOptM ``pos_of_reduceCheck #[some quoted, some cert, some cuts, some signs]
          else
            mkAppOptM ``nonneg_of_reduceCheck
              #[some quoted, some cert, some locs, some cuts, some signs]
        let signProof ← applyChecks "cas sign route" partialProof 2
        goal.assign (← mkAppM transport #[mkApp signProof x, hx])
    replaceMainGoal []

/-! ## Real roots -/

/-- Translate a polynomial written with `X`, numerals, `C` of a rational numeral, and the ring
operations into the real term it evaluates to at `x`. -/
partial def polynomialAt (x : Expr) (polynomial : Expr) : MetaM Expr := do
  let polynomial := polynomial.consumeMData
  if polynomial.isAppOfArity ``Polynomial.X 2 then
    return x
  let binary (name : Name) := do
    let arguments := polynomial.getAppArgs
    mkAppM name #[← polynomialAt x arguments[4]!, ← polynomialAt x arguments[5]!]
  if polynomial.isAppOfArity ``HAdd.hAdd 6 then return ← binary ``HAdd.hAdd
  if polynomial.isAppOfArity ``HSub.hSub 6 then return ← binary ``HSub.hSub
  if polynomial.isAppOfArity ``HMul.hMul 6 then return ← binary ``HMul.hMul
  if polynomial.isAppOfArity ``Neg.neg 3 then
    return ← mkAppM ``Neg.neg #[← polynomialAt x polynomial.appArg!]
  if polynomial.isAppOfArity ``HPow.hPow 6 then
    let exponent := polynomial.getAppArgs[5]!
    unless (← getNatValue? exponent).isSome do
      throwError "cas root route: the exponent{indentExpr exponent}\nis not a numeral"
    return ← mkAppM ``HPow.hPow #[← polynomialAt x polynomial.getAppArgs[4]!, exponent]
  -- `C c` is a coercion of the ring homomorphism `Polynomial.C`.
  if polynomial.isAppOf ``DFunLike.coe && polynomial.getAppNumArgs == 6 &&
      polynomial.getAppArgs[4]!.consumeMData.isAppOf ``Polynomial.C then
    let some q ← Tactic.Classify.rationalLiteral? polynomial.appArg!
      | throwError "cas root route: the coefficient{indentExpr polynomial.appArg!}\nis not a \
          rational numeral"
    return ← realOfRat q
  if let some q ← Tactic.Classify.rationalLiteral? polynomial then
    return ← realOfRat q
  throwError "cas root route: write the polynomial with `X`, numerals, `C`, `+`, `-`, `*` and \
    numeral powers; found{indentExpr polynomial}"

/-- The polynomial and the real carrier of `Fintype.card (p.rootSet ℝ)`. -/
def rootSetPolynomial? (card : Expr) : MetaM (Option Expr) := do
  let card := card.consumeMData
  unless card.isAppOf ``Fintype.card do return none
  let some set := card.getAppArgs[0]? | return none
  let set := set.consumeMData
  unless set.isAppOf ``Set.Elem do return none
  let some rootSet := set.getAppArgs[1]? | return none
  let rootSet := rootSet.consumeMData
  unless rootSet.isAppOf ``Polynomial.rootSet do return none
  let arguments := rootSet.getAppArgs
  let some polynomial := arguments[2]? | return none
  let some carrier := arguments[3]? | return none
  unless ← isDefEq carrier (mkConst ``Real) do return none
  return some polynomial

/-- Prove `statement`, the hypothesis `∀ y : ℝ, aeval y p = quoted.eval ![y]` of
`card_rootSet_of_exprRootCheck`, from the bridge `∀ y, quoted.eval ![y] = t y`, where `t` is the
translation of `p` by `polynomialAt`. -/
def aevalBridge (statement quoted translation : Expr) : TermElabM Expr := do
  let hBridge ← bridge quoted translation
  -- `aeval` is an algebra homomorphism; its value is the translation, up to numeral casts.
  let goal ← mkFreshExprSyntheticOpaqueMVar statement
  let bridgeSyntax ← Term.exprToSyntax hBridge
  let remaining ←
    try
      KernelReadBack.withSuppressedMessagesMeta <|
        KernelReadBack.runTacticOnGoal goal.mvarId! (← `(tactic|
          (intro y
           rw [$bridgeSyntax:term]
           simp only [map_add, map_sub, map_mul, map_neg, map_pow, Polynomial.aeval_X,
             Polynomial.aeval_C, map_one, map_zero, map_ofNat, map_natCast, map_intCast,
             eq_ratCast, eq_intCast]
           all_goals (try push_cast)
           all_goals ring)))
    catch error =>
      throwError "cas root route could not evaluate the polynomial as a real function:\
        {indentD error.toMessageData}"
  unless remaining.isEmpty do
    throwError "cas root route could not evaluate the polynomial as a real function; left\
      {indentD (MessageData.joinSep (remaining.map MessageData.ofGoal) "\n")}"
  mkExpectedTypeHint (← instantiateMVars goal) statement

/-- A rational at which a nonzero polynomial does not vanish. -/
def nonRoot (poly : Sparse.Univariate) : Option ℚ := Id.run do
  for k in [0:64] do
    let q : ℚ := if k % 2 == 0 then (k / 2 : ℕ) else -(((k + 1) / 2 : ℕ) : ℚ)
    if Sparse.evalRat poly q != 0 then return some q
  return none

/-- Close `Fintype.card (p.rootSet ℝ) = n`. -/
def closeRootCount : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let some (_, card, count) := target.eq?
    | throwError "cas root route expected an equality"
  let some polynomial ← rootSetPolynomial? card
    | throwError "cas root route expected `Fintype.card (p.rootSet ℝ) = n`"
  let some n ← getNatValue? count
    | throwError "cas root route: the stated count{indentExpr count}\nis not a numeral"
  let (expr, translation, poly, data) ← withLocalDeclD `x (mkConst ``Real) fun x ↦ do
    let term ← polynomialAt x polynomial
    let (expr, poly, data) ← polynomialData x term
    return (expr, ← mkLambdaFVars #[x] term, poly, data)
  let intervals := rootIntervals data.cert.cells
  let points := data.locs.filterMap RootLoc.pointPart
  let found := intervals.length + points.length
  let some q := nonRoot poly
    | throwError "cas root route: no rational point where the polynomial does not vanish"
  let quoted ← Command.quoteVerifiedExpr expr
  let partialProof ← mkAppOptM ``card_rootSet_of_exprRootCheck
    #[none, none, none, some polynomial, some quoted,
      some (← Roots.quoteCertificate 20 data.cert), some (← Roots.quoteIntervals 20 intervals),
      some (← quoteRats points), some (← quoteRat q)]
  let .forallE _ evaluation _ _ ← whnfR (← inferType partialProof)
    | throwError "cas root route: unexpected count theorem shape"
  let heval ← aevalBridge evaluation quoted translation
  let cardProof ← applyChecks "cas root route" (mkApp partialProof heval) 2
  let some (_, _, length) := (← inferType cardProof).eq?
    | throwError "cas root route: unexpected count theorem shape"
  -- The count is certified before a different stated count is reported as wrong.
  unless found == n do
    throwError "cas root route: the polynomial has exactly {found} distinct real roots \
      (certified), not {n}"
  let lengthProof ← decideByKernel "cas root route" (← mkEq length count)
  goal.assign (← mkEqTrans cardProof lengthProof)
  replaceMainGoal []

/-- The conjuncts of a conjunction. -/
partial def conjuncts (proposition : Expr) : Array Expr :=
  let proposition := proposition.consumeMData
  if proposition.isAppOfArity ``And 2 then
    conjuncts proposition.getAppArgs[0]! ++ conjuncts proposition.getAppArgs[1]!
  else #[proposition]

/-- A bound `c < x`, `c ≤ x`, `x < c` or `x ≤ c` with a rational numeral `c`, as
`(isLower, c, strict)`. -/
def bound? (x proposition : Expr) : MetaM (Option (Bool × ℚ × Bool)) := do
  let some (lhs, rhs, strict) ← relation? proposition | return none
  if lhs == x then
    if let some c ← Tactic.Classify.rationalLiteral? rhs then return some (false, c, strict)
  if rhs == x then
    if let some c ← Tactic.Classify.rationalLiteral? lhs then return some (true, c, strict)
  return none

/-- Whether every point of the open interval `(lo, hi)` satisfies the bounds. -/
def intervalSatisfies (bounds : Array (Bool × ℚ × Bool)) (lo hi : ℚ) : Bool :=
  bounds.all fun (isLower, c, _) ↦ if isLower then c ≤ lo else hi ≤ c

/-- Whether the rational `r` satisfies the bounds. -/
def pointSatisfies (bounds : Array (Bool × ℚ × Bool)) (r : ℚ) : Bool :=
  bounds.all fun (isLower, c, strict) ↦
    if isLower then (if strict then c < r else c ≤ r) else (if strict then r < c else r ≤ c)

/-- Split the conjunctions of the main goal into goals, with `And.intro`. -/
partial def splitConjunctions (goal : MVarId) : MetaM (List MVarId) := do
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  if target.isAppOfArity ``And 2 then
    let goals ← goal.apply (mkConst ``And.intro)
    return (← goals.mapM splitConjunctions).flatten
  return [goal]

/-- Close `∃ x : ℝ, p x = q x ∧ bounds` for polynomials `p`, `q` and bounds of `x` by rational
numerals. -/
def closeRootExistence : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOfArity ``Exists 2 do
    throwError "cas root route expected an existential statement"
  unless ← isDefEq target.getAppArgs[0]! (mkConst ``Real) do
    throwError "cas root route expected an existential over ℝ"
  let body := target.getAppArgs[1]!
  let (expr, poly, data, difference, bounds) ← withLocalDeclD `x (mkConst ``Real) fun x ↦ do
    let parts := conjuncts (mkApp body x).headBeta
    let mut equation? : Option Expr := none
    let mut bounds : Array (Bool × ℚ × Bool) := #[]
    for part in parts do
      if let some (type, lhs, rhs) := part.eq? then
        if equation?.isNone && (← isDefEq type (mkConst ``Real)) then
          equation? := some (← mkAppM ``HSub.hSub #[lhs, rhs])
          continue
      let some bound ← bound? x part
        | throwError "cas root route: the condition{indentExpr part}\nis neither the polynomial \
            equation nor a bound of the variable by a rational numeral"
      bounds := bounds.push bound
    let some difference := equation?
      | throwError "cas root route expected a polynomial equation among the conditions"
    let (expr, poly, data) ← polynomialData x difference
    return (expr, poly, data, ← mkLambdaFVars #[x] difference, bounds)
  let _ := poly
  let intervals := rootIntervals data.cert.cells
  let points := data.locs.filterMap RootLoc.pointPart
  let quoted ← Command.quoteVerifiedExpr expr
  let partialProof ← mkAppOptM ``of_exprRootCheck
    #[some quoted, some (← Roots.quoteCertificate 20 data.cert),
      some (← Roots.quoteIntervals 20 intervals),
      some (← quoteRats points)]
  let rootList ← applyChecks "cas root route" partialProof 1
  let hBridge ← bridge quoted difference
  let bridgeSyntax ← Term.exprToSyntax hBridge
  -- A witness: an exact rational root, or the root isolated in an interval, inside the bounds.
  let witness ← if let some r := points.find? (pointSatisfies bounds) then
      let membership ← decideByKernel "cas root route"
        (← mkAppM ``Membership.mem #[← quoteRats points,
          ← quoteRat r])
      let isRoot ← mkAppM ``And.left #[← mkAppM ``And.right #[rootList]]
      let rootProof := mkApp2 isRoot (← quoteRat r) membership
      let rootSyntax ← Term.exprToSyntax rootProof
      let cast ← Term.exprToSyntax (← ratCast r)
      pure (← `(tactic|
        (have hroot := $rootSyntax:term
         refine ⟨$cast, ?_⟩
         rw [$bridgeSyntax:term] at hroot)))
    else if let some (lo, hi) := intervals.find? fun (lo, hi) ↦ intervalSatisfies bounds lo hi then
      let pair ← mkAppM ``Prod.mk #[← quoteRat lo, ← quoteRat hi]
      let intervalList ← Roots.quoteIntervals 20 intervals
      let membership ← decideByKernel "cas root route"
        (← mkAppM ``Membership.mem #[intervalList, pair])
      let unique ← mkAppM ``And.left #[rootList]
      let rootProof := mkApp2 unique pair membership
      let rootSyntax ← Term.exprToSyntax rootProof
      pure (← `(tactic|
        (obtain ⟨x, ⟨⟨hlo, hhi⟩, hroot⟩, -⟩ := $rootSyntax:term
         refine ⟨x, ?_⟩
         rw [$bridgeSyntax:term] at hroot
         norm_num at hlo hhi)))
    else
      throwError "cas root route: no rational root and no isolating interval of the root list, \
        refined to 20 decimals, lies within the bounds; this route does not refine further"
  let goals ← KernelReadBack.runTacticOnGoal goal witness
  let [goal'] := goals | throwError "cas root route: unexpected goals after choosing the root"
  for leaf in ← splitConjunctions goal' do
    let remaining ← KernelReadBack.runTacticOnGoal leaf (← `(tactic|
      first
        | linarith
        | (norm_num at *; linarith)
        | (norm_num at *; done)))
    unless remaining.isEmpty do
      throwError "cas root route could not prove a condition of the chosen root"
  replaceMainGoal []

/-- Close `∃ x : ℝ, f x = g x ∧ bounds`, with bounds of `x` by rational numerals or
`x ∈ Set.Icc a b`, and `∃! x : ℝ, x ∈ Set.Icc a b ∧ f x = g x`, for any one-variable
expressions, with the certificate of `#cas [findRoot]` (`existsUnique_root_of_rootCheck`): a
checked sign change and a derivative of one sign, on a narrow interval found by bisection for
`∃`, on `[a, b]` itself for `∃!`. -/
def closeFindRoot : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let unique := target.isAppOfArity ``ExistsUnique 2
  unless target.isAppOfArity ``Exists 2 || unique do
    throwError "cas root route expected an existential statement"
  unless ← isDefEq target.getAppArgs[0]! (mkConst ``Real) do
    throwError "cas root route expected an existential over ℝ"
  let body := target.getAppArgs[1]!
  let (expr, difference, bounds, shapeOk) ← withLocalDeclD `x (mkConst ``Real) fun x ↦ do
    let parts := conjuncts (mkApp body x).headBeta
    let mut equation? : Option Expr := none
    let mut bounds : Array (Bool × ℚ × Bool) := #[]
    let mut interval := false
    for part in parts do
      if let some (type, lhs, rhs) := part.eq? then
        if equation?.isNone && (← isDefEq type (mkConst ``Real)) then
          equation? := some (← mkAppM ``HSub.hSub #[lhs, rhs])
          continue
      if part.isAppOfArity ``Membership.mem 5 && part.getArg! 4 == x then
        let set := (part.getArg! 3).consumeMData
        if set.isAppOfArity ``Set.Icc 4 then
          if let (some a, some b) := (← Tactic.Classify.rationalLiteral? (set.getArg! 2),
              ← Tactic.Classify.rationalLiteral? (set.getArg! 3)) then
            bounds := bounds.push (true, a, false) |>.push (false, b, false)
            interval := true
            continue
      let some bound ← bound? x part
        | throwError "cas root route: the condition{indentExpr part}\nis neither the equation \
            nor a bound of the variable by a rational numeral"
      bounds := bounds.push bound
    let some difference := equation?
      | throwError "cas root route expected an equation among the conditions"
    -- `∃!` is treated in the shape `x ∈ Set.Icc a b ∧ f x = g x` only, membership first.
    let shapeOk := !unique || (parts.size == 2 && interval &&
      parts[0]!.isAppOfArity ``Membership.mem 5)
    return (← reifyIn x difference, ← mkLambdaFVars #[x] difference, bounds, shapeOk)
  unless shapeOk do
    throwError "cas root route: a unique root is stated as `∃! x, x ∈ Set.Icc a b ∧ f x = g x`"
  let lowers := bounds.filterMap fun (isLower, c, _) ↦ if isLower then some c else none
  let uppers := bounds.filterMap fun (isLower, c, _) ↦ if isLower then none else some c
  let (some a, some b) := (lowers.foldl (fun m c ↦ some (match m with
      | some m => max m c | none => c)) none, uppers.foldl (fun m c ↦ some (match m with
      | some m => min m c | none => c)) none)
    | throwError "cas root route: the variable needs a lower and an upper rational bound"
  unless a < b do throwError "cas root route: the bounds leave no interval"
  let p := CAS.Continuum.DigitsEval.precisionFor 20
  let (lo, hi) ← if unique then pure (a, b) else
    let some (a', b', sa) := FindRoot.firstSignChange? p expr a b
      | throwError "cas root route: no sign change of the expression at 65 equally spaced points \
          of [{a}, {b}]"
    let (lo, hi) := FindRoot.bisect p expr a' b' sa ((b - a) / 2 ^ 40)
    unless pointSatisfies bounds lo && pointSatisfies bounds hi do
      throwError "cas root route: the root lies too close to a strict bound"
    pure (lo, hi)
  let root ← FindRoot.rootCertificate p expr (← quoteRat lo) (← quoteRat hi) lo hi
  let rootSyntax ← Term.exprToSyntax root
  let bridgeSyntax ← Term.exprToSyntax (← bridge (← Command.quoteVerifiedExpr expr) difference)
  let leaf ← `(tactic| first
    | assumption
    | linarith
    | (norm_num at *; first | assumption | linarith | (constructor <;> linarith))
    | (simp only [Set.mem_Icc] at *; constructor <;> linarith))
  let script ← if unique then `(tactic|
      (obtain ⟨x, ⟨hx, hfx⟩, huniq⟩ := $rootSyntax:term
       rw [Verified.Expr.univariateEval_eq_eval, $bridgeSyntax:term] at hfx
       refine ⟨x, ⟨?_, ?_⟩, fun y hy ↦ huniq y ⟨?_, ?_⟩⟩
       · simp only [Set.mem_Icc] at hx ⊢
         push_cast at hx ⊢
         constructor <;> linarith [hx.1, hx.2]
       · linarith
       · have hy1 := hy.1
         simp only [Set.mem_Icc] at hy1 ⊢
         push_cast at hy1 ⊢
         constructor <;> linarith [hy1.1, hy1.2]
       · rw [Verified.Expr.univariateEval_eq_eval, $bridgeSyntax:term]
         linarith [hy.2]))
    else `(tactic|
      (obtain ⟨x, ⟨hx, hfx⟩, -⟩ := $rootSyntax:term
       rw [Verified.Expr.univariateEval_eq_eval, $bridgeSyntax:term] at hfx
       simp only [Set.mem_Icc] at hx
       push_cast at hx
       obtain ⟨hlo, hhi⟩ := hx
       refine ⟨x, ?_⟩))
  let goals ← KernelReadBack.runTacticOnGoal goal script
  if unique then
    unless goals.isEmpty do throwError "cas root route could not prove the unique root"
  else
    let [goal'] := goals | throwError "cas root route: unexpected goals after choosing the root"
    for part in ← splitConjunctions goal' do
      let remaining ← KernelReadBack.runTacticOnGoal part leaf
      unless remaining.isEmpty do
        throwError "cas root route could not prove a condition of the chosen root"
  replaceMainGoal []

/-! ## The route -/

/-- The route of bare `cas` for the statements of `#cas` commands, registered under `command`. -/
@[cas_route command]
def route : Tactic.RouteRegistry.Closer := fun _ ↦ do
  let target ← withMainContext do instantiateMVars (← getMainTarget)
  let target := target.consumeMData
  let theoremName ←
    -- The goals of the algebra, matrix and number theory commands (`CAS.Command.AlgebraGoals`).
    if CAS.Tactic.CommandShapes.isAlgebraStatement target then
      AlgebraGoals.close
      pure ``AlgebraGoals.close
    else if target.isAppOf ``Filter.Tendsto then
      closeLimit
    else if (← withMainContext do
        match target.eq? with
        | some (_, lhs, _) => return (← rootSetPolynomial? lhs).isSome
        | none => return false) then
      closeRootCount
      pure ``card_rootSet_of_exprRootCheck
    else if target.isAppOfArity ``Exists 2 || target.isAppOfArity ``ExistsUnique 2 then
      -- Polynomial equations first; other one-variable equations by the `#cas [findRoot]`
      -- certificate.
      if target.isAppOfArity ``ExistsUnique 2 then
        closeFindRoot
        pure ``Verified.Expr.existsUnique_root_of_rootCheck
      else
        let saved ← saveState
        try
          closeRootExistence
          pure ``of_exprRootCheck
        catch error =>
          saved.restore
          try
            closeFindRoot
            pure ``Verified.Expr.existsUnique_root_of_rootCheck
          catch error' =>
            saved.restore
            throwError "{error.toMessageData}\n{error'.toMessageData}"
    else if target.isForall || (← withMainContext (relation? target)).isSome then
      closeSign
      pure ``nonneg_of_reduceCheck
    else
      throwError "no `#cas` command states a goal of this shape"
  return { replay := ← `(tactic| cas), finalAttribution? := some theoremName }

end CAS.Command.Goals
