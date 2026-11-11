/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.BatchRange
public meta import CAS.Continuum.Quadrature.BatchRange
public meta import CAS.CEGA.Elaboration
public import CAS.Tactic.Integration.Reflection
public meta import CAS.Tactic.Integration.Reflection
public import CAS.Tactic.BoxInequality
public meta import CAS.Tactic.BoxInequality

/-!
# Interval integrals in bare `cega`

Bare `cega` proves a goal about one interval integral `∫ x in a..b, f x` with rational limits and
a closed elementary integrand. When the domain checker certifies that the integrand and its first
four derivatives are defined on `[a, b]`, one kernel evaluation of `BatchSimpson.integralCheck`
bounds the integral by composite Simpson panels with a fourth-derivative remainder. Otherwise, or
when Simpson panels do not reach the stated bound, one kernel evaluation of
`BatchRange.rangeCheck` bounds it by range panels, which need only the continuity of the
integrand. `integral_bounds_of_check` and `integral_bounds_of_rangeCheck`, with their `_symm`
forms for reversed limits, transport the checked bounds to the integral as written.

## Implementation notes

The elaborator takes the one interval integral of the goal (`intervalIntegrals`), checks that it is
over the volume measure with rational limits, reflects the integrand into `Verified.Expr (Fin 1)`
and abstracts the integral from the goal (`kabstract`). `validityOn?` reduces the domain checker
`RationalInterval.validIteratesOnIcc?` with the kernel's evaluator; its certificate gives the
continuity of the integrand (`continuousOn_of_valid`) and admits Simpson panels, and without it
`fun_prop` must prove continuity and only range panels remain. Compiled code, which is not trusted,
then searches. The panel count doubles from one to `cega.maxIntegrationPanels` unless
`(panels := n)` gives it, and the search takes the leanest working precision and the shortest
decimal bounds whose panel enclosure (`BatchSimpson.sharedPanels`, `panels (BatchRange.panel p f)`)
passes a test of the goal's relations by `DigitsEval.eval`; `(digits := d)` fixes the working
precision instead. `attempt` generalizes the integral to a real number between the proposed bounds
and proves that goal by the box route (`BoxInequality.closeMainGoal`) with the precision and depth
of the call. Only then does the kernel check `BatchSimpson.integralCheck p f d a b N lo hi = true`
or `BatchRange.rangeCheck p f a b N lo hi = true` (`KernelReadBack.decideByKernel`), so a goal that
the box route refuses costs no kernel quadrature. An integral over an empty interval is `0` by
`norm_num`, and a failed search reports the enclosure, its width and the next call to try.

The soundness proofs are in `CAS.Continuum.Quadrature`. `BatchSimpson.of_integralCheck` sums
`simpsonRule.enclosure_sound` (`CAS.Continuum.Quadrature.CompositeSimpson`) over the panels: a
panel of width `w` with sample enclosures `L`, `C`, `R` contributes `w / 6 * (L + 4 * C + R)`,
widened by `M * w ^ 5 / 2880`, where `M` bounds the fourth derivative `d` on the panel. The
widening bounds the classical remainder `-h ^ 5 / 90 * f⁽⁴⁾(ξ)` with `h = w / 2`, and the check
confirms that `d` is `f.symbolicDerivative 4`. `BatchRange.of_rangeCheck` multiplies an
enclosure of the range on each panel by its width. We try Simpson panels first because their
remainder falls like `N⁻⁴` in the panel count `N`.

## References

* NIST Digital Library of Mathematical Functions, §3.5 Quadrature, Version 1.2.8 (2026-09-15),
  <https://dlmf.nist.gov/3.5>. §3.5(ii), equations (3.5.6) to (3.5.8), for Simpson's rule, its
  composite form and their fourth-derivative remainders.
-/

@[expose] public section

namespace CAS.CEGA.Integration

open Set MeasureTheory
open CAS.Continuum

/-- The order of two rational limits, read in `ℝ`. -/
theorem cast_lt_of_lt {a b : ℚ} (h : a < b) : (a : ℝ) < b := Rat.cast_lt.mpr h

/-- An integrand whose first four derivatives are valid on `[a, b]` is continuous there. -/
theorem continuousOn_of_valid {f : Verified.Expr (Fin 1)} {a b : ℚ} (hab : (a : ℝ) < b)
    (hvalid : f.ValidIteratesOn 5 (Set.Icc (a : ℝ) b)) :
    ContinuousOn f.univariateEval (Set.Icc (a : ℝ) b) :=
  (Verified.Expr.contDiffOn_univariateEval f 0 (uniqueDiffOn_Icc hab)
    (hvalid.mono (by norm_num))).continuousOn

/-- A batch Simpson check, transported to the integral as written: the limits `A` and `B` and
the integrand `F` only need to equal the checked ones. -/
theorem integral_bounds_of_check {p : DigitsEval.Precision} {f d : Verified.Expr (Fin 1)}
    {a b : ℚ} {N : ℕ} {lo hi : ℚ} {A B : ℝ} {F : ℝ → ℝ}
    (hvalid : f.ValidIteratesOn 5 (Set.Icc (a : ℝ) b))
    (h : BatchSimpson.integralCheck p f d a b N lo hi = true)
    (ha : (a : ℝ) = A) (hb : (b : ℝ) = B) (hF : ∀ x, f.univariateEval x = F x) :
    (lo : ℝ) ≤ intervalIntegral F A B volume ∧ intervalIntegral F A B volume ≤ hi := by
  subst ha hb
  obtain rfl : (fun x ↦ f.univariateEval x) = F := funext hF
  exact BatchSimpson.of_integralCheck hvalid h

/-- A batch Simpson check on `[a, b]`, transported to the integral from `b` down to `a`. -/
theorem integral_bounds_of_check_symm {p : DigitsEval.Precision} {f d : Verified.Expr (Fin 1)}
    {a b : ℚ} {N : ℕ} {lo hi : ℚ} {A B : ℝ} {F : ℝ → ℝ}
    (hvalid : f.ValidIteratesOn 5 (Set.Icc (a : ℝ) b))
    (h : BatchSimpson.integralCheck p f d a b N lo hi = true)
    (ha : (a : ℝ) = B) (hb : (b : ℝ) = A) (hF : ∀ x, f.univariateEval x = F x) :
    ((-hi : ℚ) : ℝ) ≤ intervalIntegral F A B volume ∧
      intervalIntegral F A B volume ≤ ((-lo : ℚ) : ℝ) := by
  rw [intervalIntegral.integral_symm]
  obtain ⟨h₁, h₂⟩ := integral_bounds_of_check hvalid h ha hb hF
  push_cast
  constructor <;> linarith [h₁, h₂]

/-- A batch range check, transported to the integral as written. -/
theorem integral_bounds_of_rangeCheck {p : DigitsEval.Precision} {f : Verified.Expr (Fin 1)}
    {a b : ℚ} {N : ℕ} {lo hi : ℚ} {A B : ℝ} {F : ℝ → ℝ}
    (hcont : ContinuousOn f.univariateEval (Set.Icc (a : ℝ) b))
    (h : BatchRange.rangeCheck p f a b N lo hi = true)
    (ha : (a : ℝ) = A) (hb : (b : ℝ) = B) (hF : ∀ x, f.univariateEval x = F x) :
    (lo : ℝ) ≤ intervalIntegral F A B volume ∧ intervalIntegral F A B volume ≤ hi := by
  subst ha hb
  obtain rfl : (fun x ↦ f.univariateEval x) = F := funext hF
  exact BatchRange.of_rangeCheck hcont h

/-- A batch range check on `[a, b]`, transported to the integral from `b` down to `a`. -/
theorem integral_bounds_of_rangeCheck_symm {p : DigitsEval.Precision}
    {f : Verified.Expr (Fin 1)} {a b : ℚ} {N : ℕ} {lo hi : ℚ} {A B : ℝ} {F : ℝ → ℝ}
    (hcont : ContinuousOn f.univariateEval (Set.Icc (a : ℝ) b))
    (h : BatchRange.rangeCheck p f a b N lo hi = true)
    (ha : (a : ℝ) = B) (hb : (b : ℝ) = A) (hF : ∀ x, f.univariateEval x = F x) :
    ((-hi : ℚ) : ℝ) ≤ intervalIntegral F A B volume ∧
      intervalIntegral F A B volume ≤ ((-lo : ℚ) : ℝ) := by
  rw [intervalIntegral.integral_symm]
  obtain ⟨h₁, h₂⟩ := integral_bounds_of_rangeCheck hcont h ha hb hF
  push_cast
  constructor <;> linarith [h₁, h₂]

end CAS.CEGA.Integration

end

public meta section

namespace CAS.CEGA.Integration

open Lean Elab Tactic Meta
open CAS.Continuum CAS.Continuum.RationalInterval
open CAS.Tactic
open CAS.CEGA.Elaboration

/-- Trace bare `cega` on an interval integral: the panel count, the method and the precision of the
quadrature that encloses the integral, and the enclosure. -/
initialize registerTraceClass `cega.integration

/-- The largest panel count of the doubling search of bare `cega` on an interval integral. -/
register_option cega.maxIntegrationPanels : Nat := {
  defValue := 256
  descr := "maximum panel count of the doubling search of bare cega on an interval integral; \
    `(panels := n)` is not capped"
}

/-- The closed interval integrals of `e` outside lambdas, added to `found`, within `fuel` steps. -/
private def intervalIntegralsAux : Nat → Lean.Expr → Array Lean.Expr → Array Lean.Expr
  | 0, _, found => found
  | fuel + 1, e, found =>
    let e := e.consumeMData
    if !e.hasLooseBVars &&
        (CAS.Tactic.Integration.Reflection.intervalIntegralApplication? e).isSome then
      if found.contains e then found else found.push e
    else match e with
      | .app f a => intervalIntegralsAux fuel a (intervalIntegralsAux fuel f found)
      | .forallE _ d b _ => intervalIntegralsAux fuel b (intervalIntegralsAux fuel d found)
      | _ => found

/-- The distinct closed interval integrals of `e`, outside lambdas. -/
def intervalIntegrals (e : Lean.Expr) : Array Lean.Expr :=
  intervalIntegralsAux (e.sizeWithoutSharing + 1) e #[]

/-- The first closed interval integral of `e`. -/
def findIntegral? (e : Lean.Expr) : Option Lean.Expr :=
  (intervalIntegrals e)[0]?

/-- The validity of a quoted integrand and its first four derivatives on `[a, b]`, from the domain
checker evaluated by the kernel, with the limits written by `quote`; `none` when `b ≤ a` or when
the checker finds no certificate. -/
def validityOn? (quoted : Lean.Expr) (a b : ℚ)
    (quote : ℚ → MetaM Lean.Expr := fun q ↦ pure (toExpr q)) : MetaM (Option Lean.Expr) := do
  unless a < b do return none
  let qa ← quote a
  let qb ← quote b
  let order ← mkAppM ``cast_lt_of_lt #[← mkDecideProof (← mkAppM ``LT.lt #[qa, qb])]
  let query ← mkAppM ``CAS.Continuum.RationalInterval.validIteratesOnIcc?
    #[quoted, toExpr (5 : Nat), qa, qb, order]
  let result ← try
      KernelReadBack.kernelWhnf query "CEGA integration domain checking"
    catch _ => return none
  unless result.isAppOfArity ``Option.some 2 do return none
  return some (← mkAppM ``CAS.CertificateRoute.cert #[result.getAppArgs[1]!])

/-- A working precision of `DigitsEval` as a term. -/
def quotePrecision (p : DigitsEval.Precision) : Lean.Expr :=
  mkApp3 (mkConst ``CAS.Continuum.DigitsEval.Precision.mk) (toExpr p.bits) (toExpr p.terms)
    (toExpr p.logTerms)

/-- The rational `q` as a real number. -/
private def realRational (q : ℚ) : MetaM Lean.Expr :=
  mkAppOptM ``Rat.cast #[some (mkConst ``Real), none, some (toExpr q)]

/-- A proof of `(a : ℝ) < b` for rationals `a < b`. -/
private def orderProof (a b : ℚ) : MetaM Lean.Expr := do
  mkAppM ``cast_lt_of_lt #[← mkDecideProof (← mkAppM ``LT.lt #[toExpr a, toExpr b])]

/-- The interval `[a, b]` of real numbers. -/
private def intervalDomain (a b : ℚ) : MetaM Lean.Expr := do
  mkAppM ``Set.Icc #[← realRational a, ← realRational b]

/-- Prove `type` by `script`, or report the goals that remain. -/
private def prove (type : Lean.Expr) (script : TSyntax `tactic) : MetaM Lean.Expr := do
  let goal ← mkFreshExprSyntheticOpaqueMVar type
  let remaining ← KernelReadBack.runTacticOnGoal goal.mvarId! script
  unless remaining.isEmpty do
    let targets ← remaining.mapM fun remainingGoal ↦
      remainingGoal.withContext remainingGoal.getType
    throwError "cega: the integral route could not prove\
      {indentD (MessageData.joinSep (targets.map MessageData.ofExpr) "\n")}"
  instantiateMVars goal

/-- The integrand as a checked expression in its one variable, and the caller-local definitions
unfolded to expose it. -/
private def reflectIntegrand (function : Lean.Expr) :
    MetaM (Verified.Expr (Fin 1) × Array Name) := do
  let real := mkConst ``Real
  unless ← Elaboration.RealExpression.hasType function (← mkArrow real real) do
    throwError "cega: the integrand is not an ordinary function ℝ → ℝ"
  withLocalDeclD `t real fun binder ↦ do
    let application := mkApp function binder
    let definitions ← RealExpression.collectDependentLocalDefinitions binder application
    let body ← withTransparency .reducible <| whnf application
    let definitions ← RealExpression.collectDependentLocalDefinitions binder body definitions
    let reflection ← CAS.Elaboration.RealExpression.reify {
      operation := "cega"
      coordinates := #[binder]
      rationalLiterals := true
      unfoldLimit := RealExpression.localUnfoldLimit
    } body
    unless reflection.dimension = 1 do
      throwError "cega: the integrand depends on terms other than its variable; the integral \
        route needs a closed elementary integrand: write numerical coefficients as exact \
        rational arithmetic, or supply a proved quadrature certificate with `cega using`"
    let some checked ← reflection.toVerifiedExpr?
      | throwError "cega: the integrand has a symbolic natural exponent, which the kernel \
          evaluator cannot reduce; a literal exponent is needed"
    let f : Verified.Expr (Fin 1) := checked.mapVars fun _ ↦ .var 0
    return (f, definitions)

/-- The decimal exponent `e` and the first two significant digits `d` (rounded up, so
`w ≤ d / 10 * 10 ^ e`) of a positive rational `w`. Each step multiplies or divides by 10, so the
number of decimal digits of the numerator and the denominator bounds the steps. -/
private def magnitude (w : ℚ) : Int × Nat := Id.run do
  let mut exponent : Int := 0
  let mut mantissa := w
  for _ in [:(toString w.num.natAbs).length + (toString w.den).length + 2] do
    if mantissa < 1 then
      mantissa := mantissa * 10
      exponent := exponent - 1
    else if 10 ≤ mantissa then
      mantissa := mantissa / 10
      exponent := exponent + 1
  let leading := (⌈mantissa * 10⌉).toNat
  if leading ≥ 100 then (exponent + 1, 10) else (exponent, leading)

/-- `q` rounded down, or up when `up`, to `places` decimal places, and the rounded value. -/
private def roundDecimal (q : ℚ) (places : Nat) (up : Bool) : String × ℚ :=
  let scaled := q * (10 ^ places : ℚ)
  let n : Int := if up then ⌈scaled⌉ else ⌊scaled⌋
  let digits := toString n.natAbs
  let digits := "".pushn '0' (places + 1 - min (places + 1) digits.length) ++ digits
  let whole := digits.length - places
  ((if n < 0 then "-" else "") ++ (digits.take whole).toString ++
    (if places = 0 then "" else "." ++ (digits.drop whole).toString),
   (n : ℚ) / (10 ^ places : ℚ))

/-- `q` as an exact decimal when it has at most 60 decimal places, and as a fraction otherwise. -/
private def showRational (q : ℚ) : String := Id.run do
  for places in [:61] do
    if (q * 10 ^ places).den = 1 then return (roundDecimal q places false).1
  return toString q

/-- The working precision that decides whether a panel count reaches the goal. -/
private def reference : DigitsEval.Precision := ⟨128, 48, 96⟩

/-- The working precisions tried for the checked enclosure, leanest first. -/
private def ladder : List DigitsEval.Precision :=
  [⟨16, 6, 12⟩, ⟨20, 7, 14⟩, ⟨24, 8, 16⟩, ⟨32, 11, 22⟩, ⟨40, 14, 28⟩, ⟨48, 17, 34⟩,
    ⟨64, 22, 44⟩, ⟨96, 33, 66⟩]

/-- `q` rounded down, or up when `up`, to `k` significant decimal digits. -/
private def roundSig (q : ℚ) (k : Nat) (up : Bool) : ℚ :=
  if q = 0 then 0 else
    let (exponent, _) := magnitude |q|
    let shift : Int := (k : Int) - 1 - exponent
    let scale : ℚ := if 0 ≤ shift then 10 ^ shift.toNat else 1 / 10 ^ (-shift).toNat
    let n : Int := if up then ⌈q * scale⌉ else ⌊q * scale⌋
    (n : ℚ) / scale

/-- The two panel rules of the integral route. -/
private inductive PanelMethod where
  /-- Composite Simpson panels with a fourth-derivative remainder. -/
  | simpson
  /-- Range panels, which need only continuity. -/
  | range

/-- The panel rule as the reports name it. -/
private def PanelMethod.describe : PanelMethod → String
  | .simpson => "Simpson"
  | .range => "range"

/-- The enclosure of the integral over `[a, b]` by `N` panels of `method` at precision `p`: the
computation that `BatchSimpson.integralCheck` and `BatchRange.rangeCheck` repeat in the
kernel. -/
private def PanelMethod.enclosure : PanelMethod → DigitsEval.Precision →
    Verified.Expr (Fin 1) → Verified.Expr (Fin 1) → ℚ → ℚ → Nat → Option RationalInterval
  | .simpson, p, f, d, a, b, N => BatchSimpson.sharedPanels p f d a ((b - a) / N) N
  | .range, p, f, _, a, b, N => panels (BatchRange.panel p f) a ((b - a) / N) N

/-- A quadrature that the search chose for the kernel check. -/
private structure PanelQuadrature where
  /-- The panel rule. -/
  method : PanelMethod
  /-- The number of panels. -/
  panels : Nat
  /-- The working precision of the panel enclosures. -/
  precision : DigitsEval.Precision
  /-- The checked lower bound of the integral over `[a, b]`. -/
  lo : ℚ
  /-- The checked upper bound of the integral over `[a, b]`. -/
  hi : ℚ

/-- The result of the search over panel counts. -/
private inductive SearchOutcome where
  /-- A quadrature whose enclosure passes the test of the goal. -/
  | found (quadrature : PanelQuadrature)
  /-- No panel count passed: the last count that gave an enclosure, and that enclosure. -/
  | short (panels : Nat) (enclosure? : Option RationalInterval)

/-- The panel counts to search: `n` for `(panels := n)`, and the powers of two up to `cap`
otherwise. -/
private def panelCounts (panels? : Option Nat) (cap : Nat) : List Nat :=
  match panels? with
  | some panels => [panels]
  | none =>
    let cap := max cap 1
    ((List.range (cap.log2 + 1)).map (2 ^ ·)).filter (· ≤ cap)

/-- The first panel count of `counts` whose enclosure at `decider` passes `ok`, with the leanest
precision of `rungs` that still passes and the shortest outward decimal rounding of its
enclosure that passes. -/
private def search (method : PanelMethod) (f d : Verified.Expr (Fin 1)) (a b : ℚ)
    (counts : List Nat) (rungs : List DigitsEval.Precision) (decider : DigitsEval.Precision)
    (ok : RationalInterval → Bool) : SearchOutcome := Id.run do
  let mut outcome : SearchOutcome := .short 0 none
  for panels in counts do
    match method.enclosure decider f d a b panels with
    | none =>
      if outcome matches .short _ none then outcome := .short panels none
    | some I =>
      outcome := .short panels (some I)
      if ok I then
        for p in rungs do
          if let some J := method.enclosure p f d a b panels then
            if ok J then
              for k in [1:40] do
                let lo := roundSig J.lo k false
                let hi := roundSig J.hi k true
                if h : lo ≤ hi then
                  if ok (ofBounds lo hi h) then
                    return .found { method, panels, precision := p, lo, hi }
              return .found { method, panels, precision := p, lo := J.lo, hi := J.hi }
  return outcome

/-- One relation of the generalized goal, read for the test of an enclosure of the integral. -/
private structure RelationLeaf where
  /-- The number of atoms of the reflected expression. -/
  dimension : Nat
  /-- The expression whose bound the relation states, over its atoms. -/
  expression : Verified.Expr (Fin dimension)
  /-- The interval of each atom from its hypotheses, and `none` at the generalized integral. -/
  intervals : Array (Option RationalInterval)
  /-- The stated bound. -/
  stated : StatedBound

/-- Whether an enclosure `E` of the expression of a relation gives its stated bound. -/
private def admits : StatedBound → RationalInterval → Bool
  | .enclosure lo hi, E => decide (lo ≤ E.lo) && decide (E.hi ≤ hi)
  | .upper c strict, E => if strict then decide (E.hi < c) else decide (E.hi ≤ c)
  | .lower c strict, E => if strict then decide (c < E.lo) else decide (c ≤ E.lo)
  | .absolute c strict, E =>
    let m := max |E.lo| |E.hi|
    if strict then decide (m < c) else decide (m ≤ c)
  | .approx _ _, _ => false

/-- Whether the relation holds for every value of the integral in `I`, by one evaluation at the
reference precision. -/
private def RelationLeaf.holdsOn (leaf : RelationLeaf) (I : RationalInterval) : Bool :=
  let env : Fin leaf.dimension → RationalInterval := fun i ↦
    match leaf.intervals[i.val]? with
    | some (some J) => J
    | _ => I
  match DigitsEval.eval reference env leaf.expression with
  | some E => admits leaf.stated E
  | none => false

/-- The sides of a real comparison `≤`, `<`, `≥` or `>`, the smaller first, and whether it is
strict. -/
private def realComparison? (target : Lean.Expr) :
    MetaM (Option (Lean.Expr × Lean.Expr × Bool)) := do
  let target := target.consumeMData
  let arguments := target.getAppArgs
  let sides? : Option (Lean.Expr × Lean.Expr × Lean.Expr × Bool) :=
    if let some (type, smaller, larger) := target.le? then some (type, smaller, larger, false)
    else if let some (type, smaller, larger) := target.lt? then some (type, smaller, larger, true)
    else if target.isAppOfArity ``GE.ge 4 then
      some (arguments[0]!, arguments[3]!, arguments[2]!, false)
    else if target.isAppOfArity ``GT.gt 4 then
      some (arguments[0]!, arguments[3]!, arguments[2]!, true)
    else none
  let some (type, smaller, larger, strict) := sides? | return none
  unless ← isDefEq type (mkConst ``Real) do return none
  return some (smaller, larger, strict)

/-- Read one relation of the goal over the generalized integral `y`. -/
private def readLeaf (y relation : Lean.Expr) : MetaM RelationLeaf := do
  let (expression, stated) ← do
    if let some (recognized, stated) ← BoxInequality.statedBound? relation then
      pure (recognized.expression, stated)
    else if let some (smaller, larger, strict) ← realComparison? relation then
      pure (← mkAppM ``HSub.hSub #[smaller, larger], StatedBound.upper 0 strict)
    else
      throwError "cega: the relation{indentExpr relation}\nis not one of \
        {BoxInequality.relationShapes}"
  let ⟨dimension, reflected⟩ ← BoxInequality.reflectOverBoundedVariables "cega" expression
  let intervals ← reflected.bounds.mapM fun found ↦ do
    if found.atom == y then return none
    if h : found.lower.value ≤ found.upper.value then
      return some (ofBounds found.lower.value found.upper.value h)
    throwError "cega: the hypotheses on `{found.atom}` give the empty interval \
      [{showRational found.lower.value}, {showRational found.upper.value}]"
  return { dimension, expression := reflected.expression, intervals, stated }

/-- The test of an enclosure `I` of the integral over `[a, b]`: every relation of the goal holds
for every value in `I`, negated when the limits are reversed. -/
private def goalTest (motive : Lean.Expr) (reversed : Bool) :
    MetaM (RationalInterval → Bool) :=
  withLocalDeclD `integral (mkConst ``Real) fun y ↦ do
    -- Placeholder bounds, so that the integral is a bounded atom; its interval is the argument.
    let zero ← realRational 0
    let lower ← mkAppM ``LE.le #[zero, y]
    let upper ← mkAppM ``LE.le #[y, zero]
    withLocalDeclD `hlo lower fun _ ↦ withLocalDeclD `hhi upper fun _ ↦
      forallTelescope (motive.instantiate1 y) fun _ body ↦ do
        let leaves ← (← BoxInequality.relationLeaves body).mapM (readLeaf y)
        return fun I ↦ leaves.all (·.holdsOn (if reversed then I.neg else I))

/-- The report of a search whose proposed interval does not give the goal: the interval rounded
outward, its width, and the call with twice the panels when the cap allows one. -/
private def shortReport (method : PanelMethod) (panels : Nat) (enclosure : RationalInterval)
    (config : BareConfig) (cap : Nat) : MessageData :=
  let rawWidth := enclosure.hi - enclosure.lo
  let (rawExponent, _) := if rawWidth ≤ 0 then ((0 : Int), 0) else magnitude rawWidth
  let places := min 40 (max 6 (2 - rawExponent).toNat)
  let (lower, lowerValue) := roundDecimal enclosure.lo places false
  let (upper, upperValue) := roundDecimal enclosure.hi places true
  -- The width of the interval as printed, so that the two agree.
  let (exponent, leading) := magnitude (upperValue - lowerValue + (1 : ℚ) / 10 ^ (places + 1))
  let rule := method.describe ++ " panel" ++ (if panels = 1 then "" else "s")
  let effect := match method with
    | .simpson => "Each doubling of the panels divides the Simpson remainder by 16"
    | .range => "Range panels need only the continuity of the integrand, and more panels \
        usually narrow the interval"
  let next := if config.panels?.isNone && cap < 2 * panels then
      s!"a doubling needs more than the {cap} panels that `cega.maxIntegrationPanels` \
        allows; raise that option, or give `(panels := n)`"
    else
      s!"try `cega{renderConfig config.precision} (panels := {2 * panels})`"
  m!"cega: with {panels} {rule} the search proposes [{lower}, {upper}] for the integral, an \
    interval of width less than {leading / 10}.{leading % 10}e{exponent} that does not prove \
    the stated bound. {effect}; {next}."

/-- An interval integral of the goal, read for the panel search and the kernel check. -/
private structure IntegralProblem where
  /-- The integral as written. -/
  integral : Lean.Expr
  /-- Its integrand and limits. -/
  view : CAS.Tactic.Integration.Reflection.IntervalIntegralApplication
  /-- The goal with the integral abstracted. -/
  motive : Lean.Expr
  /-- The caller-local definitions unfolded to reflect the integrand. -/
  definitions : Array Name
  /-- The smaller limit. -/
  a : ℚ
  /-- The larger limit. -/
  b : ℚ
  /-- Whether the upper limit is the smaller one. -/
  reversed : Bool
  /-- The reflected integrand as a term. -/
  quoted : Lean.Expr
  /-- The validity certificate of the integrand and its first four derivatives on `[a, b]` and
  the quoted fourth derivative, when the domain checker finds one. -/
  simpson? : Option (Lean.Expr × Lean.Expr)
  /-- A proof that the integrand is continuous on `[a, b]`. -/
  continuity : Lean.Expr

/-- The checked statement of a quadrature, its arguments (the implicit arguments of the transport
lemma before the limits), the hypothesis of the lemma, and the lemma. -/
private def quadratureStatement (problem : IntegralProblem) (q : PanelQuadrature) :
    MetaM (Lean.Expr × Array Lean.Expr × Lean.Expr × Name) := do
  let tail := #[toExpr problem.a, toExpr problem.b, toExpr q.panels, toExpr q.lo, toExpr q.hi]
  match q.method, problem.simpson? with
  | .simpson, some (validity, derivative) =>
    let arguments := #[quotePrecision q.precision, problem.quoted, derivative] ++ tail
    let check := mkAppN (mkConst ``BatchSimpson.integralCheck) arguments
    return (← mkEq check (mkConst ``Bool.true), arguments, validity,
      if problem.reversed then ``integral_bounds_of_check_symm else ``integral_bounds_of_check)
  | .simpson, none => throwError "cega: Simpson panels need the validity certificate"
  | .range, _ =>
    let arguments := #[quotePrecision q.precision, problem.quoted] ++ tail
    let check := mkAppN (mkConst ``BatchRange.rangeCheck) arguments
    return (← mkEq check (mkConst ``Bool.true), arguments, problem.continuity,
      if problem.reversed then ``integral_bounds_of_rangeCheck_symm
      else ``integral_bounds_of_rangeCheck)

/-- Close the main goal from the quadrature `q`: transport the checked bounds to the integral as
written, prove the goal generalized to any real between them by the box route, and only then
evaluate the check in the kernel. When the box route fails, the error is `short?` if given (the
report of a search that came up short), and otherwise the proposed interval and the box route's
error; every other failure is reported as it is. -/
private def attempt (config : BareConfig) (problem : IntegralProblem) (q : PanelQuadrature)
    (short? : Option MessageData := none) : TacticM Unit := do
  let mainGoal ← getMainGoal
  let (checkType, arguments, hypothesis, transport) ← quadratureStatement problem q
  let checkMVar ← mkFreshExprMVar checkType
  let (lowerLimit, upperLimit) := if problem.reversed then
      (problem.view.upper, problem.view.lower)
    else (problem.view.lower, problem.view.upper)
  let ha ← prove (← mkEq (← realRational problem.a) lowerLimit) (← `(tactic| norm_num))
  let hb ← prove (← mkEq (← realRational problem.b) upperLimit) (← `(tactic| norm_num))
  let hFType ← withLocalDeclD `x (mkConst ``Real) fun x ↦ do
    mkForallFVars #[x] (← mkEq (← mkAppM ``Verified.Expr.univariateEval #[problem.quoted, x])
      (mkApp problem.view.function x).headBeta)
  let definitions ← problem.definitions.mapM fun name ↦
    `(Lean.Parser.Tactic.simpLemma| $(mkIdent name):ident)
  -- `rfl` comes last: on `√(x ^ 2) = |x|`, the reflection of the absolute value, it exceeds the
  -- recursion limit, which `first` does not catch. Only the second attempt writes natural powers
  -- as real powers, since that hides the square from `Real.sqrt_sq_eq_abs`.
  let hF ← prove hFType (← `(tactic| (intro x; first
    | (simp only [Verified.Expr.univariateEval, Verified.Expr.eval, PiLp.toLp_apply,
        WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.isValue,
        Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Int.cast_ofNat, Int.cast_zero,
        Int.cast_one, Int.cast_neg, Int.cast_natCast, one_div, Real.tan_eq_sin_div_cos,
        Real.sinh_eq, Real.cosh_eq, Real.tanh_eq, Real.sqrt_sq_eq_abs, $definitions,*]; done)
    | (simp only [Verified.Expr.univariateEval, Verified.Expr.eval, PiLp.toLp_apply,
        WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.isValue,
        Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Int.cast_ofNat, Int.cast_zero,
        Int.cast_one, Int.cast_neg, Int.cast_natCast, one_div, Real.tan_eq_sin_div_cos,
        Real.sinh_eq, Real.cosh_eq, Real.tanh_eq, Real.sqrt_sq_eq_abs, ← Real.rpow_natCast,
        Real.rpow_intCast, $definitions,*]; done)
    | (norm_num [Verified.Expr.univariateEval, Verified.Expr.eval, PiLp.toLp_apply,
        WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.isValue,
        Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Int.cast_ofNat, Int.cast_zero,
        Int.cast_one, Int.cast_neg, Int.cast_natCast, one_div, Real.tan_eq_sin_div_cos,
        Real.sinh_eq, Real.cosh_eq, Real.tanh_eq, Real.sqrt_sq_eq_abs, ← Real.rpow_natCast,
        Real.rpow_intCast, $definitions,*]; done)
    | rfl)))
  -- The limits of the lemma are those of the integral as written, in either order of `a, b`.
  let bounds := mkAppN (mkConst transport) (arguments ++
    #[problem.view.lower, problem.view.upper, problem.view.function, hypothesis, checkMVar, ha,
      hb, hF])
  Lean.Meta.check bounds
  let boundsType ← instantiateMVars (← inferType bounds)
  let some (lowerBound, upperBound) := boundsType.and?
    | throwError "cega: unexpected shape of the quadrature bound{indentExpr boundsType}"
  let (some (_, loReal, _), some (_, _, hiReal)) := (lowerBound.le?, upperBound.le?)
    | throwError "cega: unexpected shape of the quadrature bound{indentExpr boundsType}"
  let generalized ← withLocalDeclD `integral (mkConst ``Real) fun y ↦ do
    let lower ← mkAppM ``LE.le #[loReal, y]
    let upper ← mkAppM ``LE.le #[y, hiReal]
    withLocalDeclD `hlo lower fun hlo ↦ withLocalDeclD `hhi upper fun hhi ↦
      mkForallFVars #[y, hlo, hhi] (problem.motive.instantiate1 y)
  let goal ← mkFreshExprSyntheticOpaqueMVar generalized
  let (shownLo, shownHi) := if problem.reversed then (-q.hi, -q.lo) else (q.lo, q.hi)
  let saved ← getGoals
  try
    setGoals [goal.mvarId!]
    discard <| BoxInequality.closeMainGoal "cega" config.precision true
  catch error =>
    if let some report := short? then throwError report
    throwError "cega: the quadrature search proposes [{showRational shownLo}, \
      {showRational shownHi}] for the integral, and the box route did not prove the goal from \
      that interval:{indentD error.toMessageData}"
  finally
    setGoals saved
  let closed ← instantiateMVars goal
  if closed.hasExprMVar then
    throwError "cega: the box route left goals of the generalized integral bound"
  let operation := match q.method with
    | .simpson => "CEGA batch quadrature"
    | .range => "CEGA range quadrature"
  checkMVar.mvarId!.assign (← KernelReadBack.decideByKernel operation checkType)
  let proof ← instantiateMVars <| mkApp3 closed problem.integral
    (mkApp3 (mkConst ``And.left) lowerBound upperBound bounds)
    (mkApp3 (mkConst ``And.right) lowerBound upperBound bounds)
  mainGoal.assign proof
  replaceMainGoal []
  trace[cega.integration] "{q.panels} {q.method.describe} panels at the precision \
    ({q.precision.bits}, {q.precision.terms}, {q.precision.logTerms}) put the integral in \
    [{showRational shownLo}, {showRational shownHi}]"

/-- Prove a goal about one interval integral with rational limits and a closed elementary
integrand, as the module documentation describes, and return the replay of the call. -/
def close (config : BareConfig) : TacticM (TSyntax `tactic) := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let integrals := intervalIntegrals target
  let some integral := integrals[0]? | throwError "cega: the goal has no interval integral"
  if 1 < integrals.size then
    throwError "cega: the goal has {integrals.size} interval integrals; the integral route \
      bounds one integral at a time: prove a bound on each with `have` and combine them"
  let some view := CAS.Tactic.Integration.Reflection.intervalIntegralApplication? integral
    | throwError "cega: the interval integral{indentExpr integral}\ncould not be read"
  CAS.Tactic.Integration.Reflection.ensureVolumeMeasure view.measure
  let some A ← Classify.rationalLiteral? view.lower
    | throwError "cega: the integral route needs rational limits; the lower limit is\
        {indentExpr view.lower}"
  let some B ← Classify.rationalLiteral? view.upper
    | throwError "cega: the integral route needs rational limits; the upper limit is\
        {indentExpr view.upper}"
  let replay ← BoxInequality.bareSyntax config.precision config.panels?
  if A = B then
    let siblings := (← getGoals).drop 1
    evalTactic (← `(tactic| norm_num [intervalIntegral.integral_same]))
    unless (← getGoals) == siblings do
      let remaining ← (← getGoals).filterM fun goal ↦ return !siblings.contains goal
      let shown ← remaining.mapM fun goal ↦ goal.withContext do instantiateMVars (← goal.getType)
      let shown := MessageData.joinSep (shown.map MessageData.ofExpr) "\n"
      throwError "cega: the integral is over an empty interval, so it is 0, and `norm_num` did \
        not prove the goal that remains:{indentD shown}"
    return replay
  let a := min A B
  let b := max A B
  let reversed := decide (B < A)
  let (f, definitions) ← reflectIntegrand view.function
  discard <| validateQueryInput .plain config.precision f
  let quoted ← CAS.Command.quoteVerifiedExpr f
  let motive ← kabstract target integral
  let ok ← goalTest motive reversed
  let cap := cega.maxIntegrationPanels.get (← getOptions)
  let counts := panelCounts config.panels? cap
  let (rungs, decider) := match config.precision.digits with
    | some digits => ([DigitsEval.precisionFor digits], DigitsEval.precisionFor digits)
    | none => (ladder ++ [reference], reference)
  let validity? ← validityOn? quoted a b
  let derivative := f.symbolicDerivative 4
  let simpson? ← validity?.mapM fun validity ↦ do
    return (validity, ← CAS.Command.quoteVerifiedExpr derivative)
  let continuity ← match validity? with
    | some validity => do
      pure <| mkAppN (mkConst ``continuousOn_of_valid)
        #[quoted, toExpr a, toExpr b, ← orderProof a b, validity]
    | none => do
      let type ← mkAppM ``ContinuousOn
        #[← mkAppM ``Verified.Expr.univariateEval #[quoted], ← intervalDomain a b]
      try
        prove type (← `(tactic|
          (unfold Verified.Expr.univariateEval
           dsimp only [Verified.Expr.eval]
           fun_prop)))
      catch _ =>
        throwError "cega: the integral route needs the integrand to be continuous on \
          [{showRational a}, {showRational b}]: the domain checker found no certificate that \
          it and its first four derivatives are defined there, and `fun_prop` did not prove \
          its continuity"
  let problem : IntegralProblem :=
    { integral, view, motive, definitions, a, b, reversed, quoted, simpson?, continuity }
  -- Simpson panels first when the integrand is smooth; their shortfall is the one reported.
  let (method, outcome) : PanelMethod × SearchOutcome :=
    match simpson? with
    | none => (.range, search .range f f a b counts rungs decider ok)
    | some _ =>
      match search .simpson f derivative a b counts rungs decider ok with
      | .found q => (.simpson, .found q)
      | .short panels enclosure? =>
        match search .range f f a b counts rungs decider ok with
        | .found q => (.range, .found q)
        | .short rangePanels rangeEnclosure? =>
          if enclosure?.isNone && rangeEnclosure?.isSome then
            (.range, .short rangePanels rangeEnclosure?)
          else (.simpson, .short panels enclosure?)
  match outcome with
  | .found q => attempt config problem q
  | .short panels (some enclosure) =>
    attempt config problem
      { method, panels, precision := decider, lo := enclosure.lo, hi := enclosure.hi }
      (shortReport method panels (if reversed then enclosure.neg else enclosure) config cap)
  | .short _ none =>
    throwError "cega: the integrand could not be enclosed on the panels of \
      [{showRational a}, {showRational b}] at any panel count tried; it may be undefined or \
      unbounded there"
  return replay

end CAS.CEGA.Integration

end
