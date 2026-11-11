/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.CEGA.Query
public import CAS.Elaboration.RealExpression
public import CAS.Command.Syntax
public import CAS.Exact.ExpressionSideConditions
public import CAS.Tactic.KernelReadBack
public meta import CAS.Continuum.IntervalEval.Core
public meta import CAS.Continuum.IntervalEval.Planning.Precision
public meta import CAS.Continuum.IntervalEval.Registry.Monotonicity
public meta import Lean.Meta.Native
public meta import CAS.Numerics.CompactLiteral
public import CAS.Numerics.CompactLiteral
import Lean.Meta.Native

/-!
# Elaboration support for finite-dimensional CEGA queries

Elaboration code shared by the numerical `#cas` commands and the `cega` tactics, so that a
command and a tactic give an input the same meaning. `parseBindings` reads the box `x in [a, b]`
(category `cegaIntervalBinding`, rational endpoints with `a ≤ b`); `parsePrecision` reads the
options `(prec := n)`, `(depth := n)`, `(expOrder := n)`, `(sqrtDigits := n)`, `(logTerms := n)`
and `(digits := n)`, and `parseBareConfig` these and the Simpson panels `(panels := n)` of an
integral bound in bare `cega`. A query encloses the expression on the box by an
`EnclosureMethod`, the planner of `CAS.CEGA.Query` on the whole box or the hull of its enclosures
after checked subdivision, and states one projection of it, a `BoxQueryMode`: the enclosure, an
upper bound, an absolute bound or a midpoint approximation. `runBoxQuery` returns the rationals
to display with a kernel-checked theorem and the semantic certificate rebuilt from it, or `none`
when no route succeeds; `runEncloseViews` states all four projections of one enclosure in one
theorem, and `checkStatedBounds` proves bounds that a goal states with rationals. InfoView
rendering and tactic-state management stay in the frontends.

## Implementation notes

A frontend passes the box and the expression reflected into `Verified.Expr`. We quote both, with
the precision policy, into the closed term `encloseBoxWith? precision box expr`, or into
`encloseBoxSubdividedAtWith?` with the first split at the widest coordinate the expression
mentions (`selectSubdivisionCoordinate?`, untrusted). `runBoxQuery` and `runEncloseViews` reduce
that term with the kernel's evaluator (`kernelWhnf`), so the kernel runs the search, and read all
displayed rationals in one more kernel evaluation (`Verified.Expr.Serial.encodeRationals`). We
reduce in the kernel because the elaborator's `whnf` counts the planner's nesting against
`maxRecDepth`, which even `x ^ 2 + x` on `[0, 1]` exceeds, and because the kernel is faster.
Nothing read back is trusted. The theorem applies `BoxQueryMode.soundTheorem` (the
`..._of_interval_eq` theorems of `CAS.Continuum.IntervalEval.Attempt`) and the
`..._of_rational_components` transports to the payload and to `Eq.refl` proofs that its fields
have the numerators and denominators read; `addKernelCheckedTheorem` hands it to the kernel
through the auxiliary-lemma cache (`ProofCarrier.mkKernelAuxLemma`). A theorem of the same
proposition that the kernel has already checked in this environment, with the standard axioms
only, is reused with no evaluation; otherwise the kernel checks the new theorem, which evaluates
the query again. `boxQueryCache` memoizes the reductions of `runBoxQuery`, not the checks of
theorems.

`checkStatedBounds` reads nothing back. It applies `StatedBound.checkTheorem`, an `..._of_check`
theorem of `CAS.CEGA.Query`, to the unevaluated query and to `Eq.refl true`, as `decide +kernel`
does, with the tests of several bounds joined by `&&`: the kernel runs the planner once and
compares its interval with every stated rational while it checks the theorem. `addStatedTheorem`
never takes a theorem from Lean's auxiliary-lemma cache, which is keyed on the statement alone,
so a bound checked at one precision never stands in for a query at another; `statedBoundCache`
keeps the kernel's verdicts, rejections included. A rejected bound is reported with the values
that `readQueryDisplay?` reads in one kernel evaluation, without a certificate theorem. Since the
kernel runs the search, `validateQueryInput` and `validateQueryBox` refuse a query before any
kernel work when it exceeds `boxQueryNodeLimit` nodes, natural exponent 4096, `cega.maxDimension`
coordinates, `cega.maxFaceReductions` possible monotonicity reductions (`plannerFaceReductions`),
`cega.maxPrecision` or `cas.maxDigits`, or, when subdivided, `cega.maxRefinementWork` estimated
planner calls (`refinementWorkWithin?`).

`decideClosedCertificate` proves a closed decidable statement by `KernelReadBack.decideByKernel`,
a theorem `of_decide_eq_true (Eq.refl true)` checked in the kernel. Only `cega [fast]` with
`cega.nativeCertificates = true` evaluates natively. It sets the internal option
`cega.nativePolynomial`; a plain box query then computes `RationalInterval.evalPolynomial` in
compiled code, proves `evalPolynomial box expr = some I` by `nativeEqTrue` under the name
`cegaFast` and makes the enclosure by `polynomialBoxAttempt`, and `decideClosedCertificate` with
`native` evaluates a closed decision procedure the same way unless a kernel theorem of the
statement is already cached. Such a proof also trusts Lean's compiler and runtime, through the
axiom that `nativeEqTrue` adds; the projections and transports around it are still checked by
the kernel. Native proofs are added outside the auxiliary-lemma cache and never memoized, so no
kernel route receives one, and `checkStatedBounds` never evaluates natively.
-/

public meta section

namespace CAS.CEGA.Elaboration

open Lean Elab Term Meta
open CAS
open CAS.Certificate
open CAS.Continuum
open CAS.Continuum.RationalInterval

/--
Expose certified rational endpoints as real numerator/denominator quotients.
The component equalities tie the displayed literals to the original enclosure.
-/
theorem enclosedOn_of_rational_components
    {α : Type} {f : α → ℝ} {s : Set α} {lo hi : ℚ}
    (h : EnclosedOn f s (lo : ℝ) (hi : ℝ))
    (loNum hiNum : ℤ) (loDen hiDen : ℕ)
    (hloNum : lo.num = loNum) (hloDen : lo.den = loDen)
    (hhiNum : hi.num = hiNum) (hhiDen : hi.den = hiDen) :
    EnclosedOn f s
      ((loNum : ℝ) / (loDen : ℝ))
      ((hiNum : ℝ) / (hiDen : ℝ)) := by
  subst loNum loDen hiNum hiDen
  simpa only [Rat.cast_def] using h

/-- Transport a certified upper bound to quotient syntax after checking its rational components. -/
theorem boundOn_of_rational_components
    {α : Type} {f : α → ℝ} {s : Set α} {upper : ℚ}
    (h : BoundOn f s (upper : ℝ))
    (upperNum : ℤ) (upperDen : ℕ)
    (hupperNum : upper.num = upperNum)
    (hupperDen : upper.den = upperDen) :
    BoundOn f s ((upperNum : ℝ) / (upperDen : ℝ)) := by
  subst upperNum upperDen
  simpa only [Rat.cast_def] using h

/--
Expose a constant approximation and its error radius as real quotients, with
component equalities preserving the certified center and radius.
-/
theorem approxOn_of_rational_components
    {α : Type} {f : α → ℝ} {s : Set α} {center radius : ℚ}
    (h : ApproxOn f (fun _ ↦ (center : ℝ)) s (radius : ℝ))
    (centerNum radiusNum : ℤ) (centerDen radiusDen : ℕ)
    (hcenterNum : center.num = centerNum)
    (hcenterDen : center.den = centerDen)
    (hradiusNum : radius.num = radiusNum)
    (hradiusDen : radius.den = radiusDen) :
    ApproxOn f
      (fun _ ↦ (centerNum : ℝ) / (centerDen : ℝ))
      s ((radiusNum : ℝ) / (radiusDen : ℝ)) := by
  subst centerNum centerDen radiusNum radiusDen
  simpa only [Rat.cast_def] using h

/-! ## Input syntax and exact boxes -/

/-- What a box query certifies about the values of its expression on the box, read off the
interval of its enclosure: the projection that the goal needs. How that enclosure is computed is
the query's `EnclosureMethod`. -/
inductive BoxQueryMode where
  /-- Lower and upper bounds, as `EnclosedOn`. -/
  | enclose
  /-- An upper bound, as `BoundOn`. -/
  | bound
  /-- An upper bound for the absolute value, as `BoundOn` of `|f ·|`. -/
  | absBound
  /-- A constant midpoint approximation and its uniform error, as `ApproxOn`. -/
  | approx
deriving DecidableEq, Repr, Hashable

namespace BoxQueryMode

/-- Internal name of each query mode, as the `trace.cega.stated` output shows it. The command and
tactic syntax spells every query `[enclose ...]`: the goal selects the projection, and
`(depth := n)` the subdivided enclosure. -/
def surfaceName : BoxQueryMode → String
  | .enclose => "enclose"
  | .bound => "bound"
  | .absBound => "absBound"
  | .approx => "approx"

/-- The certificate a query in each mode produces, as messages name it. -/
def certificateName : BoxQueryMode → String
  | .enclose => "enclosure"
  | .bound => "upper bound"
  | .absBound => "absolute bound"
  | .approx => "midpoint approximation"

/-- Soundness theorem underlying the kernel-checked result for each query mode. -/
def soundTheorem : BoxQueryMode → Name
  | .enclose => ``EnclosureAttempt.enclosedOn_of_interval_eq
  | .bound => ``EnclosureAttempt.boundOn_of_interval_eq
  | .absBound => ``EnclosureAttempt.boundOn_abs_of_interval_eq
  | .approx => ``EnclosureAttempt.approxOn_center_of_interval_eq

end BoxQueryMode

/-- How a box query computes the enclosure that its mode projects. Every mode reads its result
off either one, since both are enclosures of the expression on the whole box. -/
inductive EnclosureMethod where
  /-- The planner's enclosure of the whole box (`CAS.CEGA.encloseBoxWith?`). -/
  | plain
  /-- The hull of the planner's enclosures of the pieces of the box after checked bisection, to
  the subdivision depth of the precision policy (`CAS.CEGA.encloseBoxSubdividedAtWith?`). -/
  | subdivided
deriving DecidableEq, Repr, Hashable

/-- The name of a query in messages and traces, such as `subdivided bound query`. -/
def queryLabel (mode : BoxQueryMode) (method : EnclosureMethod) : String :=
  match method with
  | .plain => s!"{mode.surfaceName} query"
  | .subdivided => s!"subdivided {mode.surfaceName} query"

/-! ## Failure diagnostics -/

/-- Branch-sensitive operations occurring in one finite-box expression. -/
private structure DomainFeatures where
  division : Bool := false
  logarithm : Bool := false

namespace DomainFeatures

private def append (a b : DomainFeatures) : DomainFeatures where
  division := a.division || b.division
  logarithm := a.logarithm || b.logarithm

private def ofExpr {ι : Type*} : Verified.Expr ι → DomainFeatures
  | .nat _ | .int _ | .rat _ _ | .pi | .e | .var _ => {}
  | .add a b | .mul a b | .sub a b => (ofExpr a).append (ofExpr b)
  | .div a b =>
      { ((ofExpr a).append (ofExpr b)) with division := true }
  | .neg a | .pow a _ | .sin a | .cos a | .atan a | .asin a | .acos a | .exp a => ofExpr a
  | .log a => { (ofExpr a) with logarithm := true }
  | .sqrt a => ofExpr a
  | .rpow a b => { ((ofExpr a).append (ofExpr b)) with logarithm := true }

private def requirements (features : DomainFeatures) : List String :=
  (if features.division then
      ["check whether denominator intervals exclude zero"]
    else []) ++
  (if features.logarithm then
      ["check whether nonconstant logarithm argument intervals exclude zero"]
    else [])

end DomainFeatures

/-- Suggest possible obstructions after route search fails, without asserting a domain violation. -/
def boxQueryFailureMessage {ι : Type*}
    (method : EnclosureMethod) (expr : Verified.Expr ι)
    (subdivision : String := "`(depth := n)` subdivision") :
    String :=
  let requirements := (DomainFeatures.ofExpr expr).requirements
  if requirements.isEmpty then
    match method with
    | .subdivided =>
        "no checked interval route could enclose this expression on all required child boxes; \
          simplify the expression or restrict the domain"
    | .plain =>
        s!"no checked interval route could enclose this expression on the requested box; \
          simplify the expression, restrict the domain, or try {subdivision}"
  else
    let joined := "; ".intercalate requirements
    let remedy :=
      match method with
      | .subdivided =>
          "The checked split did not produce an enclosure. Restrict the domain or rewrite \
            the expression to make these facts interval-visible; even then, a supported \
            route may be unavailable"
      | .plain =>
          s!"Restrict the domain or rewrite the expression to make these facts interval-visible. \
            {subdivision} still needs a checked enclosure on every child box"
    s!"no checked interval route succeeded on this box. Possible domain obstruction: \
      {joined}. This is a search diagnostic, not a proof that the expression is singular. {remedy}"

/-- A named coordinate together with its exact rational interval. -/
structure BoxBinding where
  /-- Coordinate name used while reifying the input expression. -/
  coordinate : Name
  /-- Checked interval assembled from the ordered endpoints. -/
  interval : RationalInterval

/-- Syntax category for one coordinate of an exact rational box. -/
declare_syntax_cat cegaIntervalBinding

/-- A coordinate name and its closed rational interval. -/
syntax ident " in " "[" term ", " term "]" : cegaIntervalBinding

/-- Render a rational without a denominator when it is an integer. -/
def renderRational (value : ℚ) : String :=
  if value.den = 1 then
    toString value.num
  else
    s!"{value.num}/{value.den}"

/--
Parse one exact coordinate binding.

The endpoint parser accepts only rational syntax, and the order proof stored
in `RationalInterval` is constructed only after deciding the exact inequality.
-/
def parseBinding {m : Type → Type} [Monad m] [MonadError m]
    (stx : Syntax) : m BoxBinding := do
  match stx with
  | `(cegaIntervalBinding| $coordinate:ident in [$lower:term, $upper:term]) =>
      let a ← CAS.Command.parseRationalLiteral lower
      let b ← CAS.Command.parseRationalLiteral upper
      if h : a ≤ b then
        return {
          coordinate := coordinate.getId
          interval := RationalInterval.ofBounds a b h
        }
      else
        throwErrorAt stx
          "interval endpoints are reversed: {renderRational a} > {renderRational b}"
  | _ =>
      throwErrorAt stx "malformed numerical coordinate binding"

/-- Parse an array of exact coordinate bindings; nonemptiness is a frontend requirement. -/
def parseBindings {m : Type → Type} [Monad m] [MonadError m]
    (bindings : Array Syntax) : m (List BoxBinding) :=
  bindings.toList.mapM parseBinding

/-! ## Precision options -/

/-- Render a precision policy for reports. -/
def renderPrecision (precision : Precision) : String :=
  s!"exp order {precision.expOrder}, sqrt digits {precision.sqrtDigits}, \
    log terms {precision.logTerms}, subdivision depth {precision.depth}" ++
    match precision.digits with
    | some digits => s!", {digits} digits"
    | none => ""

/-- The configuration items, as written before the brackets of a `cega` call, that request
`precision`: every field that differs from the default policy, with three equal
elementary-function fields written as the one `(prec := n)` that sets them, and a leading space
when there is any. `"cega" ++ renderConfig p` is the bare call with policy `p`. -/
def renderConfig (precision : Precision) : String :=
  let defaults : Precision := {}
  let item (name : String) (value : Nat) : String := s!" ({name} := {value})"
  let uniform := precision.expOrder = precision.sqrtDigits ∧
    precision.sqrtDigits = precision.logTerms ∧ precision.expOrder ≠ defaults.expOrder
  let fields :=
    if uniform then item "prec" precision.expOrder
    else
      (if precision.expOrder ≠ defaults.expOrder then item "expOrder" precision.expOrder
        else "") ++
      (if precision.sqrtDigits ≠ defaults.sqrtDigits then item "sqrtDigits" precision.sqrtDigits
        else "") ++
      (if precision.logTerms ≠ defaults.logTerms then item "logTerms" precision.logTerms
        else "")
  let depth := if precision.depth ≠ defaults.depth then item "depth" precision.depth else ""
  let digits := match precision.digits with
    | some digits => item "digits" digits
    | none => ""
  fields ++ depth ++ digits

/-- `precision` with its three elementary-function fields raised to one value, at least `16` and
at least twice each current field, so that no field decreases: the policy to suggest when an
enclosure may be limited by precision. -/
def raisedPrecision (precision : Precision) : Precision :=
  precision.withPrec <| max 16 <|
    2 * max precision.expOrder (max precision.sqrtDigits precision.logTerms)

/-- The name, the syntax of the name and the value of one configuration item `(name := n)` of a
CEGA query. -/
private def configValue {m : Type → Type} [Monad m] [MonadError m] (item : Syntax) :
    m (Name × Syntax × Nat) := do
  -- A value item is `"(" ident ":=" term ")"`; other item shapes are Boolean toggles.
  let some (name, value) := CAS.Command.valueConfigItem? item
    | throwErrorAt item "CEGA precision options have the form `(name := n)`"
  let some n := value.isNatLit?
    | throwErrorAt value "CEGA precision options take natural-number literals"
  return (name, item[1], n)

/-- `precision` with the precision option `name` set to `n`, or `none` when `name` is not a
precision option. -/
private def withPrecisionItem (precision : Precision) (name : Name) (n : Nat) :
    Option Precision :=
  match name with
  | `prec => some (precision.withPrec n)
  | `depth => some (precision.withDepth n)
  | `expOrder => some { precision with expOrder := n }
  | `sqrtDigits => some { precision with sqrtDigits := n }
  | `logTerms => some { precision with logTerms := n }
  | `digits => some { precision with digits := some n }
  | _ => none

/--
Parse the optional configuration group of a numerical query.

Supported items are `(prec := n)`, which requests `n` Taylor terms for `exp` and
`log` and `n` binary digits for square roots; `(depth := n)`, the requested
bisection-depth budget of the subdivided enclosure; the individual fields
`(expOrder := n)`, `(sqrtDigits := n)`, and `(logTerms := n)`; and `(digits := n)`, the
requested decimal digits, with which box enclosures first try `DigitsEval.eval`. Values are
natural-number literals. The command and tactic select an initial split even
when `n = 0`; its children receive an additional depth budget of `n - 1`, with
subtraction truncated at zero. The policy selects which certificate to construct;
each successful result still requires its soundness proof.
-/
def parsePrecision {m : Type → Type} [Monad m] [MonadError m]
    (optConfig : Syntax) : m Precision := do
  let mut precision : Precision := {}
  for item in CAS.Command.configItems 16 optConfig do
    let (name, option, n) ← configValue item
    if let some updated := withPrecisionItem precision name n then
      precision := updated
    else if name == `panels then
      throwErrorAt option "`panels` sets the Simpson panels of an integral bound in bare \
        `cega`; an enclosure query has no integral"
    else
      throwErrorAt option
        "unknown CEGA precision option '{name}'; expected prec, depth, expOrder, \
          sqrtDigits, logTerms, or digits"
  return precision

/-- The configuration of bare `cega`, the items of its group `(name := n)`. -/
structure BareConfig where
  /-- The precision policy of its box queries and of the quadrature of an integral bound. -/
  precision : Precision := {}
  /-- The value of an explicit `(prec := n)`, which also sets the working precision of the
  interval route for a closed goal. -/
  prec? : Option Nat := none
  /-- The value of an explicit `(panels := n)`: the number of panels of an integral bound, used
  as given instead of the doubling search. -/
  panels? : Option Nat := none

/-- Parse the configuration group of bare `cega`: the precision options that `parsePrecision`
reads and `(panels := n)` with `n ≥ 1`. -/
def parseBareConfig {m : Type → Type} [Monad m] [MonadError m]
    (optConfig : Syntax) : m BareConfig := do
  let mut config : BareConfig := {}
  for item in CAS.Command.configItems 16 optConfig do
    let (name, option, n) ← configValue item
    if let some precision := withPrecisionItem config.precision name n then
      config := { config with precision }
      if name == `prec then
        config := { config with prec? := some n }
    else if name == `panels then
      if n = 0 then
        throwErrorAt option "`(panels := 0)` gives no panel; the panels of an integral bound \
          are `(panels := n)` with `n ≥ 1`"
      config := { config with panels? := some n }
    else
      throwErrorAt option
        "unknown CEGA option '{name}'; expected prec, depth, expOrder, sqrtDigits, \
          logTerms, digits, or panels"
  return config

/-- The enclosure method that the configuration group `optConfig` requests: subdivision when
it sets the depth `(depth := n)`, the plain enclosure otherwise. -/
def requestedMethod (optConfig : Syntax) : EnclosureMethod :=
  if (CAS.Command.configItems 16 optConfig).any fun item ↦
      (CAS.Command.valueConfigItem? item).any (·.1 == `depth) then
    .subdivided
  else
    .plain

/-! ## Checked query reduction -/

/-- Values projected from a checked CEGA result, parameterized by representation. -/
inductive BoxQueryDisplay (α : Type) where
  /-- Lower and upper enclosure endpoints. -/
  | enclosure (lower upper : α)
  /-- A one-sided upper bound. -/
  | upperBound (upper : α)
  /-- A one-sided absolute-value bound. -/
  | absoluteBound (upper : α)
  /-- Midpoint and uniform approximation radius. -/
  | midpointApprox (center radius : α)
deriving Repr

/--
The checked output shared by the command and tactic frontends.

The proposition is the type of `proof`, an auxiliary theorem already checked
by the kernel, while the underlying soundness theorem is determined by the
query mode. `certificate` is the ordinary semantic certificate rebuilt from
the same proof for `CAS.Tactic.Certificate`.
-/
structure BoxQueryResult where
  private mk ::
  /-- Exact rational values presented to users. -/
  display : BoxQueryDisplay ℚ
  /-- Compact semantic certificate whose fields match the displayed values. -/
  certificate : Lean.Expr
  /--
  Kernel-checked proof of the concise semantic proposition.

  This is the constant naming the auxiliary theorem that the query added to the
  environment; the kernel accepted its proof before the result was returned.
  -/
  proof : Lean.Expr

private def integerExprAsReal (value : Lean.Expr) : MetaM Lean.Expr :=
  mkAppOptM ``Int.cast #[
    some (mkConst ``Real),
    none,
    some value
  ]

private def rationalComponentsAsReal
    (numerator denominator : Lean.Expr) : MetaM Lean.Expr := do
  mkAppM ``HDiv.hDiv #[
    ← integerExprAsReal numerator,
    ← CAS.Elaboration.RealExpression.realNatCast denominator
  ]

private def functionDomain (fn : Lean.Expr) : MetaM Lean.Expr := do
  match ← whnf (← inferType fn) with
  | .forallE _ domain _ _ => return domain
  | _ =>
      throwError
        "internal CEGA numerical error: certified expression is not a function"

/--
Construct the concise proposition displayed for checked numerical evidence.

The full evaluator internals remain in the certificate; this proposition
states the exact function, box, and rational output certified by the query.
-/
private def compactProposition
    (mode : BoxQueryMode) (box quotedExpr : Lean.Expr)
    (display : BoxQueryDisplay Lean.Expr) : MetaM Lean.Expr := do
  let fn ← mkAppM ``Exact.exprFn #[quotedExpr]
  let domain ← mkAppM ``boxDomain #[box]
  match mode, display with
  | .enclose, .enclosure lower upper =>
      mkAppM ``EnclosedOn #[fn, domain, lower, upper]
  | .bound, .upperBound upper =>
      mkAppM ``BoundOn #[fn, domain, upper]
  | .absBound, .absoluteBound upper => do
      let absFn ← withLocalDeclD `x (← functionDomain fn) fun x ↦ do
        let value ← mkAppM ``abs #[mkApp fn x]
        mkLambdaFVars #[x] value
      mkAppM ``BoundOn #[absFn, domain, upper]
  | .approx, .midpointApprox center radius => do
      let reference ← withLocalDeclD `x (← functionDomain fn) fun x ↦
        mkLambdaFVars #[x] center
      mkAppM ``ApproxOn #[fn, reference, domain, radius]
  | _, _ =>
      throwError "internal CEGA numerical error: mode and display data disagree"

/--
Reduce a closed expression to weak head normal form with the kernel's evaluator.

Checked queries and their certificate projections evaluate through nested
rational arithmetic and route selection whose depth grows with the
certificate. The elaborator's `whnf` counts that nesting against
`maxRecDepth`, which even `x ^ 2 + x` on `[0, 1]` exceeds; the kernel evaluator
has no such limit, is considerably faster, and is the evaluator that checks
the resulting certificate theorem anyway. Nothing read from the result is
trusted: the theorem built from it is checked by the kernel separately.
-/
def kernelWhnf (expression : Lean.Expr) : MetaM Lean.Expr :=
  Tactic.KernelReadBack.kernelWhnf expression "CEGA query evaluation"

/-- Reduce a closed natural-number expression to a literal. -/
private def reducedNatValue? (expression : Lean.Expr) : MetaM (Option Nat) := do
  getNatValue? (← kernelWhnf expression)

/-- Reduce a closed integer expression to a literal through its constructor form. -/
private def reducedIntValue? (expression : Lean.Expr) : MetaM (Option Int) := do
  let reduced ← kernelWhnf expression
  if let some value ← getIntValue? reduced then
    return some value
  match_expr reduced with
  | Int.ofNat n => return (← reducedNatValue? n).map Int.ofNat
  | Int.negSucc n => return (← reducedNatValue? n).map Int.negSucc
  | _ => return none

private structure EvaluatedRationalProjection where
  value : ℚ
  term : Lean.Expr
  numerator : Lean.Expr
  denominator : Lean.Expr
  numeratorProof : Lean.Expr
  denominatorProof : Lean.Expr

private structure EvaluatedProjectionValue (α : Type) where
  value : α
  term : Lean.Expr
  proof : Lean.Expr

/--
Evaluate one closed structure projection to a literal.

The projection is reduced only to read the displayed value. The returned
equality between the projection and its literal is stated with `Eq.refl` and
is not verified here: the kernel verifies it, by evaluating the projection
again, when `runBoxQueryCore` adds the finished certificate theorem to the
environment.
-/
private def evaluateProjectionValue
    {α : Type} (field : String) (expression : Lean.Expr)
    (read? : Lean.Expr → MetaM (Option α)) (quote : α → Lean.Expr) :
    MetaM (EvaluatedProjectionValue α) := do
  let value? ← profileitM Exception s!"CEGA reduce {field}" (← getOptions) do
    read? expression
  let some value := value?
    | throwError
        "numerical certificate field '{field}' did not reduce to a closed display value"
  let normalized := quote value
  let proof := mkExpectedPropHint (← mkEqRefl normalized) (← mkEq expression normalized)
  return { value, term := normalized, proof }

/--
Evaluate the numerator and denominator of one rational projection.

The semantic term uses only real casts of those components. It therefore
does not embed the rational constructor's internal coprimality proof into
every generated theorem. The numerator and denominator are read separately;
their projection equalities are checked in the finished certificate theorem.
-/
private def evaluateRationalProjection
    (field : String) (expression : Lean.Expr) :
    MetaM EvaluatedRationalProjection := do
  let numerator ←
    evaluateProjectionValue s!"{field} numerator"
      (← mkAppM ``Rat.num #[expression]) reducedIntValue? Lean.toExpr
  let denominator ←
    evaluateProjectionValue s!"{field} denominator"
      (← mkAppM ``Rat.den #[expression]) reducedNatValue? Lean.toExpr
  if denominator.value = 0 then
    throwError "numerical certificate field '{field}' has a zero rational denominator"
  return {
    value := mkRat numerator.value denominator.value
    term := ← rationalComponentsAsReal numerator.term denominator.term
    numerator := numerator.term
    denominator := denominator.term
    numeratorProof := numerator.proof
    denominatorProof := denominator.proof
  }

/-- The evaluated projection of the rational field `field` whose numerator and denominator are
the literals `num` and `den`: the terms and the `Eq.refl` proofs that `evaluateRationalProjection`
builds after reading the same literals. -/
private def rationalProjectionOfLiterals
    (field : String) (expression : Lean.Expr) (num : Int) (den : Nat) :
    MetaM EvaluatedRationalProjection := do
  if den = 0 then
    throwError "numerical certificate field '{field}' has a zero rational denominator"
  let numeratorTerm := Lean.toExpr num
  let denominatorTerm := Lean.toExpr den
  let numeratorProof := mkExpectedPropHint (← mkEqRefl numeratorTerm)
    (← mkEq (← mkAppM ``Rat.num #[expression]) numeratorTerm)
  let denominatorProof := mkExpectedPropHint (← mkEqRefl denominatorTerm)
    (← mkEq (← mkAppM ``Rat.den #[expression]) denominatorTerm)
  return {
    value := mkRat num den
    term := ← rationalComponentsAsReal numeratorTerm denominatorTerm
    numerator := numeratorTerm
    denominator := denominatorTerm
    numeratorProof
    denominatorProof
  }

/--
Evaluate the rational projections `fields` (a label and a closed expression each) of one reduced
query.

The fields read the same certificate payload, but every kernel evaluation starts with an empty
cache, so reading each numerator and denominator on its own evaluates the payload's interval up to
four times. Here one kernel evaluation of `Verified.Expr.Serial.encodeRationals` reads all of them,
and the payload is evaluated once. When that evaluation fails or does not decode, the fields are
read one at a time by `evaluateRationalProjection`, whose errors name the field at fault; the
literals, terms and proofs are the same either way.
-/
private def evaluateRationalProjections (fields : Array (String × Lean.Expr)) :
    MetaM (Array EvaluatedRationalProjection) := do
  let batched? ← profileitM Exception "CEGA reduce rational fields" (← getOptions) do
    try
      let list ← mkListLit (mkConst ``Rat) (fields.map (·.2)).toList
      let reduced ← kernelWhnf (← mkAppM ``Verified.Expr.Serial.encodeRationals #[list])
      pure <| reduced.rawNatLit?.bind (Verified.Expr.Serial.decodeRationals fields.size)
    catch _ =>
      pure none
  match batched? with
  | some values =>
      (fields.zip values.toArray).mapM fun ((field, expression), (num, den)) ↦
        rationalProjectionOfLiterals field expression num den
  | none => fields.mapM fun (field, expression) ↦ evaluateRationalProjection field expression

/--
Add a closed proof as an auxiliary theorem so that the kernel checks it.

The generated certificate proofs end in `Eq.refl` steps whose verification
amounts to evaluating the checked query. Handing the whole theorem to the
kernel makes that evaluation a kernel computation, and the elaborator never
has to unfold the query itself. The returned constant is the proof used by the
tactic and command frontends; its type is exactly `proposition`. Kernel
rejections are raised here instead of being deferred to asynchronous checking.

A kernel proof goes through the auxiliary-lemma cache, which deduplicates repeated queries but
never returns a lemma that depends on a nonstandard axiom (`ProofCarrier.mkKernelAuxLemma`). A
proof containing a native certificate (`native := true`) uses a kernel theorem of the same
proposition already in the cache, if there is one (the native evaluation has run by then, and its
unused axiom stays in the environment), and is otherwise added under a fresh name outside the
cache, so that no kernel query can receive it. The kernel check gets the heartbeats
the declaration has left, and a kernel timeout ends the tactic (`ProofCarrier.runKernelCheck`).
-/
private def addKernelCheckedTheorem
    (description : String) (proposition proof : Lean.Expr) (native : Bool := false) :
    MetaM Lean.Expr := do
  if proposition.hasFVar ∨ proposition.hasMVar ∨ proof.hasFVar ∨ proof.hasMVar then
    throwError "{description}: the generated certificate theorem is not closed"
  if native then
    if let some name ← Tactic.ProofCarrier.cachedKernelLemma? [] proposition then
      return mkConst name
  let kind := (← getMainModule) ++ `_cega
  let name ← Tactic.ProofCarrier.runKernelCheck description
      (if native then
        Tactic.ProofCarrier.addUncachedTheorem [] proposition proof kind
      else
        Tactic.ProofCarrier.mkKernelAuxLemma [] proposition proof kind)
      fun error ↦ throwError
        "{description}: the kernel rejected the generated certificate theorem, which may be an \
          ill-typed certificate from the query{indentD error.toMessageData}"
  return mkConst name

/-- Quote a precision policy as a closed kernel term. -/
private def quotePrecision (precision : Precision) : MetaM Lean.Expr :=
  mkAppM ``Precision.mk #[Lean.toExpr precision.expOrder, Lean.toExpr precision.sqrtDigits,
    Lean.toExpr precision.logTerms, Lean.toExpr precision.depth,
    Lean.toExpr precision.digits]

/-- Quote one checked rational interval as a closed kernel term. -/
def quoteRationalInterval
    (interval : RationalInterval) : MetaM Lean.Expr := do
  let lower := Lean.toExpr interval.lo
  let upper := Lean.toExpr interval.hi
  let ordered ← mkDecideProof (← mkAppM ``LE.le #[lower, upper])
  mkAppM ``RationalInterval.ofBounds #[lower, upper, ordered]

/-- Quote an exact rational box as a closed `Fin n → RationalInterval` term. -/
private def quoteRationalBox
    (box : List RationalInterval) : MetaM Lean.Expr := do
  let intervals ← box.mapM quoteRationalInterval
  let intervalList ← mkListLit (mkConst ``RationalInterval) intervals
  withLocalDeclD `coordinate (Command.quotedVariableType box.length) fun coordinate ↦ do
    let body ← mkAppM ``List.get #[intervalList, coordinate]
    mkLambdaFVars #[coordinate] body

private def compactCertificate
    (mode : BoxQueryMode) (quotedExpr : Lean.Expr)
    (display : BoxQueryDisplay Lean.Expr) (proof : Lean.Expr) : MetaM Lean.Expr := do
  let fn ← mkAppM ``Exact.exprFn #[quotedExpr]
  match mode, display with
  | .enclose, .enclosure lower upper =>
      mkAppM ``EnclosureCert.mk #[fn, lower, upper, proof]
  | .bound, .upperBound upper =>
      mkAppM ``BoundCert.mk #[fn, upper, proof]
  | .absBound, .absoluteBound upper => do
      let absFn ← withLocalDeclD `x (← functionDomain fn) fun x ↦ do
        let value ← mkAppM ``abs #[mkApp fn x]
        mkLambdaFVars #[x] value
      mkAppM ``BoundCert.mk #[absFn, upper, proof]
  | .approx, .midpointApprox center radius => do
      let reference ← withLocalDeclD `x (← functionDomain fn) fun x ↦
        mkLambdaFVars #[x] center
      mkAppM ``ApproxCert.mk #[fn, reference, radius, proof]
  | _, _ =>
      throwError "internal CEGA numerical error: mode and display data disagree"

private def largestNaturalExponent {ι : Type*} : Verified.Expr ι → Nat
  | .nat _ | .int _ | .rat _ _ | .pi | .e | .var _ => 0
  | .add a b | .mul a b | .sub a b | .div a b =>
      max (largestNaturalExponent a) (largestNaturalExponent b)
  | .neg a | .sin a | .cos a | .atan a | .asin a | .acos a | .exp a | .log a | .sqrt a =>
      largestNaturalExponent a
  | .pow a exponent => max exponent (largestNaturalExponent a)
  | .rpow a b => max (largestNaturalExponent a) (largestNaturalExponent b)

private def coordinateWidth {n : Nat}
    (box : List RationalInterval) (coordinate : Fin n) : ℚ :=
  match box[coordinate.val]? with
  | some interval => interval.hi - interval.lo
  | none => 0

private def widestCoordinate? {n : Nat}
    (box : List RationalInterval) : List (Fin n) → Option (Fin n)
  | [] => none
  | first :: rest =>
      some <| rest.foldl
        (fun best candidate ↦
          if coordinateWidth box best < coordinateWidth box candidate then
            candidate
          else
            best)
        first

/--
Choose the widest active coordinate for the first checked refinement.

This is untrusted planner data. The selected coordinate is passed to the
kernel-checked binary-cover constructor and does not occur in its soundness
assumptions.
-/
private def selectSubdivisionCoordinate? {n : Nat}
    (box : List RationalInterval) (expr : Verified.Expr (Fin n)) : Option (Fin n) :=
  let coordinates := List.finRange n
  let active := coordinates.filter expr.containsVar
  widestCoordinate? box (if active.isEmpty then coordinates else active)

/--
Run one CEGA query with Lean's safe numeral exponentiation threshold raised
only as far as the largest natural power already accepted by `runBoxQuery`.
-/
private def withBoxQueryExponentiationThreshold
    {α : Type} (threshold : Nat) (action : TermElabM α) : TermElabM α :=
  withOptions
      (fun options ↦
        options.set `exponentiation.threshold
          (max (options.get `exponentiation.threshold 256) threshold))
      action

/--
Reduced data of one checked query.

Everything stored here is a closed term over library constants and the quoted
query inputs, so it is meaningful in every environment branch of the module.
The stored proof value is not trusted: every use hands it to the kernel again
through `addKernelCheckedTheorem`.
-/
structure ReducedBoxQuery where
  /-- Exact rational values presented to users. -/
  display : BoxQueryDisplay ℚ
  /-- The same values quoted as real-number terms. -/
  quotedDisplay : BoxQueryDisplay Lean.Expr
  /-- The concise semantic proposition certified by the query. -/
  proposition : Lean.Expr
  /-- The closed proof of `proposition`, ending in kernel-evaluated `Eq.refl` steps. -/
  soundValue : Lean.Expr

/--
Per-process memo table of reduced queries, keyed on the query mode and the
closed query term.

Repeating a query in one file otherwise re-runs the kernel evaluator on the
query and on its displayed endpoints, which dominates the cost of a numerical
tactic; `Lean.Meta.mkAuxLemma` deduplicates only the final theorem and only
within one environment branch. A hit skips that evaluation but still hands the
certificate theorem to `addKernelCheckedTheorem` in the current branch: the kernel checks it
there unless that branch already holds a checked theorem of the same proposition, which the
auxiliary-lemma cache then returns. Native queries are not memoized. The table is bounded by
`boxQueryCacheLimit`.
-/
initialize boxQueryCache :
    IO.Ref (Std.HashMap (BoxQueryMode × Lean.Expr) ReducedBoxQuery) ← IO.mkRef {}

/-- Largest number of reduced queries retained per process. -/
def boxQueryCacheLimit : Nat := 512

/--
Largest number of expression nodes accepted by one query.

Kernel evaluation time grows with the expression, and a runaway reduction
blocks the elaborator, so oversized inputs are rejected before reduction.
-/
def boxQueryNodeLimit : Nat := 4096

/-- Choose compiled evaluation for explicitly requested finite certificates. The default
`false` keeps `cega [fast]` in the kernel; the fast build profile sets it to `true`. -/
register_option cega.nativeCertificates : Bool := {
  defValue := false
  descr := "allow native checking for explicit CEGA finite certificates"
}

/-- Set by `cega [fast]` around the routes where its native polynomial enclosures may run; the
box queries read it, together with `cega.nativeCertificates`, to choose the natural interval
evaluator checked by `nativeEqTrue`. It is internal: a user setting it elsewhere changes nothing
unless `cega.nativeCertificates` is also set. -/
register_option cega.nativePolynomial : Bool := {
  defValue := false
  descr := "internal: set by `cega [fast]` while its native polynomial enclosures may run; \
    not a user setting"
}

/-- Trace finite native certificate stages and restored fallback diagnostics on request. -/
initialize registerTraceClass `cega.native

/-- Prove a decidable certificate closed after expanding local definitions.
No local assumptions are used; a genuine free variable still prevents finite checking.
Native evaluation adds a `cegaFast` axiom; kernel evaluation checks the same statement. -/
def decideClosedCertificate (statement : Expr) (native : Bool) : MetaM Expr := do
  let statement ← instantiateMVars statement
  -- Keep the exact target when it is closed. Deep zeta reduction also changes proof
  -- arguments inside finite indices, forcing the unifier to revisit numerical data
  -- when it compares the registered certificate with the original goal.
  let statement ← if statement.hasFVar then zetaReduce statement else pure statement
  trace[cega.native] "Checking finite certificate applicability (native requested: {native})"
  if statement.hasFVar || statement.hasMVar || statement.hasLooseBVars then
    trace[cega.native] "Finite certificate refused: the proposition is open"
    throwError "CEGA finite certificate checking requires a closed proposition"
  unless ← isProp statement do
    throwError "CEGA finite certificate checking requires a proposition"
  trace[cega.native] "Starting finite Decidable synthesis"
  let decision ← profileitM Exception "CEGA finite Decidable synthesis" (← getOptions) do
    zetaReduce (← instantiateMVars (← mkDecide statement))
  trace[cega.native] "Finite Decidable synthesis completed"
  if decision.hasFVar || decision.hasMVar || decision.hasLooseBVars then
    throwError "CEGA finite certificate checking requires a closed Decidable instance"
  if native && (← getOptions).getBool `cega.nativeCertificates false then
    -- A kernel theorem of this statement in the cache (from an earlier kernel route in this
    -- environment branch) is used as is: native evaluation would only add trust.
    let levels := (collectLevelParams {} statement).params.toList
    if let some name ← Tactic.ProofCarrier.cachedKernelLemma? levels statement then
      trace[cega.native] "Reusing the cached kernel theorem {name}"
      return mkConst name (levels.map mkLevelParam)
  if native && (← getOptions).getBool `cega.nativeCertificates false then
      CAS.Numerics.withLiteralEnv do
    -- Naming the instance keeps proof elaboration from expanding a large finite
    -- decision tree. Its body is still checked by the kernel and compiled normally.
    -- Compiled code reads compact literals from their definitions in this environment.
    let instanceName ← mkAuxDeclName `_finiteDecision
    let instanceValue ← Tactic.ProofCarrier.runKernelCheck "CEGA finite decision procedure"
      (mkAuxDefinition instanceName (mkApp (mkConst ``Decidable) statement) decision.appArg!)
      fun error ↦ throw error
    setReducibilityStatus instanceName .irreducible
    let decision := mkApp2 (mkConst ``decide) statement instanceValue
    trace[cega.native] "Starting finite native compilation and evaluation \
      (remaining elaboration heartbeats: {(← getRemainingHeartbeats) / 1000})"
    let result ← try
      profileitM Exception "CEGA finite native compilation and evaluation" (← getOptions) do
        nativeEqTrue `cegaFast decision
    catch error =>
      trace[cega.native] "Finite native compilation or evaluation failed: {error.toMessageData}"
      throw error
    let evidence ← match result with
      | .notTrue =>
          trace[cega.native] "Finite native evaluation returned false"
          throwError "CEGA finite certificate evaluates to false"
      | .success proof =>
          trace[cega.native] "Finite native evaluation succeeded \
            (remaining elaboration heartbeats: {(← getRemainingHeartbeats) / 1000})"
          pure proof
    let proof := mkApp3 (mkConst ``of_decide_eq_true) statement decision.appArg! evidence
    -- Check the numerical proof once in the kernel; later carrier checks inspect its theorem.
    trace[cega.native] "Registering checked finite proof"
    -- The statement and decision are closed. Avoid closure conversion, which
    -- otherwise inspects types through the full numerical decision procedure.
    let levels := (collectLevelParams (collectLevelParams {} statement) proof).params.toList
    -- A fresh theorem outside the auxiliary-lemma cache: a kernel route (`decide +kernel`,
    -- bare `cega`) asking for the same statement must not receive this native proof.
    let name ← Tactic.ProofCarrier.runKernelCheck "CEGA finite native certificate"
      (Tactic.ProofCarrier.addUncachedTheorem levels statement proof `cegaFinite)
      fun error ↦ throw error
    trace[cega.native] "Checked finite proof registered"
    return mkConst name (levels.map mkLevelParam)
  else
    trace[cega.native] "Using the finite kernel certificate profile"
    Tactic.KernelReadBack.decideByKernel "CEGA finite certificate" statement

/-- The largest estimated number of planner calls of a subdivided CEGA query, the recursive
refinement previews included; a query whose estimate is larger is refused before any kernel work.
Raising it permits a larger search; it never changes the requested depth. -/
register_option cega.maxRefinementWork : Nat := {
  defValue := 4096
  descr := "maximum estimated planner calls for a subdivided CEGA query"
}

/-- The largest value of each precision parameter of the elementary functions in a CEGA query
(Taylor order, logarithm terms, square-root digits); a larger value is refused. -/
register_option cega.maxPrecision : Nat := {
  defValue := 256
  descr := "maximum Taylor order, logarithm terms, or square-root digits in a CEGA query"
}

/-- The largest number of coordinates of a CEGA box query; a query with more is refused before
any kernel work. -/
register_option cega.maxDimension : Nat := {
  defValue := 8
  descr := "maximum number of coordinates of a CEGA box query"
}

/-- The largest number of nested monotonicity reductions of the CEGA planner. The planner reduces a
box to the two faces of a coordinate whose partial derivative keeps one sign and reruns itself on
each face, so each reduction roughly doubles its kernel work: a sum of `k` squares on `[1, 2]^k`,
where every coordinate can be reduced, costs about 10 s for `k = 2`, 47 s for `k = 4`, and
385 s and 42 GB for `k = 6`. -/
register_option cega.maxFaceReductions : Nat := {
  defValue := 5
  descr := "maximum number of coordinates the CEGA planner may reduce by monotonicity"
}

/--
Conservative count of planner calls for the explicit first split and recursive previews.

A preview tree satisfies `P(d + 1) = 1 + 2 * P(d)`. An adaptive certificate may
inspect both preview subtrees and then build both children, so its cost satisfies
`A(d + 1) = 2 + 2 * P(d) + 2 * A(d)`, with `P(0) = A(0) = 1`.
The explicit first split costs `1 + 2 * A(depth - 1)`, including at depth zero.
Counting stops as soon as the budget is exceeded, without constructing `2^depth`.
-/
def refinementWorkWithin? (budget depth : Nat) : Option Nat := Id.run do
  let mut preview := 1
  let mut adaptive := 1
  if budget < 1 + 2 * adaptive then
    return none
  for _ in [:depth - 1] do
    adaptive := 2 + 2 * preview + 2 * adaptive
    preview := 1 + 2 * preview
    if budget < 1 + 2 * adaptive then
      return none
  return some (1 + 2 * adaptive)

private def exprNodeCount {ι : Type*} : Verified.Expr ι → Nat
  | .nat _ | .int _ | .rat _ _ | .pi | .e | .var _ => 1
  | .add a b | .mul a b | .sub a b | .div a b | .rpow a b =>
      exprNodeCount a + exprNodeCount b + 1
  | .neg a | .pow a _ | .sin a | .cos a | .atan a | .asin a | .acos a | .exp a | .log a |
      .sqrt a =>
      exprNodeCount a + 1

/--
Reduce the closed query `query` with the kernel evaluator to the certificate payload it returns,
an `EnclosureAttempt`, or `none` when no route succeeds. Only the head `Option.some` is
exposed; the payload's fields are evaluated later, as the display fields require.
-/
private def reduceQueryPayload? (query : Lean.Expr) : TermElabM (Option Lean.Expr) := do
  let reduced ← profileitM Exception "CEGA query reduction" (← getOptions) do
    kernelWhnf query
  if reduced.isAppOfArity ``Option.none 1 then
    return none
  -- Dependent registry reduction may remain opaque when no route applies.
  unless reduced.isAppOfArity ``Option.some 2 do
    return none
  let payload := reduced.getAppArgs[1]!
  if payload.hasMVar ∨ payload.hasSorry then
    throwError "CEGA query returned incomplete certificate evidence"
  -- The payload is not type-checked here: the kernel checks it with the certificate theorem
  -- (`addKernelCheckedTheorem`), whose rejection message names an ill-typed payload.
  return some payload

/-- The rational fields of the interval `interval` of a certificate payload that the mode `mode`
displays, each with its label. -/
private def displayFields (mode : BoxQueryMode) (interval : Lean.Expr) :
    MetaM (Array (String × Lean.Expr)) := do
  match mode with
  | .enclose =>
      let rawInterval ← mkAppM ``RationalInterval.toFloatLib #[interval]
      return #[("lower endpoint", ← mkAppM ``FloatLib.Numerics.Interval.lo #[rawInterval]),
        ("upper endpoint", ← mkAppM ``FloatLib.Numerics.Interval.hi #[rawInterval])]
  | .bound =>
      let rawInterval ← mkAppM ``RationalInterval.toFloatLib #[interval]
      return #[("upper endpoint", ← mkAppM ``FloatLib.Numerics.Interval.hi #[rawInterval])]
  | .absBound => return #[("absolute bound", ← mkAppM ``RationalInterval.absMax #[interval])]
  | .approx =>
      return #[("midpoint", ← mkAppM ``RationalInterval.center #[interval]),
        ("radius", ← mkAppM ``RationalInterval.radius #[interval])]

/-- The theorem `name`, stated for a domain `α : Type*` as the check and projection theorems of
`CAS.CEGA.Query` and `EnclosureAttempt` are, at the universe of the query's domain `α`. -/
private def constAt (name : Name) (α : Lean.Expr) : MetaM Lean.Expr :=
  return Lean.mkConst name [← getDecLevel α]

/--
The values that the mode `mode` displays for the certificate payload `payload` of a query on the
box `quotedBox` of the expression `quotedExpr`, as rationals and as real terms, with the closed
proof of the mode's proposition, from the fields of `displayFields mode` and their evaluations.

The proof applies the mode's projection theorem (`BoxQueryMode.soundTheorem`) to the payload and
ends in `Eq.refl` steps that the kernel evaluates when the finished certificate theorem is added
to the environment.
-/
private def displayProof (mode : BoxQueryMode) (quotedBox quotedExpr payload : Lean.Expr)
    (fields : Array (Lean.Expr × EvaluatedRationalProjection)) :
    MetaM (BoxQueryDisplay ℚ × BoxQueryDisplay Lean.Expr × Lean.Expr) := do
  let fn ← mkAppM ``Exact.exprFn #[quotedExpr]
  let domain ← mkAppM ``boxDomain #[quotedBox]
  let α ← functionDomain fn
  -- These indices are fixed by the query. Supplying them directly avoids unfolding
  -- the numerical computation during elaborator unification; the kernel still checks
  -- every argument when the completed certificate theorem is added.
  let soundPrefix := #[α, domain, fn, payload]
  match mode, fields with
  | .enclose, #[(lowerExpr, lower), (upperExpr, upper)] => do
    let intervalProof := mkAppN (← constAt mode.soundTheorem α) (soundPrefix ++ #[
        lowerExpr, upperExpr,
        ← mkEqRefl lowerExpr, ← mkEqRefl upperExpr
      ])
    let proof := mkAppN (mkConst ``enclosedOn_of_rational_components) #[
        α, fn, domain, lowerExpr, upperExpr,
        intervalProof,
        lower.numerator, upper.numerator,
        lower.denominator, upper.denominator,
        lower.numeratorProof, lower.denominatorProof,
        upper.numeratorProof, upper.denominatorProof
      ]
    return (
      BoxQueryDisplay.enclosure lower.value upper.value,
      BoxQueryDisplay.enclosure lower.term upper.term,
      proof)
  | .bound, #[(upperExpr, upper)] => do
    let intervalProof := mkAppN (← constAt mode.soundTheorem α) (soundPrefix ++ #[
        upperExpr, ← mkEqRefl upperExpr
      ])
    let proof := mkAppN (mkConst ``boundOn_of_rational_components) #[
        α, fn, domain, upperExpr,
        intervalProof,
        upper.numerator, upper.denominator,
        upper.numeratorProof, upper.denominatorProof
      ]
    return (
      BoxQueryDisplay.upperBound upper.value,
      BoxQueryDisplay.upperBound upper.term,
      proof)
  | .absBound, #[(upperExpr, upper)] => do
    let intervalProof := mkAppN (← constAt mode.soundTheorem α) (soundPrefix ++ #[
        upperExpr, ← mkEqRefl upperExpr
      ])
    let absFn ← withLocalDeclD `x α fun x ↦ do
      mkLambdaFVars #[x] (← mkAppM ``abs #[mkApp fn x])
    let proof := mkAppN (mkConst ``boundOn_of_rational_components) #[
        α, absFn, domain, upperExpr,
        intervalProof,
        upper.numerator, upper.denominator,
        upper.numeratorProof, upper.denominatorProof
      ]
    return (
      BoxQueryDisplay.absoluteBound upper.value,
      BoxQueryDisplay.absoluteBound upper.term,
      proof)
  | .approx, #[(centerExpr, center), (radiusExpr, radius)] => do
    let intervalProof := mkAppN (← constAt mode.soundTheorem α) (soundPrefix ++ #[
        centerExpr, radiusExpr,
        ← mkEqRefl centerExpr, ← mkEqRefl radiusExpr
      ])
    let proof := mkAppN (mkConst ``approxOn_of_rational_components) #[
        α, fn, domain, centerExpr, radiusExpr,
        intervalProof,
        center.numerator, radius.numerator,
        center.denominator, radius.denominator,
        center.numeratorProof, center.denominatorProof,
        radius.numeratorProof, radius.denominatorProof
      ]
    return (
      BoxQueryDisplay.midpointApprox center.value radius.value,
      BoxQueryDisplay.midpointApprox center.term radius.term,
      proof)
  | _, _ => throwError "internal CEGA numerical error: endpoint read-back"

/--
Reduce one checked CEGA box query with the kernel evaluator and extract its
displayed endpoints, proposition, and proof value.

The query and its rational display fields are reduced with the kernel
evaluator; the equalities tying the fields to the payload are `Eq.refl` steps
that the kernel verifies when the finished certificate theorem is added to the
environment.
-/
private def reduceBoxQuery
    (mode : BoxQueryMode) (quotedBox quotedExpr query : Lean.Expr) :
    TermElabM (Option ReducedBoxQuery) := do
  let some payload ← reduceQueryPayload? query
    | return none
  let interval ← mkAppM ``EnclosureAttempt.interval #[payload]
  let (display, quotedDisplay, soundValue) ←
    profileitM Exception "CEGA endpoint and soundness extraction" (← getOptions) do
      let fields ← displayFields mode interval
      let values ← evaluateRationalProjections fields
      displayProof mode quotedBox quotedExpr payload ((fields.map (·.2)).zip values)
  let proposition ← profileitM Exception "CEGA compact proposition" (← getOptions) do
    compactProposition mode quotedBox quotedExpr quotedDisplay
  if soundValue.hasMVar ∨ soundValue.hasSorry then
    throwError "CEGA query returned incomplete soundness evidence"
  return some { display, quotedDisplay, proposition, soundValue }

/-- Reduce a query, or reuse the reduction memoized for the same closed query term. A query
containing a native certificate (`native`) names an axiom of the current environment branch, so
it is never memoized. -/
private def reduceBoxQueryMemo
    (mode : BoxQueryMode) (quotedBox quotedExpr query : Lean.Expr) (native : Bool) :
    TermElabM (Option ReducedBoxQuery) := do
  if native then
    return ← reduceBoxQuery mode quotedBox quotedExpr query
  let key := (mode, query)
  if let some cached := (← boxQueryCache.get)[key]? then
    return some cached
  let some reduced ← reduceBoxQuery mode quotedBox quotedExpr query
    | return none
  boxQueryCache.modify fun cache ↦
    if cache.size < boxQueryCacheLimit then cache.insert key reduced else cache
  return some reduced

/--
The closed query term of one box query that computes its enclosure by `method`, with the quoted
box and expression it is built from. The subdivided query bisects the coordinate chosen by
`selectSubdivisionCoordinate?` first.
-/
private def boxQueryTerm
    {n : Nat} (method : EnclosureMethod) (precision : Precision) (box : List RationalInterval)
    (expr : Verified.Expr (Fin n)) : TermElabM (Lean.Expr × Lean.Expr × Lean.Expr) := do
  unless box.length = n do
    throwError
      "internal CEGA numerical error: box dimension {box.length} does not match \
        expression dimension {n}"
  let quotedPrecision ← quotePrecision precision
  let quotedBox ← quoteRationalBox box
  let quotedExpr ← CAS.Command.quoteVerifiedExpr expr
  let query ←
    match method with
    | .plain => mkAppM ``encloseBoxWith? #[quotedPrecision, quotedBox, quotedExpr]
    | .subdivided =>
        let some coordinate := selectSubdivisionCoordinate? box expr
          | throwError "`(depth := n)` subdivides the box of the bindings `x in [a, b]`, and a \
              closed expression has none"
        mkAppM ``encloseBoxSubdividedAtWith?
          #[quotedPrecision, Lean.toExpr coordinate, quotedBox, quotedExpr]
  Term.synthesizeSyntheticMVarsNoPostponing
  return (quotedBox, quotedExpr, ← instantiateMVars query)

/--
Run one checked CEGA box query and extract its public proof data.

Every successful result contains the exact certificate later supplied to the
theorem-facing tactic. No result is returned unless `addKernelCheckedTheorem`
accepts its soundness proof, whether or not the reduction came from the memo table.
The default route checks the computation in the kernel; the explicit fast route
supplies a native-checked equality for the natural interval computation.
-/
private def runBoxQueryCore
    {n : Nat} (mode : BoxQueryMode) (method : EnclosureMethod) (precision : Precision)
    (box : List RationalInterval) (expr : Verified.Expr (Fin n)) :
    TermElabM (Option BoxQueryResult) := do
  let (quotedBox, quotedExpr, query) ← boxQueryTerm method precision box expr
  let native := method = .plain && (← getOptions).getBool `cega.nativePolynomial false &&
    (← getOptions).getBool `cega.nativeCertificates false
  let query ← if native then do
    let env : Fin n → RationalInterval := fun i ↦
      box.getD i.val (RationalInterval.ofBounds 0 0 (by decide))
    let some interval := RationalInterval.evalPolynomial env expr
      | throwError "CEGA fast natural interval route does not support this expression"
    let quotedInterval ← quoteRationalInterval interval
    let evaluation ← mkAppM ``RationalInterval.evalPolynomial #[quotedBox, quotedExpr]
    let result ← mkAppM ``Option.some #[quotedInterval]
    let statement ← mkEq evaluation result
    let decision ← mkDecide statement
    let equality ← match ← nativeEqTrue `cegaFast decision (axiomDeclRange? := (← getRef)) with
      | .notTrue => throwError "CEGA fast natural interval certificate was rejected"
      | .success proof =>
          pure <| mkApp3 (mkConst ``of_decide_eq_true) statement decision.appArg! proof
    let attempt ← mkAppM ``polynomialBoxAttempt
      #[quotedBox, quotedExpr, quotedInterval, equality]
    mkAppM ``Option.some #[attempt]
  else pure query
  let some reduced ← reduceBoxQueryMemo mode quotedBox quotedExpr query native
    | return none
  -- The kernel checks the endpoint equalities and the match between the
  -- soundness theorem and the semantic proposition in one step.
  let soundProof ←
    profileitM Exception "CEGA kernel certificate check" (← getOptions) do
      addKernelCheckedTheorem "CEGA query" reduced.proposition reduced.soundValue native
  let certificate ← profileitM Exception "CEGA compact certificate" (← getOptions) do
    compactCertificate mode quotedExpr reduced.quotedDisplay soundProof
  if certificate.hasMVar ∨ certificate.hasSorry then
    throwError "CEGA query returned an incomplete semantic certificate"
  let certificateValid ←
    profileitM Exception "CEGA certificate validation" (← getOptions) do
      withTraceNode `cas.profile.validation (fun _ ↦ return m!"CEGA certificate validation")
        (isTypeCorrect certificate)
  unless certificateValid do
    throwError "CEGA query returned an ill-typed semantic certificate"
  return some {
    display := reduced.display
    certificate
    proof := soundProof
  }

/--
The most coordinates the box planner can reduce by monotonicity on `box`, an upper bound on the
nesting of its face recursion in one planner call (`CAS.CEGA.encloseBoxWithFuel?`),
computed with the planner's own tests on the simplified expression: zero when the derivative
routes do not apply (`derivativeRoutesApply`), otherwise the number of reducible coordinates
(`reducibleCoordinates`) capped by the dimension, which is the planner's fuel. No coordinate
becomes reducible after the root: a face fixes its coordinate to a point, the expression does not
change, and whether the raw derivative `expr.diff i` contains a square root does not depend on
`i` (only the derivative of a variable depends on `i`, and both of its values are numerals). A
subdivided query calls the planner once per child box, each within this bound. This is admission
data, not a proof obligation.
-/
def plannerFaceReductions {n : Nat} (box : List RationalInterval)
    (expr : Verified.Expr (Fin n)) : Nat :=
  let intervals : Fin n → RationalInterval := fun i ↦
    box.getD i.val (RationalInterval.ofBounds 0 0 (by decide))
  let simplified := Verified.Expr.simplify expr
  if RationalInterval.derivativeRoutesApply intervals simplified then
    min n (RationalInterval.reducibleCoordinates intervals simplified).length
  else
    0

/-- Refuse a box query whose dimension or monotonicity nesting exceeds its budget
(`cega.maxDimension`, `cega.maxFaceReductions`) before any kernel work. -/
def validateQueryBox {n : Nat} (box : List RationalInterval) (expr : Verified.Expr (Fin n)) :
    MetaM Unit := do
  let options ← getOptions
  let dimensionLimit := cega.maxDimension.get options
  if dimensionLimit < n then
    throwError
      "CEGA box query with {n} coordinates exceeds cega.maxDimension ({dimensionLimit}); \
       bound fewer variables at once, or explicitly increase that resource budget"
  let reductions := plannerFaceReductions box expr
  let reductionLimit := cega.maxFaceReductions.get options
  if reductionLimit < reductions then
    throwError
      "CEGA box query could reduce {reductions} coordinates by monotonicity, which exceeds \
       cega.maxFaceReductions ({reductionLimit}). Each reduction reruns the planner on two \
       faces, so its kernel work doubles with each one (a sum of six squares on a \
       six-dimensional box took minutes and tens of gigabytes); bound fewer variables at once, \
       or explicitly increase that resource budget"

/-- Validate a query whose enclosure is computed by `method` before a frontend starts
derivative construction or other preprocessing. Returns its largest natural exponent, also used by
the checked power evaluator. -/
def validateQueryInput
    {n : Nat} (method : EnclosureMethod) (precision : Precision)
    (expr : Verified.Expr (Fin n)) : TermElabM Nat := do
  let exponent := largestNaturalExponent expr
  if 4096 < exponent then
    throwError
      "natural exponent {exponent} exceeds the CEGA query limit 4096; \
       rewrite the expression or prove a problem-specific power bound first"
  let nodes := exprNodeCount expr
  if boxQueryNodeLimit < nodes then
    throwError
      "expression with {nodes} nodes exceeds the CEGA query limit {boxQueryNodeLimit}; \
       split the expression or prove the bound in stages"
  let options ← getOptions
  let precisionLimit := cega.maxPrecision.get options
  if precisionLimit < max precision.expOrder (max precision.sqrtDigits precision.logTerms) then
    throwError
      "CEGA precision exceeds cega.maxPrecision ({precisionLimit}); \
       reduce the precision or explicitly increase that resource budget"
  let digitsLimit := CAS.Command.cas.maxDigits.get options
  if let some digits := precision.digits then
    if digitsLimit < digits then
      throwError
        "CEGA query with {digits} digits exceeds cas.maxDigits ({digitsLimit}); \
         request fewer digits or explicitly increase that resource budget"
  if method = .subdivided then
    let budget := cega.maxRefinementWork.get options
    if (refinementWorkWithin? budget precision.depth).isNone then
      throwError
        "CEGA subdivision depth {precision.depth} exceeds the estimated planner-call \
         budget cega.maxRefinementWork ({budget}); reduce depth or explicitly increase \
         that resource budget. The requested depth has not been truncated"
  return exponent

/--
Reduce one checked CEGA box query with bounded natural powers and expression
size at the requested precision.

The interval power backend uses direct endpoint formulas, so its algorithmic
depth does not grow with the exponent. Lean's safe numeral evaluator still
guards large exponentiation by an option threshold; this function raises that
threshold only for the exponent actually present in a bounded query.
-/
def runBoxQuery
    {n : Nat} (mode : BoxQueryMode) (method : EnclosureMethod) (precision : Precision)
    (box : List RationalInterval) (expr : Verified.Expr (Fin n)) :
    TermElabM (Option BoxQueryResult) := do
  let exponent ← validateQueryInput method precision expr
  validateQueryBox box expr
  withBoxQueryExponentiationThreshold exponent
    (runBoxQueryCore mode method precision box expr)

/-! ## Views of one enclosure -/

/-- One view of a certified enclosure: the values of the mode `mode` and a proof of its
proposition, which is the type of `proof`. -/
structure EncloseView where
  private mk ::
  /-- The mode whose projection theorem (`BoxQueryMode.soundTheorem`) states the view. -/
  mode : BoxQueryMode
  /-- Exact rational values presented to users. -/
  display : BoxQueryDisplay ℚ
  /-- A proof of the view's proposition: a projection of the theorem of `runEncloseViews`, which
  the kernel has checked. -/
  proof : Lean.Expr

/-- The views of one certified enclosure, with the route steps of its query. -/
structure EncloseViews where
  private mk ::
  /-- The enclosure, upper-bound, absolute-bound and midpoint views, in that order. -/
  views : Array EncloseView
  /-- Route steps retained for diagnostic rendering. -/
  routeSteps : Lean.Expr

/-- The conjunction `p₀ ∧ (p₁ ∧ …)` of the propositions `propositions`. -/
private def conjunctionOf : List Lean.Expr → Lean.Expr
  | [] => mkConst ``True
  | [p] => p
  | p :: rest => mkApp2 (mkConst ``And) p (conjunctionOf rest)

/-- The proof of `conjunctionOf` of the propositions of `facts` from their proofs. -/
private def conjunctionProof : List (Lean.Expr × Lean.Expr) → Lean.Expr
  | [] => mkConst ``True.intro
  | [(_, hp)] => hp
  | (p, hp) :: rest =>
      mkApp4 (mkConst ``And.intro) p (conjunctionOf (rest.map (·.1))) hp (conjunctionProof rest)

/-- The proofs of the propositions `propositions` from a proof `h` of their `conjunctionOf`. -/
private def conjuncts (h : Lean.Expr) : List Lean.Expr → List Lean.Expr
  | [] => []
  | [_] => [h]
  | p :: rest =>
      let q := conjunctionOf rest
      mkApp3 (mkConst ``And.left) p q h :: conjuncts (mkApp3 (mkConst ``And.right) p q h) rest

/--
Run the enclosure query of `expr` on `box` once, with the enclosure computed by `method`, and
state each view of its interval: the enclosure, the upper bound, the bound on the absolute value
and the midpoint with its radius, each through the projection theorem of its mode
(`BoxQueryMode.soundTheorem`). Returns `none` when no route succeeds.

The displayed fields of all views are read in one kernel evaluation, and the kernel checks one
theorem, the conjunction of the views, so the query's interval is evaluated once there as well;
the proof of each view is a projection of that theorem.
-/
def runEncloseViews
    {n : Nat} (method : EnclosureMethod) (precision : Precision) (box : List RationalInterval)
    (expr : Verified.Expr (Fin n)) : TermElabM (Option EncloseViews) := do
  let exponent ← validateQueryInput method precision expr
  validateQueryBox box expr
  withBoxQueryExponentiationThreshold exponent do
    let (quotedBox, quotedExpr, query) ← boxQueryTerm method precision box expr
    let some payload ← reduceQueryPayload? query
      | return none
    let interval ← mkAppM ``EnclosureAttempt.interval #[payload]
    let modes : Array BoxQueryMode := #[.enclose, .bound, .absBound, .approx]
    let views ← profileitM Exception "CEGA endpoint and soundness extraction" (← getOptions) do
      let fields ← modes.mapM (displayFields · interval)
      let values ← evaluateRationalProjections fields.flatten
      let mut views : Array (BoxQueryMode × BoxQueryDisplay ℚ × Lean.Expr × Lean.Expr) := #[]
      let mut offset := 0
      for viewMode in modes, viewFields in fields do
        let evaluated :=
          (viewFields.map (·.2)).zip (values.extract offset (offset + viewFields.size))
        offset := offset + viewFields.size
        let (display, quotedDisplay, proof) ←
          displayProof viewMode quotedBox quotedExpr payload evaluated
        let proposition ← compactProposition viewMode quotedBox quotedExpr quotedDisplay
        if proof.hasMVar ∨ proof.hasSorry then
          throwError "CEGA query returned incomplete soundness evidence"
        views := views.push (viewMode, display, proposition, proof)
      pure views
    let propositions := views.toList.map (·.2.2.1)
    let theoremProof ← profileitM Exception "CEGA kernel certificate check" (← getOptions) do
      addKernelCheckedTheorem "CEGA enclosure" (conjunctionOf propositions)
        (conjunctionProof (views.toList.map (·.2.2)))
    let proofs := conjuncts theoremProof propositions
    return some {
      views := (views.zip proofs.toArray).map fun ((mode, display, _), proof) ↦
        { mode, display, proof }
      routeSteps := ← mkAppM ``EnclosureAttempt.steps #[payload]
    }

/-! ## Stated bounds -/

/-- A bound that a goal states with rational numbers. `checkStatedBounds` compares it with the
interval of a query inside one kernel check, through the theorems of `CAS.CEGA.Query`. -/
inductive StatedBound where
  /-- `lo ≤ f x ∧ f x ≤ hi` on the box, as `EnclosedOn f s lo hi`. -/
  | enclosure (lo hi : ℚ)
  /-- `f x ≤ c`, as `BoundOn f s c`, or `f x < c` when `strict`. -/
  | upper (c : ℚ) (strict : Bool)
  /-- `c ≤ f x`, or `c < f x` when `strict`. -/
  | lower (c : ℚ) (strict : Bool)
  /-- `|f x| ≤ c`, as `BoundOn (|f ·|) s c`, or `|f x| < c` when `strict`. -/
  | absolute (c : ℚ) (strict : Bool)
  /-- `ApproxOn f (fun _ ↦ center) s radius`, with `center` the midpoint of the interval. -/
  | approx (center radius : ℚ)
deriving Repr

/-- The stated bound as a short relation, for traces: `∈ [lo, hi]`, `≤ c`, `> c`, `|·| ≤ c`, …. -/
def StatedBound.render : StatedBound → String
  | .enclosure lo hi => s!"∈ [{renderRational lo}, {renderRational hi}]"
  | .upper c strict => s!"{if strict then "<" else "≤"} {renderRational c}"
  | .lower c strict => s!"{if strict then ">" else "≥"} {renderRational c}"
  | .absolute c strict => s!"|·| {if strict then "<" else "≤"} {renderRational c}"
  | .approx center radius => s!"= {renderRational center} ± {renderRational radius}"

/-- The mode whose projection states the bound: the enclosure for an enclosure or a lower bound,
the upper bound, the absolute bound, or the midpoint approximation. -/
def StatedBound.mode : StatedBound → BoxQueryMode
  | .enclosure .. | .lower .. => .enclose
  | .upper .. => .bound
  | .absolute .. => .absBound
  | .approx .. => .approx

/-- Trace the stated-bound route: each kernel check of a stated bound and its outcome. -/
initialize registerTraceClass `cega.stated

/-- The theorem of `CAS.CEGA.Query` that turns the kernel's comparison into the stated
proposition, and the rational arguments it takes after the query. -/
def StatedBound.checkTheorem : StatedBound → Name × Array ℚ
  | .enclosure lo hi => (``enclosedOn_of_check, #[lo, hi])
  | .upper c false => (``boundOn_of_check, #[c])
  | .upper c true => (``lt_of_check, #[c])
  | .lower c false => (``le_of_check_lower, #[c])
  | .lower c true => (``lt_of_check_lower, #[c])
  | .absolute c false => (``boundOn_abs_of_check, #[c])
  | .absolute c true => (``abs_lt_of_check, #[c])
  | .approx center radius => (``approxOn_of_check, #[center, radius])

/-- Whether the reduction of the box query of `mode` and `method` is in the per-process memo
table, so that `runBoxQuery` would skip its search. -/
def boxQueryMemoized {n : Nat} (mode : BoxQueryMode) (method : EnclosureMethod)
    (precision : Precision) (box : List RationalInterval) (expr : Verified.Expr (Fin n)) :
    TermElabM Bool := do
  let (_, _, query) ← boxQueryTerm method precision box expr
  let memoized := (← boxQueryCache.get).contains (mode, query)
  if memoized then
    trace[cega.stated] "{queryLabel mode method}: memoized, so the search route runs"
  return memoized

/--
The proposition and proof that `checkStatedBounds` states for one bound, from the proof `checked`
of `checkedType` given by `StatedBound.checkTheorem`. A certificate proposition (`EnclosedOn`,
`BoundOn`, `ApproxOn`) states its rationals as real quotients of their numerators and
denominators through the `..._of_rational_components` theorems, exactly as `runBoxQuery` states
the endpoints it reads back, so that the transports to the goal are the same; the strict and lower
bounds keep their rational casts.
-/
private def statedPresentation (stated : StatedBound) (fn domain checked checkedType : Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr) := do
  let α ← functionDomain fn
  let literal (field : String) (value : ℚ) :=
    rationalProjectionOfLiterals field (Lean.toExpr value) value.num value.den
  match stated with
  | .enclosure lo hi => do
      let lower ← literal "lower bound" lo
      let upper ← literal "upper bound" hi
      let proof := mkAppN (mkConst ``enclosedOn_of_rational_components) #[
        α, fn, domain, Lean.toExpr lo, Lean.toExpr hi, checked,
        lower.numerator, upper.numerator, lower.denominator, upper.denominator,
        lower.numeratorProof, lower.denominatorProof, upper.numeratorProof, upper.denominatorProof]
      return (← mkAppM ``EnclosedOn #[fn, domain, lower.term, upper.term], proof)
  | .upper c false | .absolute c false => do
      let bound ← literal "bound" c
      let boundedFn ← if stated matches .absolute .. then
          withLocalDeclD `x α fun x ↦ do mkLambdaFVars #[x] (← mkAppM ``abs #[mkApp fn x])
        else pure fn
      let proof := mkAppN (mkConst ``boundOn_of_rational_components) #[
        α, boundedFn, domain, Lean.toExpr c, checked,
        bound.numerator, bound.denominator, bound.numeratorProof, bound.denominatorProof]
      return (← mkAppM ``BoundOn #[boundedFn, domain, bound.term], proof)
  | .approx center radius => do
      let centerValue ← literal "center" center
      let radiusValue ← literal "radius" radius
      let proof := mkAppN (mkConst ``approxOn_of_rational_components) #[
        α, fn, domain, Lean.toExpr center, Lean.toExpr radius, checked,
        centerValue.numerator, radiusValue.numerator,
        centerValue.denominator, radiusValue.denominator,
        centerValue.numeratorProof, centerValue.denominatorProof,
        radiusValue.numeratorProof, radiusValue.denominatorProof]
      let reference ← withLocalDeclD `x α fun x ↦ mkLambdaFVars #[x] centerValue.term
      return (← mkAppM ``ApproxOn #[fn, reference, domain, radiusValue.term], proof)
  | _ => return (checkedType, checked)

/--
Add a stated-bound theorem and check it in the kernel now. The check never takes a theorem from
Lean's auxiliary-lemma cache, whose key is the statement alone, so that a bound checked for a query
at one precision does not stand in for a query at another; a kernel-only theorem then becomes the
cache entry for its statement, replacing an entry that depends on a nonstandard axiom, as
`ProofCarrier.mkKernelAuxLemma` does.
-/
private def addStatedTheorem (proposition proof : Lean.Expr) (kind : Name) : MetaM Name := do
  unless ← Tactic.ProofCarrier.kernelClean #[proposition, proof] do
    return ← Tactic.ProofCarrier.addUncachedTheorem [] proposition proof kind
  mkAuxLemma [] proposition proof (kind? := some kind) (cache := false)

/--
Per-process table of the stated-bound checks already made, keyed on the closed proof term: the
query, with its precision policy, and the stated rationals. A repeated check of the same bound for
the same query reuses its theorem (`some name`) when the current environment holds it, with this
proof, and is rejected again at once after a rejection (`none`), since the kernel's verdict on the
same term does not change; a check that ran out of the kernel's recursion limit or was interrupted
is not recorded. Unlike Lean's auxiliary-lemma cache, which is keyed on the statement alone, the
table never returns a theorem checked for a query at another precision (`addStatedTheorem`). It
is bounded by `boxQueryCacheLimit`.
-/
initialize statedBoundCache : IO.Ref (Std.HashMap Lean.Expr (Option Name)) ← IO.mkRef {}

/-- The outcome of `checkStatedBounds`. -/
inductive StatedCheck where
  /-- The kernel accepted the bounds: a proof of each stated proposition, in order. -/
  | checked (proofs : Array Lean.Expr)
  /-- The kernel rejected the bounds, now or in an earlier check of the same term. -/
  | rejected
  /-- Nothing was decided: with `reuseOnly` there was no earlier check, or the kernel ran out of
  its recursion limit or was interrupted. -/
  | inconclusive

/-- The test `fun a ↦ t₀ a && (t₁ a && …)` on the attempts of type `attempt` that passes when
every test of `tests` passes. -/
private def joinTests (attempt : Lean.Expr) : List Lean.Expr → MetaM Lean.Expr
  | [] => throwError "internal CEGA error: no stated bound to check"
  | [t] => return t
  | t :: rest => do
      let u ← joinTests attempt rest
      withLocalDeclD `a attempt fun a ↦
        mkLambdaFVars #[a] <|
          mkApp2 (mkConst ``Bool.and) (mkApp t a).headBeta (mkApp u a).headBeta

/-- Proofs that the query `query` passes each test of `tests`, from a proof `h` that it passes
their `joinTests`, through `check_and_left` and `check_and_right`. -/
private def splitTests (attempt α domain fn query : Lean.Expr) :
    Lean.Expr → List Lean.Expr → MetaM (List Lean.Expr)
  | _, [] => return []
  | h, [_] => return [h]
  | h, t :: rest => do
      let arguments := #[α, domain, fn, query, t, ← joinTests attempt rest, h]
      let others ← splitTests attempt α domain fn query
        (mkAppN (← constAt ``check_and_right α) arguments) rest
      return mkAppN (← constAt ``check_and_left α) arguments :: others

/-- The propositions that `statedPresentation` states for the bounds `stateds` of one query
`query`, and the proof of their conjunction by one joint test of the query: `prefixes` holds the
check theorem of each bound with its arguments before the test. The proof applies a function of
the joint test to `Eq.refl true`, so the kernel evaluates the query once. -/
private def jointPresentation (stateds : Array StatedBound)
    (prefixes : Array (Name × Array Lean.Expr)) (α domain fn query : Lean.Expr) :
    MetaM (List Lean.Expr × Lean.Expr) := do
  let mut tests : Array Lean.Expr := #[]
  let mut conclusions : Array Lean.Expr := #[]
  for (theoremName, arguments) in prefixes do
    let .forallE _ hypothesis conclusion _ ←
        instantiateForall (← inferType (← constAt theoremName α)) arguments
      | throwError "internal CEGA error: the check theorem {theoremName} takes no test"
    -- `hypothesis` is `Option.any test query = true`.
    tests := tests.push hypothesis.consumeMData.getAppArgs[1]!.getAppArgs[1]!
    conclusions := conclusions.push conclusion
  let attempt ← mkAppM ``EnclosureAttempt #[α, domain, fn]
  let joint ← joinTests attempt tests.toList
  let jointHypothesis ← mkEq (mkApp3 (mkConst ``Option.any [Level.zero]) attempt joint query)
    (Lean.mkConst ``Bool.true)
  withLocalDeclD `h jointHypothesis fun h ↦ do
    let passes ← splitTests attempt α domain fn query h tests.toList
    let mut parts : Array (Lean.Expr × Lean.Expr) := #[]
    for (stated, (theoremName, arguments), conclusion, pass) in
        stateds.zip (prefixes.zip (conclusions.zip passes.toArray)) do
      parts := parts.push (← statedPresentation stated fn domain
        (mkApp (mkAppN (← constAt theoremName α) arguments) pass) (conclusion.instantiate1 pass))
    let proof ← mkLambdaFVars #[h] (conjunctionProof parts.toList)
    return (parts.toList.map (·.1), mkApp proof (← mkEqRefl (Lean.mkConst ``Bool.true)))

/--
Prove the bounds `stateds` of `expr` on `box` with one kernel check, without the search of
`runBoxQuery`. The theorem `StatedBound.checkTheorem` of each bound is applied to the query that
computes the enclosure by `method` itself; the tests of several bounds are joined with `&&` and
split again by `check_and_left` and `check_and_right` (`jointPresentation`). The test is applied
to `Eq.refl true`, so the kernel runs the planner once while it checks the theorem and compares
the interval it returns with every stated rational; nothing is evaluated in the elaborator and no
endpoint is read back. The checked theorem states the bounds as propositions on `boxDomain box`
with `Exact.exprFn` of the quoted expression, their conjunction for several bounds, and the
result holds a proof of each bound (`StatedCheck.checked`). The kernel rejects the theorem when
the query finds no interval or its interval does not give a bound (`StatedCheck.rejected`), and it
may stop for a resource, such as its recursion limit (`StatedCheck.inconclusive`). A check of the
same bounds for the same query earlier in this environment is reused, and a rejected one is not
repeated (`statedBoundCache`); with `reuseOnly`, only such an earlier result counts, and nothing
is checked. Admission and the exponent threshold are those of `runBoxQuery`, and so is a kernel
timeout, which ends the tactic. Native evaluation is never used.
-/
def checkStatedBounds
    {n : Nat} (method : EnclosureMethod) (precision : Precision) (box : List RationalInterval)
    (expr : Verified.Expr (Fin n)) (stateds : Array StatedBound) (reuseOnly : Bool := false) :
    TermElabM StatedCheck := do
  let some first := stateds[0]?
    | return .checked #[]
  let exponent ← validateQueryInput method precision expr
  validateQueryBox box expr
  let mode := if stateds.all (·.mode == first.mode) then first.mode else .enclose
  let bounds := ", ".intercalate (stateds.toList.map (·.render))
  let label := s!"{queryLabel mode method}, stated bound{if stateds.size == 1 then "" else "s"} \
    {bounds}"
  withBoxQueryExponentiationThreshold exponent do
    let (quotedBox, quotedExpr, query) ← boxQueryTerm method precision box expr
    let fn ← mkAppM ``Exact.exprFn #[quotedExpr]
    let domain ← mkAppM ``boxDomain #[quotedBox]
    let α ← functionDomain fn
    -- The implicit arguments are fixed by the query, as in `reduceBoxQuery`; the kernel checks
    -- that they agree with its type.
    let prefixes := stateds.map fun stated ↦
      let (theoremName, values) := stated.checkTheorem
      (theoremName, #[α, domain, fn, query] ++ values.map Lean.toExpr)
    let (propositions, proof) ← match stateds, prefixes with
      | #[stated], #[(theoremName, arguments)] => do
          let check ← constAt theoremName α
          let arguments := arguments.push (← mkEqRefl (Lean.mkConst ``Bool.true))
          let (proposition, proof) ← statedPresentation stated fn domain (mkAppN check arguments)
            (← instantiateForall (← inferType check) arguments)
          pure ([proposition], proof)
      | _, _ => jointPresentation stateds prefixes α domain fn query
    let proposition := conjunctionOf propositions
    if proposition.hasFVar ∨ proposition.hasMVar ∨ proof.hasFVar ∨ proof.hasMVar then
      throwError "CEGA stated bound: the generated theorem is not closed"
    let proofs (name : Name) : StatedCheck :=
      .checked (conjuncts (Lean.mkConst name) propositions).toArray
    match (← statedBoundCache.get)[proof]? with
    | some (some name) =>
        -- The environment may have been restored since, and the name given to another theorem.
        if ((← getEnv).find? name).bind (·.value? (allowOpaque := true)) == some proof then
          trace[cega.stated] "{label}: reusing the theorem checked for this query"
          return proofs name
    | some none =>
        trace[cega.stated] "{label}: rejected by the kernel before"
        return .rejected
    | none => pure ()
    if reuseOnly then
      return .inconclusive
    -- `(name?, final)`: a rejection is final unless the kernel ran out of a resource.
    let (name?, final) ← profileitM Exception "CEGA stated-bound kernel check" (← getOptions) do
      Tactic.ProofCarrier.runKernelCheck "CEGA stated bound"
        (return (some (← addStatedTheorem proposition proof ((← getMainModule) ++ `_cega)), true))
        fun error ↦ do
          let text ← error.toMessageData.toString
          let resource := (← Tactic.ProofCarrier.isKernelDeepRecursion error) ||
            text.startsWith "(kernel) interrupted"
          return (none, !resource)
    trace[cega.stated] "{label}: \
      {if name?.isSome then "checked by the kernel" else "rejected by the kernel"}"
    if final then
      statedBoundCache.modify fun cache ↦
        if cache.size < boxQueryCacheLimit then cache.insert proof name? else cache
    return match name? with
      | some name => proofs name
      | none => if final then .rejected else .inconclusive

/--
The values that the query of `mode` would display for `expr` on `box`, with the enclosure computed
by `method`, read in one kernel evaluation and with no certificate theorem; `none` when the query
finds no enclosure. A rejected stated bound is reported with them, without the search of
`runBoxQuery`.
-/
def readQueryDisplay? {n : Nat} (mode : BoxQueryMode) (method : EnclosureMethod)
    (precision : Precision) (box : List RationalInterval) (expr : Verified.Expr (Fin n)) :
    TermElabM (Option (BoxQueryDisplay ℚ)) := do
  let exponent ← validateQueryInput method precision expr
  validateQueryBox box expr
  withBoxQueryExponentiationThreshold exponent do
    let (_, _, query) ← boxQueryTerm method precision box expr
    let queryType ← instantiateMVars (← inferType query)
    unless queryType.isAppOfArity ``Option 1 do
      throwError "internal CEGA numerical error: a query does not return an optional enclosure"
    let (encoder, count) ← withLocalDeclD `a queryType.appArg! fun a ↦ do
      let fields ← displayFields mode (← mkAppM ``EnclosureAttempt.interval #[a])
      let list ← mkListLit (mkConst ``Rat) (fields.map (·.2)).toList
      return (← mkLambdaFVars #[a] (← mkAppM ``Verified.Expr.Serial.encodeRationals #[list]),
        fields.size)
    -- `0` for no enclosure; `encodeRationals` starts at `1`.
    let read ← mkAppOptM ``Option.elim
      #[none, some (mkConst ``Nat), some query, some (mkRawNatLit 0), some encoder]
    let reduced ← profileitM Exception "CEGA reduce displayed fields" (← getOptions) do
      kernelWhnf read
    let some values := reduced.rawNatLit?.bind (Verified.Expr.Serial.decodeRationals count)
      | return none
    let rationals := values.toArray.map fun (num, den) ↦ mkRat num den
    return match mode, rationals with
      | .enclose, #[lo, hi] => some (.enclosure lo hi)
      | .bound, #[hi] => some (.upperBound hi)
      | .absBound, #[c] => some (.absoluteBound c)
      | .approx, #[center, radius] => some (.midpointApprox center radius)
      | _, _ => none

/-- The real term `↑num / ↑den` of the rational `q`, as the box queries state their rationals. -/
def rationalTerm (q : ℚ) : MetaM Lean.Expr :=
  rationalComponentsAsReal (Lean.toExpr q.num) (Lean.toExpr q.den)

end CAS.CEGA.Elaboration
