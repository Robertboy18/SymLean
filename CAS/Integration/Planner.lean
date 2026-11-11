/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalEval.Digits
public import CAS.Integration.Bioche
public import CAS.Integration.Check
public import CAS.Integration.ExponentialTrig
public import CAS.Integration.Rational

/-!
# Symbolic antiderivative planning

The search half of symbolic integration. `candidate?` proposes antiderivatives and uses
algebraic and semantic derivative checks to prune the search. `integrate?` returns only
certificates produced by the full checked side-conditioned route, so no proof
depends on the planner.

The planner combines the following search mechanisms:

* sparse-polynomial integration, followed by the elementary antiderivative table;
* polynomials in the sine and cosine of one phase over a denominator free of both, by the
  reduction formulas;
* Bioche's substitutions `t = cos u`, `t = sin u` and `t = tan u` for rational functions of
  `sin u` and `cos u`, chosen from the symmetries of the integrand;
* compositional linearity and constant-factor rules;
* substitution into a fresh variable, recursively using the same integrators;
* finite coupled polynomial recurrences for exponential-trigonometric forms;
* exact rational quotient and proper-remainder reduction in any selected coordinate,
  including bounded parameter-dependent linear and quadratic denominators;
* the tangent half-angle substitution for the rational functions of `sin u` and `cos u` that
  no Bioche substitution handles;
* bounded integration by parts with a LIATE-style factor ordering.

The theorems in `CAS.Calculus.Antiderivative` take certificates from the checker
and transport their symbolic derivative identity to analytic calculus.

## Implementation notes

We keep the whole search outside the trusted part. `integrate?` passes the candidate to
`IntegrationCheck.certifyCandidate?`, which accepts it only when `IntegrationCheck.route`
reduces the residual `candidate' - integrand` to literal zero; the integration tactic decides
that equation, with the requirement lists of the certificate, in one `decide +kernel`, and
`IntegrationCheck.AntiderivativeCert.eval_diff_eq` gives the derivative identity wherever the
requirements hold. A wrong heuristic can therefore only make the integration fail.

Integration by parts is represented once. Polynomial-times-exponential,
polynomial-times-trigonometric, polynomial-times-logarithmic, and standalone
logarithmic or inverse-trigonometric expressions all use the same recursive
transformation. Search is fuel-bounded because an integration-by-parts
correction need not be structurally smaller than its input. Exhausting fuel
returns `none`; it does not affect soundness. `integrationByPartsRank` orders the factor to
differentiate as in the LIATE mnemonic of calculus courses (logarithmic and inverse
trigonometric before algebraic), and only these three kinds are differentiated.

After the structural search fails on a variable-dependent quotient, the
planner retries a theorem-side normal form once with less fuel. This exposes
integrable sums hidden by cancellation while every resulting candidate is
still checked against the original integrand.

Polynomial amplitudes multiplying a common exponential and sine/cosine phase
use exact finite operator inversion instead. This resolves the cyclic
recurrence without increasing search fuel or introducing formula-specific
tables.

The derivative check of the search is exact on small residuals: the residual of a candidate
must normalize to zero. A residual heavier than `exactCheckWeight` is evaluated instead with
outward-rounded intervals at a few rational points, and the candidate is rejected only when an
enclosure excludes zero, since exact normalization of a large residual can take far longer than
the rest of the search. A candidate that this screen keeps is still checked by `integrate?`
before any certificate is produced. Two kinds of candidate skip the search check: the primitive
of a trigonometric polynomial (`Bioche.trigPolynomialCandidate?`), and the rational candidate
returned when everything else fails, since the search check omits the full square-root route;
`integrate?` checks them like every other.

## Not supported

The search is much narrower than a general-purpose computer algebra system such
as SymPy. Every gap fails closed (`candidate?` returns `none`, so `integrate?` produces no
certificate). Readers comparing outputs should expect the following to fail:

* general rational integration with symbolic denominator coefficients beyond the bounded
  planner for linear denominators and for quadratics `a*x^2 + b*x + c` with `4*a*c - b^2 > 0`
  (the arctangent branch). That planner accepts numerator degree at most sixteen and retains
  its coefficient and branch conditions. Numerator coefficients may depend on parameters, and
  unused coordinates do not restrict rational reduction;
* general algebraic substitutions, including `√(1 - x²)` and `1/√(x² + 1)`. The
  expression language has no `asinh`/`acosh`, although some such primitives can be written with
  logarithms and square roots;
* product-to-sum reduction for different trigonometric phases, such as `sin x · cos (2x)`.
  Rational functions of the sine and cosine of one phase use Bioche's substitutions or the
  half-angle substitution, but the resulting rational reduction must still succeed;
* irreducible denominators of degree three or more in the rational integrator, apart from two
  candidate families of `RationalElementary.candidate?`, which `integrate?` still has to check:
  a numerator that is a constant multiple of the derivative of the denominator, of any degree,
  and the reciprocal quartics `x^4 + a*x^2 + 1` with `-2 < a < 2`;
* `|t|` across zero: the reifier lowers `abs` to `√(t²)`, whose `ValidAt` condition
  `0 < t²` fails at `t = 0`, so `∫_{-1}^{1} |t| dt = 1` is not provable this way;
* improper but convergent integrals such as `∫_0^1 1/√(1 - t²) dt`, since the checker
  demands the antiderivative's validity conditions on the whole closed interval.
-/

@[expose] public section

namespace CAS.IntegrationPlanner

/-- Collect non-atomic substitution phases, in preorder, without guessing primitives. -/
def substitutionPhasesAux {ι : Type*} :
    Verified.Expr ι → List (Verified.Expr ι) → List (Verified.Expr ι)
  | .nat _, tail | .int _, tail | .rat _ _, tail | .pi, tail |
      .e, tail | .var _, tail => tail
  | expr@(.add a b), tail | expr@(.mul a b), tail | expr@(.sub a b), tail |
      expr@(.div a b), tail | expr@(.rpow a b), tail =>
      expr :: substitutionPhasesAux a (substitutionPhasesAux b tail)
  | expr@(.neg a), tail | expr@(.pow a _), tail | expr@(.atan a), tail |
      expr@(.asin a), tail | expr@(.acos a), tail | expr@(.sqrt a), tail |
      expr@(.log a), tail | expr@(.exp a), tail | expr@(.sin a), tail |
      expr@(.cos a), tail => expr :: substitutionPhasesAux a tail

/-- The arguments of the sines and cosines of an expression, in preorder and without repeats. -/
def trigPhases {ι : Type*} [DecidableEq ι] (expr : Verified.Expr ι) : List (Verified.Expr ι) :=
  ((substitutionPhasesAux expr []).filterMap fun
    | .sin phase | .cos phase => some phase
    | _ => none).eraseDups

/--
Structural upper bound on the polynomial degree in coordinate `i`, when recognized.

A quotient with an `i`-free denominator inherits its numerator's bound, and a
transcendental function of an `i`-free argument receives the bound `0`.
Cancellation is not detected, so `x - x` still receives the bound `1`; `none`
means the syntax is not recognized as polynomial in `i`.
-/
def polynomialDegree? {n : Nat} (i : Fin n) : Verified.Expr (Fin n) → Option Nat
  | .nat _ | .int _ | .rat _ _ | .pi | .e => some 0
  | .var j => if j = i then some 1 else some 0
  | .add a b | .sub a b => do
      let da ← polynomialDegree? i a
      let db ← polynomialDegree? i b
      some (max da db)
  | .mul a b => do
      let da ← polynomialDegree? i a
      let db ← polynomialDegree? i b
      some (da + db)
  | .div a b =>
      if Verified.Expr.containsVar i b = false then
        polynomialDegree? i a
      else
        none
  | .pow a k => do
      let da ← polynomialDegree? i a
      some (da * k)
  | .neg a => polynomialDegree? i a
  | .sin a | .cos a | .atan a | .asin a | .acos a | .exp a | .log a | .sqrt a =>
      if Verified.Expr.containsVar i a = false then some 0 else none
  | .rpow a b =>
      if Verified.Expr.containsVar i a || Verified.Expr.containsVar i b then none else some 0

/--
LIATE-style rank for selecting the differentiated factor in integration by
parts. Logarithmic and inverse-trigonometric factors precede algebraic
factors. Trigonometric and exponential ranks are retained to describe the
ordering. The separate exponential-trigonometric planner solves their
polynomial cyclic recurrences directly, so this fallback still differentiates
only algebraic, logarithmic, and inverse-trigonometric factors.

The rank is only a search heuristic. Candidate validation, not this ordering,
establishes correctness.
-/
def integrationByPartsRank {n : Nat} (i : Fin n)
    (expr : Verified.Expr (Fin n)) : Nat :=
  if Verified.Expr.containsVar i expr = false then
    0
  else
    match expr with
    | .log _ | .atan _ | .asin _ | .acos _ => 5
    | .sin _ | .cos _ => 3
    | .exp _ => 2
    | _ =>
        match polynomialDegree? i expr with
        | some degree => if degree = 0 then 0 else 4
        | none => 0

/-- A factorization `differentiated * integrated` of an integrand for integration by parts. -/
structure ByPartsSplit (n : Nat) where
  /-- The factor to differentiate, selected by `integrationByPartsRank`. -/
  differentiated : Verified.Expr (Fin n)
  /-- The product of the remaining factors, which is integrated first. -/
  integrated : Verified.Expr (Fin n)
  /-- The rank of the differentiated factor; splits are tried in decreasing rank. -/
  rank : Nat

/--
Insert a split into a list ordered by decreasing rank, after every entry whose rank is at
least `split.rank`.
-/
def insertByPartsSplit {n : Nat} (split : ByPartsSplit n) :
    List (ByPartsSplit n) → List (ByPartsSplit n)
  | [] => [split]
  | head :: tail =>
      if head.rank < split.rank then
        split :: head :: tail
      else
        head :: insertByPartsSplit split tail

/--
Walk the factor list of a product and collect its admissible integration-by-parts splits.

`previous` holds the factors already passed, most recent first. For each `factor`, the
integrated part is the product of all other factors. A split is kept only when `factor` has
rank at least `4` (algebraic, logarithmic, or inverse-trigonometric) and the integrated
part still depends on `i`. The result is ordered by decreasing rank.
-/
def byPartsSplitsAux {n : Nat} (i : Fin n) :
    List (Verified.Expr (Fin n)) → List (Verified.Expr (Fin n)) → List (ByPartsSplit n)
  | _, [] => []
  | previous, factor :: rest =>
      let integrated :=
        Verified.Expr.simplifyMulList (previous.reverse ++ rest)
      let tail := byPartsSplitsAux i (factor :: previous) rest
      let rank := integrationByPartsRank i factor
      if rank < 4 || Verified.Expr.containsVar i integrated = false then
        tail
      else
        insertByPartsSplit
          { differentiated := factor, integrated, rank }
          tail

/--
Enumerate the integration-by-parts splits of `expr`, highest rank first.

A product is split along its factor list. A standalone logarithm or inverse-trigonometric
function is differentiated against the constant integrand `1`. Any other expression yields
no split.
-/
def byPartsSplits {n : Nat} (i : Fin n)
    (expr : Verified.Expr (Fin n)) : List (ByPartsSplit n) :=
  match expr with
  | .mul _ _ =>
      byPartsSplitsAux i [] (Verified.Expr.productFactors expr)
  | .log _ | .atan _ | .asin _ | .acos _ =>
      [{ differentiated := expr, integrated := 1, rank := 5 }]
  | _ => []

/-- The size of an expression with each power counted as that many copies of its base. It
decides between the exact residual tests and the interval screen, and bounds the input of the
search normalizer. -/
def residualWeight {ι : Type*} : Verified.Expr ι → Nat
  | .nat _ | .int _ | .rat _ _ | .pi | .e | .var _ => 1
  | .add a b | .mul a b | .sub a b | .div a b | .rpow a b =>
      residualWeight a + residualWeight b + 1
  | .neg a | .atan a | .asin a | .acos a | .sqrt a | .log a | .exp a | .sin a | .cos a =>
      residualWeight a + 1
  | .pow a k => residualWeight a * k + 1

/-- Residuals up to this weight get the exact tests of `searchCheckCandidate?`; heavier ones get
the interval screen. -/
def exactCheckWeight : Nat := 120

/-- Above this weight `normalizeForSearch` returns its input unchanged. -/
def searchNormalizationBudget : Nat := 400

/-- The sample points of the integration coordinate for the screen, away from the poles of the
usual integrands. -/
def screenAbscissae : List ℚ := [7/10, 13/10, 23/9, 5/13, -7/10, -13/10, 37/11, -23/9]

/-- The value of coordinate `j` other than the integration coordinate at every sample. -/
def screenParameter (j : Nat) : ℚ := (17 + 6 * j) / 11

/-- The precision of the interval evaluation of the screen. -/
def screenPrecision : Continuum.DigitsEval.Precision := ⟨64, 30, 60⟩

/-- Whether an interval lies strictly on one side of `0`. -/
def excludesZero (interval : Continuum.RationalInterval) : Bool :=
  decide (0 < interval.lo) || decide (interval.hi < 0)

/-- One sample of the screen at `x`. The result is `some true` when every recorded nonzero and
positivity requirement is decided at `x` and the enclosure of the residual excludes `0`,
`some false` when the requirements are decided and the enclosure contains `0`, and `none` when
a requirement is undecided or the evaluation fails, as at a singular point. -/
def screenSample? {n : Nat} (i : Fin n)
    (requirements : Verified.Expr.ValidityRequirements (Fin n))
    (residual : Verified.Expr (Fin n)) (x : ℚ) : Option Bool := do
  let env : Fin n → Continuum.RationalInterval := fun j ↦
    Continuum.RationalInterval.const (if j = i then x else screenParameter j.val)
  for d in requirements.nonzero do
    let interval ← Continuum.DigitsEval.eval screenPrecision env d
    guard (excludesZero interval)
  for d in requirements.positive do
    let interval ← Continuum.DigitsEval.eval screenPrecision env d
    guard (decide (0 < interval.lo))
  let interval ← Continuum.DigitsEval.eval screenPrecision env residual
  return excludesZero interval

/-- Whether one of the first three decided samples among `abscissae` refutes the residual;
`decided` counts the decided samples so far. -/
def screenRefutesAt {n : Nat} (i : Fin n)
    (requirements : Verified.Expr.ValidityRequirements (Fin n))
    (residual : Verified.Expr (Fin n)) : List ℚ → Nat → Bool
  | [], _ => false
  | x :: abscissae, decided =>
      if 3 ≤ decided then false
      else
        match screenSample? i requirements residual x with
        | some true => true
        | some false => screenRefutesAt i requirements residual abscissae (decided + 1)
        | none => screenRefutesAt i requirements residual abscissae decided

/-- Whether the interval screen refutes `residual`, the residual of `candidate` against `expr`:
an enclosure at one of the first three samples where the requirements of the candidate and of
the integrand are decided excludes `0`. -/
def screenRefutes {n : Nat} (i : Fin n) (expr candidate residual : Verified.Expr (Fin n)) :
    Bool :=
  let ofCandidate := candidate.validityRequirements
  let ofIntegrand := expr.validityRequirements
  screenRefutesAt i ⟨ofCandidate.nonzero ++ ofIntegrand.nonzero,
    ofCandidate.positive ++ ofIntegrand.positive⟩ residual screenAbscissae 0

/--
Normalize an intermediate correction term before recursively planning it.

The normalizer may cancel denominators while discovering a candidate. This is
safe because the final derivative residual is checked against the original
integrand and retains every necessary nonzero side condition. An expression heavier than
`searchNormalizationBudget` is returned unchanged, since the cost of the normalizer grows quickly
with the size of its input.
-/
def normalizeForSearch {n : Nat} (expr : Verified.Expr (Fin n)) : Verified.Expr (Fin n) :=
  if searchNormalizationBudget < residualWeight expr then expr
  else (Verified.Expr.simplifySideClaimRoute expr).rhs

/--
Normalize a quotient whose denominator depends on the integration coordinate `i`.

Any other expression returns `none`, so the normalized retry in `candidateWithFuel?` is
attempted only for variable-dependent quotients.
-/
def normalizedQuotientForSearch? {n : Nat} (i : Fin n) :
    Verified.Expr (Fin n) → Option (Verified.Expr (Fin n))
  | expr@(.div _ denominator) =>
      if Verified.Expr.containsVar i denominator then
        some (normalizeForSearch expr)
      else
        none
  | _ => none

/--
Derivative check used to prune the search.

The residual `candidate.diff i - expr` is first tested for symbolic zero by ordered polynomial
normalization. A residual of weight at most `exactCheckWeight` then gets general algebraic
normalization, side-conditioned fraction normalization and the full residual route, which
handles analytic identities such as the square of a positive square root in parameterized
quadratic primitives, and the candidate is returned when one of them succeeds. A heavier
residual gets the interval screen instead, and the candidate is returned unless the screen
refutes it. `integrate?` must still construct a checked certificate for the candidate it
returns.
-/
def searchCheckCandidate? {n : Nat} (i : Fin n)
    (expr candidate : Verified.Expr (Fin n)) : Option (Verified.Expr (Fin n)) :=
  let residual := candidate.diff i - expr
  if Verified.Expr.Alg.mvNormalizeExpr residual = (0 : Verified.Expr (Fin n)) then
    some candidate
  else if residualWeight residual ≤ exactCheckWeight then
    if Verified.Expr.Alg.normalize residual = (0 : Verified.Expr (Fin n)) ||
        (Verified.Expr.Alg.normalizeFractionWithSide residual).expr =
          (0 : Verified.Expr (Fin n)) ||
        (IntegrationCheck.route i expr candidate).rhs = (0 : Verified.Expr (Fin n)) then
      some candidate
    else
      none
  else if screenRefutes i expr candidate residual then
    none
  else
    some candidate

/-- Apply the lightweight derivative check to an optional candidate, propagating `none`. -/
def checkedCandidate? {n : Nat} (i : Fin n)
    (expr : Verified.Expr (Fin n))
    (candidate : Option (Verified.Expr (Fin n))) :
    Option (Verified.Expr (Fin n)) :=
  candidate.bind (searchCheckCandidate? i expr)

/--
Bioche's substitutions for an integrand with one trigonometric phase `u`. Each substituted
integrand in `t` is normalized and integrated by the same search, lightest first; the first
primitive that, written back in `u` and divided by the slope of `u`, passes the derivative check
is returned. The substitutions only propose candidates: the check against the original
integrand records the branch conditions, such as `cos u ≠ 0` for `t = tan u`.
-/
def biocheCandidate? {n : Nat} (i : Fin n)
    (recurse : Verified.Expr (Fin n) → Option (Verified.Expr (Fin n)))
    (phases : List (Verified.Expr (Fin n))) (expr : Verified.Expr (Fin n)) :
    Option (Verified.Expr (Fin n)) := do
  let abstracted ← Bioche.abstracted? i phases expr
  let weighted := (Bioche.substitutions i abstracted).map fun substitution ↦
    let body := normalizeForSearch substitution.body
    (residualWeight body, substitution, body)
  (weighted.mergeSort fun x y ↦ x.1 ≤ y.1).findSome? fun (_, substitution, body) ↦ do
    let primitive ← recurse body
    let restored := Bioche.restore i primitive substitution.tImage substitution.atanImage?
    checkedCandidate? i expr (some (Bioche.divideBySlope restored abstracted.slope))

/--
Rewrite `expr / phase'` in a fresh coordinate, retaining all other coordinates as parameters.

The old integration coordinate must disappear after abstraction and normalization. Only then is
it safe to reuse its slot for the new variable. This keeps nested substitutions in the same
ambient dimension and prevents a parameter from being captured. Cancellation here is discovery
only: the final residual check uses the original integrand and the restored primitive, so a
zero of `phase'` need not become an analytic side condition.
-/
def substitutionBody? {n : Nat} (i : Fin n)
    (expr phase : Verified.Expr (Fin n)) : Option (Verified.Expr (Fin n)) := do
  guard (Verified.Expr.containsVar i phase)
  let derivative := phase.diff i
  guard (derivative != 0)
  let lift := Verified.Expr.mapVars (fun j : Fin n ↦ .var j.castSucc)
  let liftedPhase := lift phase
  let abstract := Verified.Expr.abstractSubterm liftedPhase (Fin.last n)
  let quotient := lift (Verified.Expr.mkDiv expr derivative)
  let body := abstract (normalizeForSearch (abstract quotient))
  guard (Verified.Expr.containsVar i.castSucc body = false)
  let body := body.mapVars fun j ↦
    if h : j.val < n then .var ⟨j.val, h⟩ else .var i
  guard (body != expr)
  some body

/--
Integrate a transformed body and restore its phase. All recursion uses the same planner,
so substitution composes with polynomial integration, rational reduction, and integration by
parts instead of maintaining a separate primitive table.
-/
def substitutionCandidate? {n : Nat} (i : Fin n)
    (recurse : Verified.Expr (Fin n) → Option (Verified.Expr (Fin n)))
    (expr : Verified.Expr (Fin n)) : Option (Verified.Expr (Fin n)) :=
  (substitutionPhasesAux expr []).eraseDups.findSome? fun phase ↦ do
    let body ← substitutionBody? i expr phase
    let primitive ← recurse body
    checkedCandidate? i expr (some (primitive.mapVars fun j ↦
      if j = i then phase else .var j))

/--
Rationalize a common affine trigonometric phase by the tangent half-angle substitution.

For `u = sin phase / (1 + cos phase)`, replace sine by `2*u/(1+u^2)` and cosine by
`(1-u^2)/(1+u^2)`, and integrate the resulting rational expression with Jacobian
`2/(1+u^2)`. The constant phase slope is divided out after integration. Two fresh coordinates
distinguish the trigonometric atoms from all original parameters. A remaining occurrence of the
old integration coordinate refuses the transformation. The final derivative check, rather than
these replacements, certifies the primitive and records its branch restrictions.
-/
def trigonometricSubstitutionCandidate? {n : Nat} (i : Fin n)
    (recurse : Verified.Expr (Fin n) → Option (Verified.Expr (Fin n)))
    (expr : Verified.Expr (Fin n)) : Option (Verified.Expr (Fin n)) :=
  (trigPhases expr).findSome? fun phase ↦ do
    let slope ← Elementary.nonzeroIndependentDerivative? i phase
    let abstracted ← Bioche.abstractTrig? i phase expr
    let u : Verified.Expr (Fin n) := .var i
    let denominator := 1 + u ^ 2
    let transformed := abstracted.mapVars fun j ↦
      if j = Bioche.sinIndex n then 2 * u / denominator
      else if j = Bioche.cosIndex n then (1 - u ^ 2) / denominator
      else if h : j.val < n then .var ⟨j.val, h⟩ else .var i
    let body := normalizeForSearch (transformed * (2 / denominator))
    let primitive ← recurse body
    let phaseVariable := (.sin phase) / (1 + .cos phase)
    let restored := primitive.mapVars fun j ↦
      if j = i then phaseVariable else .var j
    checkedCandidate? i expr (some (Verified.Expr.simplifyDiv restored slope))

/-- Initial fuel for the top-level antiderivative search in `candidate?`. -/
def maxSearchFuel : Nat := 96

/--
Try each integration-by-parts split in turn and return the first checked candidate.

For a split with differentiated factor `u` and integrated factor `dv`, `recurse` plans a
primitive `v` of `dv` and then a primitive of the normalized correction `u' * v`. The
proposal `u * v - ∫ u' v` is kept only when `searchCheckCandidate?` accepts it against
`expr`; otherwise the remaining splits are tried.
-/
def byPartsCandidate? {n : Nat} (i : Fin n)
    (recurse : Verified.Expr (Fin n) → Option (Verified.Expr (Fin n)))
    (expr : Verified.Expr (Fin n)) :
    List (ByPartsSplit n) → Option (Verified.Expr (Fin n))
  | [] => none
  | split :: rest =>
      let candidate : Option (Verified.Expr (Fin n)) := do
        let primitive ← recurse split.integrated
        let correction :=
          normalizeForSearch
            (Verified.Expr.simplifyMul
              (split.differentiated.diff i) primitive)
        let correctionPrimitive ← recurse correction
        some
          (Verified.Expr.simplifySub
            (Verified.Expr.simplifyMul split.differentiated primitive)
            correctionPrimitive)
      match checkedCandidate? i expr candidate with
      | some checked => some checked
      | none => byPartsCandidate? i recurse expr rest

/--
Apply linearity and constant-factor rules to a sum, difference, negation, product, or
quotient.

`recurse` plans the antiderivative of each operand that depends on the integration
coordinate `i`. A product needs one `i`-free factor and a quotient an `i`-free denominator;
every other head returns `none`.
-/
def compositionalCandidate? {n : Nat} (i : Fin n)
    (recurse : Verified.Expr (Fin n) → Option (Verified.Expr (Fin n))) :
    Verified.Expr (Fin n) → Option (Verified.Expr (Fin n))
  | .add a b => do
      let candidateA ← recurse a
      let candidateB ← recurse b
      some (Verified.Expr.simplifyAdd candidateA candidateB)
  | .sub a b => do
      let candidateA ← recurse a
      let candidateB ← recurse b
      some (Verified.Expr.simplifySub candidateA candidateB)
  | .neg a => (recurse a).map Verified.Expr.mkNeg
  | .mul a b =>
      if Verified.Expr.containsVar i a = false then
        (recurse b).map (Verified.Expr.simplifyMul a)
      else if Verified.Expr.containsVar i b = false then
        (recurse a).map fun candidate ↦
          Verified.Expr.simplifyMul candidate b
      else
        none
  | .div a b =>
      if Verified.Expr.containsVar i b = false then
        (recurse a).map fun candidate ↦
          Verified.Expr.simplifyDiv candidate b
      else
        none
  | _ => none

/--
Fuel-bounded antiderivative search.

Recursive calls generated by integration by parts consume fuel even when the
correction term is not a structural subexpression. Most candidates are pruned
by the lightweight checker. The primitive of a trigonometric polynomial is exact by
construction and proposed at most once, so it defers its Pythagorean residual check
to the certificate check in `integrate?` instead of running the same checked
normalization twice.
-/
def candidateWithFuel? {n : Nat} (i : Fin n)
    (provider? : Option CAS.Polynomial.Sparse.Univariate.RationalFactorization.Provider) :
    Nat → Bool → Verified.Expr (Fin n) → Option (Verified.Expr (Fin n))
  | 0, _, _ => none
  | fuel + 1, allowNormalization, expr =>
      let recurse := candidateWithFuel? i provider? fuel allowNormalization
      let phases := trigPhases expr
      let nonRationalCandidate :=
        checkedCandidate? i expr (Polynomial.candidate? i expr)
          |>.orElse fun _ ↦
            checkedCandidate? i expr (Elementary.candidate? i expr)
          |>.orElse fun _ ↦
            Bioche.trigPolynomialCandidate? i phases expr
          |>.orElse fun _ ↦
            biocheCandidate? i recurse phases expr
          |>.orElse fun _ ↦
            checkedCandidate? i expr (compositionalCandidate? i recurse expr)
          |>.orElse fun _ ↦
            substitutionCandidate? i recurse expr
          |>.orElse fun _ ↦
            checkedCandidate? i expr (ExponentialTrig.candidate? i expr)
      match nonRationalCandidate with
      | some candidate => some candidate
      | none =>
          let rationalCandidate := Rational.candidateIn? i expr provider?
          let remainingDirectCandidate :=
            checkedCandidate? i expr rationalCandidate
              |>.orElse fun _ ↦ trigonometricSubstitutionCandidate? i recurse expr
          match remainingDirectCandidate with
          | some candidate => some candidate
          | none =>
              match byPartsCandidate? i recurse expr (byPartsSplits i expr) with
              | some candidate => some candidate
              | none =>
                  if allowNormalization then
                    let normalizedCandidate : Option (Verified.Expr (Fin n)) :=
                      do
                        let normalized ← normalizedQuotientForSearch? i expr
                        guard (normalized != expr)
                        let proposed ← candidateWithFuel? i provider? fuel false normalized
                        searchCheckCandidate? i expr proposed
                    match normalizedCandidate with
                    | some candidate => some candidate
                    | none => rationalCandidate
                  else
                    /-
                    The lightweight checker omits the full square-root route.
                    `integrate?` checks this final rational candidate.
                    -/
                    rationalCandidate

/-- Discover an antiderivative candidate; `integrate?` performs the final certificate check. -/
def candidate? {n : Nat} (i : Fin n)
    (expr : Verified.Expr (Fin n))
    (provider? : Option CAS.Polynomial.Sparse.Univariate.RationalFactorization.Provider := none) :
    Option (Verified.Expr (Fin n)) :=
  candidateWithFuel? i provider? maxSearchFuel true expr

end CAS.IntegrationPlanner
