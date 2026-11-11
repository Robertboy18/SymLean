/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Expression.Polynomial.Normalization
public import CAS.Expr.Decomposition
public import CAS.Polynomial.Sparse

/-!
# Polynomial-exponential-trigonometric antiderivative candidates

An integrand of the form

```text
exp(u) * (p * sin(v) + q * cos(v)),
```

where `p` and `q` are rational-coefficient multivariate polynomials and the phases `u` and `v`
are affine in the selected coordinate, has an antiderivative

```text
exp(u) * (P * sin(v) + Q * cos(v))
```

with polynomial amplitudes. The slopes `a = ∂u` and `c = ∂v` may contain the other coordinates,
and either factor may be missing: a missing exponential is `a = 0`, and a missing trigonometric
factor is `c = 0`, its terms counting as cosine terms. The amplitudes satisfy

```text
P' + a P - c Q = p,
Q' + c P + a Q = q,
```

that is `(P, Q)' + M (P, Q) = (p, q)` with `M = [[a, -c], [c, a]]`. `candidate?` parses the
integrand (`parse?`, after algebraic normalization when the raw form does not parse) and solves
this system with `candidateOfForm?`.

The readers `Term`, `term?`, `terms?` and their helpers parse a sum of terms
`c xᵏ e ^ (a x) trig (b x)` with `a`, `b` and `c` free of `x`. Commands that read such sums
from their input use them; the Laplace transform extends them by `cosh` and `sinh`.

## Implementation notes

We invert `∂ + M` on polynomials by a terminating series. Two new coordinates stand
for `α = a / (a² + c²)` and `γ = c / (a² + c²)`, so that the inverse of `M` is
`[[α, γ], [-γ, α]]`, and

```text
(P, Q) = Σₖ (-M⁻¹ ∂)ᵏ M⁻¹ (p, q)
```

is a finite sum over `ℚ[α, γ]` (`solveLifted?`), because each derivative lowers the degree in the
selected coordinate. The new coordinates are then replaced by their values over the common
denominator `(a² + c²) ^ k` (`numeratorOver`), which is divided out when it is a rational
constant. Without a trigonometric factor `α` is `1 / a` and `γ` drops out; without an exponential
factor `γ` is `1 / c` and `α` drops out. The planner uses this solver for these integrands in
place of repeated integration by parts, whose recurrence for them is cyclic.

Everything here is candidate generation. The condition `a² + c² ≠ 0` (or `a ≠ 0`, or `c ≠ 0`)
is not assumed: the integration checker differentiates the candidate and records the condition
among the requirements of the result, and `integrate?` accepts the candidate only through
`IntegrationCheck.certifyCandidate?`, when `IntegrationCheck.route` reduces its derivative
residual to literal zero.
-/

@[expose] public section

namespace CAS.IntegrationPlanner.ExponentialTrig

open CAS.Polynomial
open CAS.Verified.Expr.Alg (MvPoly MvMonomial mvOne mvVar mvAdd mvSub mvScaleMonomial
  mvMulPoly mvPowPoly mvConstant? mvPolyOf? mvNormalize mvPolyExpr)

/-- Whether a trigonometric factor is a sine or a cosine. -/
inductive TrigKind where
  | sin
  | cos
deriving DecidableEq

/--
Accumulator for `scanFactors`: the exponential and trigonometric factors found so far in a
product, together with the remaining factors that make up the polynomial amplitude.
-/
structure FactorScan (n : Nat) where
  /-- Argument of the unique `exp` factor found so far, if any. -/
  exponentialPhase : Option (Verified.Expr (Fin n)) := none
  /-- Kind and argument of the unique `sin` or `cos` factor found so far, if any. -/
  trigPhase : Option (TrigKind × Verified.Expr (Fin n)) := none
  /-- The remaining factors, most recent first; they must multiply to a polynomial amplitude. -/
  amplitudeFactors : List (Verified.Expr (Fin n)) := []

/--
Classify the factors of a product into `scan`. A single `exp` factor and a single `sin` or
`cos` factor are recorded in their slots; a second factor of either kind makes the scan fail
with `none`. Every other factor is pushed onto `amplitudeFactors`.
-/
def scanFactors {n : Nat} :
    List (Verified.Expr (Fin n)) → FactorScan n → Option (FactorScan n)
  | [], scan => some scan
  | factor :: rest, scan =>
      match factor with
      | .exp phase =>
          if scan.exponentialPhase.isSome then
            none
          else
            scanFactors rest
              { scan with exponentialPhase := some phase }
      | .sin phase =>
          if scan.trigPhase.isSome then
            none
          else
            scanFactors rest
              { scan with trigPhase := some (.sin, phase) }
      | .cos phase =>
          if scan.trigPhase.isSome then
            none
          else
            scanFactors rest
              { scan with trigPhase := some (.cos, phase) }
      | _ =>
          scanFactors rest
            { scan with
              amplitudeFactors := factor :: scan.amplitudeFactors }

/-- One additive term `amplitude * exp(u) * trig(v)`, where either transcendental factor may be
missing and the amplitude is a polynomial in all coordinates. -/
structure ParsedTerm (n : Nat) where
  /-- The exponential phase `u`, or `none` without an exponential factor. -/
  expPhase? : Option (Verified.Expr (Fin n))
  /-- The kind and the phase of the trigonometric factor, or `none` without one. -/
  trig? : Option (TrigKind × Verified.Expr (Fin n))
  /-- The normalized polynomial amplitude. -/
  amplitude : MvPoly n

/-- Parse one additive term with `scanFactors`. The factors other than `exp`, `sin` and `cos`
must multiply to a polynomial, which is returned in normalized form. -/
def parseTerm? {n : Nat} (term : Verified.Expr (Fin n)) : Option (ParsedTerm n) := do
  let scan ← scanFactors (Verified.Expr.productFactors term) {}
  let amplitude ← mvPolyOf? (Verified.Expr.simplifyMulList scan.amplitudeFactors.reverse)
  some { expPhase? := scan.exponentialPhase, trig? := scan.trigPhase,
         amplitude := mvNormalize amplitude }

/-- A sum `exp(u) * (p * sin(v) + q * cos(v))` in which either phase may be missing. A term
without a trigonometric factor goes to `q`, the cosine of a missing phase being `1`. -/
structure Form (n : Nat) where
  /-- The exponential phase `u` shared by all terms. -/
  expPhase? : Option (Verified.Expr (Fin n))
  /-- The trigonometric phase `v` shared by all terms. -/
  trigPhase? : Option (Verified.Expr (Fin n))
  /-- The amplitude `p` of `sin(v)`. -/
  sinAmplitude : MvPoly n := []
  /-- The amplitude `q` of `cos(v)`. -/
  cosAmplitude : MvPoly n := []

/-- Add a parsed term to a form, or `none` when the phases of the term differ from those of the
form. -/
def Form.addTerm? {n : Nat} (form : Form n) (term : ParsedTerm n) : Option (Form n) := do
  guard (decide (term.expPhase? = form.expPhase?) &&
    decide (term.trig?.map (·.2) = form.trigPhase?))
  match term.trig? with
  | some (.sin, _) => some { form with sinAmplitude := mvAdd form.sinAmplitude term.amplitude }
  | _ => some { form with cosAmplitude := mvAdd form.cosAmplitude term.amplitude }

/-- Split `expr` into signed additive terms and collect them into one form. The result is `none`
when a term does not parse, when two terms have different phases, or when neither phase occurs. -/
def parse? {n : Nat} (expr : Verified.Expr (Fin n)) : Option (Form n) := do
  let terms ← (Verified.Expr.signedAdditiveTerms expr).mapM parseTerm?
  let first ← terms.head?
  let form ← terms.foldlM Form.addTerm?
    ({ expPhase? := first.expPhase?, trigPhase? := first.trig?.map (·.2) } : Form n)
  guard (form.expPhase?.isSome || form.trigPhase?.isSome)
  return form

/-- The slope of a phase in the coordinate `i`, as a polynomial in the other coordinates, and
the zero polynomial for a missing factor. The result is `none` when the phase is not affine in
`i`. -/
def slope? {n : Nat} (i : Fin n) : Option (Verified.Expr (Fin n)) → Option (MvPoly n)
  | none => some []
  | some phase => do
      let slope := mvNormalize (← mvPolyOf? (phase.diff i))
      guard (Sparse.degreeAt i slope = 0)
      return slope

/-- The coordinate appended for `α = a / (a² + c²)`. -/
def alphaIndex (n : Nat) : Fin (n + 2) := ⟨n, by omega⟩

/-- The coordinate appended for `γ = c / (a² + c²)`. -/
def gammaIndex (n : Nat) : Fin (n + 2) := ⟨n + 1, by omega⟩

/-- A monomial in `n` coordinates read in `n + 2` coordinates, with no power of `α` or `γ`. -/
def liftMono {n : Nat} (m : MvMonomial n) : MvMonomial (n + 2) :=
  fun j ↦ if h : j.val < n then m ⟨j.val, h⟩ else 0

/-- A polynomial in `n` coordinates read in `n + 2` coordinates. -/
def liftPoly {n : Nat} (p : MvPoly n) : MvPoly (n + 2) :=
  p.map fun term ↦ (term.1, liftMono term.2)

/-- The powers of the first `n` coordinates of a monomial in `n + 2` coordinates. -/
def lowerMono {n : Nat} (m : MvMonomial (n + 2)) : MvMonomial n :=
  fun j ↦ m j.castSucc.castSucc

/-- The inverse of the phase matrix `[[a, -c], [c, a]]`, its adjugate `[[a, c], [-c, a]]` over
`a² + c²`, written `[[α, γ], [-γ, α]]`: it maps `(s, t)` to `(α s + γ t, α t - γ s)`. -/
def adjugate {n : Nat} (s t : MvPoly (n + 2)) : MvPoly (n + 2) × MvPoly (n + 2) :=
  let alpha := mvVar (alphaIndex n)
  let gamma := mvVar (gammaIndex n)
  (mvAdd (mvScaleMonomial 1 alpha s) (mvScaleMonomial 1 gamma t),
   mvSub (mvScaleMonomial 1 alpha t) (mvScaleMonomial 1 gamma s))

/-- The sum `Σₖ (-step ∂)ᵏ (s, t)` added to `(accS, accT)`, where `∂` differentiates in the
coordinate `i`. It stops when both derivatives vanish, and is `none` when the fuel runs out
first. -/
def solveAux {m : Nat} (i : Fin m) (step : MvPoly m → MvPoly m → MvPoly m × MvPoly m) :
    Nat → MvPoly m → MvPoly m → MvPoly m → MvPoly m → Option (MvPoly m × MvPoly m)
  | 0, s, t, accS, accT =>
      if Sparse.isZero s && Sparse.isZero t then some (accS, accT) else none
  | fuel + 1, s, t, accS, accT =>
      let accS := mvAdd accS s
      let accT := mvAdd accT t
      let ds := Sparse.derivative i s
      let dt := Sparse.derivative i t
      if Sparse.isZero ds && Sparse.isZero dt then some (accS, accT)
      else
        let next := step (Sparse.scale (-1) ds) (Sparse.scale (-1) dt)
        solveAux i step fuel next.1 next.2 accS accT

/-- The amplitudes `(P, Q) = Σₖ (-M⁻¹ ∂)ᵏ M⁻¹ (p, q)` over `ℚ[α, γ]`. The sum is finite because
each derivative lowers the degree in the coordinate `i`. -/
def solveLifted? {n : Nat} (i : Fin n) (p q : MvPoly n) :
    Option (MvPoly (n + 2) × MvPoly (n + 2)) :=
  let first := adjugate (liftPoly p) (liftPoly q)
  let fuel := max (Sparse.degreeAt i p) (Sparse.degreeAt i q) + 1
  solveAux i.castSucc.castSucc adjugate fuel first.1 first.2 [] []

/-- The values of `α` and `γ` over a common denominator: `α = alpha / denominator` and
`γ = gamma / denominator`. -/
structure Images (n : Nat) where
  /-- The numerator of `α`. -/
  alpha : MvPoly n
  /-- The numerator of `γ`. -/
  gamma : MvPoly n
  /-- The common denominator. -/
  denominator : MvPoly n

/-- The constant polynomial `1`. -/
def unitPoly (n : Nat) : MvPoly n := [(1, mvOne n)]

/-- The values of `α` and `γ` for the slopes `a` and `c`: `(a, c)` over `a² + c²`, or `(1, 0)`
over `a` when `c` is zero, or `(0, 1)` over `c` when `a` is zero. The result is `none` when both
slopes are zero. -/
def images? {n : Nat} (a c : MvPoly n) : Option (Images n) :=
  if a.isEmpty && c.isEmpty then none
  else if c.isEmpty then some ⟨unitPoly n, [], a⟩
  else if a.isEmpty then some ⟨[], unitPoly n, c⟩
  else some ⟨a, c, mvAdd (mvMulPoly a a) (mvMulPoly c c)⟩

/-- The total power of `α` and `γ` in a monomial. -/
def slopeWeight {n : Nat} (m : MvMonomial (n + 2)) : Nat :=
  m (alphaIndex n) + m (gammaIndex n)

/-- Whether a monomial has no power of `α` or `γ` whose value is zero. -/
def survives {n : Nat} (images : Images n) (m : MvMonomial (n + 2)) : Bool :=
  (m (alphaIndex n) == 0 || !images.alpha.isEmpty) &&
    (m (gammaIndex n) == 0 || !images.gamma.isEmpty)

/-- The numerator over `denominator ^ top` of a polynomial over `ℚ[α, γ]`: the monomial
`q m α^j γ^k` becomes `q m alpha^j gamma^k denominator^(top - j - k)`. -/
def numeratorOver {n : Nat} (images : Images n) (top : Nat) (p : MvPoly (n + 2)) : MvPoly n :=
  mvNormalize <| p.flatMap fun term ↦
    if survives images term.2 then
      mvMulPoly [(term.1, lowerMono term.2)]
        (mvMulPoly (mvPowPoly images.alpha (term.2 (alphaIndex n)))
          (mvMulPoly (mvPowPoly images.gamma (term.2 (gammaIndex n)))
            (mvPowPoly images.denominator (top - slopeWeight term.2))))
    else []

/-- The candidate `exp(u) * (P * sin(v) + Q * cos(v))` of a form. The amplitudes are solved over
`ℚ[α, γ]`, and the values of `α` and `γ` are put in over the common denominator
`denominator ^ top`, where `top` is the largest power of `α` and `γ` that survives; a rational
constant denominator is divided out. -/
def candidateOfForm? {n : Nat} (i : Fin n) (form : Form n) :
    Option (Verified.Expr (Fin n)) := do
  let a ← slope? i form.expPhase?
  let c ← slope? i form.trigPhase?
  let images ← images? a c
  let (sinSolution, cosSolution) ← solveLifted? i form.sinAmplitude form.cosAmplitude
  let top := (sinSolution ++ cosSolution).foldl (fun acc term ↦
    if survives images term.2 then max acc (slopeWeight term.2) else acc) 0
  let sinNumerator := numeratorOver images top sinSolution
  let cosNumerator := numeratorOver images top cosSolution
  let power := mvPowPoly images.denominator top
  let (sinNumerator, cosNumerator, denominator?) :=
    match mvConstant? power with
    | some r => (Sparse.scale r⁻¹ sinNumerator, Sparse.scale r⁻¹ cosNumerator, none)
    | none => (sinNumerator, cosNumerator,
        some (Verified.Expr.mkPow (mvPolyExpr images.denominator) top))
  let sinAmplitude := Verified.Expr.simplify (mvPolyExpr sinNumerator)
  let cosAmplitude := Verified.Expr.simplify (mvPolyExpr cosNumerator)
  let trigPart : Verified.Expr (Fin n) :=
    match form.trigPhase? with
    | some v => Verified.Expr.simplifyAdd (Verified.Expr.simplifyMul sinAmplitude (.sin v))
        (Verified.Expr.simplifyMul cosAmplitude (.cos v))
    | none => cosAmplitude
  let body : Verified.Expr (Fin n) :=
    match form.expPhase? with
    | some u => Verified.Expr.simplifyMul (.exp u) trigPart
    | none => trigPart
  return match denominator? with
    | some d => Verified.Expr.simplifyDiv body d
    | none => body

/--
Propose an antiderivative for a polynomial-exponential-trigonometric form.

The raw expression is tried first. If its common exponential or trigonometric factor has not
been distributed, the algebraic normalizer supplies an expanded search form. The integration
checker always checks the returned candidate against the caller's original expression.
-/
def candidate? {n : Nat} (i : Fin n)
    (expr : Verified.Expr (Fin n)) : Option (Verified.Expr (Fin n)) :=
  match parse? expr with
  | some form => candidateOfForm? i form
  | none =>
      let normalized := Verified.Expr.Alg.normalize expr
      (parse? normalized).bind (candidateOfForm? i)

/-- A term `c xᵏ e ^ (a x) trig (b x)`. -/
structure Term (N : Nat) where
  /-- The coefficient `c`, free of `x`. -/
  coeff : Verified.Expr (Fin N)
  /-- The power `k` of `x`. -/
  power : Nat
  /-- The rate `a` of `e ^ (a x)`; `none` without an exponential factor. -/
  rate : Option (Verified.Expr (Fin N))
  /-- The frequency `b`, with `true` for `sin (b x)` and `false` for `cos (b x)`; `none`
  without a trigonometric factor. -/
  freq : Option (Verified.Expr (Fin N) × Bool)

variable {N : Nat}

/-- No occurrence of `x`, the variable of index `0`. -/
def isFree (ex : Verified.Expr (Fin N)) : Bool :=
  !(List.finRange N).any fun i ↦ i.val = 0 && ex.containsVar i

/-- No variable at all. -/
def isConst (ex : Verified.Expr (Fin N)) : Bool :=
  !(List.finRange N).any fun i ↦ ex.containsVar i

/-- The variable `x` itself. -/
def isX (ex : Verified.Expr (Fin N)) : Bool :=
  match ex with
  | .var i => i.val = 0
  | _ => false

/-- `e = α x` with `α` free of `x`. -/
partial def linear? (ex : Verified.Expr (Fin N)) : Option (Verified.Expr (Fin N)) :=
  if isX ex then some (.nat 1) else
  match ex with
  | .mul a b => if isFree a && isX b then some a else if isX a && isFree b then some b
      else none
  | .neg a => (linear? a).map .neg
  | .div a d => if isFree d then (linear? a).map (.div · d) else none
  | _ => none

/-- The product `a b` of two coefficients, without a factor `1`. -/
def mulCoeff (a b : Verified.Expr (Fin N)) : Verified.Expr (Fin N) :=
  match a, b with
  | .nat 1, _ => b
  | _, .nat 1 => a
  | _, _ => .mul a b

/-- The product of two terms, with at most one exponential and one trigonometric factor. -/
def combine (s t : Term N) : Option (Term N) := do
  let rate ← match s.rate, t.rate with
    | some _, some _ => none
    | some r, none | none, some r => some (some r)
    | none, none => some none
  let freq ← match s.freq, t.freq with
    | some _, some _ => none
    | some f, none | none, some f => some (some f)
    | none, none => some none
  return { coeff := mulCoeff s.coeff t.coeff, power := s.power + t.power, rate, freq }

/-- Read a product `c xᵏ e ^ (a x) trig (b x)` with `a`, `b`, `c` free of `x`; `none` for
other shapes, such as two exponential or two trigonometric factors. -/
partial def term? (ex : Verified.Expr (Fin N)) : Option (Term N) :=
  if isFree ex then some { coeff := ex, power := 0, rate := none, freq := none } else
  if isX ex then some { coeff := .nat 1, power := 1, rate := none, freq := none } else
  match ex with
  | .mul a b => do combine (← term? a) (← term? b)
  | .neg a => do
      let t ← term? a
      return { t with coeff := .neg t.coeff }
  | .div a d => do
      unless isFree d do none
      let t ← term? a
      return { t with coeff := .div t.coeff d }
  | .pow b k => if isX b then some { coeff := .nat 1, power := k, rate := none, freq := none }
      else none
  | .exp A => do
      let a ← linear? A
      return { coeff := .nat 1, power := 0, rate := some a, freq := none }
  | .cos B => do
      let b ← linear? B
      return { coeff := .nat 1, power := 0, rate := none, freq := some (b, false) }
  | .sin B => do
      let b ← linear? B
      return { coeff := .nat 1, power := 0, rate := none, freq := some (b, true) }
  | _ => none

/-- Read a sum of terms `c xᵏ e ^ (a x) trig (b x)`, each with the flag `true` when it is
subtracted; factors free of `x` go into the coefficients. -/
partial def terms? (ex : Verified.Expr (Fin N)) : Option (List (Bool × Term N)) :=
  match ex with
  | .add a b => return (← terms? a) ++ (← terms? b)
  | .sub a b => return (← terms? a) ++ ((← terms? b).map fun (s, t) ↦ (!s, t))
  | .neg a => return (← terms? a).map fun (s, t) ↦ (!s, t)
  | .mul a b =>
      if isFree a && !isFree b then do
        return (← terms? b).map fun (s, t) ↦ (s, { t with coeff := mulCoeff a t.coeff })
      else if isFree b && !isFree a then do
        return (← terms? a).map fun (s, t) ↦ (s, { t with coeff := mulCoeff t.coeff b })
      else do return [(false, ← term? ex)]
  | _ => do return [(false, ← term? ex)]

end CAS.IntegrationPlanner.ExponentialTrig
