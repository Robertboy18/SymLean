/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Laplace
public import CAS.Command.SpecialFunctions
public import CAS.Command.Admission
public import CAS.Calculus.NDSolve
public meta import CAS.Calculus.NDSolve
public meta import CAS.Polynomial.CoefficientList

/-!
# Certified numerical solutions of ODEs: `#cas [ndsolve y t in [t₀, T], y t₀ = y₀] (y' = f)`

`#cas (digits := d) [ndsolve y t in [t₀, T], y t₀ = y₀ (, at [τ₁, …])] (y' = f)`, for `f` a
polynomial in `t` and `y` with rational coefficients and rational `t₀ < T`, `y₀`,
`τᵢ ∈ [t₀, T]` (by default `[T]`), proves

`(∃ y : ℝ → ℝ, y t₀ = y₀ ∧ IsIntegralCurveOn y (fun t y ↦ f) (Set.Icc t₀ T)) ∧
 (∀ y z, y t₀ = y₀ → IsIntegralCurveOn y … → z t₀ = y₀ → IsIntegralCurveOn z … →
   Set.EqOn y z (Set.Icc t₀ T)) ∧
 (∀ y, y t₀ = y₀ → IsIntegralCurveOn y … → (lo₁ ≤ y τ₁ ∧ y τ₁ ≤ hi₁ ∧ hi₁ - lo₁ ≤ 1 / 10 ^ d) ∧ …)`

with decimals `loᵢ`, `hiᵢ` of `d + 1` places (`1 ≤ d ≤ 15`, default 6): `d` bounds the absolute
width. The vector field is the input `f` as written (elaborated over `ℝ` with `Real` open) as
`fun t y ↦ f`, with the user's names; `IsIntegralCurveOn` is Mathlib's, with derivatives within
`Icc t₀ T` (one-sided at the ends).

## Implementation notes

The search (untrusted) proposes, at each piece start, the Taylor polynomial of degree 16 of the
solution through the current centre (`taylor`, by the recursion `(k + 1) qₖ₊₁ = [f (tᵢ + u, q)]ₖ`
with truncated core polynomial arithmetic), its coefficients rounded to `d + 10` significant
digits, and halves the step until the residual stays within the budget and the tube closes;
pieces end at every output time. When the radius at an output time exceeds `3 / 10 ^ (d + 1)`,
the bound that keeps the rounded enclosure within `10 ^ (-d)`, the residual budget shrinks and
the search runs again with eight more digits, four runs in all. The proof is
`CAS.Calculus.NDSolve.check_sound` with the checker `check` decided by the kernel
(`decide +kernel`) on the pieces of the search, then `fieldEval F = fun t y ↦ f` (`simp`,
`push_cast`, `ring`) and the casts of the rational data. The bounds that `check` verifies and
the proof of `check_sound` (a one-sided Grönwall bound in a tube around each piece,
Picard-Lindelöf for the clamped field, uniqueness) are in `CAS/Calculus/NDSolve.lean`.

Refused, before the work they bound: `f` not a polynomial (also a quotient by an expression in
`t` or `y`, even when it cancels), degree over 4 in `t` or in `y`, more than 20 monomials,
coefficients over 1024 bits, powers with an exponent over 64 or a degree over 16 before
simplification, constants over 4096 bits (`CAS.Command.Admission`), `|t₀|, |T| > 100`,
`T - t₀ > 20`, denominators of `t₀`, `T`, `τ` over 1000 and of `y₀` over `10 ^ 12`, `|y₀| > 100`,
an empty or longer than 8 list of output times, `d > 15`, inputs in a section with `variable`s
(the statement is elaborated without them), the input limits of `#cas [laplace]`, and problems
without a certified enclosure within 200 pieces (for instance when the solution blows up before
`T`, or when it needs steps below the search's resolution).

## References

* Ramon E. Moore, *Interval Analysis*, Prentice-Hall, Englewood Cliffs, N.J., 1966,
  <https://zbmath.org/?q=an:0176.13301>. Its zbMATH review lists the automatic computation of
  Taylor series coefficients for initial-value problems, which `taylor` does in rounded rational
  arithmetic.
-/

public meta section

namespace CAS.Command.NDSolve

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Calculus.NDSolve
open CAS.Polynomial
open CAS.Verified.Expr.Alg

/-- The largest degree of `f` in `y`. -/
def maxDegreeY : Nat := 4
/-- The largest degree of `f` in `t`. -/
def maxDegreeT : Nat := 4
/-- The most monomials of `f`. -/
def maxMonomials : Nat := 20
/-- The most pieces. -/
def maxPieces : Nat := 200
/-- The most output times. -/
def maxOutputs : Nat := 8
/-- The most digits. -/
def maxNDigits : Nat := 15
/-- The largest `|t₀|`, `|T|` and `|y₀|`. -/
def maxValue : ℚ := 100
/-- The longest interval `T - t₀`. -/
def maxSpan : ℚ := 20
/-- The largest total degree of the expression `f` as read, and of each of its subexpressions,
before expansion (`Admission.degreeBounds`, numerator and denominator). -/
def maxReadDegree : Nat := 16
/-- The degree of the Taylor polynomials. -/
def taylorDegree : Nat := 16

/-- `x` rounded to `s` significant decimal digits. -/
def roundSig (x : ℚ) (s : Nat) : ℚ :=
  if x = 0 then 0 else
  let e := CAS.Command.Digits.decimalExponent |x|
  let p : ℚ := (10 : ℚ) ^ ((s : Int) - 1 - e)
  (round (x * p) : ℚ) / p

/-- A nonnegative `x` rounded up to `s` significant decimal digits (`≥ x`). -/
def ceilSig (x : ℚ) (s : Nat) : ℚ :=
  if x ≤ 0 then 0 else
  let e := CAS.Command.Digits.decimalExponent x
  let p : ℚ := (10 : ℚ) ^ ((s : Int) - 1 - e)
  (⌈x * p⌉ : ℚ) / p

/-- `f (t₀ + u, q (u))` modulo `u ^ n`. -/
def composeTrunc (f : List (List ℚ)) (t₀ : ℚ) (q : List ℚ) (n : Nat) : List ℚ :=
  f.foldr (fun c acc ↦ (coeffAdd (coeffShift t₀ c) (coeffMul q acc)).take n) []

/-- The Taylor polynomial of degree `n` at `t₀` of the solution through `c`, its coefficients
rounded to `s` significant digits: `(k + 1) qₖ₊₁ = [f (t₀ + u, q (u))]ₖ`. -/
def taylor (f : List (List ℚ)) (t₀ c : ℚ) (n s : Nat) : List ℚ := Id.run do
  let mut q : List ℚ := [roundSig c s]
  for k in [0:n] do
    let F := composeTrunc f t₀ q (k + 1)
    q := q ++ [roundSig (F.getD k 0 / ((k : ℚ) + 1)) s]
  return q

/-- The pieces from `a` to `b`, ending at every stop, with residual rate `rate` (the residual
budget per unit of time). -/
def solve (f : List (List ℚ)) (a b y₀ : ℚ) (stops : List ℚ) (rate : ℚ) (n s : Nat) :
    Except String (List Piece) := do
  let span := b - a
  let D := fieldDerivY f
  let tiny : ℚ := 1 / 10 ^ (s + 10)
  let mut t := a
  let mut c := y₀
  let mut r : ℚ := 0
  let mut h := roundSig (span / 8) 2
  let mut pieces : Array Piece := #[]
  while t < b do
    if pieces.size ≥ maxPieces then
      throw s!"no certified enclosure within {maxPieces} pieces (reached t = {t}); the \
        solution may blow up, or the problem is stiff"
    let next := (stops.filter (· > t)).foldl min b
    let q := taylor f t c n s
    let ρ := Piece.residualPoly f ⟨t, 0, q, 0, 0, 0, 0, 0⟩
    let gq := compose D t q
    let δ₀ := r + |c - coeffEvalRat q 0|
    let mut hh := min h (next - t)
    let mut found : Option Piece := none
    for _ in [0:60] do
      if found.isSome || hh ≤ 0 then break
      let δraw := absEval ρ hh
      if δraw > rate * hh then
        hh := roundSig (hh / 2) 2
        continue
      let δ := ceilSig δraw 2
      let mut R := 4 * (δ₀ + δ * hh) + tiny
      let mut tooLong := false
      for _ in [0:8] do
        if found.isSome || tooLong then break
        let Y := absEval q hh + R
        let L := upperEval gq hh + (lipBound t hh Y D).2 * R
        let K := max (ceilSig L 3) (1 / 10 ^ 6)
        if K * hh > 1 then
          tooLong := true
          break
        let E := ceilSig (expUpper (K * hh)) 10
        let e := ceilSig (δ₀ * E + δ * (E - 1) / K) 3
        if e < R then
          found := some ⟨t, hh, q, δ, K, E, R, e⟩
        else
          R := 2 * e
      if found.isNone then hh := roundSig (hh / 2) 2
    match found with
    | none => throw s!"no certified step at t = {t}; the solution may blow up there"
    | some P =>
      pieces := pieces.push P
      c := coeffEvalRat q P.length
      r := P.error
      t := t + P.length
      h := min (roundSig (2 * P.length) 2) span
  return pieces.toList

/-- The node `(τ, c, r)` of a list of pieces at the time `τ`. -/
def nodes (f : List (List ℚ)) (a y₀ : ℚ) (ps : List Piece) : List (ℚ × ℚ × ℚ) :=
  match run f a y₀ 0 ps with
  | some (_, ns) => ns
  | none => []

/-- The coefficient lists `cⱼ` (in `t`) of `f = Σ cⱼ (t) yʲ`, from a polynomial in the variables
`t` (index 0) and `y` (index 1). -/
def fieldOfPoly (p : MvPoly 2) : List (List ℚ) := Id.run do
  let dy := p.foldl (fun m (_, mono) ↦ max m (mono 1)) 0
  let dt := p.foldl (fun m (_, mono) ↦ max m (mono 0)) 0
  let mut out : List (List ℚ) := []
  for j in [0:dy + 1] do
    let cs := (List.range (dt + 1)).map fun i ↦
      p.foldl (fun acc (q, mono) ↦ if mono 0 = i && mono 1 = j then acc + q else acc) 0
    out := out ++ [cs]
  return out

/-- `z / 10 ^ k` as a decimal literal (`2.7182818`, `-0.5`, `3`). -/
def decimalSyntax (z : Int) (k : Nat) : TermElabM (TSyntax `term) := do
  if z = 0 then return ← `((0 : ℝ))
  let body := CAS.Command.Digits.renderDecimal z.natAbs k
  -- A decimal literal, typed `ℝ` (an untyped one defaults to `Float`); `m / 10 ^ k` when it would
  -- start with more than four zeros after the point.
  let lit ← if k = 0 then pure (⟨Syntax.mkNumLit body⟩ : TSyntax `term)
    else if z ≠ 0 && (toString z.natAbs).length + 4 < k then
      `(($(⟨Syntax.mkNumLit (toString z.natAbs)⟩) / 10 ^ $(⟨Syntax.mkNumLit (toString k)⟩) : ℝ))
    else `(($(⟨Syntax.mkScientificLit body⟩) : ℝ))
  if z < 0 then `(-$lit) else pure lit

/-- A list of rationals as syntax. -/
def ratListSyntax (l : List ℚ) : TermElabM (TSyntax `term) := do
  let items ← l.mapM fun q ↦ ratSyntax q
  `([$(items.toArray),*])

/-- A piece as syntax. -/
def pieceSyntax (P : Piece) : TermElabM (TSyntax `term) := do
  `((⟨$(← ratSyntax P.start), $(← ratSyntax P.length), $(← ratListSyntax P.poly),
      $(← ratSyntax P.residual), $(← ratSyntax P.lipschitz), $(← ratSyntax P.growth),
      $(← ratSyntax P.radius), $(← ratSyntax P.error)⟩ : CAS.Calculus.NDSolve.Piece))

/-- Run `#cas (digits := d) [ndsolve y t in [a, b], y a = y₀ (, at [τ, …])] (y' = f)`. -/
def logNDSolve (ref : Syntax) (y t : TSyntax `ident) (aS bS : Syntax) (initial : Syntax)
    (times? : Option (Array Syntax)) (digits : Nat) (equation : Syntax) : CommandElabM Unit := do
  if digits = 0 || digits > maxNDigits then
    throwErrorAt ref "ndsolve accepts between 1 and {maxNDigits} digits"
  if y.getId == t.getId then
    throwErrorAt t "ndsolve: the function and the variable must have different names"
  unless (← getScope).varDecls.isEmpty do
    throwErrorAt equation "ndsolve is not supported in a section with `variable`s"
  -- The equation `y' = f`.
  let yPrime := y.getId.appendAfter "'"
  let rhs ← match equation with
    | `(($lhs:ident = $rhs:term)) => if lhs.getId == yPrime then pure rhs else
        throwErrorAt equation "ndsolve: expected an equation {yPrime} = f"
    | `($lhs:ident = $rhs:term) => if lhs.getId == yPrime then pure rhs else
        throwErrorAt equation "ndsolve: expected an equation {yPrime} = f"
    | _ => throwErrorAt equation "ndsolve: expected an equation {yPrime} = f"
  let shape := s!"ndsolve: f must be a polynomial in {t.getId} and {y.getId} with rational \
    coefficients"
  if Laplace.hasLongAtom rhs then
    throwErrorAt rhs "ndsolve: a literal has more than {Laplace.maxLiteral} characters"
  if Laplace.hasLargeDecimal rhs then
    throwErrorAt rhs "ndsolve: a decimal literal has a power of ten over {Laplace.maxExponent}"
  if Laplace.inputSize rhs > Laplace.maxSize then
    throwErrorAt rhs "ndsolve: the input is too large"
  let reified ← try parseExact rhs [t.getId, y.getId] catch _ => throwErrorAt rhs shape
  -- Before any expansion: powers, degrees and constants of the expression as read; a quotient
  -- by an expression with a variable is not a polynomial, and the reader would cancel it with a
  -- gcd whose intermediate results the bounds do not cover.
  Admission.checkExpr "ndsolve" rhs maxReadDegree reified.expr
  if Admission.hasQuotient reified.expr then throwErrorAt rhs shape
  -- The polynomial without the gcds of the rational reader (`Admission.polyOf?`).
  let poly : MvPoly 2 ← if h2 : reified.names.length = 2 then
      match Admission.polyOf? reified.expr with
      | some p => pure (h2 ▸ mvNormalize p)
      | none => throwErrorAt rhs shape
    else throwErrorAt rhs shape
  if poly.length > maxMonomials then
    throwErrorAt rhs "ndsolve accepts at most {maxMonomials} monomials"
  if poly.any fun (_, m) ↦ m 1 > maxDegreeY then
    throwErrorAt rhs "ndsolve accepts degree at most {maxDegreeY} in {y.getId}"
  if poly.any fun (_, m) ↦ m 0 > maxDegreeT then
    throwErrorAt rhs "ndsolve accepts degree at most {maxDegreeT} in {t.getId}"
  if poly.any fun (q, _) ↦ (Laplace.capped q).isNone then
    throwErrorAt rhs "ndsolve: a coefficient has more than {Laplace.maxBits} bits"
  let F := fieldOfPoly poly
  -- The interval, the initial value and the output times.
  let a ← Admission.boundedRational "ndsolve" aS
  let b ← Admission.boundedRational "ndsolve" bS
  unless a < b do throwErrorAt bS "ndsolve: expected t₀ < T"
  if |a| > maxValue || |b| > maxValue then
    throwErrorAt aS "ndsolve accepts |t₀|, |T| ≤ {maxValue}"
  if b - a > maxSpan then throwErrorAt bS "ndsolve accepts T - t₀ ≤ {maxSpan}"
  if a.den > 1000 || b.den > 1000 then
    throwErrorAt aS "ndsolve accepts t₀, T with denominators of at most 1000"
  let y₀ ← match initial with
    | `($f:ident $s:term = $v:term) => do
        unless f.getId == y.getId do
          throwErrorAt initial "ndsolve: expected the initial condition {y.getId} t₀ = y₀"
        let s' ← Admission.boundedRational "ndsolve" s
        unless s' = a do
          throwErrorAt s "ndsolve: the initial condition must be at t₀ = {a}"
        Admission.boundedRational "ndsolve" v
    | _ => throwErrorAt initial "ndsolve: expected the initial condition {y.getId} t₀ = y₀"
  if |y₀| > maxValue || y₀.den > 10 ^ 12 then
    throwErrorAt initial "ndsolve accepts |y₀| ≤ {maxValue} with a denominator of at most 10^12"
  if let some ts := times? then
    if ts.isEmpty then throwErrorAt ref "ndsolve: the list of output times is empty"
    if ts.size > maxOutputs then
      throwErrorAt ref "ndsolve accepts at most {maxOutputs} output times"
  let times ← match times? with
    | some ts => ts.toList.mapM (Admission.boundedRational "ndsolve")
    | none => pure [b]
  for τ in times do
    unless a ≤ τ && τ ≤ b do throwErrorAt ref "ndsolve: the output time {τ} is not in [{a}, {b}]"
    if τ.den > 1000 then
      throwErrorAt ref "ndsolve accepts output times with denominators of at most 1000"
  let times := times.eraseDups
  -- Untrusted search, then the enclosures.
  let k := digits + 1
  let target : ℚ := 3 / 10 ^ k
  let mut rate : ℚ := target / (b - a) / 4
  let mut result : Option (List Piece × List (ℚ × ℚ × ℚ)) := none
  for attempt in [0:4] do
    if result.isSome then break
    let s := digits + 10 + 8 * attempt
    let ps ← match solve F a b y₀ times rate taylorDegree s with
      | .ok ps => pure ps
      | .error message => throwErrorAt equation "ndsolve: {message}"
    let ns := nodes F a y₀ ps
    let worst := times.foldl (fun m τ ↦ match ns.find? (·.1 = τ) with
      | some (_, _, r) => max m r
      | none => m) 0
    if worst ≤ target then
      let mut outs : List (ℚ × ℚ × ℚ) := []
      for τ in times do
        let some (_, c, r) := ns.find? (·.1 = τ)
          | throwErrorAt equation "ndsolve: internal error: no node at the output time {τ}"
        outs := outs ++ [(τ, (⌊(c - r) * 10 ^ k⌋ : ℚ) / 10 ^ k, (⌈(c + r) * 10 ^ k⌉ : ℚ) / 10 ^ k)]
      result := some (ps, outs)
    else
      rate := rate * target / worst / 4
  let some (ps, outs) := result
    | throwErrorAt equation "ndsolve: the enclosure is wider than 10^-{digits}"
  let yT : TSyntax `term := ⟨y.raw⟩
  let zI : TSyntax `ident := mkIdent (Name.mkSimple (if y.getId == `z then "w" else "z"))
  let (proposition, proof) ← liftTermElabM do
    let aT ← Laplace.realLit a
    let bT ← Laplace.realLit b
    let y0T ← Laplace.realLit y₀
    let aQ ← ratSyntax a
    let bQ ← ratSyntax b
    let y0Q ← ratSyntax y₀
    let field ← `(fun ($t $y : ℝ) ↦ open Real in ($(⟨rhs⟩) : ℝ))
    let icc ← `(Set.Icc ($aT : ℝ) $bT)
    let dT : TSyntax `term := ⟨Syntax.mkNumLit (toString digits)⟩
    let mut encl : Array (TSyntax `term) := #[]
    let mut parts : Array (TSyntax `term) := #[]
    for (τ, lo, hi) in outs do
      let τT ← Laplace.realLit τ
      let loT ← decimalSyntax (lo * 10 ^ k).num k
      let hiT ← decimalSyntax (hi * 10 ^ k).num k
      encl := encl.push (← `($loT ≤ $yT $τT ∧ $yT $τT ≤ $hiT ∧ ($hiT : ℝ) - $loT ≤ 1 / 10 ^ $dT))
      let τQ ← ratSyntax τ
      let loQ ← ratSyntax lo
      let hiQ ← ratSyntax hi
      parts := parts.push (← `((by
        have h := k3 $yT h0 h1 (($τQ : ℚ), ($loQ : ℚ), ($hiQ : ℚ)) (by simp)
        dsimp only at h
        have e1 : (($τQ : ℚ) : ℝ) = $τT := by norm_num
        have e2 : (($loQ : ℚ) : ℝ) = $loT := by norm_num
        have e3 : (($hiQ : ℚ) : ℝ) = $hiT := by norm_num
        simp only [e1, e2, e3] at h
        exact ⟨h.1, h.2, by norm_num⟩)))
    let mut enclosure ← `($(encl.back!))
    for e in encl.pop.reverse do
      enclosure ← `($e ∧ $enclosure)
    let mut proofOuts ← `($(parts.back!))
    for p in parts.pop.reverse do
      proofOuts ← `(⟨$p, $proofOuts⟩)
    let statement ← `(
      (∃ $y:ident : ℝ → ℝ, $yT $aT = $y0T ∧ IsIntegralCurveOn $yT $field $icc) ∧
      (∀ $y:ident $zI:ident : ℝ → ℝ, $yT $aT = $y0T → IsIntegralCurveOn $yT $field $icc →
        $zI $aT = $y0T → IsIntegralCurveOn $zI $field $icc → Set.EqOn $yT $zI $icc) ∧
      (∀ $y:ident : ℝ → ℝ, $yT $aT = $y0T → IsIntegralCurveOn $yT $field $icc → $enclosure))
    let FT ← `([$(← F.toArray.mapM ratListSyntax),*])
    let psT ← `([$(← ps.toArray.mapM pieceSyntax),*])
    let outsT ← `([$(← outs.toArray.mapM fun (τ, lo, hi) ↦ do
      `((($(← ratSyntax τ) : ℚ), ($(← ratSyntax lo) : ℚ), ($(← ratSyntax hi) : ℚ)))),*])
    Algebra.proveStatement "ndsolve" statement (← `(tactic| (
      have key := CAS.Calculus.NDSolve.check_sound (f := $FT) (a := $aQ) (b := $bQ)
        (y₀ := $y0Q) (ps := $psT) (outs := $outsT) (by decide +kernel)
      have hF : CAS.Calculus.NDSolve.fieldEval $FT = $field := by
        funext $t:ident $y:ident
        simp only [CAS.Calculus.NDSolve.fieldEval, CAS.Polynomial.coeffEval_cons,
          CAS.Polynomial.coeffEval_nil]
        push_cast
        ring
      have ha : (($aQ : ℚ) : ℝ) = $aT := by norm_num
      have hb : (($bQ : ℚ) : ℝ) = $bT := by norm_num
      have hy : (($y0Q : ℚ) : ℝ) = $y0T := by norm_num
      simp only [hF, ha, hb, hy] at key
      obtain ⟨k1, k2, k3⟩ := key
      exact ⟨k1, k2, fun $y:ident h0 h1 ↦ $proofOuts⟩)))
  let shown := outs.map fun (τ, lo, hi) ↦
    let loZ : Int := ⌊lo * 10 ^ k⌋
    let hiZ : Int := ⌈hi * 10 ^ k⌉
    s!"{y.getId}({τ}) ∈ {CAS.Command.Digits.renderOutcome (.enclosure loZ hiZ k)}"
  logReport ref {
    domain := s!"{t.getId} ∈ [{a}, {b}]"
    input := s!"{surfaceText equation}, \
      {surfaceText initial}"
    inputType := "polynomial initial value problem"
    output := ", ".intercalate shown
    outputType := s!"certified enclosures of width at most 10^-{digits}; the solution exists \
      and is unique on [{a}, {b}] ({countText ps.length "piece"})"
  } #[← liftTermElabM <| Algebra.checkedEvidence "ndsolve"
    s!"Existence, uniqueness and enclosures" proposition proof]

end CAS.Command.NDSolve

namespace CAS.Command

open Lean Elab Command

/-- `#cas [ndsolve y t in [t₀, T], y t₀ = y₀] (y' = f)` solves the initial-value problem
`y' = f`, `y t₀ = y₀` numerically on `[t₀, T]` for a polynomial `f` in `t` and `y`, and prints
certified enclosures of `y` at the output times, by default `T`.

## Theorem
With the field `F = fun t y ↦ f`, the report proves that a solution exists,
`∃ y : ℝ → ℝ, y t₀ = y₀ ∧ IsIntegralCurveOn y F (Set.Icc t₀ T)`, that two solutions `y` and `z`
satisfy `Set.EqOn y z (Set.Icc t₀ T)`, and that every solution satisfies
`lo ≤ y τ ∧ y τ ≤ hi ∧ hi - lo ≤ 1 / 10 ^ d` at each output time `τ` with the printed `[lo, hi]`
(`CAS.Calculus.NDSolve.check_sound`).

## Conditions and limits
`f` is a polynomial in `t` and `y` with rational coefficients, of degree at most 4 in each
variable and with at most 20 monomials. The endpoints are rational with `t₀ < T`,
`|t₀|, |T| ≤ 100` and `T - t₀ ≤ 20`; the initial condition is at `t₀` with a rational `y₀` and
`|y₀| ≤ 100`. `, at [τ₁, …]` lists at most 8 output times in `[t₀, T]`. The solver uses at most
200 pieces, and it refuses where no certified step exists, as near a blow-up of the solution.

## Options
`(digits := d)`: every printed enclosure has width at most `10 ^ (-d)`; `d` is 1 to 15,
default 6.

## Examples
```lean
#cas [ndsolve y t in [0, 1], y 0 = 0] (y' = 1 + y ^ 2)
```
```output
Output (certified enclosures of width at most 10^-6; the solution exists and is unique on [0, 1]
(5 pieces)): y(1) ∈ [1.5574077, 1.5574078]
```
```lean
#cas (digits := 10) [ndsolve y t in [0, 1], y 0 = 1, at [1/2, 1]] (y' = y)
```
```output
Output (certified enclosures of width at most 10^-10; the solution exists and is unique on
[0, 1] (5 pieces)): y(1/2) ∈ [1.64872127070, 1.64872127071],
y(1) ∈ [2.71828182845, 2.71828182846]
```

## In a proof
```lean
theorem ndsolve_exp_bounds : 2.7182818 ≤ Real.exp 1 ∧ Real.exp 1 ≤ 2.7182819 := by
  cas
```
The tactic `cas` does not prove the statement of `ndsolve`; the solution of `y' = y`,
`y 0 = 1` is `Real.exp`, whose value at `1` it bounds directly.

## See also
Mathematica `NDSolve`, mpmath `odefun`. The modes `dsolve`, `nintegrate` and `findRoot`.

## Possible issues
```lean
#cas [ndsolve y t in [0, 2], y 0 = 1] (y' = y ^ 2)
```
```output
ndsolve: no certified step at t = 49841/50000; the solution may blow up there
```
The solution `1 / (1 - t)` blows up at `t = 1`; solve on an interval that ends before it.
```lean
#cas [ndsolve y t in [0, 1], y 0 = 1] (y' = sin y)
```
```output
ndsolve: f must be a polynomial in t and y with rational coefficients
```
Replace `f` by a polynomial, or use `dsolve` for a linear equation.
```lean
#cas [ndsolve y t in [0, 1], y 1 = 1] (y' = y)
```
```output
ndsolve: the initial condition must be at t₀ = 0
```
Start the interval at the point of the initial condition: `[ndsolve y t in [1, 2], y 1 = 1]`.
-/
syntax (name := casNDSolveCommand) "#cas" optConfig "[" &"ndsolve" ident cegaIntervalBinding
  ", " term (atomic(", " " at ") "[" term,* "]")? "]" term : command

elab_rules : command
  | `(#cas $cfg:optConfig [ndsolve $y:ident $t:ident in [$a:term, $b:term], $initial:term
      $[, at [$times:term,*]]?] $equation:term) => do
      NDSolve.logNDSolve (← getRef) y t a b initial (times.map (·.getElems.map (·.raw)))
        (← parseDigitsOption "ndsolve" cfg 6) equation

end CAS.Command
