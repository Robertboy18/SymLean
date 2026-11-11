/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.FourierTransform
public import CAS.Command.InverseLaplace
public import CAS.Command.Admission
public import CAS.Command.Integration
public import CAS.Command.Digits
public import CAS.Command.SpecialFunctions
public import CAS.Analysis.SpecialFunctions.Erf
public meta import CAS.Continuum.IntervalEval.Digits

/-!
# The error function in `#cas`: digits, Gaussian integrals, derivatives

`CAS.erf x = 2 / √π ∫₀ˣ e^(-t²) dt` (`CAS.Analysis.SpecialFunctions.Erf`, the definition of
Mathlib PR #34053; Mathlib v4.35 has no error function). Three additions:

* `#cas [N d] (erf q)` (Mathematica `N[Erf[q], d]`), rational `q` with `|q| ≤ 10` and a
  denominator of at most `1000`, `1 ≤ d ≤ 30`: proves `lo ≤ CAS.erf q ∧ CAS.erf q ≤ hi ∧
  hi - lo ≤ 1 / 10 ^ d` with decimals `lo`, `hi` of `d + 1` places; `d` bounds the absolute
  width. At `q = 0` it prints the exact value `0`. `CAS.Command.Calls` reads the call.
* `#cas [integrate x] f` and `#cas [integrate] f` for `f = c e^(-α x² + β x + γ)` with rational
  `c ≠ 0`, `α > 0`, `β`, `γ` (Mathematica `Integrate[c E^(-α x^2 + β x + γ), x]`): the primitive
  `F x = c e^(γ + β² / (4α)) √π / (2 √α) erf (√α (x - β / (2α)))`, with the theorems
  `∀ a b : ℝ, ∫ x in a..b, f x = F b - F a` and `∀ x : ℝ, HasDerivAt (fun x ↦ F x) (f x) x`.
  Every other integrand, and every input inside a section with `variable`s, is declined
  (`throwUnsupportedSyntax`) and goes to the general integrator.
* `#cas [derive x] e` and `#cas [derive] e` for `e` a sum of terms `c * erf u` (also `erf u`,
  `erf u * c`, `erf u / c`, negations and differences) with `c` free of `x` and `u` affine in `x`
  (`A x + B` up to `ring`, `A`, `B` free of `x`): `∀ x : ℝ, HasDerivAt (fun x ↦ e) D x` with
  `D = Σ c (2 / √π e^(-u²) A)` (Mathematica `D[Erf[u], x]`). Inputs without `erf` fall through
  to the existing `derive`.

`erf` in the input means `CAS.erf` (the identifier is replaced before elaboration).

## Implementation notes

The theory is in `CAS/Analysis/SpecialFunctions/Erf.lean`. For the digits the untrusted
`erfPlan` sums the Taylor series of `erf q` up to the first `N ≥ 1` with `2 q² ≤ N + 1` at which
twice the first omitted term is at most `10 ^ -(d + 3)`, encloses `√π` by `sqrtBounds` with
`d + 6` decimals around Machin's interval `CAS.Continuum.DigitsEval.piInterval` at
`(d + 6) * 3322 / 1000 + 12` bits, and rounds the enclosure outward to `d + 1` places. The kernel
decides `erfCheck` for these numbers, `CAS.erfCheck_sound` turns it into the bounds (the tail is
at most twice the first omitted term, `erf_tail_bound`), and `norm_num` checks the width.

The integrals are a backend of the one `#cas [integrate x]` command, registered in
`CAS/Command/GaussianIntegral.lean` (`gaussianIntegralBackend`) together with the route
`gaussianIntegralRoute` by which bare `cas` proves `∫ x in a..b, f x = v` for such `f`. We read
the integrand as `#cas [fourierTransform]` does (`gauss?`, `quad?`, the same resource limits)
and prove the two theorems by `CAS.integral_gaussian_eq` and `CAS.hasDerivAt_gaussianPrimitive`.
A Gaussian with `α ≠ 0` has no elementary primitive, so the general integrator refuses it, and
its answers for every other input are unchanged. A derivative has at most 8 terms; for each we
compose `CAS.hasDerivAt_erf` with the derivative of `u`, and `HasDerivAt.add`, `HasDerivAt.sub`
and `HasDerivAt.neg` combine them.
-/

public meta section

namespace CAS.Command.Erf

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Command.Laplace
open CAS.Command.FourierTransform

/-! ### Digits -/

/-- The largest `|q|`. -/
def maxArgument : ℚ := 10
/-- The largest denominator of `q`. -/
def maxDenominator : Nat := 1000
/-- The most digits. -/
def maxErfDigits : Nat := 30

/-- Whether `stx` is the identifier `erf` or `CAS.erf`. -/
def isErfIdent (stx : Syntax) : Bool :=
  stx.isIdent && (stx.getId == `erf || stx.getId == `CAS.erf)

/-- Recognize `erf q`. -/
def erfCall? (stx : Syntax) : Option Syntax :=
  match SpecialFunctions.unparen stx with
  | `($f:ident $q:term) => if isErfIdent f then some q else none
  | _ => none

/-- `⌊√x⌋₁₀ₖ`, `⌈√x⌉₁₀ₖ` as rationals with `k` decimals, for `x ≥ 0`: `s₁² ≤ x ≤ s₂²`. -/
def sqrtBounds (x : ℚ) (k : Nat) : ℚ × ℚ :=
  let scale : ℚ := 10 ^ (2 * k)
  let n : Nat := ⌊x * scale⌋.toNat
  let r := n.sqrt
  ((r : ℚ) / 10 ^ k, ((r + 1 : Nat) : ℚ) / 10 ^ k)

/-- The plan for `erf q` at `digits`: the number of terms `N`, the bits `w` of `π`, the bounds of
`√π` and the enclosure `[lo, hi]` with `digits + 1` decimals; `none` if no `N ≤ 2000` reaches
the tolerance. -/
def erfPlan (q : ℚ) (digits : Nat) : Option (Nat × Nat × ℚ × ℚ × Int × Int) := Id.run do
  let k := digits + 1
  let tolerance : ℚ := 1 / 10 ^ (digits + 3)
  let w := (digits + 6) * 3322 / 1000 + 12
  let I := CAS.Continuum.DigitsEval.piInterval w
  let (s₁, _) := sqrtBounds I.lo (digits + 6)
  let (_, s₂) := sqrtBounds I.hi (digits + 6)
  let mut t : ℚ := q
  let mut S : ℚ := 0
  for N in [0:2000] do
    if 1 ≤ N && 2 * q ^ 2 ≤ (N : ℚ) + 1 && 2 * |t| ≤ tolerance then
      let T := 2 * |t|
      let lows := [2 / s₂ * (S - T), 2 / s₁ * (S - T)]
      let highs := [2 / s₂ * (S + T), 2 / s₁ * (S + T)]
      let lo := lows.foldl min (lows.head!)
      let hi := highs.foldl max (highs.head!)
      return some (N, w, s₁, s₂, ⌊lo * 10 ^ k⌋, ⌈hi * 10 ^ k⌉)
    S := S + t
    t := t * (-(q ^ 2)) * (2 * N + 1) / (((N + 1) * (2 * N + 3) : Nat) : ℚ)
  return none

/-- A real decimal literal for `z / 10 ^ k`, typed `ℝ`. -/
def decimalLit (z : Int) (k : Nat) : TermElabM (TSyntax `term) := do
  if z = 0 then return ← `((0 : ℝ))
  let body := CAS.Command.Digits.renderDecimal z.natAbs k
  let lit ← if k = 0 then pure (⟨Syntax.mkNumLit body⟩ : TSyntax `term)
    else if z ≠ 0 && (toString z.natAbs).length + 4 < k then
      `(($(⟨Syntax.mkNumLit (toString z.natAbs)⟩) / 10 ^ $(⟨Syntax.mkNumLit (toString k)⟩) : ℝ))
    else `(($(⟨Syntax.mkScientificLit body⟩) : ℝ))
  if z < 0 then `(-$lit) else pure lit

/-- Run `#cas [N d] (erf q)`. -/
def logErfValue (ref : Syntax) (digits : Nat) (argument input : Syntax) : CommandElabM Unit := do
  checkDigitCount ref "N" digits
  if digits > maxErfDigits then
    throwErrorAt ref "erf accepts at most {maxErfDigits} digits"
  let q ← Admission.boundedRational "erf" argument
  if |q| > maxArgument || q.den > maxDenominator then
    throwErrorAt argument "erf accepts rational points with |q| ≤ {maxArgument} and a \
      denominator of at most {maxDenominator}"
  let some (N, w, s₁, s₂, loZ, hiZ) := erfPlan q digits
    | throwErrorAt input "erf: no number of terms found"
  let k := digits + 1
  unless hiZ - loZ ≤ 10 do
    throwErrorAt input "erf: the enclosure is wider than 10^-{digits}"
  let lo : ℚ := (loZ : ℚ) / 10 ^ k
  let hi : ℚ := (hiZ : ℚ) / 10 ^ k
  let (proposition, proof) ← liftTermElabM do
    let qQ ← ratSyntax q
    let loQ ← ratSyntax lo
    let hiQ ← ratSyntax hi
    let qT ← realLit q
    let loT ← decimalLit loZ k
    let hiT ← decimalLit hiZ k
    let NT : TSyntax `term := ⟨Syntax.mkNumLit (toString N)⟩
    let wT : TSyntax `term := ⟨Syntax.mkNumLit (toString w)⟩
    let dT : TSyntax `term := ⟨Syntax.mkNumLit (toString digits)⟩
    let statement ← `($loT ≤ CAS.erf $qT ∧ CAS.erf $qT ≤ $hiT ∧ ($hiT : ℝ) - $loT ≤ 1 / 10 ^ $dT)
    Algebra.proveStatement "erf" statement (← `(tactic| (
      have h := CAS.erfCheck_sound (q := $qQ) (N := $NT) (w := $wT) (s₁ := $(← ratSyntax s₁))
        (s₂ := $(← ratSyntax s₂)) (lo := $loQ) (hi := $hiQ) (by decide +kernel)
      have e1 : (($qQ : ℚ) : ℝ) = $qT := by norm_num
      have e2 : (($loQ : ℚ) : ℝ) = $loT := by norm_num
      have e3 : (($hiQ : ℚ) : ℝ) = $hiT := by norm_num
      simp only [e1, e2, e3] at h
      exact ⟨h.1, h.2, by norm_num⟩)))
  let (output, outputType) :=
    if loZ = hiZ then (s!"{lo}", "exact value")
    else (CAS.Command.Digits.renderOutcome (.enclosure loZ hiZ k),
      s!"decimal enclosure of width at most 10^-{digits}, with {countText N "term"} of the series")
  let evidence ← liftTermElabM <| Algebra.checkedEvidence "erf" s!"Enclosure of erf {q}"
    proposition proof (some ``CAS.erfCheck_sound)
  logReport ref {
    domain := "error function erf x = 2/√π ∫₀ˣ e^(-t²) dt at a rational point"
    input := surfaceText input
    inputType := "scalar ℝ"
    output
    outputType
  } #[evidence]
  offerExample (some proposition)

/-! ### Gaussian integrals -/

/-- `√r` as a real term (`r > 0`): the rational root when `r` is a rational square, `√r`
otherwise. -/
def sqrtLit (r : ℚ) : TermElabM (TSyntax `term) := do
  match InverseLaplace.ratSqrt? r with
  | some q => realLit q
  | none => `(Real.sqrt $(← realLit r))

/-- The primitive `F (x)` of `c e^(-α x² + β x + γ)` at the term `x`: `k √π e^r / √α erf (√α (x -
x₀))` with `k = c / 2`, `r = γ + β² / (4 α)`, `x₀ = β / (2 α)`, omitting `e^r` for `r = 0`, `√α`
for `α = 1` and `x₀` for `x₀ = 0`. -/
def primitiveSyntax (c α β γ : ℚ) (x : TSyntax `term) : TermElabM (TSyntax `term) := do
  let k := c / 2
  let r := γ + β ^ 2 / (4 * α)
  let x₀ := β / (2 * α)
  let arg ← if x₀ = 0 then pure x else `(($x - $(← realLit x₀)))
  let arg ← if α = 1 then pure arg else `($(← sqrtLit α) * $arg)
  let mut coeff ← `(Real.sqrt Real.pi)
  unless r = 0 do coeff ← `($coeff * Real.exp $(← realLit r))
  unless α = 1 do coeff ← `($coeff / $(← sqrtLit α))
  let scaled ← if k = 1 then pure coeff else `($(← realLit k) * $coeff)
  `($scaled * CAS.erf $arg)

/-- The tactic `have h : ∀ x : ℝ, CAS.gaussianPrimitive α β γ c x = F` with `F` the primitive that
`primitiveSyntax` writes at `x`. Its proof unfolds `CAS.gaussianPrimitive`, evaluates the rational
parts and `√α` when `α` is the square of a rational, and closes the rest by `field_simp` and
`ring_nf`. -/
def primitiveEquation (c α β γ : ℚ) (h x : Ident) : TermElabM (TSyntax `tactic) := do
  let cT ← realLit c
  let αT ← realLit α
  let βT ← realLit β
  let γT ← realLit γ
  let xT : TSyntax `term := ⟨x.raw⟩
  let Fx ← primitiveSyntax c α β γ xT
  let rT ← realLit (γ + β ^ 2 / (4 * α))
  let x0T ← realLit (β / (2 * α))
  -- `√α = q` for a rational square `α`, as printed by `sqrtLit`.
  let sqrtRw ← match InverseLaplace.ratSqrt? α with
    | some q => `(tactic| rw [show Real.sqrt $αT = $(← realLit q) by
        rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]; norm_num])
    | none => `(tactic| skip)
  `(tactic| have $h:ident : ∀ $x:ident : ℝ,
      CAS.gaussianPrimitive $αT $βT $γT $cT $xT = $Fx := by
    intro $x:ident
    unfold CAS.gaussianPrimitive
    have hr : ($γT + $βT ^ 2 / (4 * $αT) : ℝ) = $rT := by norm_num
    have hx0 : ($βT / (2 * $αT) : ℝ) = $x0T := by norm_num
    rw [hr, hx0]
    $sqrtRw:tactic
    have hsα : (0 : ℝ) < Real.sqrt $αT := Real.sqrt_pos.2 (by norm_num)
    try simp only [Real.sqrt_one, Real.exp_zero, sub_zero, mul_one, one_mul, div_one]
    try field_simp
    try ring_nf)

/-- Run `#cas [integrate x] f` for a Gaussian `f`, or decline (`throwUnsupportedSyntax`). -/
def logGaussianIntegral (ref : Syntax) (x : Name) (input : TSyntax `term) :
    CommandElabM Unit := do
  -- Decline everything that is not a Gaussian, before any refusal: the existing integrators see
  -- those inputs unchanged.
  unless (← getScope).varDecls.isEmpty do throwUnsupportedSyntax
  if hasTanh input || hasLongAtom input || hasLargeDecimal input || inputSize input > maxSize then
    throwUnsupportedSyntax
  let reified ← try parseExact input [x] catch _ => throwUnsupportedSyntax
  let some (cE, A) := gauss? reified.expr | throwUnsupportedSyntax
  let some c := ratOf? cE | throwUnsupportedSyntax
  let some [γ, β, a2] := quad? A | throwUnsupportedSyntax
  unless a2 < 0 && c ≠ 0 do throwUnsupportedSyntax
  let α := -a2
  let xI := mkIdent x
  let xT : TSyntax `term := ⟨xI.raw⟩
  let (proposition, proof, Fpp) ← liftTermElabM do
    let cT ← realLit c
    let αT ← realLit α
    let βT ← realLit β
    let γT ← realLit γ
    let fT ← `(open Real in ($input : ℝ))
    let Fx ← primitiveSyntax c α β γ xT
    let aI := mkIdent (if x == `a then `u else `a)
    let bI := mkIdent (if x == `b then `v else `b)
    let Fa ← primitiveSyntax c α β γ ⟨aI.raw⟩
    let Fb ← primitiveSyntax c α β γ ⟨bI.raw⟩
    let statement ← `((∀ $xI:ident : ℝ, HasDerivAt (fun $xI:ident : ℝ ↦ $Fx) $fT $xT) ∧
      ∀ $aI:ident $bI:ident : ℝ, ∫ $xI:ident in $aI..$bI, $fT = $Fb - $Fa)
    -- `F` is `gaussianPrimitive α β γ c` (by `ring` after unfolding), `f` the Gaussian.
    let hI := mkIdent `hP
    let hP ← primitiveEquation c α β γ hI xI
    let (pr, q) ← Algebra.proveStatement "integrate" statement (← `(tactic| (
      have hf : ∀ $xI:ident : ℝ, $fT = $cT * Real.exp (-$αT * $xT ^ 2 + $βT * $xT + $γT) := by
        intro $xI:ident
        try ring_nf
      $hP:tactic
      have hα : (0 : ℝ) < $αT := by norm_num
      refine ⟨fun $xI:ident ↦ ?_, fun $aI:ident $bI:ident ↦ ?_⟩
      · have h := CAS.hasDerivAt_gaussianPrimitive hα $βT $γT $cT $xT
        rw [← hf $xT] at h
        exact (funext $hI:ident : CAS.gaussianPrimitive $αT $βT $γT $cT = _) ▸ h
      · have h := CAS.integral_gaussian_eq hα $βT $γT $cT $(⟨aI.raw⟩) $(⟨bI.raw⟩)
        rw [$hI:ident, $hI:ident] at h
        rw [← h]
        congr 1
        funext $xI:ident
        exact hf $xT)))
    let Fpp ← match pr.getAppFnArgs with
      | (``And, #[hd, _]) => forallTelescope hd fun _ body ↦ do
          match body.getAppFnArgs with
          | (``HasDerivAt, #[_, _, _, _, _, _, _, F, _, _]) =>
              lambdaTelescope F fun _ b ↦ renderTerm b
          | _ => pure "see the statement"
      | _ => pure "see the statement"
    return (pr, q, Fpp)
  -- One kernel check of the conjunction; the report states the integral first.
  let evidence ← liftTermElabM do
    let checked ← CAS.Tactic.Explanation.kernelCheckedProof "integrate" proposition proof
    evidenceReportMessage #[
      ← proofStep "Integral of the input" ``CAS.integral_gaussian_eq
        (← mkAppM ``And.right #[checked]),
      ← proofStep "Derivative of the primitive" ``CAS.hasDerivAt_gaussianPrimitive
        (← mkAppM ``And.left #[checked])]
  logReport ref {
    domain := s!"{x} ∈ ℝ"
    input := surfaceText input.raw
    inputType := "c e ^ (-α x ^ 2 + β x + γ), α > 0"
    output := Fpp
    outputType := "scalar ℝ; antiderivative (with the interval integrals)"
  } #[evidence]
  offerExample (proposition.consumeMData.and?.map (·.2))

/-! ### Derivatives of `erf` -/

/-- Whether the identifier `x` occurs in `stx`. -/
partial def mentions (x : Name) (stx : Syntax) : Bool :=
  (stx.isIdent && stx.getId == x) || stx.getArgs.any (mentions x)

/-- Whether `erf` occurs in `stx`. -/
partial def hasErf (stx : Syntax) : Bool :=
  isErfIdent stx || stx.getArgs.any hasErf

/-- `u = A x + B` with `A`, `B` free of `x`, as term syntax, read from the syntax of `u`. -/
partial def affine? (x : Name) (u : TSyntax `term) :
    TermElabM (Option (TSyntax `term × TSyntax `term)) := do
  if !mentions x u then return some (← `((0 : ℝ)), u)
  match u with
  | `(($v)) => affine? x v
  | `($v:ident) => if v.getId == x then return some (← `((1 : ℝ)), ← `((0 : ℝ))) else return none
  | `($a + $b) => do
      let some (A, B) ← affine? x a | return none
      let some (C, D) ← affine? x b | return none
      return some (← `($A + $C), ← `($B + $D))
  | `($a - $b) => do
      let some (A, B) ← affine? x a | return none
      let some (C, D) ← affine? x b | return none
      return some (← `($A - $C), ← `($B - $D))
  | `(-$a) => do
      let some (A, B) ← affine? x a | return none
      return some (← `(-$A), ← `(-$B))
  | `($a * $b) =>
      if !mentions x a then do
        let some (A, B) ← affine? x b | return none
        return some (← `($a * $A), ← `($a * $B))
      else if !mentions x b then do
        let some (A, B) ← affine? x a | return none
        return some (← `($A * $b), ← `($B * $b))
      else return none
  | `($a / $b) =>
      if mentions x b then return none else do
        let some (A, B) ← affine? x a | return none
        return some (← `($A / $b), ← `($B / $b))
  | _ => return none

/-- The terms `c * erf u` of the input, each with the flag `true` when it is subtracted: the
coefficient `c` (free of `x`) and the argument `u`. -/
partial def erfTerms? (x : Name) (e : TSyntax `term) :
    TermElabM (Option (List (Bool × TSyntax `term × TSyntax `term))) := do
  let one : TSyntax `term ← `((1 : ℝ))
  match e with
  | `(($v)) => erfTerms? x v
  | `($a + $b) => do
      let some l ← erfTerms? x a | return none
      let some r ← erfTerms? x b | return none
      return some (l ++ r)
  | `($a - $b) => do
      let some l ← erfTerms? x a | return none
      let some r ← erfTerms? x b | return none
      return some (l ++ r.map fun (s, c, u) ↦ (!s, c, u))
  | `(-$a) => do
      let some l ← erfTerms? x a | return none
      return some (l.map fun (s, c, u) ↦ (!s, c, u))
  | `($a * $b) =>
      if let some u := erfCall? b then
        return if !mentions x a then some [(false, a, ⟨u⟩)] else none
      else if let some u := erfCall? a then
        return if !mentions x b then some [(false, b, ⟨u⟩)] else none
      else return none
  | `($a / $b) =>
      if let some u := erfCall? a then
        if !mentions x b then return some [(false, ← `(1 / $b), ⟨u⟩)] else return none
      else return none
  | _ => return (erfCall? e).map fun u ↦ [(false, one, ⟨u⟩)]

/-- Replace the identifier `erf` by `CAS.erf`. -/
partial def qualifyErf (stx : Syntax) : Syntax :=
  if stx.isIdent && stx.getId == `erf then mkIdent `CAS.erf
  else match stx with
    | .node info kind args => .node info kind (args.map qualifyErf)
    | s => s

/-- The value of a numeral expression (`+ - * /`, negation, parentheses, numerals). -/
partial def ratOfSyntax? (stx : Syntax) : Option ℚ :=
  match stx.isNatLit? with
  | some n => some n
  | none =>
  match stx with
  | `(($a)) => ratOfSyntax? a
  | `(($a : ℝ)) => ratOfSyntax? a
  | `($a + $b) => return (← ratOfSyntax? a) + (← ratOfSyntax? b)
  | `($a - $b) => return (← ratOfSyntax? a) - (← ratOfSyntax? b)
  | `($a * $b) => return (← ratOfSyntax? a) * (← ratOfSyntax? b)
  | `($a / $b) => do
      let d ← ratOfSyntax? b
      if d = 0 then none else return (← ratOfSyntax? a) / d
  | `(-$a) => return -(← ratOfSyntax? a)
  | _ => none

/-- Run `#cas [derive x] e` for a sum of terms `c * erf u`, or decline. -/
def logErfDerivative (ref : Syntax) (x : Name) (input : TSyntax `term) : CommandElabM Unit := do
  unless (← getScope).varDecls.isEmpty do throwUnsupportedSyntax
  if hasLongAtom input || hasLargeDecimal input || inputSize input > maxSize then
    throwUnsupportedSyntax
  unless hasErf input do throwUnsupportedSyntax
  let some terms ← liftTermElabM (erfTerms? x input) | throwUnsupportedSyntax
  if terms.length > 8 then throwUnsupportedSyntax
  let xI := mkIdent x
  let xT : TSyntax `term := ⟨xI.raw⟩
  let some (proposition, proof, Dpp) ← liftTermElabM do
      let mut D? : Option (TSyntax `term) := none
      let mut Dshow? : Option (TSyntax `term) := none
      let mut sum? : Option (TSyntax `term) := none
      let mut steps : Array (TSyntax `tactic) := #[]
      let mut names : Array (TSyntax `ident) := #[]
      for (neg, c, u) in terms do
        let some (A, B) ← affine? x u | return none
        let A : TSyntax `term := ⟨qualifyErf A⟩
        let B : TSyntax `term := ⟨qualifyErf B⟩
        let cRaw := c
        let c : TSyntax `term ← `(open Real in ($(⟨qualifyErf c⟩) : ℝ))
        let u : TSyntax `term := ⟨qualifyErf u⟩
        let piece ← `($c * (2 / Real.sqrt Real.pi * Real.exp (-($u) ^ 2) * $A))
        let value ← `($c * CAS.erf $u)
        D? := some (← match D? with
          | none => if neg then `(-$piece) else pure piece
          | some D => if neg then `($D - $piece) else `($D + $piece))
        -- With rational `c` and `A`: `k / √π e^(-u²)` with `k = ± 2 c A`.
        let (shown, minus) ← match ratOfSyntax? cRaw, ratOfSyntax? A with
          | some cq, some aq =>
              let k := (if neg then -1 else 1) * 2 * cq * aq
              let g ← `(Real.exp (-($u) ^ 2))
              let t ← if |k| = 1 then `($g / Real.sqrt Real.pi)
                else `($(← realLit |k|) / Real.sqrt Real.pi * $g)
              pure (t, decide (k < 0))
          | _, _ => pure (piece, neg)
        Dshow? := some (← match Dshow? with
          | none => if minus then `(-$shown) else pure shown
          | some D => if minus then `($D - $shown) else `($D + $shown))
        sum? := some (← match sum? with
          | none => if neg then `(-$value) else pure value
          | some S => if neg then `($S - $value) else `($S + $value))
        let h := mkIdent (Name.mkSimple s!"hd{names.size}")
        names := names.push h
        steps := steps.push (← `(tactic| have $h:ident :
            HasDerivAt (fun $xI:ident : ℝ ↦ $value) $piece $xT := by
          have hu : HasDerivAt (fun $xI:ident : ℝ ↦ (open Real in ($u : ℝ))) $A $xT := by
            have e : (fun $xI:ident : ℝ ↦ (open Real in ($u : ℝ))) =
                fun $xI:ident ↦ $A * $xT + $B := by funext $xI:ident; ring
            rw [e]
            simpa using ((hasDerivAt_id $xT).const_mul $A).add_const $B
          exact ((CAS.hasDerivAt_erf _).comp $xT hu).const_mul _))
      let some D := D? | return none
      let some Dshow := Dshow? | return none
      let some S := sum? | return none
      let eT ← `(open Real in ($(⟨qualifyErf input⟩) : ℝ))
      let statement ← `(open Real in
        (∀ $xI:ident : ℝ, HasDerivAt (fun $xI:ident : ℝ ↦ $eT) $Dshow $xT))
      -- Combine the terms with `HasDerivAt.add`, `.sub`, `.neg`, in the order of the sum.
      let mut combined? : Option (TSyntax `term) := none
      for ((neg, _, _), h) in terms.zip names.toList do
        combined? := some (← match combined? with
          | none => if neg then `(($h).neg) else `($h)
          | some p => if neg then `(($p).sub $h) else `(($p).add $h))
      let some combined := combined? | return none
      let mut stepsT : TSyntax `tactic ← `(tactic| skip)
      for st in steps do
        stepsT ← `(tactic| ($stepsT; $st))
      let (pr, q) ← Algebra.proveStatement "derive" statement (← `(tactic| open Real in (
        intro $xI:ident
        $stepsT:tactic
        have hS : (fun $xI:ident : ℝ ↦ $eT) = fun $xI:ident : ℝ ↦ $S := by
          funext $xI:ident; ring
        rw [hS]
        exact ($combined : HasDerivAt _ $D $xT).congr_deriv (by ring))))
      let Dpp ← forallTelescope pr fun _ body ↦ do
        match body.getAppFnArgs with
        | (``HasDerivAt, #[_, _, _, _, _, _, _, _, d, _]) => renderTerm d
        | _ => return "see the statement"
      return some (pr, q, Dpp)
    | throwUnsupportedSyntax
  let evidence ← liftTermElabM <| Algebra.checkedEvidence "derive" "Derivative of the input"
    proposition proof (some ``CAS.hasDerivAt_erf)
  logReport ref {
    domain := s!"{x} ∈ ℝ"
    input := surfaceText input.raw
    inputType := "sum of c * erf (A x + B)"
    output := Dpp
    outputType := "scalar ℝ; derivative"
  } #[evidence]
  offerExample (some proposition)

/-- The identifiers of `stx`. -/
partial def identsOf (stx : Syntax) : List Name :=
  if stx.isIdent then (if stx.getId.isAnonymous then [] else [stx.getId])
  else (stx.getArgs.toList.flatMap identsOf).eraseDups

/-- The one variable of `e` for `#cas [derive] e` and `#cas [integrate] e`: the identifiers that
name no constant (also after `Real.` or `CAS.`, as the statement is elaborated with `Real` open and
`erf` means `CAS.erf`); `none` for an input over the size limits. -/
def freeIdents (stx : Syntax) : CommandElabM (Option (List Name)) := do
  if hasLongAtom stx || inputSize stx > maxSize then return none
  let mut out : List Name := []
  for n in identsOf stx do
    -- A candidate with a field list is a projection, not a constant of that name.
    let resolves (m : Name) : CommandElabM Bool := do
      return (← resolveGlobalName m).any (·.2.isEmpty)
    let global := (← resolves n) || (← resolves (`Real ++ n)) || n == `erf || n == `π ||
      n == `pi
    unless global do out := out ++ [n]
  return some out

end CAS.Command.Erf

namespace CAS.Command

open Lean Elab Command

elab_rules : command
  | `(#cas [derive $x:ident] $expr:term) => do
      Erf.logErfDerivative (← getRef) x.getId expr
  | `(#cas [derive] $expr:term) => do
      match ← Erf.freeIdents expr with
      | some [x] => Erf.logErfDerivative (← getRef) x expr
      | _ => throwUnsupportedSyntax

end CAS.Command
