/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Laplace
public import CAS.Calculus.FourierGaussian

/-!
# Fourier transforms of Gaussians: `#cas [fourierTransform x ξ] f`

`#cas [fourierTransform x ξ] f` for `f = c e ^ (-α x ^ 2 + β x + γ)` with rational `c ≠ 0`, `α > 0`,
`β`, `γ` proves, in Mathlib's convention `𝓕 f ξ = ∫ x, e ^ (-2 π i x ξ) f x`
(`FourierTransform.fourier`, `Real.fourier_real_eq_integral_exp_smul`; Mathematica's
`FourierTransform[f, x, ξ, FourierParameters -> {0, -2 Pi}]`),

`∀ ξ : ℝ, 𝓕 (fun x : ℝ ↦ ((f : ℝ) : ℂ)) ξ = c √(π / α) e ^ (p - r π ^ 2 ξ ^ 2) e ^ (-i k π ξ)`

with `p = β ^ 2 / (4 α) + γ`, `r = 1 / α`, `k = β / α` (the phase is missing if `β = 0` and
written `e ^ (i |k| π ξ)` if `k < 0`; `c = 1` is not written and `c = -1` gives `-(√(π / α) ...)`).
Normal form of the square root: with `α = a / b` in lowest terms, `√(π / α)` is printed
`√(b π / a)`, without `b` if `b = 1` and without `/ a` if `a = 1` (`√π` for `α = 1`, `√(2 π)` for
`α = 1 / 2`, `√(π / 3)` for `α = 3`, `√(2 π / 3)` for `α = 3 / 2`); square factors are not taken
out (`√(4 π)` for `α = 1 / 4`). The integrand in the theorem is the input as written (elaborated
over `ℝ` with `Real` open).

Refused: symbolic parameters (also `π`), `α ≤ 0`, exponents of degree over 2, `c = 0`, `tanh`,
inputs inside a section with `variable`s, and the resource limits of `#cas [laplace t s]`
(`CAS.Command.Laplace`): a weighted syntax budget of 600, literals of at most 320 characters,
decimal literals and constant powers with an exponent of at most 256, and rational constants
read from the input (literals and the results of `+ - * /` and `^`) of at most 1024 bits; the
derived constants `p`, `r`, `k` of the output are not capped.

## Implementation notes

The integral is Mathlib's: `integral_cexp_quadratic` evaluates `∫ e ^ (b x ^ 2 + c x + d)` for
`re b < 0`, and `fourier_gaussian_real'` of `CAS/Calculus/FourierGaussian.lean` turns it into the
transform of a real Gaussian in the convention of `FourierTransform.fourier`, with real factors
and a phase. So the command proves no analysis of its own. It reads `f` with `parseExact`, then
`gauss?` (a constant times `e ^ A`) and `quad?` (`A` a polynomial of degree at most 2 in `x`
with rational coefficients), and computes `p`, `r`, `k` and the normal form of the square root in
meta code. The kernel checks the proof: the input equals `c e ^ (-α x ^ 2 + β x + γ)`
(`ring_nf`), `fourier_gaussian_real'` rewrites the transform, and `ring` proves the identities of
the exponent, the phase, `π / α = b π / a` and the real factor. The transform of a Gaussian is
classical; ours are the reader, the printed normal form and the proof script.
-/

public meta section

namespace CAS.Command.FourierTransform

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.IntegrationPlanner.ExponentialTrig
open CAS.Command.Laplace

/-- `c e ^ A` with `c` free of `x`: the coefficient and the exponent `A`. -/
partial def gauss? {N : Nat} (ex : Verified.Expr (Fin N)) :
    Option (Verified.Expr (Fin N) × Verified.Expr (Fin N)) :=
  match ex with
  | .exp A => some (.nat 1, A)
  | .mul a b =>
      if isFree a then (gauss? b).map fun (c, A) ↦ (mulCoeff a c, A)
      else if isFree b then (gauss? a).map fun (c, A) ↦ (mulCoeff c b, A)
      else none
  | .neg a => (gauss? a).map fun (c, A) ↦ (.neg c, A)
  | .div a d => if isFree d then (gauss? a).map fun (c, A) ↦ (.div c d, A) else none
  | _ => none

/-- The product of two polynomials of degree at most 2 (coefficient lists of length 3), `none`
for a larger degree (a coefficient of `x ^ 3` or `x ^ 4` that is not `0`, each checked on its
own) or a coefficient over the bit bound. -/
def qmul (p q : List ℚ) : Option (List ℚ) := do
  let g (l : List ℚ) (i : Nat) : ℚ := l.getD i 0
  if g p 1 * g q 2 + g p 2 * g q 1 ≠ 0 then none
  if g p 2 * g q 2 ≠ 0 then none
  [g p 0 * g q 0, g p 0 * g q 1 + g p 1 * g q 0,
    g p 0 * g q 2 + g p 1 * g q 1 + g p 2 * g q 0].mapM capped

/-- The coefficients `[γ, β, a]` of `A = a x ^ 2 + β x + γ` with rational coefficients. -/
partial def quad? {N : Nat} (ex : Verified.Expr (Fin N)) : Option (List ℚ) :=
  if isFree ex then do return [← ratOf? ex, 0, 0] else
  if isX ex then some [0, 1, 0] else
  match ex with
  | .add a b => do ((← quad? a).zipWith (· + ·) (← quad? b)).mapM capped
  | .sub a b => do ((← quad? a).zipWith (· - ·) (← quad? b)).mapM capped
  | .neg a => do return (← quad? a).map (- ·)
  | .mul a b => do qmul (← quad? a) (← quad? b)
  | .div a d => do
      unless isFree d do none
      let q ← ratOf? d
      if q = 0 then none
      (← quad? a).mapM fun c ↦ capped (c / q)
  | .pow a k => do
      if k > 2 then none
      let p ← quad? a
      match k with
      | 0 => some [1, 0, 0]
      | 1 => some p
      | _ => qmul p p
  | _ => none

/-- `q t` as a term, without a factor `1`. -/
def scaled (q : ℚ) (t : TSyntax `term) : TermElabM (TSyntax `term) := do
  if q = 1 then pure t else `($(← realLit q) * $t)

/-- Run `#cas [fourierTransform x ξ] f`. -/
def logFourier (ref : Syntax) (x ξ : TSyntax `ident) (input : TSyntax `term) :
    CommandElabM Unit := do
  let shape := "fourierTransform: expected c * exp (-α x ^ 2 + β x + γ) with rational c, α, β, γ \
    and α > 0 (parameters are not supported)"
  if x.getId == ξ.getId then
    throwErrorAt ξ "fourierTransform: the variables x and ξ must be different"
  -- As in `#cas [laplace t s]`: the statement is elaborated without the section variables.
  unless (← getScope).varDecls.isEmpty do
    throwErrorAt input "fourierTransform is not supported in a section with `variable`s"
  -- Cheap syntactic checks before the shared reader, whose work and output grow with them.
  if hasTanh input then
    throwErrorAt input "fourierTransform: tanh is not supported"
  if hasLongAtom input then
    throwErrorAt input "fourierTransform: a literal has more than {maxLiteral} characters"
  if hasLargeDecimal input then
    throwErrorAt input "fourierTransform: a decimal literal has a power of ten over {maxExponent}"
  if inputSize input > maxSize then
    throwErrorAt input "fourierTransform: the input is too large (more than {maxSize} syntax \
      nodes, the arguments of sinh, cosh and tan counted twice)"
  let reified ← try parseExact input [x.getId] catch _ => throwErrorAt input shape
  let some (cE, A) := gauss? reified.expr | throwErrorAt input shape
  let some c := ratOf? cE | throwErrorAt input shape
  let some [γ, β, a2] := quad? A | throwErrorAt input shape
  unless a2 < 0 do throwErrorAt input shape
  if c = 0 then throwErrorAt input "fourierTransform: the coefficient c is 0"
  let α := -a2
  -- `𝓕 f ξ = c √(π / α) e ^ (p - r π² ξ²) e ^ (-i k π ξ)`.
  let p := β ^ 2 / (4 * α) + γ
  let r := 1 / α
  let k := β / α
  let xT : TSyntax `term := ⟨x.raw⟩
  let ξT : TSyntax `term := ⟨ξ.raw⟩
  let (proposition, proof, Fpp) ← liftTermElabM do
    let cT ← realLit c
    let αT ← realLit α
    let βT ← realLit β
    let γT ← realLit γ
    -- `π / α` as `b π / a` for `α = a / b` in lowest terms (see the module doc).
    let aT : TSyntax `term := ⟨Syntax.mkNumLit (toString α.num.natAbs)⟩
    let bT : TSyntax `term := ⟨Syntax.mkNumLit (toString α.den)⟩
    let piB ← if α.den = 1 then `(Real.pi) else `(($bT : ℝ) * Real.pi)
    let piOver ← if α.num = 1 then pure piB else `($piB / ($aT : ℝ))
    let sq ← `(Real.sqrt ($piOver))
    let quadT ← scaled r (← `(Real.pi ^ 2 * $ξT ^ 2))
    let E ← if p = 0 then `(-$quadT) else `($(← realLit p) - $quadT)
    let realPart ← if c = 1 then `($sq * Real.exp $E)
      else if c = -1 then `(-($sq * Real.exp $E))
      else `($cT * $sq * Real.exp $E)
    let phase ← scaled |k| (← `(Real.pi * $ξT))
    let F ← if k = 0 then `((($realPart : ℝ) : ℂ))
      else if k > 0 then
        `((($realPart : ℝ) : ℂ) * Complex.exp (-(($phase : ℝ) : ℂ) * Complex.I))
      else
        `((($realPart : ℝ) : ℂ) * Complex.exp ((($phase : ℝ) : ℂ) * Complex.I))
    let fT ← `(open Real in ($input : ℝ))
    let statement ← `(∀ $ξ:ident : ℝ,
      FourierTransform.fourier (fun $x:ident : ℝ ↦ (($fT : ℝ) : ℂ)) $ξT = $F)
    let (pr, q) ← Algebra.proveStatement "fourierTransform" statement (← `(tactic| (
      intro $ξ:ident
      have hf : (fun $x:ident : ℝ ↦ (($fT : ℝ) : ℂ)) = fun $x:ident : ℝ ↦
          (($cT * Real.exp (-$αT * $xT ^ 2 + $βT * $xT + $γT) : ℝ) : ℂ) := by
        funext $x:ident
        congr 1
        -- `congr 1` may already close the goal (e.g. `2 * x - 1` against `2 * x + -1`).
        try ring_nf
      rw [hf, CAS.Calculus.FourierGaussian.fourier_gaussian_real' (by norm_num)]
      have h1 : (($βT ^ 2 - 4 * Real.pi ^ 2 * $ξT ^ 2) / (4 * $αT) + $γT : ℝ) = $E := by ring
      have h2 : (Real.pi * $βT * $ξT / $αT : ℝ) = $(← realLit k) * (Real.pi * $ξT) := by ring
      have h0 : (Real.pi / $αT : ℝ) = $piOver := by ring
      have h3 : ($cT * $sq * Real.exp $E : ℝ) = $realPart := by ring
      rw [h1, h2, h0, h3]
      (try simp only [div_one, one_mul, zero_mul, Complex.ofReal_zero, neg_zero,
        Complex.exp_zero, mul_one, neg_mul, Complex.ofReal_neg, neg_neg]))))
    let Fpp ← forallTelescope pr fun _ body ↦ do
      match body.eq? with
      | some (_, _, rhs) => renderTerm rhs
      | none => return "see the statement"
    return (pr, q, Fpp)
  logReport ref {
    domain := s!"{ξ.getId} ∈ ℝ"
    input := surfaceText input.raw
    inputType := "c e ^ (-α x ^ 2 + β x + γ), α > 0"
    output := Fpp
    outputType := "Fourier transform 𝓕 f ξ = ∫ e ^ (-2 π i x ξ) f x dx (Mathlib)"
  } #[← liftTermElabM <| Algebra.checkedEvidence "fourierTransform"
    s!"Fourier transform" proposition proof]

end CAS.Command.FourierTransform

namespace CAS.Command

open Lean Elab Command

/-- `#cas [fourierTransform x ξ] f` computes the Fourier transform of the Gaussian
`f = c * exp (-α * x ^ 2 + β * x + γ)` in Mathlib's convention
`𝓕 f ξ = ∫ x, exp (-2 * π * I * x * ξ) * f x`, and proves it for every `ξ`.

## Theorem
For the printed `F`, the report proves
`∀ ξ : ℝ, FourierTransform.fourier (fun x : ℝ ↦ (f : ℂ)) ξ = F`
(`CAS.Calculus.FourierGaussian.fourier_gaussian_real'`), where `F` is
`c * √(π / α) * exp (β ^ 2 / (4 * α) + γ - π ^ 2 * ξ ^ 2 / α)` times the phase
`exp (-(π * β * ξ / α) * I)`, which is left out when `β = 0`.

## Conditions and limits
`c ≠ 0`, `α > 0`, `β` and `γ` are rational, and the exponent is a polynomial of degree at most 2
in `x`; symbolic parameters, `π` among them, are refused. With `α = a / b` in lowest terms the
square root is printed `sqrt(b*pi/a)`, such as `sqrt(2*pi)` for `α = 1 / 2`. The input limits
of `#cas [laplace t s]` apply.

## Options
None.

## Examples
```lean
#cas [fourierTransform x ξ] (exp (-x ^ 2))
```
```output
Output (Fourier transform 𝓕 f ξ = ∫ e ^ (-2 π i x ξ) f x dx (Mathlib)):
sqrt(pi)*exp(-(pi^2*ξ^2))
```
```lean
#cas [fourierTransform x ξ] (3 * exp (-(x ^ 2) + 2 * x))
```
```output
Output (Fourier transform 𝓕 f ξ = ∫ e ^ (-2 π i x ξ) f x dx (Mathlib)):
3*sqrt(pi)*exp(1 - pi^2*ξ^2)*exp(-(2*pi*ξ)*i)
```

## In a proof
```lean
theorem fourierTransform_at_zero
    (h : ∀ ξ : ℝ, FourierTransform.fourier (fun x : ℝ ↦ ((Real.exp (-x ^ 2) : ℝ) : ℂ)) ξ =
      ((√Real.pi * Real.exp (-(Real.pi ^ 2 * ξ ^ 2)) : ℝ) : ℂ)) :
    FourierTransform.fourier (fun x : ℝ ↦ ((Real.exp (-x ^ 2) : ℝ) : ℂ)) 0 = (√Real.pi : ℂ) := by
  rw [h 0]
  simp
```
A proof can take the printed theorem as a hypothesis and evaluate it, as here at `ξ = 0`.

## See also
Mathematica `FourierTransform` with `FourierParameters -> {0, -2 Pi}`, SymPy `fourier_transform`.
Mathlib `fourier_gaussian_pi`. The modes `fourier` and `laplace`.

## Possible issues
```lean
#cas [fourierTransform x ξ] (exp (-pi * x ^ 2))
```
```output
fourierTransform: expected c * exp (-α x ^ 2 + β x + γ) with rational c, α, β, γ and α > 0
(parameters are not supported)
```
`α` must be rational. Mathlib's `fourier_gaussian_pi` gives the transform of
`exp (-π * b * x ^ 2)`.
```lean
#cas [fourierTransform x ξ] (exp (x ^ 2))
```
```output
fourierTransform: expected c * exp (-α x ^ 2 + β x + γ) with rational c, α, β, γ and α > 0
(parameters are not supported)
```
The Gaussian must decay: the coefficient of `x ^ 2` in the exponent is negative.
-/
syntax (name := casFourierTransformCommand)
  "#cas" "[" &"fourierTransform" ident ident "]" term : command

elab_rules : command
  | `(#cas [fourierTransform $x:ident $ξ:ident] $f:term) => do
      FourierTransform.logFourier (← getRef) x ξ f

end CAS.Command
