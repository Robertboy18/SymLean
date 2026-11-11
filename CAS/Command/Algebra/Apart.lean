/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Algebra.Together
public meta import CAS.Tactic.RouteRegistry

/-!
# Partial fractions: `#cas [apart]`

`#cas [apart] e` (or `#cas [apart x] e`) writes a rational function of one real variable as a
polynomial plus a sum of terms `c (x) / p (x) ^ k`: each `p` is a factor of the denominator with
integer coefficients, `k` runs up to its multiplicity, and `deg c < deg p`.

The factors are not searched for here: factoring over `ℚ` is Hex's, through the optional
`CASHex`. Without Hex the factors are those written in the input, the coprime basis of the
factors of its divisors refined by gcds (`factorsOver`), so `1 / ((x - 1) * (x + 1))` splits and
a factor written as `x ^ 2 - 1` stays whole; such a factor need not be irreducible, and when one
of degree two or more remains the report says "partial fractions over the written factors,
refined by gcds". When the denominator is one nonlinear factor with exponent `1` as written,
only the polynomial part is split off (`x ^ 3 / (x ^ 2 + 1) = x - x / (x ^ 2 + 1)`), and a proper
fraction, with nothing to split, is refused (a power of one factor, such as `(x ^ 2 + 1) ^ 2`, is
expanded in that factor). With `import CASHex.Factor` (built with
`lake -R -Khex=on build CASHex`) the denominator is factored completely over `ℚ`, so its factors
are irreducible.

The theorem is `∀ x, d₁ ≠ 0 → … → dₖ ≠ 0 → e = q + ∑ c / p ^ k` over the divisors `dᵢ` of `e` as
written. It holds whichever factors are used: that they are irreducible is not part of the
theorem.

## Implementation notes

`partialFractions` is the classical decomposition by the extended Euclidean algorithm. For a
factor `p` of exponent `e` with cofactor `b`, `Dense.xgcd` gives `s` with `s b ≡ 1` modulo
`p ^ e`; the numerator of that block is `r s` modulo `p ^ e`, for the remainder `r` of the
numerator by the denominator, and its `p`-adic digits, by repeated division by `p`, are the
numerators of the terms `c / p ^ k`. The dense arithmetic is that of
`CAS/Command/Algebra/Dense.lean`. The factors come from the factorizer that `CASHex/Factor.lean`
registers (Hex's Berlekamp-Zassenhaus factorizer, found by `Tactic.RouteRegistry.factorProvider?`)
or, without it, from `factorsOver`, and `Dense.isFactorization` checks them before use. None of
this is trusted: the kernel checks only the final identity, kept as an auxiliary theorem
(`checkedEvidence`). `proveRationalIdentity` of `CAS/Command/Algebra/Basic.lean` proves it: each
`p` divides one of the divisors, which `ring1` shows, and `field_simp` and `ring1` finish.
-/

public meta section

namespace CAS.Command.Algebra

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Verified.Expr.Alg

/-- One partial fraction `constant * numerator / factor ^ power` with a primitive numerator and a
primitive factor of the denominator. -/
structure PartialFraction where
  /-- The rational constant. -/
  constant : ℚ
  /-- The primitive numerator, of degree below that of the factor. -/
  numerator : Dense
  /-- The primitive factor of the denominator. -/
  factor : Dense
  /-- The power of the factor. -/
  power : Nat

/-- The primitive polynomial with integer coefficients and positive leading coefficient, and the
rational `c` with `p = c` times it. -/
def densePrimitive (p : Dense) : ℚ × Dense :=
  let (c, q) := primitivePart (ofDense (0 : Fin 1) p)
  (c, toDense q)

/-- The polynomial part and the partial fractions of `num / den`, `den` nonzero, over the
factorization `factors` of `den`: monic, pairwise coprime factors `p` with exponents `e` such that
`den = lead den ∏ p ^ e` (`Dense.isFactorization`). -/
def partialFractions (num den : Dense) (factors : List (Dense × Nat)) :
    Dense × List PartialFraction := Id.run do
  let (quotient, remainder) := Dense.divMod num den
  let mut out : List PartialFraction := []
  for (p, e) in factors do
    let block := Dense.pow p e
    let cofactor := (Dense.divMod den block).1
    -- `s cofactor + t block = 1`.
    let (_, s, _) := Dense.xgcd cofactor block
    let numerator := (Dense.divMod (Dense.mul remainder s) block).2
    -- The `p`-adic digits of `numerator`, lowest first: `numerator = ∑ digitⱼ pʲ`.
    let mut k := e
    let mut pending := numerator
    let (pc, pPrimitive) := densePrimitive p
    while k > 0 do
      let (next, digit) := Dense.divMod pending p
      unless Dense.isZero digit do
        -- `digit / p ^ k = digit pc⁻ᵏ / pPrimitive ^ k`.
        let scaled := Dense.scale (1 / pc ^ k) digit
        let (dc, dPrimitive) := densePrimitive scaled
        out := out ++ [⟨dc, dPrimitive, pPrimitive, k⟩]
      pending := next
      k := k - 1
  return (quotient, out)

namespace PartialFraction

/-- The term as text in the variable `x`. -/
def text (x : String) (f : PartialFraction) (first : Bool) : String :=
  let names : Fin 1 → String := fun _ ↦ x
  let numerator := ofDense (0 : Fin 1) f.numerator
  let factor := factorText names (ofDense (0 : Fin 1) f.factor) f.power
  let magnitude := if f.constant < 0 then -f.constant else f.constant
  let top := scalePoly magnitude.num numerator
  let topText := polyText names top
  let topText := if (mvNormalize top).length > 1 then s!"({topText})" else topText
  let bottom := if magnitude.den = 1 then factor else s!"({magnitude.den}*{factor})"
  let body := s!"{topText}/{bottom}"
  if first then (if f.constant < 0 then s!"-{body}" else body)
  else if f.constant < 0 then s!" - {body}" else s!" + {body}"

/-- The term as real syntax, without its sign. -/
def term (x : TSyntax `term) (f : PartialFraction) : TermElabM (TSyntax `term) := do
  let vars : Fin 1 → TSyntax `term := fun _ ↦ x
  let magnitude := if f.constant < 0 then -f.constant else f.constant
  let top ← polyTerm vars (scalePoly magnitude.num (ofDense (0 : Fin 1) f.numerator))
  let factor ← factorTerm vars (ofDense (0 : Fin 1) f.factor) f.power
  let bottom ← if magnitude.den = 1 then pure factor
    else `($(natTerm magnitude.den) * $factor)
  `(($top) / ($bottom))

end PartialFraction

/-- Run `#cas [apart x] e` on an expression in the one variable `x`. The denominator is factored
by `factorize?` when it is given (`CASHex` passes Hex's complete factorization over `ℚ`), and
otherwise over the factors written in the input (`factorsOver`). -/
def logApartIn (ref input : Syntax) (reified : ReifiedExpr) (x : Name)
    (h : reified.names.length = 1)
    (factorize? : Option (Dense → List (Dense × Nat)) := none) : CommandElabM Unit := do
  let rational ← match rationalOfExpr reified.expr with
    | .ok r => pure r
    | .error message => throwErrorAt input "apart: {message}"
  -- The expression has the one variable `0`; read its parts as dense polynomials.
  let toOne (p : MvPoly reified.names.length) : MvPoly 1 := h ▸ p
  let num := toDense (toOne rational.value.num)
  let den := toDense (toOne rational.value.den)
  let xText := renderName x
  let factors ← match factorize? with
    | some factorize => pure (factorize den)
    | none =>
        let written := rational.divisors.toList.flatMap fun (d, _) ↦ (writtenFactors d).map toOne
        let factors := factorsOver written den
        -- One nonlinear factor with exponent 1: the polynomial part is still extracted, as in
        -- `x ^ 3 / (x ^ 2 + 1) = x - x / (x ^ 2 + 1)`; a proper fraction has nothing to split.
        if let [(p, 1)] := factors then
          if p.size > 2 && Dense.isZero (Dense.divMod num den).1 then
            let denText := polyText (fun _ ↦ xText) (ofDense (0 : Fin 1) den)
            throwErrorAt input "apart: the denominator {denText} is a single factor as written \
              and the fraction is proper, and without Hex `apart` \
              does not factor it: write it as a product of its factors, or use CASHex \
              (`lake -R -Khex=on build CASHex`, `import CASHex.Factor`), which factors it \
              completely over ℚ"
        pure factors
  unless Dense.isFactorization den factors do
    throwErrorAt input "apart: the factorization of the denominator is not a product of monic, \
      pairwise coprime factors; nothing is claimed"
  let (polynomial, fractions) := partialFractions num den factors
  let shown := Id.run do
    let mut out := if Dense.isZero polynomial then "" else
      polyText (fun _ ↦ xText) (ofDense (0 : Fin 1) polynomial)
    for f in fractions do
      out := out ++ f.text xText out.isEmpty
    return if out.isEmpty then "0" else out
  let (proposition, proof) ← liftTermElabM do
    let xT : TSyntax `term := ⟨(mkIdent x).raw⟩
    let mut rhs? : Option (TSyntax `term) := none
    unless Dense.isZero polynomial do
      rhs? := some (← polyTerm (fun _ ↦ xT) (ofDense (0 : Fin 1) polynomial))
    for f in fractions do
      let t ← f.term xT
      rhs? := some <| ← match rhs? with
        | none => if f.constant < 0 then `(-($t)) else pure t
        | some acc => if f.constant < 0 then `($acc - $t) else `($acc + $t)
    let rhs ← match rhs? with
      | some r => pure r
      | none => `(0)
    let factors := (fractions.map fun f ↦ f.factor).eraseDups.map fun p ↦
      h ▸ ofDense (0 : Fin 1) p
    proveRationalIdentity "apart" reified rational.divisors rhs factors
  let evidence ← liftTermElabM <|
    checkedEvidence "apart" "Identity with the partial fraction decomposition" proposition proof
  logReport ref {
    domain := renderRealDomain reified.names
    input := reified.render
    inputType := "rational function"
    output := shown
    outputType := if factorize?.isNone && factors.any (·.1.size > 2)
      then "partial fractions over the written factors, refined by gcds"
      else "partial fractions"
    conditions? := conditionsText (variableNames reified) rational.divisors
  } #[evidence]

/-- Run `#cas [apart x] e`, with the factorization `factorize?` of the denominator when it is
given (see `logApartIn`). -/
def logApart (ref : Syntax) (coordinate? : Option Name) (input : Syntax)
    (factorize? : Option (Dense → List (Dense × Nat)) := none) : CommandElabM Unit := do
  let reified ← match coordinate? with
    | some x => parseWithLeading input [x]
    | none => parseInferred input
  let some x := reified.names.head? | throwErrorAt input "apart: the expression has no variable"
  if h : reified.names.length = 1 then
    logApartIn ref input reified x h factorize?
  else
    throwErrorAt input "apart: expected a rational function of one variable, found the variables \
      {renderNames reified.names}"

end CAS.Command.Algebra

namespace CAS.Command

open Lean Elab Command

/-- `#cas [apart] e` writes the rational function `e` of one real variable as a polynomial plus a
sum of partial fractions `c / p ^ k`.

## Theorem
For the variable `x` and the divisors `d₁, …, dₖ` of `e` as written, the report proves
`∀ x : ℝ, d₁ ≠ 0 → … → dₖ ≠ 0 → e = q + ∑ c / p ^ k`, where `q` is a polynomial, each `p` is a
factor of the denominator with integer coefficients, `k` runs up to its multiplicity and
`deg c < deg p`. Each `p` divides one of the `dᵢ`, which `ring` shows, and `field_simp` and `ring`
prove the identity. The theorem does not state that the factors are irreducible.

## Conditions and limits
The input is a rational function of one variable with rational coefficients. Without Hex the
factors are those written in the input, refined by gcds: `1 / ((x - 1) * (x + 1))` splits, and a
factor written as `x ^ 2 - 1` stays whole. When a factor of degree two or more remains, the label
reads "partial fractions over the written factors, refined by gcds". When the denominator is one
nonlinear factor with exponent `1`, only the polynomial part is split off, and a proper fraction
with such a denominator is refused. With `CASHex.Factor` imported (built by
`lake -R -Khex=on build CASHex`), Hex factors the denominator completely over `ℚ`.

## Options
An optional variable after the mode name, as in `#cas [apart x] e`, names the variable.

## Examples
```lean
#cas [apart] (1/((x - 1)*(x + 1)))
```
```output
Output (partial fractions): 1/(2*(x - 1)) - 1/(2*(x + 1))
Conditions: (x - 1)*(x + 1) ≠ 0
```
```lean
#cas [apart] (x^5/((x^2+1)*(x-1)^3))
```
```output
Output (partial fractions over the written factors, refined by gcds): 1 + (x + 1)/(4*(x^2 + 1))
+ 1/(2*(x - 1)^3) + 2/(x - 1)^2 + 11/(4*(x - 1))
Conditions: (x^2 + 1)*(x - 1)^3 ≠ 0
```
```lean
#cas [apart x] (1 / ((x - 100000001) * (x - 2)))
```
```output
Output (partial fractions): 1/(99999999*(x - 100000001)) - 1/(99999999*(x - 2))
Conditions: (x - 100000001)*(x - 2) ≠ 0
```

## In a proof
```lean
theorem apart_two_factors (x : ℝ) (h : (x - 1) * (x + 1) ≠ 0) :
    1 / ((x - 1) * (x + 1)) = 1 / (2 * (x - 1)) - 1 / (2 * (x + 1)) := by
  cas
```

## See also
Mathematica `Apart`, SymPy `apart`, Hex `Hex.ZPoly.factorize` (through `CASHex.Factor`). The
modes `together`, `factor` and `integrate`.

## Possible issues
```lean
#cas [apart] (1/(x^2-1))
```
```output
apart: the denominator x^2 - 1 is a single factor as written and the fraction is proper, and
without Hex `apart` does not factor it: write it as a product of its factors, or use CASHex
(`lake -R -Khex=on build CASHex`, `import CASHex.Factor`), which factors it completely over ℚ
```
Write the denominator as `(x - 1)*(x + 1)`, or import `CASHex.Factor`.
```lean
#cas [apart] (1/(x*y))
```
```output
apart: expected a rational function of one variable, found the variables x, y
```
The mode works in one variable.
-/
syntax (name := casApartCommand) "#cas" "[" &"apart" (ppSpace ident)? "]" term : command

elab_rules : command
  | `(#cas [apart $[$x:ident]?] $e:term) => do
      Algebra.logApart e (x.map (·.getId)) e (← liftCoreM Tactic.RouteRegistry.factorProvider?)

end CAS.Command
