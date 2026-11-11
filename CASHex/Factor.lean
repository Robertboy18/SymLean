/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS
public meta import CAS
public import HexBerlekampZassenhausTheory
public meta import HexBerlekampZassenhausTheory
public meta import HexBerlekampZassenhaus.Factorization
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.Tactic.ComputeDegree

/-!
# `#cas [factor]` over the rationals through Hex

With Hex (the optional build `lake -R -Khex=on build CASHex`), `#cas [factor] p` factors a
polynomial `p` in one real variable with rational coefficients into irreducibles over `ℚ`, and the
kernel checks that every factor is irreducible in `ℚ[X]`. Without Hex, `#cas [factor]` splits off
rational roots, perfect powers and homogeneous factors only, so it leaves `x ^ 4 + 4` whole. Hex's
factorizer also becomes the factorizer over `ℚ` of the other commands and of rational
integration, and the reports of `#cas [eigenvalues]` and `#cas [eigenvectors]` gain irreducibility
theorems for the factors of the characteristic polynomial.

## Main definitions

* `factorBackend`: the backend of `#cas [factor]` (`@[cas_route factor]`).
* `denseFactors`: Hex's factorization as the factorizer over `ℚ`, a `FactorProvider` registered
  with `@[cas_route factor]` (`CAS.Tactic.RouteRegistry`).
* `irreducibleOverRationals`: the theorem `Irreducible g` in `ℚ[X]` for an integer factor `g`,
  with its proof, when Hex certifies `g`.
* `eigenvaluesBackend`, `eigenvectorsBackend`: the backends of `#cas [eigenvalues]` and
  `#cas [eigenvectors]`.

## Implementation notes

We write `p = c * q` with a rational `c` and a primitive integer polynomial `q` whose leading
coefficient is positive (`primitivePart`), and let Hex's Berlekamp-Zassenhaus factorizer
`Hex.ZPoly.factorize`, run in compiled code as an untrusted search, split `q` into factors `g`
with exponents `m`. The report then proves, in the kernel:

* the identity `∀ x : ℝ, p x = c * ∏ g x ^ m` between real functions, with `proveCandidate` as for
  the other factored forms;
* for every factor `g`, the theorem `Irreducible g` in `ℚ[X]`: Hex's `irreducibility` certifies
  irreducibility in `ℤ[X]`, an irreducible integer polynomial of positive degree is primitive
  (`Irreducible.isPrimitive`), and Gauss's lemma
  (`Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast`) carries it to `ℚ[X]`.

Since a polynomial over `ℚ` is determined by its values on `ℝ`, these give a product of a nonzero
rational and of irreducibles of `ℚ[X]`. The report does not state the identity in `ℚ[X]` itself,
nor that the factors are pairwise non-associated, so an exponent is the exponent in this product.
When Hex finds no certificate for some factor (for example the Swinnerton-Dyer polynomials, which
need its kernel replay), or the input is not a nonconstant polynomial in one variable, the command
falls back on the factorization of `CAS.Command.FullSimplify`.

With the factorizer `denseFactors`, `#cas [apart]` factors the denominator completely over `ℚ`,
`#cas [product]` the numerator and the denominator, and `#cas [inverseLaplace]` the denominator
and each written divisor, where without Hex they use only the factors written in the input. The
root splitter of `#cas [dsolve]`, `#cas [rsolve]`, `#cas [inverseLaplace]`, `#cas [eigenvalues]`
and `#cas [eigenvectors]` (`CAS.Command.RootSplit`) asks it for the square-free parts of degree
four or more, and for cubics when the rational root search ran out of its bisection budget; the
linear and quadratic factors it returns give exact roots, and the other factors keep enclosures.
The backend of `#cas [eigenvalues]` adds to the spectrum theorem the theorem `Irreducible q` in
`ℚ[X]` for each such factor `q` whose irreducibility Hex certifies, and the backend of
`#cas [eigenvectors]` adds it to the eigenvector theorem for each remaining factor `q` whose
irreducibility Hex certifies. Both reports list the factors without a certificate, such as the
Swinnerton-Dyer polynomials, and name the backend in their planner metadata. Rational integration
(`cas`, `#cas [integrate]`, `#cas [dsolve]`) splits a denominator factor of degree three or more
with it. Hex only proposes the factors there too: every factorization passes
`Dense.isFactorization` (or, for integration, the product check of `RationalFactorization.split`),
and the commands prove their identities in the kernel as they do without Hex.

## References

* The Lean FRO and the Hex contributors, *hex: Verified computational algebra in Lean 4*,
  release v0.10.0, 2026, <https://github.com/leanprover/hex/tree/v0.10.0>.
  We call its factorizer `Hex.ZPoly.factorize` (HexBerlekampZassenhaus) and its tactic
  `irreducibility` (HexBerlekampZassenhausTheory), and translate the dense polynomials of
  SymLean to Hex's with `Hex.DensePoly.ofCoeffs`.
* E. R. Berlekamp, "Factoring Polynomials Over Large Finite Fields", *Mathematics of
  Computation* 24 (1970), pp. 713-735, <https://doi.org/10.1090/S0025-5718-1970-0276200-X>.
  Hex's factorizer factors modulo a prime by the method of Section 3, Eqs. (3.05) to (3.07): a
  linear system with matrix Q - I, then gcds with its solutions shifted by the constants of the
  field. Section 8 lifts the factors modulo a prime by Hensel's lemma to a prime power and tries
  products of them as factors over the integers, as the classical search of Hex does; it also
  describes a class of polynomials, suggested by Swinnerton-Dyer, that are irreducible over the
  rationals but split into linear and quadratic factors modulo every prime. Hex's specification
  of its Berlekamp factorizer cites this paper.
-/

public meta section

namespace CASHex.Factor

open Lean Elab Command Meta
open CAS CAS.Command CAS.Command.InfoView
open CAS.Command.FullSimplify

/-- The rational `c` and the primitive integer coefficients `q`, with positive leading
coefficient, such that the coefficients `cs` (lowest degree first, no trailing zero) are
`c * q`: `Algebra.primitivePart` of the polynomial. -/
def primitivePart (cs : List ℚ) : ℚ × List Int :=
  let (c, q) := Algebra.primitivePart (Algebra.Dense.toSparse cs.toArray)
  (c, (Algebra.Dense.ofSparse q).toList.map (·.num))

/-- The polynomial with integer coefficients `coefficients` (lowest degree first) in
`Polynomial.X`, highest degree first, with numeral coefficients. -/
def polynomialSyntax (coefficients : List Int) : CommandElabM (TSyntax `term) := do
  let x ← `(Polynomial.X)
  let mut sum : Option (TSyntax `term) := none
  for (a, i) in coefficients.zipIdx.reverse do
    if a = 0 then continue
    let magnitude : Term := quote a.natAbs
    let exponent : Term := quote i
    let monomial ← if i = 0 then pure magnitude
      else if a.natAbs = 1 then
        if i = 1 then pure x else `($x ^ $exponent)
      else if i = 1 then `($magnitude * $x)
      else `($magnitude * $x ^ $exponent)
    sum := some <| ← match sum with
      | none => if a < 0 then `(-$monomial) else pure monomial
      | some s => if a < 0 then `($s - $monomial) else `($s + $monomial)
  return sum.getD (← `(0))

/-- The theorem that the factor with integer coefficients `coefficients` is irreducible in
`ℚ[X]`, and its proof, or `none` when Hex finds no certificate. -/
def irreducibleOverRationals (coefficients : List Int) :
    CommandElabM (Option (Lean.Expr × Lean.Expr)) := do
  let overZ ← polynomialSyntax coefficients
  let degree : Term := quote (coefficients.length - 1)
  let statement ← `(Irreducible ($overZ : Polynomial ℚ))
  let proof ← `(by
    have hcasIrreducible : Irreducible ($overZ : Polynomial ℤ) := by irreducibility
    have hcasDegree : ($overZ : Polynomial ℤ).natDegree ≠ 0 := by
      rw [show ($overZ : Polynomial ℤ).natDegree = $degree by compute_degree!]
      decide
    have hcasRational := (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      (hcasIrreducible.isPrimitive hcasDegree)).mp hcasIrreducible
    simpa using hcasRational)
  liftTermElabM do
    let saved ← saveState
    try
      let proposition ← Term.elabTerm statement none
      Term.synthesizeSyntheticMVarsNoPostponing
      let proposition ← instantiateMVars proposition
      let value ← Term.withoutErrToSorry <| Term.elabTerm proof (some proposition)
      Term.synthesizeSyntheticMVarsNoPostponing
      let value ← instantiateMVars value
      if value.hasSyntheticSorry || value.hasMVar then
        saved.restore
        return none
      return some (proposition, value)
    catch _ =>
      saved.restore
      return none

/-- Report `p = scalar * ∏ gᵢ ^ mᵢ` for the input `p` (in the one variable `name`), with the
factors `gᵢ` given by their integer coefficients (lowest degree first): the identity between real
functions, and for each factor the theorem `Irreducible gᵢ` in `ℚ[X]` from Hex's certificate.
The factors come from any search (`origin` names it, `search` labels the node that lists them);
a factor without a certificate, or an identity that does not hold, is `throwUnsupportedSyntax`,
on which `factorBackend` declines the command. -/
def logCertifiedFactorization (input : Syntax) (reified : ReifiedExpr) (name : Name)
    (scalar : ℚ) (factors : List (List Int × Nat)) (origin search : String) :
    CommandElabM Unit := do
  -- The certified part: each factor's irreducibility over ℚ.
  let mut certified := #[]
  for (g, _) in factors do
    let some step ← irreducibleOverRationals g | throwUnsupportedSyntax
    certified := certified.push step
  -- The identity over the reals, proved as the other factored forms are.
  let x : Form := .var name
  let factorForm (g : List Int) (m : Nat) : Form :=
    let base := polynomialForm x (g.map fun a ↦ (a : ℚ))
    if m = 1 then base else .pow base m
  let product := match factors with
    | [] => Form.num 1
    | (g, m) :: rest => rest.foldl (fun acc (h, k) ↦ .mul acc (factorForm h k)) (factorForm g m)
  let form := if scalar = 1 then product else .mul (.num scalar) product
  let lhs := Form.ofExpr reified.names reified.expr
  let candidate : Candidate := { form := form, origin }
  let some (_, identity) ← proveCandidate reified.names lhs candidate
    | throwUnsupportedSyntax
  let steps ← liftTermElabM do
    let mut steps := #[← Tactic.Explanation.UncheckedExplanationStep.ofProof
      "Identity with the factorization" identity]
    for (_, proof) in certified do
      steps := steps.push (← Tactic.Explanation.UncheckedExplanationStep.ofProof
        "Irreducible over ℚ" proof)
    return steps
  let report ← liftTermElabM (evidenceReportMessage steps)
  logReport input {
    domain := renderRealDomain reified.names
    input := reified.render
    inputType := "scalar ℝ"
    output := form.tidy.render
    outputType := "scalar ℝ, factors irreducible over ℚ"
  } #[
    computationNode search
      (factors.toArray.map fun (g, m) ↦ m!"{(polynomialForm x (g.map fun a ↦ (a : ℚ))).render}\
        {if m = 1 then "" else s!", exponent {m} in this product"}"),
    report
  ]

/-- The coefficients (lowest degree first, no trailing zero) of a polynomial in one real
variable with rational coefficients, with its variable; `throwUnsupportedSyntax` otherwise. -/
def univariateInput (reified : ReifiedExpr) : CommandElabM (Name × List ℚ) := do
  let [name] := reified.names | throwUnsupportedSyntax
  let some polynomial := Verified.Expr.Alg.mvPolyOf? (Verified.Expr.simplify reified.expr)
    | throwUnsupportedSyntax
  let some index := (List.finRange reified.names.length).head? | throwUnsupportedSyntax
  let some coefficients := univariateCoefficients polynomial index
    | throwUnsupportedSyntax
  return (name, trimCoefficients coefficients)

/-- `#cas [factor] p` with Hex, for a polynomial in one real variable with rational
coefficients, as the backend of the `#cas` mode `factor`; any other input, or a factor without a
certificate, is left to the factorization of `FullSimplify` (`false`). -/
@[cas_route factor]
def factorBackend : Tactic.RouteRegistry.CommandBackend := fun stx ↦ do
  let `(#cas [factor] $input:term) := stx | return false
  try
    let reified ← try parseInferred input catch _ => throwUnsupportedSyntax
    let (name, coefficients) ← univariateInput reified
    unless 2 ≤ coefficients.length do
      throwUnsupportedSyntax
    let (scalar, primitive) := primitivePart coefficients
    -- Untrusted search: Hex's compiled factorizer.
    let factorization := Hex.ZPoly.factorize (Hex.DensePoly.ofCoeffs primitive.toArray)
    let factors := factorization.factors.toList.map fun (g, m) ↦ (g.coeffs.toList, m)
    logCertifiedFactorization input reified name (scalar * factorization.scalar) factors
      "complete factorization over ℚ (Hex)"
      "Hex factorization (untrusted search; the irreducibility of every factor is certified below)"
    return true
  catch error =>
    match error with
    | .internal id _ =>
        unless id == unsupportedSyntaxExceptionId do throw error
        return false
    | _ => throw error

/-- The monic irreducible factors over `ℚ` of a polynomial `p` (coefficients from the constant term
up) with their exponents, `p = lead p ∏ fᵢ ^ eᵢ`, from Hex's Berlekamp-Zassenhaus factorizer
(`Hex.ZPoly.factorize`, untrusted search) applied to the primitive part of `p`; equal factors are
merged. `[]` for a constant. The factorizer over `ℚ` of the commands and of rational integration
when this module is imported. -/
@[cas_route factor]
def denseFactors : Tactic.RouteRegistry.FactorProvider := fun p ↦
  let p := Algebra.Dense.trim p
  if p.size ≤ 1 then [] else
    let (_, primitive) := primitivePart p.toList
    let factorization := Hex.ZPoly.factorize (Hex.DensePoly.ofCoeffs primitive.toArray)
    factorization.factors.toList.foldl (fun acc (g, m) ↦
      let f := Algebra.Dense.monic (g.coeffs.map fun (a : Int) ↦ (a : ℚ))
      if f.size ≤ 1 then acc
      else if acc.any (·.1 == f) then acc.map fun (h, k) ↦ if h == f then (h, k + m) else (h, k)
      else acc ++ [(f, m)]) []

/-- `#cas [eigenvalues] A` with Hex, as the backend of the `#cas` mode `eigenvalues`: the spectrum
of the core command, with the theorem `Irreducible q` in `ℚ[X]` for each factor `q` of the
characteristic polynomial whose roots are named by enclosures and whose irreducibility Hex
certifies. The report lists the factors without a certificate. -/
@[cas_route eigenvalues]
def eigenvaluesBackend : Tactic.RouteRegistry.CommandBackend := fun stx ↦ do
  let `(#cas [eigenvalues] $A:term) := stx | return false
  LinearAlgebra.logEigen A false A (some irreducibleOverRationals)
  return true

/-- `#cas [eigenvectors] A` with Hex, as the backend of the `#cas` mode `eigenvectors`: the
eigenvectors of the core command, with the theorem `Irreducible q` in `ℚ[X]` (for `q` scaled to
coprime integer coefficients) for each remaining factor `q` of the characteristic polynomial
whose irreducibility Hex certifies. The report lists the factors without a certificate. -/
@[cas_route eigenvectors]
def eigenvectorsBackend : Tactic.RouteRegistry.CommandBackend := fun stx ↦ do
  let `(#cas [eigenvectors] $A:term) := stx | return false
  LinearAlgebra.logEigen A true A (some irreducibleOverRationals)
  return true

end CASHex.Factor
