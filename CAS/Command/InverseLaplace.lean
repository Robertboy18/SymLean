/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Laplace
public import CAS.Command.Algebra.Apart
public import CAS.Command.LinearAlgebra.Basic
public import CAS.Command.Admission
public import CAS.Calculus.InverseLaplace
public import CAS.Command.RootSplit
public meta import CAS.Calculus.LinearODERoots
public meta import CAS.Tactic.RouteRegistry

/-!
# Inverse Laplace transforms: `#cas [inverseLaplace s t] F`

`#cas [inverseLaplace s t] F` (Mathematica's `InverseLaplaceTransform[F, s, t]`) for a proper
rational function `F` of `s` with rational coefficients finds `f`, a sum of terms
`c tⁿ e^(a t) g (t)` with `g` one of `1`, `cos (b t)`, `sin (b t)`, `cosh (b t)`, `sinh (b t)`
(`b = √β` printed as a square root when `β` is not the square of a rational) and of terms
over the roots of factors without closed form, and proves

`∀ s : ℝ, σ < s → IntegrableOn (fun t ↦ exp (-(s t)) f t) (Ioi 0) ∧
  ∫ t in Ioi 0, exp (-(s t)) f t = F s`

with `F s` the input as written (elaborated over `ℝ` with `Real` open). So `f` is an inverse
Laplace transform of `F`: its transform is `F` for `s > σ`. Mathlib v4.35 has no uniqueness
theorem for the Laplace transform (Lerch's theorem), so the theorem does not say that `f` is the
only one (another `f` may differ on a null set, for instance).

`σ` is the largest real zero of the written divisors of `F` and convergence bound of the terms
of `f`: `a` for `s - a` and for `(s - a) ² + β` with `β > 0`, `a + √(-β)` for `β < 0`, and the
upper ends of the enclosures of the real parts of the enclosed roots. All written divisors
count, also factors that cancel, so that every divisor of `F` as written is nonzero for
`s > σ` (with Lean's `x / 0 = 0` the theorem would fail at a cancelled zero above the poles,
as at `s = 2` for `(s - 2) / ((s - 2) (s + 1))`). Of bounds `a + √c` with one value of `a`,
`σ` takes the one with the largest `c`; with several values of `a`, each bound gives a decimal
above it. `σ` is sufficient for the theorem, not claimed optimal.

Refused: improper `F` (a polynomial part gives Dirac deltas and their derivatives), symbolic
parameters, divisors that are quotients by expressions in `s`, the size limits of
`CAS.Command.Admission` (powers over 64, degrees over 32 before simplification),
denominators of degree over 8 (also each written divisor), more than 16 terms, inputs in a section
with `variable`s, and the input limits of `#cas [laplace t s]`. A repeated factor whose roots are
known only by enclosures is refused, and so is such a factor of a written divisor that is not a
product of enclosed factors of the reduced denominator.

## Implementation notes

The search runs in meta code and is not trusted. We factor the denominator as `#cas [apart]`
does: without Hex over the factors written in the input, refined by gcds (`writtenFactors`,
`factorsOver` of `CAS/Command/Algebra/Basic.lean`), with `import CASHex.Factor` completely over
`ℚ` by Hex (`denseFactors` of `CASHex/Factor.lean`), and `Dense.isFactorization` confirms the
result. A quadratic factor `(s - a) ² + β` with `β = 0` or with `-β` the square of a rational
is split into linear factors. A factor of degree three or more goes to `RootSplit.split` of
`CAS/Command/RootSplit.lean`: its rational roots and the parts that the quadratic formula or the
factor provider solves give linear and quadratic factors, and the other parts stay whole. Their
product `R` has roots known only by enclosures, which `RootSplit.encloseDigits` finds
(Durand-Kerner centres refined by exact Newton steps). The coefficients of `f` over the linear
and quadratic factors come from a rational linear solve (`solve`, with `QMatrix.rowReduce` of
`CAS/Command/LinearAlgebra/Basic.lean`) over the basis `tⁿ e^(a t)` for a linear factor and
`tⁿ e^(a t) cos (√β t)`, `tⁿ e^(a t) sin (√β t) / √β` for a quadratic factor (`cosh` and `sinh`
of `√(-β) t` when `β < 0`, the `QuadTerm`s of `CAS/Calculus/InverseLaplace.lean`), `n` below the
multiplicity. For `R`, `enclosedSplit` takes two Bézout identities (`Dense.xgcd`) to write `F`
as `N₁ / D + B / R` and to find `W` and `T` with `W R' = B + T R`. The terms over the roots are
then `W(r) e^(r t)` for the real roots `r` of `R` and `2 Re (W(z) e^(z t))` for its pairs of
complex roots `z, z̄` (`enclosedTerms`), where `W(μ) = B(μ) / R'(μ)` is the classical residue
of `B / R`.

The kernel checks the whole theorem, so a wrong coefficient makes the proof fail, never the
theorem false. For the exact part the proof is `integral_exp_mul_quadSum` of
`CAS/Calculus/InverseLaplace.lean`, which reuses the forward `integral_exp_mul_sum` of
`CAS/Calculus/Laplace.lean`; each transform is a rational function of `s` (`simp`,
`field_simp`, `ring`), each written divisor is a nonzero product of its factors for `s > σ`, and
`field_simp` and `ring1` close the identity of rational functions. With enclosed roots the
kernel also decides three closed Boolean certificates: `Enclosures.check R D` of
`CAS/Calculus/LinearODERoots.lean` (intervals with a sign change, discs that pass the Newton test
`AlgRoot.cCheck` of `CAS/Calculus/AlgebraicRoots.lean`, as many roots as the degree), the
polynomial identity `W R' = B + T R` (`coeffEq`) and `enclosedBelow D σ`. Then `Enclosures.re_lt`
puts the real parts of the roots below `s`, `Enclosures.eval_ne_zero` gives `R(s) ≠ 0`, and
`integral_exp_mul_quadSum_enclosed` gives the transform of all the terms, the enclosed ones by
the partial fractions `Enclosures.partial_fraction`. The roots enter the theorem as the exact
numbers `AlgRoot.real R lo hi` and `AlgRoot.complex R u v ρ` named by their enclosures, so no
floating-point value is used in it. Partial fractions are classical; ours are the certificate
for roots without closed form and the bound `σ` that counts every written divisor.
-/

public meta section

namespace CAS.Command.InverseLaplace

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Command.Laplace
open CAS.Command.Algebra
open CAS.Verified.Expr.Alg

/-- The largest degree of the denominator and of each written divisor. -/
def maxDegree : Nat := 8
/-- The most terms of `f`. -/
def maxTerms : Nat := 16

/-- The largest total degree of the expression `F` as read, and of each of its subexpressions,
before expansion (`Admission.degreeBounds`, numerator and denominator). -/
def maxReadDegree : Nat := 32

/-- `√q` as a rational, when `q ≥ 0` is the square of a rational. -/
def ratSqrt? (q : ℚ) : Option ℚ :=
  if q < 0 then none else
    let n := q.num.natAbs.sqrt
    let d := q.den.sqrt
    if n * n = q.num.natAbs && d * d = q.den then some ((n : ℚ) / d) else none

/-- A factor `s - a` (`β = none`) or `(s - a) ² + β` with `β ≠ 0` and `-β` not a rational
square, with its multiplicity. -/
structure Factor where
  /-- The centre `a`. -/
  a : ℚ
  /-- `β` of a quadratic factor. -/
  β : Option ℚ
  /-- The multiplicity. -/
  mult : Nat
  deriving Inhabited

/-- The monic polynomial of a factor. -/
def Factor.dense (f : Factor) : Dense :=
  match f.β with
  | none => #[-f.a, 1]
  | some β => #[f.a ^ 2 + β, -2 * f.a, 1]

/-- The bound `(a, c)` (`a + √c`) of a factor: `(a, 0)` unless `β < 0`. -/
def Factor.bound (f : Factor) : ℚ × ℚ :=
  match f.β with
  | some β => if β < 0 then (f.a, -β) else (f.a, 0)
  | none => (f.a, 0)

/-- Normalize a monic factor of degree one or two with exponent `e`: linear factors, and a
quadratic `x ² + p x + q = (x - a) ² + β` split when `β = 0` or `-β` is a rational square. -/
def normalize (f : Dense) (e : Nat) : Option (List Factor) :=
  let f := Dense.trim f
  if f.size = 2 then some [⟨-(f.getD 0 0) / f.getD 1 1, none, e⟩]
  else if f.size = 3 then
    let p := f.getD 1 0 / f.getD 2 1
    let q := f.getD 0 0 / f.getD 2 1
    let a := -p / 2
    let β := q - p ^ 2 / 4
    if β = 0 then some [⟨a, none, 2 * e⟩]
    else match ratSqrt? (-β) with
      | some r => some [⟨a - r, none, e⟩, ⟨a + r, none, e⟩]
      | none => some [⟨a, some β, e⟩]
  else none

/-- `(P, Q) = quadPQ u β m` as dense polynomials in `u`. -/
def quadPQDense (β : ℚ) : Nat → Dense × Dense
  | 0 => (#[1], #[])
  | m + 1 =>
    let (P, Q) := quadPQDense β m
    (Dense.sub (Dense.mul P #[0, 1]) (Dense.scale β Q), Dense.add (Dense.mul Q #[0, 1]) P)

/-- A basis function: the factor index, the power `n` and `odd` (`sinQ`); for a linear factor
`odd = false`. -/
structure Basis where
  /-- The factor. -/
  factor : Factor
  /-- The power of `t`. -/
  n : Nat
  /-- `sinQ`. -/
  odd : Bool

/-- The numerator `N` of the transform `N / D` of a basis function, `D` the product of the
factors to their multiplicities. -/
def Basis.numerator (D : Dense) (b : Basis) : Dense :=
  let fac := (b.n.factorial : ℚ)
  match b.factor.β with
  | none =>
      -- `n! / (s - a) ^ (n + 1)`.
      Dense.scale fac (Dense.divMod D (Dense.pow b.factor.dense (b.n + 1))).1
  | some β =>
      -- `P` and `Q` are polynomials in `u = s - a`.
      let (P, Q) := quadPQDense β (b.n + 1)
      let top := Dense.shift (if b.odd then Q else P) (-b.factor.a)
      Dense.scale fac (Dense.mul top (Dense.divMod D (Dense.pow b.factor.dense (b.n + 1))).1)

/-- Solve `Σ xᵦ Nᵦ = N` (a square system, the basis functions of the factorization of `D`). -/
def solve (D N : Dense) (basis : List Basis) : Option (List ℚ) := Id.run do
  let m := D.size - 1
  let cols := basis.map (·.numerator D)
  unless basis.length = m do return none
  let A : CAS.Command.LinearAlgebra.QMatrix :=
    (Array.range m).map fun i ↦ (cols.toArray.map fun c ↦ c.getD i 0)
  let (R, E, pivots) := CAS.Command.LinearAlgebra.QMatrix.rowReduce A
  unless pivots.size = m do return none
  let _ := R
  let x := (Array.range m).map fun i ↦
    (Array.range m).foldl
      (fun acc j ↦ acc + CAS.Command.LinearAlgebra.QMatrix.get E i j * N.getD j 0) 0
  -- Check (untrusted search; the theorem is proved independently).
  let sum := (basis.zip x.toList).foldl
    (fun acc (b, c) ↦ Dense.add acc (Dense.scale c (b.numerator D))) #[]
  unless Dense.trim sum == Dense.trim N do return none
  return some x.toList

/-- `a + √c` as a real term (`a` for `c = 0`). -/
def boundTerm (b : ℚ × ℚ) : TermElabM (TSyntax `term) := do
  if b.2 = 0 then realLit b.1
  else if b.1 = 0 then `(Real.sqrt $(← realLit b.2))
  else `($(← realLit b.1) + Real.sqrt $(← realLit b.2))

/-- `a + √c` as text, with a radicand that is not an integer in parentheses: `√(1/2)`. -/
def boundText (b : ℚ × ℚ) : String :=
  let root := if b.2.den = 1 then s!"√{ratText b.2}" else s!"√({ratText b.2})"
  if b.2 = 0 then ratText b.1 else if b.1 = 0 then root else s!"{ratText b.1} + {root}"

/-- A rational with 8 decimal digits above `a + √c` for `b = (a, c)` with `c > 0`. -/
def boundAbove (b : ℚ × ℚ) : ℚ :=
  let up := ((Nat.sqrt (b.2 * 10 ^ 16).ceil.toNat + 1 : ℕ) : ℚ) / 10 ^ 8
  ((((b.1 + up) * 10 ^ 8).ceil : ℤ) : ℚ) / 10 ^ 8

/-- For coprime `D` and squarefree `R`, and `N` of degree below `deg D + deg R`: `N₁`, `B`, `W`
and `T` with `N = N₁ R + B D` (from `U D + V R = 1` and `B = N U mod R`) and `W R' = B + T R`
(from `U' R' + V' R = 1` and `W = B U' mod R`); `none` when a gcd is not `1` or a division is
not exact. -/
def enclosedSplit (N D R : Dense) : Option (Dense × Dense × Dense × Dense) := do
  let (g₀, U, _) := Dense.xgcd D R
  unless Dense.trim g₀ == #[1] do none
  let B := (Dense.divMod (Dense.mul N U) R).2
  let (N₁, r₁) := Dense.divMod (Dense.sub N (Dense.mul B D)) R
  unless Dense.isZero r₁ do none
  let R' := Dense.derivative R
  let (g₁, U', _) := Dense.xgcd R' R
  unless Dense.trim g₁ == #[1] do none
  let W := (Dense.divMod (Dense.mul B U') R).2
  let (T, r₂) := Dense.divMod (Dense.sub (Dense.mul W R') B) R
  unless Dense.isZero r₂ do none
  return (N₁, B, W, T)

/-- Whether `a + √c ≤ a' + √c'` (exact for the cases used: one side rational, or the same
`a`). -/
def boundLe (b b' : ℚ × ℚ) : Bool :=
  if b.2 = 0 && b'.2 = 0 then b.1 ≤ b'.1
  else if b.2 = 0 then b.1 - b'.1 ≤ 0 || (b.1 - b'.1) ^ 2 ≤ b'.2
  else if b'.2 = 0 then 0 ≤ b'.1 - b.1 && b.2 ≤ (b'.1 - b.1) ^ 2
  else b.1 == b'.1 && b.2 ≤ b'.2

/-- A proof term of `bound ≤ σ` for bounds with `boundLe`. -/
def boundLeProof (b σ : ℚ × ℚ) : TermElabM (TSyntax `term) := do
  if b.2 = 0 && σ.2 = 0 then `(by norm_num)
  else if b.2 = 0 then
    let hOr ← if b.1 - σ.1 ≤ 0 then `(Or.inl (by norm_num))
      else `(Or.inr ⟨by norm_num, by norm_num⟩)
    `(by
      have h := CAS.Calculus.Laplace.le_add_sqrt (x := $(← realLit b.1))
        (a := $(← realLit σ.1)) (c := $(← realLit σ.2)) $hOr
      linarith)
  else if σ.2 = 0 then
    `(by
      have h := CAS.Calculus.Laplace.add_sqrt_le (y := $(← realLit σ.1))
        (a := $(← realLit b.1)) (c := $(← realLit b.2)) (by norm_num) (by norm_num)
      linarith)
  else if b == σ then `(le_refl _)
  else
    `(by
      have h := Real.sqrt_le_sqrt (show ($(← realLit b.2) : ℝ) ≤ $(← realLit σ.2) by norm_num)
      linarith)

/-- The time function of a basis term with coefficient `c`, as syntax, and whether it is
subtracted. -/
def termSyntax (t : TSyntax `term) (b : Basis) (c : ℚ) : TermElabM (TSyntax `term × Bool) := do
  let mut factors : Array (TSyntax `term) := #[]
  let mut coeff := c
  if b.n > 0 then factors := factors.push (← powSyntax t b.n)
  if b.factor.a ≠ 0 then
    let rate ← if b.factor.a = 1 then pure t else if b.factor.a = -1 then `(-$t)
      else `($(← realLit b.factor.a) * $t)
    factors := factors.push (← `(Real.exp $rate))
  match b.factor.β with
  | none => pure ()
  | some β =>
      if 0 < β then
        match ratSqrt? β with
        | some r =>
            let arg ← if r = 1 then pure t else `($(← realLit r) * $t)
            if b.odd then
              coeff := coeff / r
              factors := factors.push (← `(Real.sin $arg))
            else factors := factors.push (← `(Real.cos $arg))
        | none =>
            let sq ← `(Real.sqrt $(← realLit β))
            if b.odd then factors := factors.push (← `(Real.sin ($sq * $t) / $sq))
            else factors := factors.push (← `(Real.cos ($sq * $t)))
      else
        let sq ← `(Real.sqrt $(← realLit (-β)))
        if b.odd then factors := factors.push (← `(Real.sinh ($sq * $t) / $sq))
        else factors := factors.push (← `(Real.cosh ($sq * $t)))
  let body? ← factors.foldlM (fun (acc : Option (TSyntax `term)) f ↦ do
    match acc with
    | none => pure (some f)
    | some a => some <$> `($a * $f)) none
  let mag := |coeff|
  let out ← match body? with
    | none => realLit mag
    | some body => if mag = 1 then pure body else `($(← realLit mag) * $body)
  return (out, coeff < 0)

/-- Run `#cas [inverseLaplace s t] F`, with the factorization `factorize?` when it is given
(`CASHex` passes Hex's). -/
def logInverseLaplace (ref : Syntax) (s t : TSyntax `ident) (input : TSyntax `term)
    (factorize? : Option (Dense → List (Dense × Nat)) := none) : CommandElabM Unit := do
  let shape := "inverseLaplace: expected a proper rational function of s with rational \
    coefficients (parameters are not supported)"
  if t.getId == s.getId then
    throwErrorAt t "inverseLaplace: the variables s and t must be different"
  unless (← getScope).varDecls.isEmpty do
    throwErrorAt input "inverseLaplace is not supported in a section with `variable`s"
  if hasTanh input then throwErrorAt input "inverseLaplace: tanh is not supported"
  if hasLongAtom input then
    throwErrorAt input "inverseLaplace: a literal has more than {maxLiteral} characters"
  if hasLargeDecimal input then
    throwErrorAt input "inverseLaplace: a decimal literal has a power of ten over {maxExponent}"
  if inputSize input > maxSize then
    throwErrorAt input "inverseLaplace: the input is too large"
  let reified ← try parseExact input [s.getId] catch _ => throwErrorAt input shape
  -- Before any expansion: powers, degrees and constants of the expression as read.
  Admission.checkExpr "inverseLaplace" input maxReadDegree reified.expr
  let rational ← match rationalOfExpr reified.expr with
    | .ok r => pure r
    | .error _ => throwErrorAt input shape
  unless reified.names.length = 1 do throwErrorAt input shape
  -- A divisor that is itself a quotient would need a conditional cancellation.
  if rational.divisors.any (fun (d, _) ↦ Admission.hasQuotient d) then
    throwErrorAt input "inverseLaplace: a divisor is itself a quotient; write F with polynomial \
      divisors"
  let toOne (p : MvPoly reified.names.length) : MvPoly 1 :=
    if h1 : reified.names.length = 1 then h1 ▸ p else []
  let num := toDense (toOne rational.value.num)
  let den := toDense (toOne rational.value.den)
  if [num, den].any fun p ↦ p.any fun c ↦ (capped c).isNone then
    throwErrorAt input "inverseLaplace: a coefficient has more than {maxBits} bits"
  if Dense.degree den > maxDegree then
    throwErrorAt input "inverseLaplace accepts denominators of degree at most {maxDegree}"
  unless Dense.isZero num || Dense.degree num < Dense.degree den do
    throwErrorAt input "inverseLaplace: F is not proper; its polynomial part (Dirac deltas and \
      their derivatives) is not supported"
  let gText (g : Dense) : String := polyText (fun _ ↦ toString s.getId) (ofDense (0 : Fin 1) g)
  -- Without a factor provider, a factor of degree four or more, or one whose rational roots the
  -- search may have missed, may still factor over `ℚ`.
  let hint (g : Dense) : String :=
    if factorize?.isNone && (Dense.degree g ≥ 4 || !(Dense.rationalRoots g.toList).2.2) then
      "; it may factor over ℚ: CASHex (`lake -R -Khex=on build CASHex`, \
        `import CASHex.Factor`) factors it completely"
    else ""
  -- The linear and quadratic factors of `d`, and the factors whose roots are only enclosed.
  let factorOf (d : Dense) (written : List (MvPoly 1)) :
      CommandElabM (List Factor × List (Dense × Nat)) := do
    let fs := match factorize? with
      | some fz => fz d
      | none => factorsOver written d
    unless Dense.isFactorization d fs || (Dense.trim d).size ≤ 1 do
      throwErrorAt input "inverseLaplace: no factorization of a denominator into monic, \
        pairwise coprime factors; nothing is claimed"
    let mut out : List Factor := []
    let mut enclosed : List (Dense × Nat) := []
    for (f, e) in fs do
      match normalize f e with
      | some l => out := out ++ l
      | none =>
          -- The root splitter: exact linear and quadratic factors, and parts left enclosed.
          let sp := RootSplit.split factorize? f
          for (ρ, k) in sp.exact do
            let q : Dense := match ρ with
              | .real r => #[-r, 1]
              | .realPair α γ m => #[α ^ 2 - γ ^ 2 * m, -2 * α, 1]
              | .pair α γ m => #[α ^ 2 + γ ^ 2 * m, -2 * α, 1]
            out := out ++ (normalize q (k * e)).getD []
          enclosed := enclosed ++ sp.enclosed.map fun (g, k) ↦ (g, k * e)
    return (out, enclosed)
  let written := rational.divisors.toList.flatMap fun (d, _) ↦ (writtenFactors d).map toOne
  -- The factorization of the reduced denominator, for `f`.
  let (factors, encF) ← factorOf den written
  if let some (g, _) := encF.find? (·.2 > 1) then
    throwErrorAt input "inverseLaplace: the factor {gText g} is repeated and its roots are known \
      only by enclosures, which is not supported{hint g}"
  -- The product of the enclosed factors, squarefree.
  let R : Dense := encF.foldl (fun acc (g, _) ↦ Dense.mul acc g) #[1]
  -- The written divisors and their factorizations, for `σ` and their nonvanishing; an enclosed
  -- factor of a divisor is written as a product of enclosed factors of the denominator.
  let mut divisorFactors : Array (Verified.Expr (Fin reified.names.length) × ℚ × List Factor ×
      List (Dense × Nat)) := #[]
  for (d, dp) in rational.divisors do
    let dd := toDense (toOne dp)
    if Dense.degree dd > maxDegree then
      throwErrorAt input "inverseLaplace accepts written divisors of degree at most {maxDegree}"
    let (fs, encs) ← factorOf dd ((writtenFactors d).map toOne)
    let mut parts : List (Dense × Nat) := []
    for (g, k) in encs do
      let own := encF.filter fun (h, _) ↦ Dense.isZero (Dense.divMod g h).2
      let ownProduct := own.foldl (fun acc (h, _) ↦ Dense.mul acc h) #[1]
      unless Dense.monic ownProduct == Dense.monic g do
        throwErrorAt input "inverseLaplace: the factor {gText g} of a written divisor has roots \
          known only by enclosures and is not a product of enclosed factors of the reduced \
          denominator, which is not supported{hint g}"
      parts := parts ++ own.map fun (h, _) ↦ (h, k)
    divisorFactors := divisorFactors.push (d, Dense.lead dd, fs, parts)
  -- The basis and the coefficients.
  let D := factors.foldl (fun acc (f : Factor) ↦ Dense.mul acc (Dense.pow f.dense f.mult)) #[1]
  let N := Dense.scale (1 / Dense.lead den) num
  -- With enclosed factors, `N / (D R) = N₁ / D + B / R` and `W R' = B + T R`.
  let split? : Option (Dense × Dense × Dense × Dense) :=
    if encF.isEmpty then some (N, #[], #[], #[]) else enclosedSplit N D R
  let some (N₁, B, W, T) := split?
    | throwErrorAt input "inverseLaplace: the partial fraction system has no solution"
  let basis : List Basis := factors.flatMap fun (f : Factor) ↦
    match f.β with
    | none => (List.range f.mult).map fun n ↦ ⟨f, n, false⟩
    | some _ => (List.range f.mult).flatMap fun n ↦ [⟨f, n, false⟩, ⟨f, n, true⟩]
  let coefficients ← if Dense.isZero N₁ then pure (basis.map fun _ ↦ 0) else
    match solve D N₁ basis with
    | some x => pure x
    | none => throwErrorAt input "inverseLaplace: the partial fraction system has no solution"
  -- The enclosures of the roots of `R`.
  let encD : CAS.LinearODE.Enclosures ← if encF.isEmpty then pure ⟨[], []⟩ else
    match RootSplit.encloseDigits R (toString s.getId) with
    | .ok (E, _) => pure E
    | .error e => throwErrorAt input "inverseLaplace: {e}"
  let terms := (basis.zip coefficients).filter (·.2 ≠ 0)
  if terms.length + encD.reals.length + 2 * encD.discs.length > maxTerms then
    throwErrorAt input "inverseLaplace accepts at most {maxTerms} terms"
  if terms.any (fun (_, c) ↦ (capped c).isNone) ||
      [W, B, T, R].any (fun p ↦ p.any fun c ↦ (capped c).isNone) then
    throwErrorAt input "inverseLaplace: a coefficient has more than {maxBits} bits"
  -- `σ`: of bounds `a + √c` with one `a`, the largest `c`; with several values of `a`, each
  -- gives a decimal above it. The enclosures give the upper ends of the real parts of the roots.
  let bounds : List (ℚ × ℚ) := (terms.map (·.1.factor.bound)) ++
    (divisorFactors.toList.flatMap fun (_, _, fs, _) ↦ fs.map (·.bound))
  let maxOf (l : List ℚ) : Option ℚ :=
    l.foldl (fun m b ↦ some ((m.map (max · b)).getD b)) none
  let irrational := (bounds.filter (·.2 ≠ 0)).eraseDups
  let sameCentre := irrational.all (·.1 == (irrational.headD (0, 0)).1)
  let irrationalMax : Option (ℚ × ℚ) := if sameCentre then
      irrational.foldl (fun m b ↦ some ((m.map fun x ↦ if x.2 < b.2 then b else x).getD b))
        none
    else none
  let decimalBound : Option ℚ := if sameCentre then none
    else maxOf (irrational.map boundAbove)
  let encBound := maxOf (encD.reals.map (·.2) ++ encD.discs.map fun d ↦ d.1 + d.2.2.1)
  let rationalMax := maxOf ((bounds.filter (·.2 = 0)).map (·.1) ++ decimalBound.toList ++
    encBound.toList)
  let σ : ℚ × ℚ := match rationalMax, irrationalMax with
    | some r, some b => if boundLe (r, 0) b then b else (r, 0)
    | none, some b => b
    | some r, none => (r, 0)
    | none, none => (0, 0)
  -- A decimal `σ` from an enclosure or above a square root is printed as a decimal.
  let σDecimal := σ.2 == 0 && σ.1.den != 1 && (RootSplit.decimalDigits? σ.1).isSome &&
    (encBound == some σ.1 || decimalBound == some σ.1)
  let sT : TSyntax `term := ⟨s.raw⟩
  let tT : TSyntax `term := ⟨t.raw⟩
  let names := variableIdents reified.names
  let vars := variableTerms reified
  let (proposition, proof, fPP) ← liftTermElabM do
    let σT ← boundTerm σ
    -- The terms as `QuadTerm` literals, the time function and the per-term transforms.
    let mut lits : Array (TSyntax `term) := #[]
    let mut adm : Array (TSyntax `term) := #[]
    let mut fSum : Option (TSyntax `term) := none
    let mut nonzero : TSyntax `tactic ← `(tactic| skip)
    -- Every factor (of the reduced denominator and of the written divisors) is nonzero for
    -- `s > σ`: `hfᵢ : fᵢ ≠ 0`.
    let mut allFactors : List Factor := []
    for f in factors ++ divisorFactors.toList.flatMap (·.2.2.1) do
      unless allFactors.any (fun g ↦ g.a == f.a && g.β == f.β) do
        allFactors := allFactors ++ [f]
    let mut generalizations : TSyntax `tactic ← `(tactic| skip)
    let mut substitutions : Array (TSyntax `ident) := #[]
    let mut idx := 0
    for f in allFactors do
      idx := idx + 1
      let h := mkIdent (Name.mkSimple s!"hf{idx}")
      let fT ← polyTerm (fun _ ↦ sT) (ofDense (0 : Fin 1) f.dense)
      let le ← boundLeProof f.bound σ
      let fact ← match f.β with
        | none => `(tactic| have $h:ident : ($fT : ℝ) ≠ 0 := by
            have hle : ($(← boundTerm f.bound) : ℝ) ≤ $σT := $le
            intro h0; linarith)
        | some β =>
            if 0 < β then
              `(tactic| have $h:ident : ($fT : ℝ) ≠ 0 := by
                have := sq_nonneg ($sT - $(← realLit f.a))
                intro h0; nlinarith)
            else
              `(tactic| have $h:ident : ($fT : ℝ) ≠ 0 := by
                have hle : ($(← boundTerm f.bound) : ℝ) ≤ $σT := $le
                have hp := CAS.Calculus.Laplace.sub_sq_sub_pos (s := $sT)
                  (a := $(← realLit f.a)) (c := $(← realLit (-β)))
                  (by simpa using lt_of_le_of_lt hle hs)
                intro h0; nlinarith)
      nonzero ← `(tactic| ($nonzero; $fact))
      -- As in `#cas [apart]` (`rationalIdentityScript`): every factor that is not the variable
      -- becomes an atom for `field_simp`, which would otherwise normalize it and miss `hfᵢ`.
      unless f.β.isNone && f.a = 0 do
        let u := mkIdent (Name.mkSimple s!"u{idx}")
        let e := mkIdent (Name.mkSimple s!"e{idx}")
        let g ← `(tactic| generalize $e:ident : ($fT : ℝ) = $u:ident at $h:ident ⊢)
        generalizations ← `(tactic| ($generalizations; $g))
        substitutions := substitutions.push e
    -- The written divisors of `F` as products of the factors, the enclosed ones included.
    let mut rewrites : TSyntax `tactic ← `(tactic| skip)
    for (d, lead, fs, encs) in divisorFactors do
      let dT ← exprTerm vars d
      let mut product? : Option (TSyntax `term) := none
      for f in fs do
        let fT ← polyTerm (fun _ ↦ sT) (ofDense (0 : Fin 1) f.dense)
        let pw ← `(($fT : ℝ) ^ $(natTerm f.mult))
        product? := some (← match product? with
          | none => pure pw
          | some p => `($p * $pw))
      for (g, k) in encs do
        let gT ← polyTerm (fun _ ↦ sT) (ofDense (0 : Fin 1) g)
        let pw ← `(($gT : ℝ) ^ $(natTerm k))
        product? := some (← match product? with
          | none => pure pw
          | some p => `($p * $pw))
      let some product := product? | continue
      let r ← `(tactic| try rw [show ($dT : ℝ) = $(← realLit lead) * $product by ring1])
      rewrites ← `(tactic| ($rewrites; $r))
    -- The terms.
    let mut dens : TSyntax `tactic ← `(tactic| skip)
    let mut unify : TSyntax `tactic ← `(tactic| skip)
    let mut sqrts : TSyntax `tactic ← `(tactic| skip)
    let mut seenDen : List (ℚ × ℚ) := []
    let mut seenSq : List ℚ := []
    for (b, c) in terms do
      let nT : TSyntax `term := ⟨Syntax.mkNumLit (toString b.n)⟩
      let β := b.factor.β.getD 0
      let aT ← realLit b.factor.a
      let βT ← realLit β
      let oddT ← if b.odd then `(true) else `(false)
      let lit ← `((⟨$(← realLit c), $nT, $aT, $βT, $oddT⟩ : CAS.Calculus.Laplace.QuadTerm))
      lits := lits.push lit
      let le ← boundLeProof b.factor.bound σ
      let boundT ← boundTerm b.factor.bound
      let boundEq ← if β < 0 then `(CAS.Calculus.Laplace.QuadTerm.bound_eq_add_sqrt _)
        else `(CAS.Calculus.Laplace.QuadTerm.bound_of_nonneg _ (by norm_num))
      adm := adm.push (← `((by
          have hle : ($boundT : ℝ) ≤ $σT := $le
          have hb : ($lit).bound ≤ $boundT := by
            rw [$boundEq:term]
            try norm_num
          exact lt_of_le_of_lt (hb.trans hle) hs)))
      let (ft, neg) ← termSyntax tT b c
      fSum := some (← match fSum with
        | none => if neg then `(-$ft) else pure ft
        | some acc => if neg then `($acc - $ft) else `($acc + $ft))
      -- `√β = r` for a rational square `β`, used to print `cos (r t)`.
      if 0 < β then
        if let some r := ratSqrt? β then
          unless seenSq.contains β do
            seenSq := seenSq ++ [β]
            let hs := mkIdent (Name.mkSimple s!"hsq{seenSq.length}")
            let rT ← realLit r
            let fact ← `(tactic| have $hs:ident : Real.sqrt $βT = $rT := by
                rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
                norm_num)
            sqrts ← `(tactic| ($sqrts; $fact; try simp only [$hs:ident]))
      -- The denominator `(s - a) ^ 2 + β` of the transform is nonzero, in the form it has in
      -- `QuadTerm.transform` of the literal.
      unless seenDen.contains (b.factor.a, β) do
        seenDen := seenDen ++ [(b.factor.a, β)]
        let h := mkIdent (Name.mkSimple s!"hq{seenDen.length}")
        let fact ← if β = 0 then
            `(tactic| have $h:ident : (($sT - $aT) ^ 2 + $βT : ℝ) ≠ 0 := by
              have hle : ($aT : ℝ) ≤ $σT := $le
              have h0 : ($sT - $aT : ℝ) ≠ 0 := by intro h0; linarith
              rw [add_zero]
              exact pow_ne_zero 2 h0)
          else if 0 < β then
            `(tactic| have $h:ident : (($sT - $aT) ^ 2 + $βT : ℝ) ≠ 0 := ne_of_gt (by positivity))
          else
            `(tactic| have $h:ident : (($sT - $aT) ^ 2 + $βT : ℝ) ≠ 0 := by
              have hle : ($boundT : ℝ) ≤ $σT := $le
              have hp := CAS.Calculus.Laplace.sub_sq_sub_pos (s := $sT) (a := $aT)
                (c := $(← realLit (-β))) (by simpa using lt_of_le_of_lt hle hs)
              intro h0
              linarith)
        dens ← `(tactic| ($dens; $fact))
        -- Write the denominator as the factor (`(s - a) ^ 2 + 0` as `(s - a) ^ 2`), as in the
        -- nonzero facts `hfᵢ`.
        let fT ← polyTerm (fun _ ↦ sT) (ofDense (0 : Fin 1) b.factor.dense)
        let target ← if b.factor.β.isNone then `((($fT : ℝ)) ^ 2) else `(($fT : ℝ))
        unify ← `(tactic| ($unify; try rw [show (($sT - $aT) ^ 2 + $βT : ℝ) = $target by ring]))
    -- The terms over the enclosed roots of `R`, with the facts that evaluate `W` at them.
    let realTy ← `(ℝ)
    let complexTy ← `(ℂ)
    let listQ (p : Dense) : TermElabM (TSyntax `term) := do
      `(($(← RootSplit.listSyntax (← p.mapM fun q ↦ RootSplit.ratQ q)) : List ℚ))
    let RT ← listQ R
    let BT ← listQ B
    let WT ← listQ W
    let TT ← listQ T
    let reals ← encD.reals.toArray.mapM fun (lo, hi) ↦ do
      `(($(← RootSplit.boundQ lo), $(← RootSplit.boundQ hi)))
    let discs ← encD.discs.toArray.mapM fun (u, v, ρ, κ, Rb, L) ↦ do
      `(($(← RootSplit.boundQ u), $(← RootSplit.boundQ v), $(← RootSplit.boundQ ρ),
        $(← RootSplit.ratQ κ), $(← RootSplit.ratQ Rb), $(← RootSplit.ratQ L)))
    let realsT ← RootSplit.listSyntax reals
    let discsT ← RootSplit.listSyntax discs
    let DT ← `((⟨$realsT, $discsT⟩ : CAS.LinearODE.Enclosures))
    let mut fAll := fSum
    let mut fR? : Option (TSyntax `term) := none
    let mut rootFacts : TSyntax `tactic ← `(tactic| skip)
    let mut rootLemmas : Array (TSyntax `term) := #[]
    let mut rootIdx := 0
    for (lo, hi) in encD.reals do
      rootIdx := rootIdx + 1
      let rT ← `(CAS.AlgRoot.real $RT $(← RootSplit.boundQ lo) $(← RootSplit.boundQ hi))
      let wr ← RootSplit.polySyntax W.toList rT realTy
      let h := mkIdent (Name.mkSimple s!"hr{rootIdx}")
      let fact ← `(tactic| have $h:ident : CAS.Polynomial.coeffEval $WT $rT = $wr := by
          simp only [CAS.Polynomial.coeffEval_cons, CAS.Polynomial.coeffEval_nil] <;>
            push_cast <;> try ring1)
      rootFacts ← `(tactic| ($rootFacts; $fact))
      rootLemmas := rootLemmas.push ⟨h.raw⟩
      let term ← `($wr * Real.exp ($rT * $tT))
      fAll := some (← match fAll with
        | none => pure term
        | some acc => `($acc + $term))
      fR? := some (← match fR? with
        | none => pure term
        | some acc => `($acc + $term))
    rootIdx := 0
    for (u, v, ρ, _) in encD.discs do
      rootIdx := rootIdx + 1
      let zT ← `(CAS.AlgRoot.complex $RT $(← RootSplit.boundQ u) $(← RootSplit.boundQ v)
        $(← RootSplit.boundQ ρ))
      let wz ← RootSplit.polySyntax (W.map (2 * ·)).toList zT complexTy
      let h := mkIdent (Name.mkSimple s!"hw{rootIdx}")
      let fact ← `(tactic| have $h:ident :
            (2 : ℂ) * (CAS.AlgRoot.polyC $WT).eval $zT = $wz := by
          simp only [CAS.AlgRoot.polyC_cons, CAS.AlgRoot.polyC_nil, _root_.Polynomial.eval_add,
            _root_.Polynomial.eval_mul, _root_.Polynomial.eval_C, _root_.Polynomial.eval_X,
            _root_.Polynomial.eval_zero] <;>
            push_cast <;> try ring1)
      rootFacts ← `(tactic| ($rootFacts; $fact))
      rootLemmas := rootLemmas.push ⟨h.raw⟩
      let cosT ← `(Complex.re ($wz) * (Real.exp (Complex.re ($zT) * $tT) *
        Real.cos (Complex.im ($zT) * $tT)))
      let sinT ← `(Complex.im ($wz) * (Real.exp (Complex.re ($zT) * $tT) *
        Real.sin (Complex.im ($zT) * $tT)))
      fAll := some (← match fAll with
        | none => `($cosT - $sinT)
        | some acc => `($acc + $cosT - $sinT))
      fR? := some (← match fR? with
        | none => `($cosT - $sinT)
        | some acc => `($acc + $cosT - $sinT))
    let f ← match fAll with
      | some f => pure f
      | none => `((0 : ℝ))
    let fR ← match fR? with
      | some r => pure r
      | none => `((0 : ℝ))
    let mut admProof ← `((by simp : ∀ T ∈ ([] : List CAS.Calculus.Laplace.QuadTerm),
      T.bound < $sT))
    for a in adm.reverse do
      admProof ← `(List.forall_mem_cons.2 ⟨$a, $admProof⟩)
    let FT ← `(open Real in ($input : ℝ))
    let statement ← `(∀ $s:ident : ℝ, $σT < $sT →
      MeasureTheory.IntegrableOn (fun $t:ident : ℝ ↦ Real.exp (-($sT * $tT)) * $f) (Set.Ioi 0) ∧
      ∫ $t:ident in Set.Ioi 0, Real.exp (-($sT * $tT)) * $f = $FT)
    let _ := names
    let Fr ← exprTerm vars reified.expr
    let substT ← if substitutions.isEmpty then `(tactic| skip)
      else `(tactic| subst $substitutions*)
    let exactScript ← `(tactic| (
      intro $s:ident hs
      have key := CAS.Calculus.Laplace.integral_exp_mul_quadSum [$lits,*] (s := $sT) $admProof
      have hf : (fun $t:ident : ℝ ↦ Real.exp (-($sT * $tT)) * $f) = fun $t:ident ↦
          Real.exp (-($sT * $tT)) * (([$lits,*] : List CAS.Calculus.Laplace.QuadTerm).map
            fun T ↦ T.toLaplace.eval $tT).sum := by
        funext $t:ident
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          CAS.Calculus.Laplace.QuadTerm.toLaplace, CAS.Calculus.Laplace.LaplaceTerm.eval_def]
        norm_num
        all_goals ($sqrts:tactic; try ring_nf)
      rw [hf]
      refine ⟨key.1, key.2.trans ?_⟩
      $dens:tactic
      $nonzero:tactic
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        CAS.Calculus.Laplace.QuadTerm.transform, CAS.Calculus.Laplace.quadPQ, Bool.false_eq_true,
        ↓reduceIte]
      $unify:tactic
      rw [show (open Real in ($input : ℝ)) = ($Fr : ℝ) by first | rfl | ring | norm_num]
      $rewrites:tactic
      $generalizations:tactic
      field_simp
      $substT:tactic
      ring1))
    let script ← if encF.isEmpty then pure exactScript else do
      let eBound := encBound.getD 0
      let σencQ ← RootSplit.ratQ eBound
      let encBoundT ← realLit eBound
      let leEnc ← boundLeProof (eBound, 0) σ
      let hD ← RootSplit.certified (← `(CAS.LinearODE.Enclosures.check $RT $DT = true))
      let hW ← RootSplit.certified (← `(CAS.Polynomial.coeffEq
        (CAS.Polynomial.coeffMul $WT (CAS.Polynomial.coeffDeriv $RT))
        (CAS.Polynomial.coeffAdd $BT (CAS.Polynomial.coeffMul $TT $RT)) = true))
      let hσ ← RootSplit.certified
        (← `(CAS.Calculus.Laplace.enclosedBelow $DT $σencQ = true))
      let rootSimpArgs : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
        rootLemmas.mapM fun l ↦ `(Lean.Parser.Tactic.simpLemma| $l:term)
      let rootArgs : Syntax.TSepArray [``Lean.Parser.Tactic.simpStar,
          ``Lean.Parser.Tactic.simpErase, ``Lean.Parser.Tactic.simpLemma] "," :=
        .ofElems (rootSimpArgs.map fun l ↦ ⟨l.raw⟩)
      -- The exact terms in the form of `integral_exp_mul_quadSum_enclosed`.
      let exactPart ← match fSum with
        | some fExact => `(tactic| (
            have hE : ($fExact : ℝ) = (([$lits,*] : List CAS.Calculus.Laplace.QuadTerm).map
                fun T ↦ T.toLaplace.eval $tT).sum := by
              simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                CAS.Calculus.Laplace.QuadTerm.toLaplace,
                CAS.Calculus.Laplace.LaplaceTerm.eval_def]
              norm_num
              all_goals ($sqrts:tactic; try ring_nf)
            rw [← hE]))
        | none => `(tactic| rw [List.map_nil, List.sum_nil])
      -- `R` as the product of its factors, each nonzero for `s > σ`; the factors become atoms
      -- for `field_simp`, those with more terms first.
      let mut Rprod? : Option (TSyntax `term) := none
      for (g, _) in encF do
        let gT ← polyTerm (fun _ ↦ sT) (ofDense (0 : Fin 1) g)
        Rprod? := some (← match Rprod? with
          | none => `(($gT : ℝ))
          | some p => `($p * ($gT : ℝ)))
      let Rprod ← match Rprod? with
        | some p => pure p
        | none => `((1 : ℝ))
      let Bpoly ← RootSplit.polySyntax B.toList sT realTy
      let mut hgFacts : TSyntax `tactic ← `(tactic| skip)
      let mut encGens : TSyntax `tactic ← `(tactic| skip)
      let mut encSubst : Array (TSyntax `ident) := #[]
      let mut j := 0
      let ordered := encF.mergeSort fun a b ↦
        (a.1.filter (· ≠ 0)).size ≥ (b.1.filter (· ≠ 0)).size
      for (g, _) in ordered do
        j := j + 1
        let gT ← polyTerm (fun _ ↦ sT) (ofDense (0 : Fin 1) g)
        let h := mkIdent (Name.mkSimple s!"hg{j}")
        let u := mkIdent (Name.mkSimple s!"ug{j}")
        let e := mkIdent (Name.mkSimple s!"eg{j}")
        let fact ← `(tactic| have $h:ident : ($gT : ℝ) ≠ 0 := by
            intro h0
            apply hR
            rw [hRprod, h0]
            try ring1)
        hgFacts ← `(tactic| ($hgFacts; $fact))
        let gen ← `(tactic| generalize $e:ident : ($gT : ℝ) = $u:ident at $h:ident ⊢)
        encGens ← `(tactic| ($encGens; $gen))
        encSubst := encSubst.push e
      let allSubst := encSubst ++ substitutions
      let substAll ← if allSubst.isEmpty then `(tactic| skip)
        else `(tactic| subst $allSubst*)
      `(tactic| (
        intro $s:ident hs
        have hle : (($σencQ : ℚ) : ℝ) ≤ $σT := by
          have h1 : ($encBoundT : ℝ) ≤ $σT := $leEnc
          have h2 : (($σencQ : ℚ) : ℝ) = $encBoundT := by norm_num
          exact h2.trans_le h1
        have hroots := CAS.Calculus.Laplace.Enclosures.re_lt $RT $DT $hD $hσ
          (lt_of_le_of_lt hle hs)
        have key := CAS.Calculus.Laplace.integral_exp_mul_quadSum_enclosed [$lits,*] $RT $DT
          $hD $BT $WT $TT (by decide) $hW (s := $sT) $admProof hroots
        $rootFacts:tactic
        have hfR : ∀ $t:ident : ℝ, ((CAS.Calculus.Laplace.enclosedTerms $RT $DT $WT).map
            fun T ↦ T.eval $tT).sum = $fR := by
          intro $t:ident
          simp only [CAS.Calculus.Laplace.enclosedTerms, List.map_cons, List.map_nil,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
            List.nil_append, List.sum_cons, List.sum_nil,
            CAS.Calculus.Laplace.LaplaceTerm.eval_def, add_zero, pow_zero, one_mul]
          simp only [$rootArgs,*]
          all_goals ring1
        have hf : (fun $t:ident : ℝ ↦ Real.exp (-($sT * $tT)) * $f) = fun $t:ident ↦
            Real.exp (-($sT * $tT)) * ((([$lits,*] : List CAS.Calculus.Laplace.QuadTerm).map
              fun T ↦ T.toLaplace.eval $tT).sum +
              ((CAS.Calculus.Laplace.enclosedTerms $RT $DT $WT).map
                fun T ↦ T.eval $tT).sum) := by
          funext $t:ident
          rw [hfR $tT]
          $exactPart:tactic
          all_goals ring1
        rw [hf]
        refine ⟨key.1, key.2.trans ?_⟩
        $dens:tactic
        $nonzero:tactic
        have hR := CAS.Calculus.Laplace.Enclosures.eval_ne_zero $RT $DT $hD hroots
        have hRprod : CAS.Polynomial.coeffEval $RT $sT = $Rprod := by
          simp only [CAS.Polynomial.coeffEval_cons, CAS.Polynomial.coeffEval_nil] <;>
            push_cast <;> try ring1
        have hBpoly : CAS.Polynomial.coeffEval $BT $sT = $Bpoly := by
          simp only [CAS.Polynomial.coeffEval_cons, CAS.Polynomial.coeffEval_nil] <;>
            push_cast <;> try ring1
        $hgFacts:tactic
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          CAS.Calculus.Laplace.QuadTerm.transform, CAS.Calculus.Laplace.quadPQ,
          Bool.false_eq_true, ↓reduceIte]
        rw [hRprod, hBpoly]
        $unify:tactic
        rw [show (open Real in ($input : ℝ)) = ($Fr : ℝ) by first | rfl | ring | norm_num]
        $rewrites:tactic
        $encGens:tactic
        $generalizations:tactic
        field_simp
        all_goals ($substAll:tactic; ring1)))
    let (p, q) ← proveStatement "inverseLaplace" statement script
    -- The printed `f`: the integrand of the elaborated statement, with the roots named.
    let fpp ← forallTelescope p fun _ body ↦ do
      match body.getAppFnArgs with
      | (``And, #[integ, _]) =>
          let args := integ.getAppArgs
          if integ.isAppOf ``MeasureTheory.IntegrableOn && args.size ≥ 3 then
            lambdaTelescope args[args.size - 3]! fun _ b ↦ do
              match b.getAppFnArgs with
              | (``HMul.hMul, #[_, _, _, _, _, ft]) =>
                  if encF.isEmpty then return ← renderTerm ft
                  let named ← RootSplit.letRoots ft
                  lambdaLetTelescope named fun _ b' ↦ renderTerm b'
              | _ => renderTerm b
          else return "see the statement"
      | _ => return "see the statement"
    if encF.isEmpty then return (p, q, fpp)
    let p' ← RootSplit.letRoots p
    return (p', ← mkExpectedTypeHint q p', fpp)
  let realText := encD.reals.zipIdx.map fun ((lo, hi), i) ↦
    s!"r{Nat.toSubscriptString (i + 1)} ∈ ({RootSplit.decimal lo}, {RootSplit.decimal hi})"
  let discText := encD.discs.zipIdx.map fun ((u, v, ρ, _), i) ↦
    s!"z{Nat.toSubscriptString (i + 1)} = α ± iβ, α ∈ [{RootSplit.decimal (u - ρ)}, \
      {RootSplit.decimal (u + ρ)}], β ∈ [{RootSplit.decimal (v - ρ)}, \
      {RootSplit.decimal (v + ρ)}]"
  let rootsText := if encF.isEmpty then "" else
    s!", with the roots of {RootSplit.polyString R (toString s.getId)} = 0: " ++
      ", ".intercalate (realText ++ discText)
  let σText := if σDecimal then RootSplit.decimal σ.1 else boundText σ
  logReport ref {
    domain := s!"{s.getId} > {σText}"
    input := surfaceText input.raw
    inputType := "proper rational function of s"
    output := fPP
    outputType := "an inverse Laplace transform (its transform is F for s > σ; uniqueness is \
      not claimed)" ++ rootsText
  } #[← liftTermElabM <| Algebra.checkedEvidence "inverseLaplace"
    s!"Inverse Laplace transform" proposition proof]

end CAS.Command.InverseLaplace

namespace CAS.Command

open Lean Elab Command

/-- `#cas [inverseLaplace s t] F` finds a function `f` of `t` whose Laplace transform is the proper
rational function `F` of `s`, and proves the transform for every `s` above a bound `σ`.

## Theorem
For the printed `f`, the report proves that for every `s : ℝ` with `σ < s`, the function
`fun t ↦ Real.exp (-(s * t)) * f` is integrable on `Set.Ioi 0` and
`∫ t in Set.Ioi 0, Real.exp (-(s * t)) * f = F`, with `F` as written
(`CAS.Calculus.Laplace.integral_exp_mul_quadSum`). `σ` is at least every real zero of a written
divisor of `F` and every growth rate of a term of `f`. Mathlib has no uniqueness theorem for the
Laplace transform, so the theorem does not state that `f` is the only such function.

## Conditions and limits
`F` is a proper rational function of `s` with rational coefficients and no parameters; every
written divisor has degree at most 8, and `f` has at most 16 terms. The terms of `f` are
`c * t ^ n * exp (a * t) * g t` with `g` one of `1`, `cos (b * t)`, `sin (b * t)`, `cosh (b * t)`
and `sinh (b * t)`, where `b` may be a square root, and terms over the roots of factors without a
closed form, which are known by enclosures that the kernel checks. The denominator is factored as
`#cas [apart]` factors it, completely over `ℚ` when `CASHex.Factor` is imported. A repeated factor
whose roots are known only by enclosures is refused.

## Options
None.

## Examples
```lean
#cas [inverseLaplace s t] (1 / (s ^ 2 + 4))
```
```output
Output (an inverse Laplace transform (its transform is F for s > σ; uniqueness is not claimed)):
1/2*sin(2*t)
```
```lean
#cas [inverseLaplace s t] (1 / ((s - 1) * (s + 2)))
```
```output
Output (an inverse Laplace transform (its transform is F for s > σ; uniqueness is not claimed)):
1/3*exp(t) - 1/3*exp(-2*t)
```
```lean
#cas [inverseLaplace s t] ((2 * s + 3) / ((s + 1) * (s ^ 2 + 2 * s + 5)))
```
```output
Output (an inverse Laplace transform (its transform is F for s > σ; uniqueness is not claimed)):
1/4*exp(-t) - 1/4*exp(-t)*cos(2*t) + exp(-t)*sin(2*t)
```

## In a proof
```lean
theorem inverseLaplace_at_one
    (h : ∀ s : ℝ, 0 < s → ∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-(s * t)) * (1 / 2 * Real.sin (2 * t)) = 1 / (s ^ 2 + 4)) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(1 * t)) * (1 / 2 * Real.sin (2 * t)) = 1 / 5 := by
  rw [h 1 one_pos]
  norm_num
```
A proof can take the printed theorem as a hypothesis and specialize it, as here at `s = 1`.

## See also
Mathematica `InverseLaplaceTransform`, SymPy `inverse_laplace_transform`. Hex
`Hex.ZPoly.factorize` (through `CASHex.Factor`) factors the denominator. The modes `laplace`,
`apart` and `dsolve`.

## Possible issues
```lean
#cas [inverseLaplace s t] (s ^ 2 / (s + 1))
```
```output
inverseLaplace: F is not proper; its polynomial part (Dirac deltas and their derivatives) is not
supported
```
Subtract the polynomial part, here `s - 1`, and invert the proper rest `1 / (s + 1)`.
```lean
#cas [inverseLaplace s t] (exp (-s) / s)
```
```output
inverseLaplace: expected a proper rational function of s with rational coefficients (parameters
are not supported)
```
A factor `exp (-a * s)` shifts the inverse transform by `a`, which the mode does not handle;
invert `1 / s` and shift the result by hand.
-/
syntax (name := casInverseLaplaceCommand) "#cas" "[" &"inverseLaplace" ident ident "]" term :
  command

elab_rules : command
  | `(#cas [inverseLaplace $s:ident $t:ident] $F:term) => do
      InverseLaplace.logInverseLaplace (← getRef) s t F
        (← liftCoreM Tactic.RouteRegistry.factorProvider?)

end CAS.Command
