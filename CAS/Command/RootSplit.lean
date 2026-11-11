/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.LinearODERoots
public import CAS.Command.Algebra.Basic
public import CAS.Command.Digits
public import CAS.CEGA.Elaboration
public meta import CAS.Calculus.LinearODERoots
public meta import CAS.Command.Algebra.Basic
public meta import CAS.Command.Digits
public meta import CAS.CEGA.Elaboration
public meta import CAS.Polynomial.Sparse.Euclidean
public meta import CAS.Tactic.RouteRegistry

/-!
# Splitting a rational polynomial into exact and enclosed roots

`split` makes a polynomial monic, takes its rational roots with their multiplicities
(`Dense.rationalRoots`) and splits the rest into squarefree parts (`squareFreeFactors?`). A part
of degree one gives a rational root and a part of degree two the quadratic formula
(`CharRoot.real`, `realPair` or `pair`, with a squarefree radicand). A part of degree at least
four, or of degree three when the rational root search was cut short, goes to the factor provider
registered under `factor` (`CASHex` registers Hex's), whose answer is used only when
`Dense.isFactorization` confirms it. The other parts are enclosed.

`roots` multiplies the enclosed parts into one squarefree `R` and encloses its roots
(`Enclosures.check`). It also computes the Bézout identity `U ∏ ρᵏ + V R = 1` and a precision at
which the exact roots are separated. Enclosed parts of multiplicity more than one are refused.
`Roots.terms` writes the certificate as syntax, with the kernel-checked facts that
`LinearODE.general_iff_rr`, `charC_combined`, `nodup_combined` and `eval_eq_zero_iff_combined`
take. The printing helpers (`boundQ`, `polySyntax`, `letRoots`, `decimal`) serve `dsolve`,
`rsolve`, `inverseLaplace`, `roots` and `eigenvalues`, and `enclosureParts` writes the statements
that locate the enclosed roots, with their proofs.

## Implementation notes

The split and the enclosures are found by untrusted code. `Roots.terms` gives the kernel closed
Boolean facts to decide: the product of the exact factors and `R` is the monic polynomial, the
Bézout identity holds, the exact roots are valid and separated, with positive multiplicities, the
degrees add up, and `LinearODE.Enclosures.check` accepts. The squarefree parts come from
`CAS.Polynomial.Sparse.Univariate.squareFreeFactors?` (`CAS/Polynomial/Sparse/Euclidean.lean`),
which takes repeated gcds and exact quotients starting from `gcd(p, p')`; the factor provider is
looked up by `CAS.Tactic.RouteRegistry.factorProvider?`.

The enclosures start from floating-point roots of `R` (`numericRoots`): the Durand-Kerner
iteration, which corrects each approximation `zᵢ` by `R (zᵢ) / ∏_{j ≠ i} (zᵢ - zⱼ)`, starts from
the powers of `0.4 + 0.9 i` and runs 3000 sweeps. Each new value replaces the old one at once, so
the later corrections of a sweep use it. Newton steps in exact rational arithmetic (`refineReal`,
`refineComplex`) refine each centre, rounded to `10 ^ (-d)` for `d = 8, 16, 32, …` until
`Enclosures.check` accepts; the search gives up once `d` exceeds `2 * separationDigits R + 16`,
where `separationDigits` counts the digits of a root-separation bound of Mahler type, a stopping
rule only. The check asks for a sign change on each real interval (`AlgRoot.real_spec` turns it
into a root), for the bounds of `AlgRoot.cCheck` on each disc, under which the Newton map
contracts the disc into itself (`AlgRoot.complex_spec`, in `CAS/Calculus/AlgebraicRoots.lean`),
for disjoint enclosures and for as many roots as the degree (`CAS/Calculus/LinearODERoots.lean`).

## References

* Immo O. Kerner, "Ein Gesamtschrittverfahren zur Berechnung der Nullstellen von Polynomen",
  *Numerische Mathematik* 8 (1966), pp. 290-294, <https://doi.org/10.1007/BF02162564>.
  Iteration (6) of Section 1; `numericRoots` runs it in its single-step form.
* K. Mahler, "An inequality for the discriminant of a polynomial", *Michigan Mathematical
  Journal* 11 (1964), pp. 257-262, <https://doi.org/10.1307/mmj/1028999140>. The root-separation
  bound behind `separationDigits`.
-/

public meta section

namespace CAS.Command.RootSplit

open Lean Elab Command Meta Term
open CAS.Command.Algebra (Dense)
open CAS.LinearODE (CharRoot Enclosures)
open CAS.Tactic.RouteRegistry (FactorProvider)

/-! ## Numbers and polynomials -/

/-- A complex floating-point number. -/
structure ComplexFloat where
  /-- The real part. -/
  re : Float
  /-- The imaginary part. -/
  im : Float

namespace ComplexFloat
/-- `a + b`. -/
def add (a b : ComplexFloat) : ComplexFloat := ⟨a.re + b.re, a.im + b.im⟩
/-- `a - b`. -/
def sub (a b : ComplexFloat) : ComplexFloat := ⟨a.re - b.re, a.im - b.im⟩
/-- `a b`. -/
def mul (a b : ComplexFloat) : ComplexFloat :=
  ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
/-- `a / b = a b̄ / (b.re ^ 2 + b.im ^ 2)`. -/
def div (a b : ComplexFloat) : ComplexFloat :=
  let d := b.re * b.re + b.im * b.im
  ⟨(a.re * b.re + a.im * b.im) / d, (a.im * b.re - a.re * b.im) / d⟩
/-- `‖a‖ = √(re ^ 2 + im ^ 2)`. -/
def norm (a : ComplexFloat) : Float := Float.sqrt (a.re * a.re + a.im * a.im)
end ComplexFloat

/-- `q` as a float, `num / den`. -/
def ratToFloat (q : ℚ) : Float := Float.ofInt q.num / Float.ofNat q.den

/-- Numerical roots of a polynomial (lowest degree first) by the Durand–Kerner iteration. -/
def numericRoots (cs : Array ℚ) : Array ComplexFloat := Id.run do
  let n := cs.size - 1
  let lead := ratToFloat (cs.getD n 1)
  let coeffs := cs.map fun c ↦ ratToFloat c / lead
  let eval (z : ComplexFloat) : ComplexFloat :=
    coeffs.foldr (fun c acc ↦ ComplexFloat.add (ComplexFloat.mul acc z) ⟨c, 0⟩) ⟨0, 0⟩
  let seed : ComplexFloat := ⟨0.4, 0.9⟩
  let mut zs : Array ComplexFloat := #[]
  let mut power : ComplexFloat := ⟨1, 0⟩
  for _ in [0:n] do
    zs := zs.push power
    power := ComplexFloat.mul power seed
  for _ in [0:3000] do
    for i in [0:n] do
      let zi := zs.getD i ⟨0, 0⟩
      let mut denom : ComplexFloat := ⟨1, 0⟩
      for j in [0:n] do
        if j != i then denom := ComplexFloat.mul denom (ComplexFloat.sub zi (zs.getD j ⟨0, 0⟩))
      zs := zs.set! i (ComplexFloat.sub zi (ComplexFloat.div (eval zi) denom))
  return zs

/-- `N = k ^ 2 m` with `m` squarefree, by trial division up to the cube root and a square test on
the cofactor, which then has at most two prime factors. -/
def squareFactor (N : Nat) : Nat × Nat := Id.run do
  let mut k := 1
  let mut m := 1
  let mut rest := N
  let mut i := 2
  while i * i * i ≤ rest do
    if rest % i == 0 then
      let mut e := 0
      while rest % i == 0 do
        rest := rest / i
        e := e + 1
      k := k * i ^ (e / 2)
      if e % 2 == 1 then m := m * i
    i := i + 1
  let s := rest.sqrt
  return if s * s == rest then (k * s, m) else (k, m * rest)

/-- `√q = c √m` with `m` squarefree, for `q ≥ 0`. -/
def sqrtParts (q : ℚ) : ℚ × Nat :=
  let (a, m₁) := squareFactor q.num.natAbs
  let (b, m₂) := squareFactor q.den
  ((a : ℚ) / (b * m₂ : ℚ), m₁ * m₂)

/-- `∑ cₖ vᵏ` as text, highest degree first. -/
def polyString (R : Dense) (v : String) : String :=
  let terms := ((List.range R.size).reverse.filterMap fun k ↦
    let c := R.getD k 0
    if c == 0 then none else
    let mag := if c < 0 then -c else c
    let pw := if k == 0 then "" else if k == 1 then v else s!"{v}^{k}"
    let body := if mag == 1 && k != 0 then pw else if k == 0 then s!"{mag}" else s!"{mag} {pw}"
    some (decide (c < 0), body))
  match terms with
  | [] => "0"
  | (isNeg, b) :: rest => (if isNeg then "-" else "") ++ b ++ String.join (rest.map
      fun (p : Bool × String) ↦ (if p.1 then " - " else " + ") ++ p.2)

/-! ## Enclosures -/

/-- `⌊x 10 ^ d⌉ / 10 ^ d`. -/
def roundQ (x : ℚ) (d : Nat := 8) : ℚ :=
  let s : ℚ := 10 ^ d
  (((x * s + 1 / 2).floor : ℤ) : ℚ) / s

/-- The float `x` as the rational it is, from `Float.frExp`; `NaN` and infinities give `0`. -/
def floatQ (x : Float) : ℚ :=
  if x.isNaN || x.isInf then 0 else
  let (m, e) := x.frExp
  let a := (Float.abs m * 9007199254740992.0).toUInt64.toNat
  let i : ℤ := if m < 0 then -(a : ℤ) else a
  let k : ℤ := e - 53
  if k ≥ 0 then (i : ℚ) * 2 ^ k.toNat else (i : ℚ) / 2 ^ (-k).toNat

/-- Newton steps in exact arithmetic for a complex root of `R`, rounding to `2 ^ -bits`. -/
def refineComplex (R : List ℚ) (u v : ℚ) (steps : Nat := 4) (bits : Nat := 60) :
    ℚ × ℚ := Id.run do
  let D := CAS.Polynomial.coeffDeriv R
  let scale : ℚ := 2 ^ bits
  let snap (q : ℚ) : ℚ := (((q * scale).floor : ℤ) : ℚ) / scale
  let mut u := u
  let mut v := v
  for _ in [0:steps] do
    let (pr, pim) := CAS.AlgRoot.gEval R u v
    let (dr, di) := CAS.AlgRoot.gEval D u v
    let n := dr * dr + di * di
    if n == 0 then break
    u := snap (u - (pr * dr + pim * di) / n)
    v := snap (v - (pim * dr - pr * di) / n)
  return (u, v)

/-- Newton steps in exact arithmetic for a real root of `R`, rounding to `2 ^ -bits`. -/
def refineReal (R : List ℚ) (r : ℚ) (steps : Nat := 4) (bits : Nat := 60) : ℚ := Id.run do
  let D := CAS.Polynomial.coeffDeriv R
  let scale : ℚ := 2 ^ bits
  let snap (q : ℚ) : ℚ := (((q * scale).floor : ℤ) : ℚ) / scale
  let mut r := r
  for _ in [0:steps] do
    let d := CAS.Polynomial.coeffEvalRat D r
    if d == 0 then break
    r := snap (r - CAS.Polynomial.coeffEvalRat R r / d)
  return r

/-- A rational `L > 0` with `L ^ 2 ≤ q`. -/
def sqrtLower (q : ℚ) : ℚ := Id.run do
  let f := Float.sqrt (ratToFloat q) * 0.999
  let mut L := floatQ f
  for _ in [0:60] do
    if L > 0 && L * L ≤ q then return L
    L := L / 2
  return L

/-- A number of decimal digits past which the roots of the squarefree `R` are separated: the
digit count of a root-separation bound of Mahler type, `n ^ ((n + 2) / 2) ‖R‖ ^ (n - 1)` for the
integer multiple of `R`, plus two. -/
def separationDigits (R : Dense) : Nat :=
  let n := Dense.degree R
  let scale : Nat := R.foldl (fun l c ↦ Nat.lcm l c.den) 1
  let maxCoeff : Nat := R.foldl (fun m c ↦ max m (c * (scale : ℚ)).num.natAbs) 1
  let digitsOf (k : Nat) : Nat := (toString k).length
  (n + 2) / 2 * digitsOf n + (n - 1) * digitsOf (maxCoeff * (n + 1)) + 2

/-- Enclosures of the roots of the monic squarefree `R` at `d` digits, from the numerical roots
`zs`: an interval `c ± ρ` (or `c ± 2ρ`) around each real root and a disc of radius `2ρ` around one
root of each complex pair, `ρ = 10 ^ -d`, with centres refined by exact Newton steps and rounded
to `10 ^ -d`; `none` when a bound or `Enclosures.check` fails. -/
def encloseAt (R : Dense) (zs : Array ComplexFloat) (d : Nat) : Option Enclosures := Id.run do
  let L := R.toList
  let ρ : ℚ := 1 / 10 ^ d
  let steps := 4 + Nat.log2 (d / 8)
  let bits := max 60 (4 * d + 16)
  let value (q : ℚ) : ℚ := CAS.Polynomial.coeffEvalRat L q
  let mut reals : List (ℚ × ℚ) := []
  let mut discs : List (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ) := []
  for z in zs do
    if Float.abs z.im < 1e-7 * (1 + ComplexFloat.norm z) then
      let c := roundQ (refineReal L (floatQ z.re) steps bits) d
      if value (c - ρ) * value (c + ρ) < 0 then reals := reals ++ [(c - ρ, c + ρ)]
      else if value (c - 2 * ρ) * value (c + 2 * ρ) < 0 then
        reals := reals ++ [(c - 2 * ρ, c + 2 * ρ)]
      else return none
    else if z.im > 0 then
      let (ue, ve) := refineComplex L (floatQ z.re) (floatQ z.im) steps bits
      let u := roundQ ue d
      let v := roundQ ve d
      let (dr, di) := CAS.AlgRoot.gEval (CAS.Polynomial.coeffDeriv L) u v
      let Lb := sqrtLower (dr * dr + di * di)
      let Rb := |u| + |v|
      unless CAS.AlgRoot.cCheck L u v (2 * ρ) (1 / 2) Rb Lb do return none
      discs := discs ++ [(u, v, 2 * ρ, 1 / 2, Rb, Lb)]
  let D : Enclosures := ⟨reals.mergeSort fun I J ↦ I.1 ≤ J.1,
    discs.mergeSort fun a b ↦ a.1 < b.1 || (a.1 == b.1 && a.2.1 ≤ b.2.1)⟩
  return if D.check L then some D else none

/-- Enclosures of the roots of the monic squarefree `R` and their number of digits, doubling the
digits from 8 until `Enclosures.check` holds or the separation bound is passed. -/
def encloseDigits (R : Dense) (var : String := "x") : Except String (Enclosures × Nat) :=
    Id.run do
  let zs := numericRoots R
  let bound := 2 * separationDigits R + 16
  let mut d := 8
  for _ in [0:16] do
    if let some D := encloseAt R zs d then return .ok (D, d)
    if d > bound then break
    d := 2 * d
  return .error s!"the roots of {polyString R var} could not be enclosed"

/-- Enclosures of the roots of the monic squarefree `R`. -/
def enclose (R : Dense) : Except String Enclosures := (encloseDigits R).map (·.1)

/-! ## The split -/

/-- A monic polynomial split into roots known exactly and factors whose roots are enclosed. -/
structure Split where
  /-- The monic polynomial. -/
  poly : Dense
  /-- The rational roots and the roots from the quadratic formula, with multiplicities. -/
  exact : List (CharRoot × Nat)
  /-- The monic factors whose roots are only enclosed, with multiplicities. -/
  enclosed : List (Dense × Nat)
  /-- Whether the answer of the factor provider was used. -/
  usedProvider : Bool

/-- The roots of the monic quadratic `f = X ^ 2 + b X + c`, each of multiplicity `k`:
`α ± γ √m` with `α = -b / 2`, `γ √m = √|α ^ 2 - c|` and `m` squarefree. -/
def quadraticRoots (f : Dense) (k : Nat) : List (CharRoot × Nat) :=
  let α := -(f.getD 1 0) / 2
  let q := α * α - f.getD 0 0
  if q = 0 then [(.real α, 2 * k)]
  else if q > 0 then
    let (γ, m) := sqrtParts q
    if m = 1 then [(.real (α + γ), k), (.real (α - γ), k)] else [(.realPair α γ (m : ℚ), k)]
  else
    let (γ, m) := sqrtParts (-q)
    [(.pair α γ (m : ℚ), k)]

/-- Split the nonzero polynomial `p`: rational roots, the squarefree parts of
`squareFreeFactors?`, the quadratic formula, the factor provider `factorize?` for parts of degree
at least four (or three when the rational root search was incomplete), and enclosures for the
rest. -/
def split (factorize? : Option FactorProvider) (p : Dense) : Split := Id.run do
  let poly := Dense.monic p
  let (rational, rest, complete) := Dense.rationalRoots poly.toList
  let mut exact : List (CharRoot × Nat) := rational.map fun (r, k) ↦ (.real r, k)
  let mut enclosed : List (Dense × Nat) := []
  let mut usedProvider := false
  let parts : List (Dense × Nat) :=
    if rest.size ≤ 1 then []
    else match CAS.Polynomial.Sparse.Univariate.squareFreeFactors?
        (Dense.toSparse (Dense.monic rest)) with
      | some fs => fs.map fun f ↦ (Dense.monic (Dense.ofSparse f.factor), (f.multiplicity : Nat))
      | none => [(Dense.monic rest, 1)]
  for (f, k) in parts do
    let d := Dense.degree f
    if d = 0 then continue
    if d = 1 then exact := exact ++ [(.real (-(f.getD 0 0)), k)]
    else if d = 2 then exact := exact ++ quadraticRoots f k
    else
      let answer? : Option (List (Dense × Nat)) :=
        if d ≥ 4 || !complete then
          factorize?.map fun factorize ↦ (factorize f).map fun (g, e) ↦ (Dense.monic g, e)
        else none
      match answer? with
      | some fs =>
          if Dense.isFactorization f fs && fs.all (fun (g, e) ↦ e == 1 && Dense.degree g ≥ 1) then
            usedProvider := true
            for (g, _) in fs do
              match Dense.degree g with
              | 1 => exact := exact ++ [(.real (-(g.getD 0 0)), k)]
              | 2 => exact := exact ++ quadraticRoots g k
              | _ => enclosed := enclosed ++ [(g, k)]
          else enclosed := enclosed ++ [(f, k)]
      | none => enclosed := enclosed ++ [(f, k)]
  return { poly, exact, enclosed, usedProvider }

/-- The roots of a polynomial with the data of their certificate. -/
structure Roots where
  /-- The split of the polynomial. -/
  split : Split
  /-- The product of the enclosed factors, `#[1]` when there are none. -/
  R : Dense
  /-- The enclosures of the roots of `R`. -/
  D : Enclosures
  /-- The cofactor of `∏ ρᵏ` in the Bézout identity `U ∏ ρᵏ + V R = 1`. -/
  U : Dense
  /-- The cofactor of `R` in the Bézout identity. -/
  V : Dense
  /-- A precision at which `LinearODE.separated` holds for the exact roots. -/
  prec : Nat
  /-- The number of decimal digits of the enclosures. -/
  digits : Nat

/-- The roots of the nonzero polynomial `p` with their certificate data; `var` names the
variable in the messages. Enclosed factors of multiplicity more than one are refused. -/
def roots (factorize? : Option FactorProvider) (p : Dense) (var : String := "r") :
    Except String Roots := do
  let s := split factorize? p
  if let some (f, _) := s.enclosed.find? (·.2 > 1) then
    throw s!"the repeated factor {polyString f var} has roots known only by enclosures, which \
      are not treated"
  let R := s.enclosed.foldl (fun acc (f, _) ↦ Dense.mul acc f) #[1]
  let (D, digits) ← if Dense.degree R = 0 then pure ((⟨[], []⟩ : Enclosures), 8)
    else encloseDigits R var
  let Q := CAS.LinearODE.charList s.exact
  unless CAS.Polynomial.coeffMul Q R.toList == s.poly.toList do
    throw "the factorization of the polynomial failed"
  let (g, U, V) := Dense.xgcd Q.toArray R
  unless g == #[1] do throw "the exact and the enclosed factors have a common factor"
  let mut prec := 8
  let mut found := false
  for _ in [0:12] do
    if CAS.LinearODE.separated s.exact prec then
      found := true
      break
    prec := 2 * prec
  unless found do throw "the roots could not be separated"
  return { split := s, R, D, U, V, prec, digits }

/-- `roots` with the factor provider registered in the environment, if any. -/
def rootsHere {m : Type → Type} [Monad m] [MonadEnv m] [MonadOptions m] [MonadError m]
    (p : Dense) (var : String := "r") : m (Except String Roots) := do
  return roots (← CAS.Tactic.RouteRegistry.factorProvider?) p var

/-! ## Syntax and certificates -/

/-- The term `(q : ℚ)`. -/
def ratQ {m : Type → Type} [Monad m] [MonadQuotation m] (q : ℚ) : m (TSyntax `term) := do
  `(($(← ratSyntax q) : ℚ))

/-- The numeral `n`. -/
def natLit {m : Type → Type} [Monad m] (n : Nat) : m (TSyntax `term) :=
  pure ⟨Syntax.mkNumLit (toString n)⟩

/-- The root as a term `LinearODE.CharRoot.real r`, `realPair α c m` or `pair α c m`. -/
def rootSyntax {m : Type → Type} [Monad m] [MonadQuotation m] : CharRoot → m (TSyntax `term)
  | .real r => do `(LinearODE.CharRoot.real $(← ratQ r))
  | .realPair α c n => do
      `(LinearODE.CharRoot.realPair $(← ratQ α) $(← ratQ c) $(← ratQ (n : ℚ)))
  | .pair α c n => do `(LinearODE.CharRoot.pair $(← ratQ α) $(← ratQ c) $(← ratQ (n : ℚ)))

/-- The list literal `[x₁, …, xₙ]` of the terms `xs`. -/
def listSyntax {m : Type → Type} [Monad m] [MonadQuotation m] (xs : Array (TSyntax `term)) :
    m (TSyntax `term) := `([$xs,*])

/-- The least `d ≤ 64` with `q 10 ^ d` an integer, if there is one. -/
def decimalDigits? (q : ℚ) : Option Nat := Id.run do
  let mut d := q.den
  let mut twos := 0
  let mut fives := 0
  while d % 2 == 0 do
    d := d / 2
    twos := twos + 1
  while d % 5 == 0 do
    d := d / 5
    fives := fives + 1
  return if d == 1 && max twos fives ≤ 64 then some (max twos fives) else none

/-- A decimal rendering of a rational: all its digits when it is a decimal with at most 64 of
them, with at least 8, and otherwise rounded to 8 digits. -/
def decimal (q : ℚ) : String :=
  let neg := q < 0
  let a := if neg then -q else q
  let d := max 8 ((decimalDigits? a).getD 8)
  let s : ℚ := 10 ^ d
  let scaled := ((a * s + 1 / 2).floor).toNat
  let ip := scaled / 10 ^ d
  let fp := scaled % 10 ^ d
  let fs := toString fp
  let fs := String.ofList (List.replicate (d - fs.length) '0') ++ fs
  (if neg then "-" else "") ++ s!"{ip}.{fs}"

/-- A decimal rational that is not an integer as a decimal literal of type `ty`, other rationals
as they are. -/
def boundAt {m : Type → Type} [Monad m] [MonadQuotation m] (ty : TSyntax `term) (q : ℚ) :
    m (TSyntax `term) := do
  if q.den != 1 && (decimalDigits? q).isSome then
    let a := if q < 0 then -q else q
    let lit : TSyntax `term := ⟨Syntax.mkScientificLit (decimal a)⟩
    if q < 0 then `((-$lit : $ty)) else `(($lit : $ty))
  else `(($(← ratSyntax q) : $ty))

/-- `q` as a term of type `ℚ`, by `boundAt`. -/
def boundQ {m : Type → Type} [Monad m] [MonadQuotation m] (q : ℚ) : m (TSyntax `term) := do
  boundAt (← `(ℚ)) q

/-- `q` as a term of type `ℝ`, by `boundAt`. -/
def boundR {m : Type → Type} [Monad m] [MonadQuotation m] (q : ℚ) : m (TSyntax `term) := do
  boundAt (← `(ℝ)) q

/-- `Digits.evaluateNumerals`, keeping decimal literals. -/
def evaluateNumerals (proof : Lean.Expr) : MetaM Lean.Expr := do
  let type ← inferType proof
  let literal (e : Lean.Expr) : Bool := e.isAppOfArity ``OfScientific.ofScientific 5
  let keep (e : Lean.Expr) : Bool :=
    literal e || (e.isAppOfArity ``Neg.neg 3 && literal (e.getArg! 2))
  let methods : Simp.Methods := {
    pre := fun e ↦ if keep e then return .done { expr := e }
      else Mathlib.Meta.NormNum.tryNormNum (post := false) e
    post := fun e ↦ if keep e then return .done { expr := e }
      else Mathlib.Meta.NormNum.tryNormNum (post := true) e
    discharge? := Simp.dischargeGround }
  let context ← Simp.mkContext {} (simpTheorems := #[]) (congrTheorems := ← getSimpCongrTheorems)
  let (result, _) ← Simp.main type context (methods := methods)
  let restored := Digits.restoreNames type result.expr
  match result.proof? with
  | none => mkExpectedTypeHint proof restored
  | some equality => mkExpectedTypeHint (← mkEqMP equality proof) restored

/-- `∑ cₖ tᵏ` as syntax. -/
def polySyntax {m : Type → Type} [Monad m] [MonadQuotation m] (R : List ℚ) (t : TSyntax `term)
    (ty : TSyntax `term) : m (TSyntax `term) := do
  let mut out : Option (TSyntax `term) := none
  for k in (List.range R.length).reverse do
    let c := R.getD k 0
    if c == 0 then continue
    let mag := if c < 0 then -c else c
    let pw ← if k == 0 then `((1 : $ty)) else if k == 1 then pure t
      else `($t ^ $(Syntax.mkNumLit (toString k)))
    let term ← if mag == 1 then pure pw
      else if k == 0 then `(($(← ratSyntax mag) : $ty)) else `(($(← ratSyntax mag) : $ty) * $pw)
    out := some (← match out with
      | none => if c < 0 then `(-$term) else pure term
      | some o => if c < 0 then `($o - $term) else `($o + $term))
  match out with
  | some t => return t
  | none => `((0 : $ty))

/-- Subterms with head `AlgRoot.real` or `AlgRoot.complex`, in order of appearance. -/
partial def rootTerms (e : Lean.Expr) (acc : Array Lean.Expr := #[]) : Array Lean.Expr :=
  if e.isAppOfArity ``CAS.AlgRoot.real 3 ||
      e.isAppOfArity ``CAS.AlgRoot.complex 4 then
    if acc.contains e then acc else acc.push e
  else
    match e with
    | .app f a => rootTerms a (rootTerms f acc)
    | .lam _ t b _ => rootTerms b (rootTerms t acc)
    | .forallE _ t b _ => rootTerms b (rootTerms t acc)
    | .letE _ t v b _ => rootTerms b (rootTerms v (rootTerms t acc))
    | .mdata _ b => rootTerms b acc
    | .proj _ _ b => rootTerms b acc
    | _ => acc

/-- `let r₁ := …; let z₁ := …; type`, abstracting the root terms of `type`. -/
def letRoots (type : Lean.Expr) : MetaM Lean.Expr := do
  let terms := rootTerms type
  let mut names : Array (Name × Lean.Expr × Lean.Expr) := #[]
  let mut realCount := 0
  let mut complexCount := 0
  for t in terms do
    if t.isAppOfArity ``CAS.AlgRoot.real 3 then
      realCount := realCount + 1
      names := names.push (Name.mkSimple s!"r{Nat.toSubscriptString realCount}",
        mkConst ``Real, t)
    else
      complexCount := complexCount + 1
      names := names.push (Name.mkSimple s!"z{Nat.toSubscriptString complexCount}",
        mkConst ``Complex, t)
  -- Innermost first: abstract the last root, then wrap outwards.
  let mut body := type
  for (n, ty, v) in names.reverse do
    let abstracted ← kabstract body v
    body := .letE n ty v abstracted false
  return body

/-- The last conjunct of `a ∧ b ∧ ⋯`. -/
partial def lastConjunct (e : Lean.Expr) : Lean.Expr :=
  if e.isAppOfArity ``And 2 then lastConjunct (e.getArg! 1) else e

/-- A kernel-checked proof of the closed decidable proposition `prop`, as syntax. -/
def certified (prop : TSyntax `term) : TermElabM (TSyntax `term) := do
  let type ← elabType prop
  synthesizeSyntheticMVarsNoPostponing
  let type ← instantiateMVars type
  exprToSyntax (← CAS.CEGA.Elaboration.decideClosedCertificate type false)

/-- The identifier `n` with the macro scope of the command, so that the generated binders never
capture a sequence or an index of the input with the same name. -/
def hygienicIdent (n : Name) : TermElabM (TSyntax `ident) :=
  return mkIdent (← MonadQuotation.addMacroScope n)

/-- The statements `r ∈ (lo, hi) ∧ R r = 0` and `Re z ∈ […] ∧ Im z ∈ […] ∧ R z = 0` of the
enclosed roots, with their proofs. -/
def enclosureParts (R : Dense) (D : Enclosures) (RT : TSyntax `term) :
    TermElabM (Array (TSyntax `term) × Array (TSyntax `term)) := do
  let t ← hygienicIdent `t
  let h₁ ← hygienicIdent `h₁
  let h₂ ← hygienicIdent `h₂
  let mut statements : Array (TSyntax `term) := #[]
  let mut proofs : Array (TSyntax `term) := #[]
  for (lo, hi) in D.reals do
    let loT ← boundQ lo
    let hiT ← boundQ hi
    let r ← `(AlgRoot.real $RT $loT $hiT)
    let hlt ← certified (← `(($loT : ℚ) < $hiT))
    let hsign ← certified (← `((CAS.Polynomial.coeffEvalRat $RT $loT) *
      (CAS.Polynomial.coeffEvalRat $RT $hiT) < 0))
    let poly ← polySyntax R.toList r (← `(ℝ))
    statements := statements.push
      (← `($r ∈ Set.Ioo $(← boundR lo) $(← boundR hi) ∧ $poly = 0))
    proofs := proofs.push (← `(⟨by
        have $t:ident := (AlgRoot.real_spec $RT $hlt $hsign).1
        push_cast at $t:ident
        exact ⟨by linarith [($t).1], by linarith [($t).2]⟩,
      by
        have $t:ident := (AlgRoot.real_spec $RT $hlt $hsign).2
        simp only [CAS.Polynomial.coeffEval_cons, CAS.Polynomial.coeffEval_nil] at $t:ident
        push_cast at $t:ident
        linear_combination $t:ident⟩))
  for (u, v, ρ, κ, Rb, L) in D.discs do
    let uT ← boundQ u
    let vT ← boundQ v
    let ρT ← boundQ ρ
    let z ← `(AlgRoot.complex $RT $uT $vT $ρT)
    let hcc ← certified
      (← `(AlgRoot.cCheck $RT $uT $vT $ρT $(← ratQ κ) $(← ratQ Rb) $(← ratQ L) = true))
    let poly ← polySyntax R.toList z (← `(ℂ))
    statements := statements.push
      (← `(($z).re ∈ Set.Icc $(← boundR (u - ρ)) $(← boundR (u + ρ)) ∧
        ($z).im ∈ Set.Icc $(← boundR (v - ρ)) $(← boundR (v + ρ)) ∧ $poly = 0))
    proofs := proofs.push (← `(⟨by
        have $h₁:ident :=
          (AlgRoot.re_mem_of_mem_closedBall (AlgRoot.complex_spec $RT $hcc).1).1
        push_cast at $h₁:ident
        exact ⟨by linarith [($h₁).1], by linarith [($h₁).2]⟩,
      by
        have $h₂:ident :=
          (AlgRoot.re_mem_of_mem_closedBall (AlgRoot.complex_spec $RT $hcc).1).2
        push_cast at $h₂:ident
        exact ⟨by linarith [($h₂).1], by linarith [($h₂).2]⟩,
      by
        have $t:ident := (AlgRoot.complex_spec $RT $hcc).2
        simp only [AlgRoot.polyC_cons, AlgRoot.polyC_nil, _root_.Polynomial.eval_add,
          _root_.Polynomial.eval_mul, _root_.Polynomial.eval_C, _root_.Polynomial.eval_X,
          _root_.Polynomial.eval_zero] at $t:ident
        push_cast at $t:ident
        linear_combination $t:ident⟩))
  return (statements, proofs)

/-- The certificate of `Roots` as syntax: the data, and the kernel-checked facts that
`LinearODE.general_iff_rr`, `charC_combined`, `nodup_combined` and `eval_eq_zero_iff_combined`
take. -/
structure RootTerms where
  /-- The exact roots with multiplicities, a `List (LinearODE.CharRoot × ℕ)`. -/
  rs : TSyntax `term
  /-- The product `R` of the enclosed factors, a `List ℚ`. -/
  R : TSyntax `term
  /-- The enclosures of the roots of `R`. -/
  D : TSyntax `term
  /-- The coefficients of the monic polynomial, a `List ℚ`. -/
  a : TSyntax `term
  /-- The cofactor `U` of the Bézout identity. -/
  U : TSyntax `term
  /-- The cofactor `V` of the Bézout identity. -/
  V : TSyntax `term
  /-- The separation precision of the exact roots. -/
  prec : TSyntax `term
  /-- The degree of the polynomial. -/
  d : TSyntax `term
  /-- All the roots, `LinearODE.combined rs R D`. -/
  all : TSyntax `term
  /-- `∀ e ∈ rs, e.1.Valid`. -/
  hv : TSyntax `term
  /-- `∀ e ∈ rs, 0 < e.2`. -/
  hpos : TSyntax `term
  /-- `LinearODE.separated rs prec = true`. -/
  hsep : TSyntax `term
  /-- `LinearODE.Enclosures.check R D = true`. -/
  hD : TSyntax `term
  /-- `CAS.Polynomial.coeffMul (LinearODE.charList rs) R = a`. -/
  hA : TSyntax `term
  /-- `coeffEq (coeffAdd (coeffMul U (charList rs)) (coeffMul V R)) [1] = true`, with the list
  operations of `CAS.Polynomial`: the Bézout identity `U ∏ ρᵏ + V R = 1`. -/
  hb : TSyntax `term
  /-- `LinearODE.degQ rs + (R.length - 1) = d`. -/
  hlen : TSyntax `term

/-- The certificate of `r` as syntax, its facts decided by the kernel. -/
def Roots.terms (r : Roots) : TermElabM RootTerms := do
  let RSq ← listSyntax (← r.split.exact.toArray.mapM fun (ρ, k) ↦ do
    `(($(← rootSyntax ρ), $(← natLit k))))
  let RT ← `(($(← listSyntax (← r.R.mapM ratQ)) : List ℚ))
  let realsT ← listSyntax (← r.D.reals.toArray.mapM fun (lo, hi) ↦ do
    `(($(← boundQ lo), $(← boundQ hi))))
  let discsT ← listSyntax (← r.D.discs.toArray.mapM fun (u, v, ρ, κ, Rb, L) ↦ do
    `(($(← boundQ u), $(← boundQ v), $(← boundQ ρ), $(← ratQ κ), $(← ratQ Rb), $(← ratQ L))))
  let DT ← `((⟨$realsT, $discsT⟩ : LinearODE.Enclosures))
  let all ← `(LinearODE.combined $RSq $RT $DT)
  let A ← listSyntax (← r.split.poly.mapM ratQ)
  let UT ← listSyntax (← r.U.mapM ratQ)
  let VT ← listSyntax (← r.V.mapM ratQ)
  let dT ← natLit (r.split.poly.size - 1)
  let precT ← natLit r.prec
  let hv ← certified (← `(∀ e ∈ ($RSq : List (LinearODE.CharRoot × ℕ)), e.1.Valid))
  let hsep ← certified (← `(LinearODE.separated $RSq $precT = true))
  let hpos ← certified (← `(∀ e ∈ ($RSq : List (LinearODE.CharRoot × ℕ)), 0 < e.2))
  let hD ← certified (← `(LinearODE.Enclosures.check $RT $DT = true))
  let hA ← certified (← `(CAS.Polynomial.coeffMul (LinearODE.charList $RSq) $RT = ($A : List ℚ)))
  let hb ← certified (← `(CAS.Polynomial.coeffEq (CAS.Polynomial.coeffAdd
    (CAS.Polynomial.coeffMul ($UT : List ℚ) (LinearODE.charList $RSq))
    (CAS.Polynomial.coeffMul ($VT : List ℚ) $RT)) ([1] : List ℚ) = true))
  let hlen ← certified (← `(LinearODE.degQ $RSq + (($RT : List ℚ).length - 1) = $dT))
  return {
    rs := RSq, R := RT, D := DT, a := A, U := UT, V := VT, prec := precT, d := dT, all,
    hv, hpos, hsep, hD, hA, hb, hlen }

end CAS.Command.RootSplit
