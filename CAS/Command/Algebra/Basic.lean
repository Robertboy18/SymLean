/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Algebra.Dense
public import CAS.Command.FullSimplify
public meta import CAS.Polynomial.Sparse.MultivariateGcd
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Data.List.GetD
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.Tactic.IntervalCases

/-!
# Exact algebra for the `#cas` algebra commands

The commands of `CAS.Command.Algebra` (`apart`, `together`, `cancel`, `collect`, `coefficient`,
`polynomialGCD`, …) share the computations and the proof scripts defined here. A rational
expression of the calculator grammar becomes a `RatFun` (numerator and denominator) together with
the list of its divisors, the subterms `b` of its quotients `a / b`; the statements proved by the
commands assume exactly that these divisors do not vanish, which is what Lean's total division
needs for the familiar identities to hold. Nothing computed here is trusted: every result reaches
the user only as an ordinary proposition whose proof the kernel checks, built from Mathlib tactics
(`ring1`, `field_simp`, `norm_num`) or Mathlib lemmas.

## Implementation notes

We compute with two representations of polynomials with rational coefficients. `MvPoly n`
(`CAS.Verified.Expr.Alg`) is sparse in `n` named variables, with the gcd and the exact quotients
of `CAS/Polynomial/Sparse/MultivariateGcd.lean` (`gcdPoly`, `exactDiv?`), and `RatFun.reduce`
divides by that gcd. `Dense` (`CAS/Command/Algebra/Dense.lean`) holds the coefficients of a
polynomial in one variable from the constant term up, with ring arithmetic, division with
remainder, gcd and extended gcd, derivative and shift. We do not factor over `ℚ`: `apart` and
`product` use the factors written in the input (`factorsOver`), and the routes of
`CASHex/Factor.lean`, in the optional `CASHex` (`lake -R -Khex=on build CASHex`), give them Hex's
complete factorization instead.

`coprimeBasis` is factor refinement by gcds: while a polynomial `q` has a nonconstant gcd `g`
with an element `b` of the basis, we replace `b` and `q` by `g`, `b / g` and `q / g`, made
primitive. `rationalIdentityScript` proves a rational identity over such a basis of the divisors
and of the factors of the result. Each basis polynomial divides a divisor, so it is nonzero under
the hypotheses; each divisor is rewritten as a product over the basis, and the basis polynomials
that are not variables are generalized to atoms, so that `field_simp` meets only products of
atoms known to be nonzero and `ring1` closes the cleared identity. Polynomial identities in
`ℚ[X]` and `ℝ[X]` go by evaluation (`polynomialIdentityTactic`), and `checkedEvidence` has the
kernel check each proved statement as an auxiliary theorem.

## References

* Eric Bach, James Driscoll and Jeffrey Shallit, "Factor Refinement", *Journal of Algorithms* 15
  (1993), pp. 199-222, <https://doi.org/10.1006/jagm.1993.1038>. For the refinement of a
  factorization by gcds (`coprimeBasis`).
-/

public meta section

namespace CAS.Command.Algebra

open Lean Elab Command Meta Term
open CAS.Verified.Expr.Alg

/-! ## Multivariate polynomials -/

/-- The constant polynomial `q`. -/
def constPoly (n : Nat) (q : ℚ) : MvPoly n := if q = 0 then [] else [(q, mvOne n)]

/-- The variable `xᵢ`. -/
def varPoly {n : Nat} (i : Fin n) : MvPoly n := [(1, mvVar i)]

/-- The value of a constant polynomial, `none` for a nonconstant one. The polynomial is canonical,
so a constant has at most one term. -/
def constValue? {n : Nat} (p : MvPoly n) : Option ℚ :=
  match p with
  | [] => some 0
  | [(c, m)] => if mvTotalDegree m = 0 then some c else none
  | _ => none

/-- Whether a polynomial is constant. -/
def isConstant {n : Nat} (p : MvPoly n) : Bool := (constValue? p).isSome

/-- The total degree. -/
def totalDegree {n : Nat} (p : MvPoly n) : Nat :=
  p.foldl (fun d t ↦ max d (mvTotalDegree t.2)) 0

/-- `c p` for a canonical `p`, which a nonzero factor `c` keeps canonical. -/
def scalePoly {n : Nat} (c : ℚ) (p : MvPoly n) : MvPoly n :=
  if c = 0 then [] else p.map fun (a, m) ↦ (c * a, m)

/-- The positive rational `c` and the primitive polynomial `q` with integer coefficients and a
positive leading coefficient (graded lexicographic order) such that `p = c q`; `(1, 0)` for zero.
-/
def primitivePart {n : Nat} (p : MvPoly n) : ℚ × MvPoly n :=
  let p := mvNormalize p
  match p with
  | [] => (1, [])
  | (lead, _) :: _ =>
      let numerators := p.foldl (fun (g : Nat) (a, _) ↦ Nat.gcd g a.num.natAbs) 0
      let denominators := p.foldl (fun (l : Nat) (a, _) ↦ Nat.lcm l a.den) 1
      let c : ℚ := (numerators : ℚ) / denominators
      let c := if lead < 0 then -c else c
      (c, scalePoly (1 / c) p)

/-- Exact quotient `a / b` of canonical polynomials, or `none`. -/
def exactDiv? {n : Nat} (a b : MvPoly n) : Option (MvPoly n) :=
  if a.isEmpty then some [] else
  match constValue? b with
  | some c => if c = 0 then none else some (scalePoly (1 / c) a)
  | none => CAS.Polynomial.Sparse.Multivariate.exactQuotient? a b

/-- A gcd of two polynomials (monic in graded lexicographic order). -/
def gcdPoly {n : Nat} (a b : MvPoly n) : MvPoly n :=
  CAS.Polynomial.Sparse.Multivariate.gcd a b

/-- Whether the variable `i` occurs in `p`. -/
def mentions {n : Nat} (p : MvPoly n) (i : Fin n) : Bool := p.any fun (_, m) ↦ m i ≠ 0

/-! ## Rational functions -/

/-- A quotient of two canonical polynomials. Every operation below keeps both canonical. -/
structure RatFun (n : Nat) where
  /-- The numerator. -/
  num : MvPoly n
  /-- The denominator, nonzero. -/
  den : MvPoly n

namespace RatFun

variable {n : Nat}

/-- Divide out the gcd of numerator and denominator and make the leading coefficient of the
denominator `1`; the leading term of a canonical polynomial is its first. -/
def reduce (r : RatFun n) : RatFun n :=
  if r.num.isEmpty then ⟨[], constPoly n 1⟩ else
  let g := gcdPoly r.num r.den
  let (num, den) := match exactDiv? r.num g, exactDiv? r.den g with
    | some a, some b => (a, b)
    | _, _ => (r.num, r.den)
  match den with
  | (c, _) :: _ => ⟨scalePoly (1 / c) num, scalePoly (1 / c) den⟩
  | [] => ⟨num, den⟩

/-- A polynomial as a quotient. -/
def ofPoly (p : MvPoly n) : RatFun n := ⟨mvNormalize p, constPoly n 1⟩

/-- `a + b`. -/
def add (a b : RatFun n) : RatFun n :=
  reduce ⟨mvAdd (mvMulPoly a.num b.den) (mvMulPoly b.num a.den), mvMulPoly a.den b.den⟩

/-- `-a`. -/
def neg (a : RatFun n) : RatFun n := ⟨mvNeg a.num, a.den⟩

/-- `a b`. -/
def mul (a b : RatFun n) : RatFun n :=
  reduce ⟨mvMulPoly a.num b.num, mvMulPoly a.den b.den⟩

/-- `a / b` for `b ≠ 0`. -/
def div (a b : RatFun n) : RatFun n :=
  reduce ⟨mvMulPoly a.num b.den, mvMulPoly a.den b.num⟩

/-- `a ^ k`. -/
def pow (a : RatFun n) (k : Nat) : RatFun n := ⟨mvPowPoly a.num k, mvPowPoly a.den k⟩

/-- Whether this is a polynomial. -/
def isPoly (a : RatFun n) : Bool := isConstant a.den

end RatFun

/-- A rational expression read as a quotient of polynomials, with its divisors: each subterm `b` of
a quotient `a / b`, as written, together with its polynomial value. -/
structure Rational (n : Nat) where
  /-- The value. -/
  value : RatFun n
  /-- The divisors, as written, and their polynomial values. -/
  divisors : Array (Verified.Expr (Fin n) × MvPoly n)

/-- The rational function of a calculator expression made of numerals, variables, field
operations and natural powers. The divisors must be polynomials. -/
partial def rationalOf {n : Nat} (expr : Verified.Expr (Fin n)) :
    StateT (Array (Verified.Expr (Fin n) × MvPoly n)) (Except String) (RatFun n) := do
  match expr with
  | .nat k => return .ofPoly (constPoly n k)
  | .int k => return .ofPoly (constPoly n k)
  | .rat p q => if q = 0 then throw "a literal has the denominator zero" else
      return .ofPoly (constPoly n ((p : ℚ) / q))
  | .var i => return .ofPoly (varPoly i)
  | .add a b => return (← rationalOf a).add (← rationalOf b)
  | .sub a b => return (← rationalOf a).add (← rationalOf b).neg
  | .neg a => return (← rationalOf a).neg
  | .mul a b => return (← rationalOf a).mul (← rationalOf b)
  | .pow a k => return ((← rationalOf a).pow k).reduce
  | .div a b =>
      let numerator ← rationalOf a
      let divisor ← rationalOf b
      unless divisor.isPoly do
        throw "a divisor is itself a quotient; write the expression with polynomial divisors"
      let some c := constValue? divisor.den | throw "internal error: divisor"
      let value := scalePoly (1 / c) divisor.num
      if (mvNormalize value).isEmpty then throw "the expression divides by zero"
      unless isConstant value do
        let known := (← get).any fun (written, _) ↦ written == b
        unless known do modify (·.push (b, value))
      return numerator.div divisor
  | _ => throw "the expression is not a rational function: it has a function other than the \
      field operations and natural powers"

/-- Read an expression as a rational function with its divisors. -/
def rationalOfExpr {n : Nat} (expr : Verified.Expr (Fin n)) : Except String (Rational n) := do
  let (value, divisors) ← (rationalOf expr).run #[]
  return ⟨value.reduce, divisors⟩

/-! ## Coprime bases -/

/-- Refine a list of nonconstant polynomials into pairwise coprime primitive polynomials, each
dividing one of the inputs, such that every input is a constant times a product of their
powers (factor refinement by gcds). -/
partial def coprimeBasis {n : Nat} (polys : List (MvPoly n)) : List (MvPoly n) := Id.run do
  let mut basis : List (MvPoly n) := []
  let mut pending : List (MvPoly n) := polys.map fun p ↦ (primitivePart p).2
  let mut fuel := 10000
  while !pending.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let q := pending.head!
    pending := pending.tail
    if isConstant q then continue
    match basis.find? fun b ↦ !isConstant (gcdPoly b q) with
    | none => basis := basis ++ [q]
    | some b =>
        let g := (primitivePart (gcdPoly b q)).2
        basis := basis.filter (· != b)
        let parts := [g, (exactDiv? b g).getD [], (exactDiv? q g).getD []]
        pending := parts.filter (fun p ↦ !isConstant p) |>.map (primitivePart · |>.2) |>.append
          pending
  return basis

/-- The constant `c` and exponents `kᵢ` with `p = c ∏ bᵢ ^ kᵢ` over a coprime basis, or `none`
when `p` is not such a product. -/
def exponentsOver {n : Nat} (basis : List (MvPoly n)) (p : MvPoly n) :
    Option (ℚ × List Nat) := Id.run do
  let mut rest := mvNormalize p
  if rest.isEmpty then return none
  let mut exponents : List Nat := []
  for b in basis do
    let mut k := 0
    let mut fuel := totalDegree p + 1
    while fuel > 0 do
      fuel := fuel - 1
      match exactDiv? rest b with
      | some quotient =>
          if isConstant b then break
          rest := quotient
          k := k + 1
      | none => break
    exponents := exponents ++ [k]
  match constValue? rest with
  | some c => return some (c, exponents)
  | none => return none

/-! ## Dense univariate polynomials -/

namespace Dense

/-- The rational roots of the nonzero polynomial `cs` (lowest degree first) with multiplicities
and the remaining factor, by `RootIsolation.rationalRoots` and, for a remaining linear factor, its
root; and whether every rational root was found, which fails only when an isolating interval of
the search could not be narrowed within its bisection budget (for the zero polynomial the flag
says nothing). -/
def rationalRoots (cs : List ℚ) : List (ℚ × Nat) × Dense × Bool :=
  let (roots, rest, complete) := CAS.Command.RootIsolation.rationalRoots cs
  match rest with
  | [c₀, c₁] => (roots ++ [(-c₀ / c₁, 1)], #[c₁], true)
  | _ => (roots, trim rest.toArray, rest.length ≤ 1 || complete)

/-- The polynomial as a sparse univariate polynomial. -/
def toSparse (p : Dense) : CAS.Polynomial.Sparse.Univariate :=
  ((List.range p.size).filterMap fun k ↦
    let c := p.getD k 0
    if c = 0 then none else some (c, fun _ ↦ k)).reverse

/-- A sparse univariate polynomial as a dense one. -/
def ofSparse (p : CAS.Polynomial.Sparse.Univariate) : Dense := Id.run do
  let d := p.foldl (fun d (_, m) ↦ max d (m 0)) 0
  let mut out : Array ℚ := Array.replicate (d + 1) 0
  for (c, m) in p do
    out := out.set! (m 0) (out[m 0]! + c)
  return trim out

/-- Whether `p = lead p ∏ fᵢ ^ eᵢ` for the `(fᵢ, eᵢ)` of `factors`, with the `fᵢ` monic,
nonconstant and pairwise coprime: the factorizations that `apart` and `product` accept. -/
def isFactorization (p : Dense) (factors : List (Dense × Nat)) : Bool :=
  let product := factors.foldl (fun acc (f, e) ↦ mul acc (pow f e)) #[1]
  factors.all (fun (f, e) ↦ f.size > 1 && trim f == f && f.back! == 1 && e > 0) &&
    trim product == monic p &&
    (factors.zipIdx.all fun ((f, _), i) ↦ factors.zipIdx.all fun ((g, _), j) ↦
      i == j || (gcd f g).size == 1)

end Dense

/-- A polynomial in one variable as a dense polynomial (the variable `0`). -/
def toDense (p : MvPoly 1) : Dense := Dense.ofSparse p

/-- A dense polynomial in the variable `0` of `n`. -/
def ofDense {n : Nat} (i : Fin n) (p : Dense) : MvPoly n :=
  mvNormalize <| (List.range p.size).filterMap fun k ↦
    let c := p.getD k 0
    if c = 0 then none else some (c, mvPowMonomial (mvVar i) k)

/-- The polynomial factors of an expression as written: the nonconstant polynomial factors of its
products, quotients, negations and natural powers. -/
partial def writtenFactors {n : Nat} (expr : Verified.Expr (Fin n)) : List (MvPoly n) :=
  match expr with
  | .mul a b | .div a b => writtenFactors a ++ writtenFactors b
  | .neg a | .pow a _ => writtenFactors a
  | _ =>
      match rationalOfExpr expr with
      | .ok r => if r.value.isPoly && !isConstant r.value.num then [r.value.num] else []
      | .error _ => []

/-- The monic factors `fᵢ` with exponents `eᵢ` such that `p = lead p ∏ fᵢ ^ eᵢ` over the coprime
basis (`coprimeBasis`) of the polynomials `written` and `p`: the factorization that the factors
written in the input give, refined by gcds only. Nothing is factored further, so a factor need not
be irreducible; complete factoring over `ℚ` is Hex's, through `CASHex`. -/
def factorsOver (written : List (MvPoly 1)) (p : Dense) : List (Dense × Nat) :=
  let q := ofDense (0 : Fin 1) p
  let basis := coprimeBasis (written ++ [q])
  match exponentsOver basis q with
  | some (_, exponents) =>
      ((basis.zip exponents).filter (·.2 > 0)).map fun (b, k) ↦ (Dense.monic (toDense b), k)
  | none => if (Dense.trim p).size ≤ 1 then [] else [(Dense.monic p, 1)]

/-! ## Rendering -/

/-- A rational coefficient as text. -/
def ratText (q : ℚ) : String :=
  if q.den = 1 then s!"{q.num}" else s!"{q.num}/{q.den}"

/-- A rational as the base of a power: parenthesized unless it is a natural number, so that
`(-2)^n` and `(2/3)^n` do not read as `-(2^n)` and `2/(3^n)`. -/
def powerBaseText (q : ℚ) : String :=
  if q.den = 1 && 0 ≤ q then s!"{q.num}" else s!"({ratText q})"

/-- A rational number as an expression to print: a natural or integer literal, or `p/q`. -/
def ratDisplayExpr {n : Nat} (q : ℚ) : Verified.Expr (Fin n) :=
  if q.den = 1 then (if 0 ≤ q.num then .nat q.num.toNat else .int q.num) else .rat q.num q.den

/-- The term `c * m` as an expression to print, with the sign of `c` on its first factor, so
that it prints as `2*x*y`, `-x*y` or `-1/2`. -/
def termDisplayExpr {n : Nat} (c : ℚ) (m : MvMonomial n) : Verified.Expr (Fin n) :=
  let powers : List (Verified.Expr (Fin n)) := (List.finRange n).filterMap fun i ↦
    match m i with
    | 0 => none
    | 1 => some (.var i)
    | k => some (.pow (.var i) k)
  match powers with
  | [] => ratDisplayExpr c
  | first :: rest =>
      let first := if c = 1 then first else if c = -1 then .neg first
        else .mul (ratDisplayExpr c) first
      rest.foldl (fun out power ↦ .mul out power) first

/-- A polynomial as an expression to print: its terms in descending graded lexicographic order,
each after the first added or subtracted with its magnitude. -/
def polyDisplayExpr {n : Nat} (p : MvPoly n) : Verified.Expr (Fin n) :=
  match mvNormalize p with
  | [] => .nat 0
  | (c, m) :: rest => rest.foldl (fun out (c, m) ↦
      if c < 0 then .sub out (termDisplayExpr (-c) m) else .add out (termDisplayExpr c m))
      (termDisplayExpr c m)

/-- A polynomial as text, terms in descending graded lexicographic order. -/
def polyText {n : Nat} (names : Fin n → String) (p : MvPoly n) : String :=
  (polyDisplayExpr p).renderWith names

/-- Whether the text of a polynomial needs parentheses as a factor. -/
def needsParens {n : Nat} (p : MvPoly n) : Bool :=
  match mvNormalize p with
  | [(c, _)] => c < 0
  | _ => true

/-- Whether the text of a polynomial needs parentheses as the base of a power: unless it is a
single variable, `x ^ 3` and `x * y` must read `(x^3)^2` and `(x*y)^2`. -/
def needsParensAsBase {n : Nat} (p : MvPoly n) : Bool :=
  match mvNormalize p with
  | [(c, m)] => c != 1 || (List.finRange n).foldl (fun s i ↦ s + m i) 0 != 1
  | _ => true

/-- A factor `p ^ k` as an expression to print. -/
def factorDisplayExpr {n : Nat} (p : MvPoly n) (k : Nat) : Verified.Expr (Fin n) :=
  if k = 1 then polyDisplayExpr p else .pow (polyDisplayExpr p) k

/-- A factor `p ^ k` as text. -/
def factorText {n : Nat} (names : Fin n → String) (p : MvPoly n) (k : Nat) : String :=
  let base := polyText names p
  if k = 1 then (if needsParens p then s!"({base})" else base)
  else if needsParensAsBase p then s!"({base})^{k}" else s!"{base}^{k}"

/-- The natural numeral `k` as term syntax. -/
def natTerm (k : Nat) : TSyntax `term := ⟨Syntax.mkNumLit (toString k)⟩

/-- A monomial `c * x ^ i * …` as real term syntax over the given variables, with `c ≠ 0`
positive or negative handled by the caller. -/
def monomialTerm {n : Nat} (vars : Fin n → TSyntax `term) (c : ℚ) (m : MvMonomial n) :
    TermElabM (TSyntax `term) := do
  let powers ← (List.finRange n).filterMapM fun i ↦ do
    match m i with
    | 0 => pure none
    | 1 => pure (some (vars i))
    | k => some <$> `($(vars i) ^ $(natTerm k))
  let product? ← powers.foldlM (fun (acc : Option (TSyntax `term)) t ↦ do
    match acc with
    | none => pure (some t)
    | some a => some <$> `($a * $t)) none
  match product? with
  | none => ratSyntax c
  | some body =>
      if c = 1 then pure body else
      let coefficient ← ratSyntax c
      `($coefficient * $body)

/-- A polynomial as real term syntax, built from its terms in descending order. -/
def polyTerm {n : Nat} (vars : Fin n → TSyntax `term) (p : MvPoly n) :
    TermElabM (TSyntax `term) := do
  let p := mvNormalize p
  let mut out? : Option (TSyntax `term) := none
  for (c, m) in p do
    match out? with
    | none => out? := some (← if c < 0 then do `(-$(← monomialTerm vars (-c) m))
        else monomialTerm vars c m)
    | some acc =>
        if c < 0 then out? := some (← `($acc - $(← monomialTerm vars (-c) m)))
        else out? := some (← `($acc + $(← monomialTerm vars c m)))
  match out? with
  | some t => pure t
  | none => `(0)

/-- `p ^ k` as term syntax. -/
def factorTerm {n : Nat} (vars : Fin n → TSyntax `term) (p : MvPoly n) (k : Nat) :
    TermElabM (TSyntax `term) := do
  let base ← polyTerm vars p
  if k = 1 then `(($base)) else `(($base) ^ $(natTerm k))

/-! ## Polynomial rings

Statements about one polynomial in a variable `x` live in `ℚ[X]`, or in `ℝ[X]` with the other
variables as real parameters (`∀ y : ℝ, ((X + C y) ^ 3 : ℝ[X]).coeff 2 = 3 * y`). -/

/-- The coefficients of `p` as a polynomial in `xᵢ`, from the constant term up: polynomials in the
other variables. -/
def coefficientsAlong {n : Nat} (i : Fin n) (p : MvPoly n) : Array (MvPoly n) := Id.run do
  let p := mvNormalize p
  let d := p.foldl (fun d (_, m) ↦ max d (m i)) 0
  let mut out : Array (MvPoly n) := Array.replicate (d + 1) []
  for (c, m) in p do
    let rest : MvMonomial n := fun j ↦ if j = i then 0 else m j
    out := out.set! (m i) (out[m i]! ++ [(c, rest)])
  return out.map mvNormalize

/-- The polynomial ring of a statement: `ℚ[X]` without parameters, `ℝ[X]` with them. -/
def polynomialRing (parameters : Bool) : TermElabM (TSyntax `term) :=
  if parameters then `(Polynomial ℝ) else `(Polynomial ℚ)

/-- The coefficient `c` as a term of the coefficient ring: a rational numeral `(c : ℚ)` or a real
term in the parameters. -/
def coefficientTerm {n : Nat} (vars : Fin n → TSyntax `term) (parameters : Bool) (c : MvPoly n) :
    TermElabM (TSyntax `term) := do
  if parameters then `(($(← polyTerm vars c) : ℝ))
  else
    let some q := constValue? c | throwError "internal error: a coefficient is not constant"
    `(($(← ratSyntax q) : ℚ))

/-- A polynomial in `xᵢ` as the term `C c_d * X ^ d + … + C c_0 * X ^ 0` of the polynomial ring
(the form the coefficient lemmas read). The exponents are written `(k : ℕ)`: an untyped numeral
would wait for its default instance, and the elaborator would retry every waiting exponent after
each term. -/
def expandedPolynomialTerm {n : Nat} (vars : Fin n → TSyntax `term) (parameters : Bool) (i : Fin n)
    (p : MvPoly n) : TermElabM (TSyntax `term) := do
  let coefficients := coefficientsAlong i p
  let ring ← polynomialRing parameters
  let mut out? : Option (TSyntax `term) := none
  for k in (List.range coefficients.size).reverse do
    let c := coefficients[k]!
    if (mvNormalize c).isEmpty then continue
    let coefficient ← coefficientTerm vars parameters c
    let t ← `(Polynomial.C ($coefficient) * (Polynomial.X : $ring) ^ ($(natTerm k) : ℕ))
    out? := some <| ← match out? with
      | none => pure t
      | some acc => `($acc + $t)
  match out? with
  | some t => pure t
  | none => `((0 : $ring))

/-- Whether a calculator expression mentions a variable. -/
def hasVariable {n : Nat} : Verified.Expr (Fin n) → Bool
  | .var _ => true
  | .add a b | .sub a b | .mul a b | .div a b | .rpow a b => hasVariable a || hasVariable b
  | .neg a | .pow a _ | .sin a | .cos a | .atan a | .asin a | .acos a | .exp a | .log a
  | .sqrt a => hasVariable a
  | _ => false

/-- A calculator expression, polynomial in `xᵢ` with the other variables as parameters, as a term
of the polynomial ring: `xᵢ` becomes `X`, a parameter `y` becomes `C y`, a rational `q` becomes
`C q`, and division by a nonzero constant becomes multiplication by `C` of its inverse. -/
partial def polynomialRingTerm {n : Nat} (vars : Fin n → TSyntax `term) (parameters : Bool)
    (i : Fin n) : Verified.Expr (Fin n) → TermElabM (TSyntax `term)
  | .nat k => do `(($(natTerm k) : $(← polynomialRing parameters)))
  | .int k => do
      if k < 0 then `((-$(natTerm k.natAbs) : $(← polynomialRing parameters)))
      else `(($(natTerm k.toNat) : $(← polynomialRing parameters)))
  | .rat p q => do
      let c ← if parameters then `(($(← ratSyntax ((p : ℚ) / q)) : ℝ))
        else `(($(← ratSyntax ((p : ℚ) / q)) : ℚ))
      `(Polynomial.C $c)
  | .var j => do
      if j = i then `((Polynomial.X : $(← polynomialRing parameters)))
      else `(Polynomial.C ($(vars j) : ℝ))
  | .add a b => do
      `($(← polynomialRingTerm vars parameters i a) + $(← polynomialRingTerm vars parameters i b))
  | .sub a b => do
      `($(← polynomialRingTerm vars parameters i a) - ($(← polynomialRingTerm vars parameters i b)))
  | .neg a => do `(-($(← polynomialRingTerm vars parameters i a)))
  | .mul a b => do
      let left ← polynomialRingTerm vars parameters i a
      `(($left) * ($(← polynomialRingTerm vars parameters i b)))
  | .pow a k => do `(($(← polynomialRingTerm vars parameters i a)) ^ $(natTerm k))
  | .div a b => do
      -- Only a divisor written without variables is a constant: a divisor such as `x * (1 / x)`
      -- has a constant rational function but is not the constant under Lean's division.
      let some value := (if hasVariable b then none else match rationalOfExpr b with
        | .ok r => if r.value.isPoly then constValue? r.value.num else none
        | .error _ => none)
        | throwError "the expression divides by a term with a variable"
      if value = 0 then throwError "the expression divides by zero"
      let c ← if parameters then `(($(← ratSyntax (1 / value)) : ℝ))
        else `(($(← ratSyntax (1 / value)) : ℚ))
      `(Polynomial.C ($c) * ($(← polynomialRingTerm vars parameters i a)))
  | _ => throwError "the expression is not a polynomial"

/-- The tactic proving an identity between two polynomials of `ℚ[X]` or `ℝ[X]` (infinite
coefficient rings) by evaluation: `Polynomial.funext`, the evaluation lemmas, then `ring1` on
what `simp` leaves, so `simp` runs once. -/
def polynomialIdentityTactic : TermElabM (TSyntax `tactic) :=
  `(tactic| (apply Polynomial.funext; intro r; first | (simp <;> ring1) | ring1))

/-- A polynomial of `ℚ[X]` as readable term syntax: integer coefficients as numerals, others as
`C q`, terms from the highest degree down, with subtraction for negative coefficients. -/
def qPolyTerm (p : Dense) : TermElabM (TSyntax `term) := do
  let p := Dense.trim p
  let mut out? : Option (TSyntax `term) := none
  for k in (List.range p.size).reverse do
    let c := p[k]!
    if c = 0 then continue
    let magnitude := if c < 0 then -c else c
    let power ← match k with
      | 0 => pure none
      | 1 => some <$> `((Polynomial.X : Polynomial ℚ))
      | _ => some <$> `((Polynomial.X : Polynomial ℚ) ^ $(natTerm k))
    let coefficient ← if magnitude.den = 1 then `(($(natTerm magnitude.num.toNat) : Polynomial ℚ))
      else `(Polynomial.C (($(← ratSyntax magnitude)) : ℚ))
    let term ← match power with
      | none => pure coefficient
      | some x => if magnitude = 1 then pure x else `($coefficient * $x)
    out? := some <| ← match out? with
      | none => if c < 0 then `(-$term) else pure term
      | some acc => if c < 0 then `($acc - $term) else `($acc + $term)
  match out? with
  | some t => `(($t : Polynomial ℚ))
  | none => `((0 : Polynomial ℚ))

/-- A polynomial in one variable as text in `x`. -/
def denseText (x : String) (p : Dense) : String := polyText (fun _ ↦ x) (ofDense (0 : Fin 1) p)

/-! ## Statements and proofs -/

/-- The variables of a reified expression as identifiers. -/
def variableIdents (names : List Name) : Array (TSyntax `ident) :=
  names.toArray.map mkIdent

/-- Elaborate `statement` and prove it by `tactic`; fails, without `sorry`, when the tactic does
not close the goal. Returns the proposition and its proof. -/
def proveStatement (operation : String) (statement : TSyntax `term) (tactic : TSyntax `tactic) :
    TermElabM (Lean.Expr × Lean.Expr) := do
  let proof ← elabCheckedProof operation statement (← `(by $tactic:tactic))
  return (← inferType proof, proof)

/-- Kernel-check a proved proposition as an auxiliary theorem and build the report's evidence,
naming `theoremName?` as the lemma its proof applies. -/
def checkedEvidence (operation label : String) (proposition proof : Lean.Expr)
    (theoremName? : Option Name := none) : TermElabM MessageData := do
  let checked ← CAS.Tactic.Explanation.kernelCheckedProof operation proposition proof
  evidenceReportMessage
    #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof label checked theoremName?]

/-- Hypothesis names `h₀, h₁, …`. -/
def hypothesisIdent (k : Nat) : TSyntax `ident := mkIdent (Name.mkSimple s!"h{k}")

/-- The statement `∀ vars : ℝ, d₀ ≠ 0 → d₁ ≠ 0 → … → body` over the divisors of a rational
expression. -/
def realStatement (vars : Array (TSyntax `ident)) (divisors : Array (TSyntax `term))
    (body : TSyntax `term) : TermElabM (TSyntax `term) := do
  let mut statement := body
  for d in divisors.reverse do
    statement ← `($d ≠ 0 → $statement)
  if vars.isEmpty then return statement
  `(∀ $vars* : ℝ, $statement)

/-- The basis polynomials as a coprime basis of the divisors and the given factors, largest
first, so that generalizing a factor never captures part of a factor generalized later. -/
def identityBasis {n : Nat} (divisors : Array (Verified.Expr (Fin n) × MvPoly n))
    (factors : List (MvPoly n)) : List (MvPoly n) :=
  let basis := coprimeBasis (divisors.toList.map (·.2) ++ factors)
  basis.mergeSort fun a b ↦ totalDegree a > totalDegree b ||
    (totalDegree a == totalDegree b && (mvNormalize a).length ≥ (mvNormalize b).length)

/-- Whether a polynomial is a single variable. -/
def isVariable {n : Nat} (p : MvPoly n) : Bool :=
  match mvNormalize p with
  | [(1, m)] => mvTotalDegree m = 1
  | _ => false

/-- The script proving a rational identity `lhs = rhs` after the variables and the divisor
hypotheses `h₀, h₁, …` are introduced; the denominators of `rhs` are products of powers of
`factors`.

Over a coprime basis of the divisors and the factors, every basis polynomial `b` divides some
divisor `d = b q` (by `ring1`), so `b ≠ 0`. Each divisor is rewritten as its product over the
basis, every basis polynomial that is not a variable is generalized to a fresh atom, so that
`field_simp` sees products of atoms known to be nonzero, and after the substitution back the
cleared identity is a polynomial identity for `ring1`. When this fails, `field_simp; ring1` and
the calculator's own `cas` are tried. -/
def rationalIdentityScript {n : Nat} (vars : Fin n → TSyntax `term)
    (divisors : Array (Verified.Expr (Fin n) × MvPoly n)) (factors : List (MvPoly n)) :
    TermElabM (TSyntax `tactic) := do
  let basis := identityBasis divisors factors
  let mut facts : Array (TSyntax `tactic) := #[]
  let mut rewrites : Array (TSyntax `tactic) := #[]
  let mut generalizations : Array (TSyntax `tactic) := #[]
  let mut substitutions : Array (TSyntax `ident) := #[]
  for (b, k) in basis.zipIdx do
    let some (j, cofactor) := (divisors.zipIdx.findSome? fun ((_, value), j) ↦
        (exactDiv? value b).map (j, ·))
      | throwError "internal error: a basis polynomial divides no divisor"
    let written ← exprTerm vars divisors[j]!.1
    let bT ← polyTerm vars b
    let qT ← polyTerm vars cofactor
    let hj := hypothesisIdent j
    let gk := mkIdent (Name.mkSimple s!"g{k}")
    facts := facts.push (← `(tactic|
      have $gk : ($bT : ℝ) ≠ 0 := fun hzero ↦ $hj (by
        rw [show ($written : ℝ) = ($bT) * ($qT) by ring1, hzero, zero_mul])))
    unless isVariable b do
      let uk := mkIdent (Name.mkSimple s!"u{k}")
      let ek := mkIdent (Name.mkSimple s!"e{k}")
      generalizations := generalizations.push (← `(tactic|
        generalize $ek:ident : ($bT : ℝ) = $uk:ident at $gk:ident ⊢))
      substitutions := substitutions.push ek
  for (written, value) in divisors do
    let some (c, exponents) := exponentsOver basis value
      | throwError "internal error: a divisor is not a product over the basis"
    let parts := (basis.zip exponents).filter (·.2 > 0)
    if c = 1 && parts.length == 1 && parts.head!.2 == 1 then continue
    let mut product? : Option (TSyntax `term) := none
    unless c = 1 do product? := some (← ratSyntax c)
    for (b, e) in parts do
      let t ← factorTerm vars b e
      product? := some <| ← match product? with
        | none => pure t
        | some acc => `($acc * $t)
    let product ← match product? with
      | some t => pure t
      | none => ratSyntax c
    let writtenT ← exprTerm vars written
    rewrites := rewrites.push (← `(tactic| rw [show ($writtenT : ℝ) = $product by ring1]))
  let mut pipeline : TSyntax `tactic ← `(tactic| skip)
  for t in rewrites ++ generalizations do
    pipeline ← `(tactic| ($pipeline:tactic; $t:tactic))
  pipeline ← `(tactic| ($pipeline:tactic; field_simp))
  unless substitutions.isEmpty do
    pipeline ← `(tactic| ($pipeline:tactic; subst $substitutions*))
  pipeline ← `(tactic| ($pipeline:tactic; ring1))
  let mut script : TSyntax `tactic ← `(tactic| skip)
  for fact in facts do
    script ← `(tactic| ($script:tactic; $fact:tactic))
  `(tactic| ($script:tactic; first
    | ring1
    | $pipeline:tactic
    | (field_simp; ring1)
    | cas))

/-- The variables of a reified expression as term syntax. -/
def variableTerms (reified : ReifiedExpr) : Fin reified.names.length → TSyntax `term :=
  fun i ↦ ⟨(mkIdent (reified.names.get i)).raw⟩

/-- The variable names of a reified expression as text. -/
def variableNames (reified : ReifiedExpr) : Fin reified.names.length → String :=
  fun i ↦ renderName (reified.names.get i)

/-- The conditions line of a report: the divisors of the input. -/
def conditionsText {n : Nat} (names : Fin n → String)
    (divisors : Array (Verified.Expr (Fin n) × MvPoly n)) : Option String :=
  if divisors.isEmpty then none else
  some <| "; ".intercalate (divisors.toList.map fun (d, _) ↦ s!"{d.renderWith names} ≠ 0")

/-- Prove `∀ vars, divisors ≠ 0 → (e : ℝ) = rhs` for a rational identity whose right side has
denominators made of `factors`. Returns the proposition and the proof. -/
def proveRationalIdentity (operation : String) (reified : ReifiedExpr)
    (divisors : Array (Verified.Expr (Fin reified.names.length) × MvPoly reified.names.length))
    (rhs : TSyntax `term) (factors : List (MvPoly reified.names.length)) :
    TermElabM (Lean.Expr × Lean.Expr) := do
  let vars := variableTerms reified
  let idents := variableIdents reified.names
  let lhs ← exprTerm vars reified.expr
  let divisorTerms ← divisors.mapM fun (d, _) ↦ do `(($(← exprTerm vars d) : ℝ))
  let statement ← realStatement idents divisorTerms (← `(($lhs : ℝ) = $rhs))
  let hyps := (List.range divisors.size).toArray.map hypothesisIdent
  let intros : TSyntax `tactic ← if idents.isEmpty && hyps.isEmpty then `(tactic| skip)
    else `(tactic| intro $(idents ++ hyps)*)
  let script ← rationalIdentityScript vars divisors factors
  proveStatement operation statement (← `(tactic| ($intros:tactic; $script:tactic)))

end CAS.Command.Algebra
