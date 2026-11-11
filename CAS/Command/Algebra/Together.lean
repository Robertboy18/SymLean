/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Algebra.Basic

/-!
# Common denominators: `#cas [together]`, `[cancel]`, `[numerator]`, `[denominator]`

`#cas [together] e` writes a rational expression in several real variables as one fraction
`N / D` in lowest terms: the denominator is a product of powers of pairwise coprime polynomials
obtained from the divisors of `e` by gcds (so it stays factored as far as the input factors it),
the numerator is expanded, and common factors are cancelled. `#cas [cancel] e` cancels common
factors in each summand of `e` separately, and `#cas [numerator] e` and `#cas [denominator] e`
print the two parts of the `together` form.

The theorem is `∀ x y …, d₁ ≠ 0 → … → dₖ ≠ 0 → e = N / D`, where `d₁, …, dₖ` are the divisors of
`e` as written: under Lean's total division, `e` is not the rational function it denotes when a
divisor vanishes. The divisors must be polynomials (no quotient inside a divisor).

## Implementation notes

We compute with the sparse polynomials of `CAS/Command/Algebra/Basic.lean`, and nothing computed
is trusted. `rationalOfExpr` reads `e` as a quotient divided by the gcd of its numerator and
denominator (the recursive gcd of `CAS/Polynomial/Sparse/MultivariateGcd.lean`), and
`togetherForm` writes the denominator over `coprimeBasis`, the factor refinement of the divisors
and the denominator by gcds. `proveRationalIdentity` then proves the identity from the divisor
hypotheses: each factor of `D` divides some `dᵢ`, which `ring1` shows, so it is nonzero; the
factors that are not variables become atoms, and `field_simp` and `ring1` finish. The kernel
checks the proof as an auxiliary theorem (`checkedEvidence`). We keep `D` as a product over the
basis rather than expanded so that every factor `field_simp` must know to be nonzero comes from
a hypothesis.
-/

public meta section

namespace CAS.Command.Algebra

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Verified.Expr.Alg

/-- A fraction `c N / ∏ fᵢ ^ kᵢ` with `N` a primitive polynomial with integer coefficients, `c`
rational, and the factors pairwise coprime and primitive. -/
structure Fraction (n : Nat) where
  /-- The rational constant of the numerator. -/
  constant : ℚ
  /-- The primitive numerator. -/
  numerator : MvPoly n
  /-- The factors of the denominator with their exponents, all positive. -/
  factors : List (MvPoly n × Nat)

/-- The `together` form of a rational function whose divisors are `divisors`. -/
def togetherForm {n : Nat} (value : RatFun n) (divisors : List (MvPoly n)) :
    Except String (Fraction n) := do
  let basis := coprimeBasis (divisors ++ [value.den])
  let some (c, exponents) := exponentsOver basis value.den
    | throw "internal error: the denominator is not a product over the coprime basis"
  let (content, primitive) := primitivePart value.num
  let factors := (basis.zip exponents).filter (·.2 > 0)
  return { constant := content / c, numerator := primitive, factors }

namespace Fraction

variable {n : Nat}

/-- The numerator `a N` when the constant is `a / b`. -/
def numeratorPoly (r : Fraction n) : MvPoly n := scalePoly r.constant.num r.numerator

/-- The denominator as text, factored. -/
def denominatorText (names : Fin n → String) (r : Fraction n) : String :=
  let constant := if r.constant.den = 1 then [] else [s!"{r.constant.den}"]
  "*".intercalate (constant ++ r.factors.map fun (f, k) ↦ factorText names f k)

/-- The fraction as an expression to print: the expanded numerator over the factored
denominator. -/
def displayExpr (r : Fraction n) : Verified.Expr (Fin n) :=
  let constant : List (Verified.Expr (Fin n)) :=
    if r.constant.den = 1 then [] else [.nat r.constant.den]
  match constant ++ r.factors.map fun (f, k) ↦ factorDisplayExpr f k with
  | [] => polyDisplayExpr r.numeratorPoly
  | first :: rest =>
      .div (polyDisplayExpr r.numeratorPoly) (rest.foldl (fun out part ↦ .mul out part) first)

/-- The fraction as text. -/
def text (names : Fin n → String) (r : Fraction n) : String :=
  r.displayExpr.renderWith names

/-- The denominator as real term syntax, factored. -/
def denominatorTerm (vars : Fin n → TSyntax `term) (r : Fraction n) :
    TermElabM (Option (TSyntax `term)) := do
  let mut parts : Array (TSyntax `term) := #[]
  if r.constant.den ≠ 1 then parts := parts.push (natTerm r.constant.den)
  for (f, k) in r.factors do
    parts := parts.push (← factorTerm vars f k)
  if parts.isEmpty then return none
  let mut out := parts[0]!
  for p in parts[1:] do
    out ← `($out * $p)
  return some out

/-- The fraction as real term syntax. -/
def term (vars : Fin n → TSyntax `term) (r : Fraction n) : TermElabM (TSyntax `term) := do
  let numerator ← polyTerm vars r.numeratorPoly
  match ← r.denominatorTerm vars with
  | none => pure numerator
  | some denominator => `(($numerator) / ($denominator))

end Fraction

/-- What the commands of this module print. -/
inductive TogetherOutput where
  | together
  | numerator
  | denominator
  deriving BEq

/-- Run `#cas [together] e`, `[numerator] e` or `[denominator] e`. -/
def logTogether (ref : Syntax) (output : TogetherOutput) (input : Syntax) :
    CommandElabM Unit := do
  let operation := match output with
    | .together => "together" | .numerator => "numerator" | .denominator => "denominator"
  let reified ← parseInferred input
  let rational ← match rationalOfExpr reified.expr with
    | .ok r => pure r
    | .error message => throwErrorAt input "{operation}: {message}"
  let names := variableNames reified
  let form ← match togetherForm rational.value (rational.divisors.toList.map (·.2)) with
    | .ok f => pure f
    | .error message => throwErrorAt input "{operation}: {message}"
  let (proposition, proof) ← liftTermElabM do
    let rhs ← form.term (variableTerms reified)
    proveRationalIdentity operation reified rational.divisors rhs (form.factors.map (·.1))
  let evidence ← liftTermElabM <|
    checkedEvidence operation "Identity with the common-denominator form" proposition proof
  let shown := match output with
    | .together => form.text names
    | .numerator => polyText names form.numeratorPoly
    | .denominator => if form.factors.isEmpty then s!"{form.constant.den}"
        else form.denominatorText names
  logReport ref {
    domain := renderRealDomain reified.names
    input := reified.render
    inputType := "rational function"
    output := shown
    outputType := match output with
      | .together => "common denominator" | .numerator => "numerator"
      | .denominator => "denominator"
    conditions? := conditionsText names rational.divisors
  } #[evidence]

/-- The summands of a sum, with their signs. -/
partial def summands {ι : Type} : Verified.Expr ι → List (Bool × Verified.Expr ι)
  | .add a b => summands a ++ summands b
  | .sub a b => summands a ++ (summands b).map fun (s, t) ↦ (!s, t)
  | expr => [(true, expr)]

/-- Run `#cas [cancel] e`: cancel common factors in each summand. -/
def logCancel (ref : Syntax) (input : Syntax) : CommandElabM Unit := do
  let reified ← parseInferred input
  let n := reified.names.length
  let names := variableNames reified
  let rational ← match rationalOfExpr reified.expr with
    | .ok r => pure r
    | .error message => throwErrorAt input "cancel: {message}"
  let mut forms : Array (Bool × Fraction n) := #[]
  for (sign, summand) in summands reified.expr do
    let part ← match rationalOfExpr summand with
      | .ok r => pure r
      | .error message => throwErrorAt input "cancel: {message}"
    match togetherForm part.value (part.divisors.toList.map (·.2)) with
    | .ok f => forms := forms.push (sign, f)
    | .error message => throwErrorAt input "cancel: {message}"
  let kept := forms.filter fun (_, f) ↦ !(mvNormalize f.numerator).isEmpty
  let (proposition, proof) ← liftTermElabM do
    let vars := variableTerms reified
    let mut rhs? : Option (TSyntax `term) := none
    for (sign, f) in kept do
      let t ← f.term vars
      rhs? := some <| ← match rhs?, sign with
        | none, true => pure t
        | none, false => `(-($t))
        | some acc, true => `($acc + $t)
        | some acc, false => `($acc - $t)
    let rhs ← match rhs? with
      | some r => pure r
      | none => `(0)
    let factors := kept.toList.flatMap fun (_, f) ↦ f.factors.map (·.1)
    proveRationalIdentity "cancel" reified rational.divisors rhs factors
  let evidence ← liftTermElabM <|
    checkedEvidence "cancel" "Identity with the cancelled form" proposition proof
  -- The sum of the signed summands as one expression for the printer: the first carries its
  -- sign in its constant, and each later one is added or subtracted with its magnitude, so a
  -- subtracted sum prints in parentheses.
  let shown := match kept.toList with
    | [] => "0"
    | (sign, f) :: rest =>
        let first : Fraction n := if sign then f else { f with constant := -f.constant }
        let sum : Verified.Expr (Fin n) := rest.foldl (fun out (sign, f) ↦
          let negative := decide (f.constant < 0)
          let magnitude : Fraction n :=
            { f with constant := if negative then -f.constant else f.constant }
          if sign != negative then .add out magnitude.displayExpr
          else .sub out magnitude.displayExpr) first.displayExpr
        sum.renderWith names
  logReport ref {
    domain := renderRealDomain reified.names
    input := reified.render
    inputType := "rational function"
    output := shown
    outputType := "cancelled"
    conditions? := conditionsText names rational.divisors
  } #[evidence]

end CAS.Command.Algebra

namespace CAS.Command

open Lean Elab Command

/-- `#cas [together] e` writes the rational expression `e` as one fraction `N / D` in lowest terms.

## Theorem
For the variables `x₁, …, xₙ` of `e` and its divisors `d₁, …, dₖ` as written, the report proves
`∀ x₁ … xₙ : ℝ, d₁ ≠ 0 → … → dₖ ≠ 0 → e = N / D` about Mathlib's real division, by `field_simp`
and `ring`. Each factor of `D` divides one of the `dᵢ`, which `ring` shows.

## Conditions and limits
The input is built from real variables and rational numbers by `+`, `-`, `*`, `/` and natural
powers, and every divisor is a polynomial. The denominator `D` is a product of powers of pairwise
coprime polynomials obtained from the divisors by gcds, so it stays factored as far as the input
factors it; the numerator `N` is expanded. The conditions are the divisors as written, since
Lean's division by zero gives zero.

## Options
None.

## Examples
```lean
#cas [together] (1/x + 1/y)
```
```output
Output (common denominator): (x + y)/(x*y)
Conditions: x ≠ 0; y ≠ 0
```
```lean
#cas [together] (1/(x^2-1) + 1/(x-1))
```
```output
Output (common denominator): (x + 2)/((x - 1)*(x + 1))
Conditions: x^2 - 1 ≠ 0; x - 1 ≠ 0
```
```lean
#cas [together] (x/2 + y/3)
```
```output
Output (common denominator): (3*x + 2*y)/6
```

## In a proof
```lean
theorem together_sum (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    1 / x + 1 / y = (x + y) / (x * y) := by
  cas
```

## See also
Mathematica `Together`, SymPy `together` and `cancel`. The modes `cancel`, `numerator`,
`denominator`, `apart` and `simplify`.

## Possible issues
```lean
#cas [together] (1/(1 + 1/x))
```
```output
together: a divisor is itself a quotient; write the expression with polynomial divisors
```
Multiply the inner fraction out first, here `x/(x + 1)`.
```lean
#cas [together] (sin x / x)
```
```output
together: the expression is not a rational function: it has a function other than the field
operations and natural powers
```
`#cas [simplify]` and `#cas [fullSimplify]` accept the elementary functions.
-/
syntax (name := casTogetherCommand) "#cas" "[" &"together" "]" term : command

/-- `#cas [cancel] e` cancels the common factors of the numerator and the denominator in each
summand of the rational expression `e`.

## Theorem
For the variables `x₁, …, xₙ` of `e`, its divisors `d₁, …, dₖ` as written and the printed sum
`e'`, the report proves `∀ x₁ … xₙ : ℝ, d₁ ≠ 0 → … → dₖ ≠ 0 → e = e'`, by `field_simp` and
`ring`.

## Conditions and limits
The input is a rational expression as for `#cas [together]`. The summands are not brought to a
common denominator.

## Options
None.

## Examples
```lean
#cas [cancel] ((x^2-1)/(x-1) + 1/x)
```
```output
Output (cancelled): x + 1 + 1/x
Conditions: x - 1 ≠ 0; x ≠ 0
```
```lean
#cas [cancel] ((x^3 - y^3)/(x - y) + 1/y)
```
```output
Output (cancelled): x^2 + x*y + y^2 + 1/y
Conditions: x - y ≠ 0; y ≠ 0
```
```lean
#cas [cancel] ((x^2 - y^2)/(x - y) - (x^3 - 1)/(x - 1))
```
```output
Output (cancelled): x + y - (x^2 + x + 1)
Conditions: x - y ≠ 0; x - 1 ≠ 0
```

## In a proof
```lean
theorem cancel_sum (x : ℝ) (h : x - 1 ≠ 0) :
    (x ^ 2 - 1) / (x - 1) + 1 / x = x + 1 + 1 / x := by
  cas
```

## See also
Mathematica `Cancel`, SymPy `cancel`. The modes `together`, `simplify` and `factor`.

## Possible issues
```lean
#cas [cancel] (sin x / x)
```
```output
cancel: the expression is not a rational function: it has a function other than the field
operations and natural powers
```
`#cas [simplify]` cancels common factors in expressions with elementary functions.
-/
syntax (name := casCancelCommand) "#cas" "[" &"cancel" "]" term : command

/-- `#cas [numerator] e` prints the numerator `N` of the `together` form `N / D` of the rational
expression `e`.

## Theorem
The report proves the theorem of `#cas [together] e`:
`∀ x₁ … xₙ : ℝ, d₁ ≠ 0 → … → dₖ ≠ 0 → e = N / D`, over the divisors `dᵢ` of `e` as written.

## Conditions and limits
The input is a rational expression as for `#cas [together]`. `N` is expanded and has no common
factor with `D`.

## Options
None.

## Examples
```lean
#cas [numerator] (1/x + 1/y)
```
```output
Output (numerator): x + y
Conditions: x ≠ 0; y ≠ 0
```
```lean
#cas [numerator] (x/(x^2 - 1) + 1/(x + 1))
```
```output
Output (numerator): 2*x - 1
Conditions: x^2 - 1 ≠ 0; x + 1 ≠ 0
```

## In a proof
```lean
theorem numerator_mul (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    (1 / x + 1 / y) * (x * y) = x + y := by
  cas
```

## See also
Mathematica `Numerator` of `Together`, SymPy `numer` of `together`. The modes `denominator`,
`together` and `cancel`.

## Possible issues
```lean
#cas [numerator] (sqrt x / x)
```
```output
numerator: the expression is not a rational function: it has a function other than the field
operations and natural powers
```
The mode accepts only rational expressions; `#cas [simplify]` accepts `sqrt`.
-/
syntax (name := casNumeratorCommand) "#cas" "[" &"numerator" "]" term : command

/-- `#cas [denominator] e` prints the denominator `D` of the `together` form `N / D` of the rational
expression `e`.

## Theorem
The report proves the theorem of `#cas [together] e`:
`∀ x₁ … xₙ : ℝ, d₁ ≠ 0 → … → dₖ ≠ 0 → e = N / D`, over the divisors `dᵢ` of `e` as written.

## Conditions and limits
The input is a rational expression as for `#cas [together]`. `D` is a product of powers of
pairwise coprime polynomials obtained from the divisors by gcds; a rational number when `e` has
no variable divisor.

## Options
None.

## Examples
```lean
#cas [denominator] (1/(x-1) - 1/(x+1))
```
```output
Output (denominator): (x - 1)*(x + 1)
Conditions: x - 1 ≠ 0; x + 1 ≠ 0
```
```lean
#cas [denominator] (x/2 + y/3)
```
```output
Output (denominator): 6
```

## In a proof
```lean
theorem denominator_difference (x : ℝ) (h₁ : x - 1 ≠ 0) (h₂ : x + 1 ≠ 0) :
    1 / (x - 1) - 1 / (x + 1) = 2 / ((x - 1) * (x + 1)) := by
  cas
```

## See also
Mathematica `Denominator` of `Together`, SymPy `denom` of `together`. The modes `numerator`,
`together` and `apart`.

## Possible issues
```lean
#cas [denominator] (1/(1 + 1/x))
```
```output
denominator: a divisor is itself a quotient; write the expression with polynomial divisors
```
Write every divisor as a polynomial, here `x/(x + 1)`.
-/
syntax (name := casDenominatorCommand) "#cas" "[" &"denominator" "]" term : command

elab_rules : command
  | `(#cas [together] $e:term) => Algebra.logTogether e .together e
  | `(#cas [numerator] $e:term) => Algebra.logTogether e .numerator e
  | `(#cas [denominator] $e:term) => Algebra.logTogether e .denominator e
  | `(#cas [cancel] $e:term) => Algebra.logCancel e e

end CAS.Command
