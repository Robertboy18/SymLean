/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Algebra.Basic
public import Mathlib.Algebra.Polynomial.CoeffList

/-!
# Coefficients: `#cas [collect]`, `[coefficient]`, `[coefficientList]`, `[exponent]`

For a polynomial `e` in several real variables and a chosen variable `x`:

* `#cas [collect x] e` writes `e` as `∑ cₖ xᵏ` with the coefficients `cₖ` expanded polynomials in
  the other variables, with the theorem `∀ x y …, e = ∑ cₖ * x ^ k`.
* `#cas [coefficient x k] e` gives `cₖ`, `#cas [coefficientList x] e` the list `[c₀, …, c_d]`,
  and `#cas [exponent x] e` the degree `d`. Their theorems are about Mathlib's polynomials: `e`
  with `x` read as `X` is a polynomial `P` in `ℚ[X]`, or in `ℝ[X]` with the other variables `y` as
  constants `C y`, and the statements are `P.coeff k = cₖ`,
  `∀ k, P.coeff k = [c₀, …, c_d].getD k 0` and `P.natDegree = d`; when the leading coefficient
  involves the other variables, the degree is stated under the hypothesis that it does not
  vanish.

## Implementation notes

The coefficients are computed in compiled code (`coefficientsAlong` of
`CAS/Command/Algebra/Basic.lean`) and only proposed: each statement is proved by a tactic script,
and the kernel checks the proof as an auxiliary theorem (`checkedEvidence`). The theorem of
`collect` is proved by `ring1`. The list is proved in one step: by `Polynomial.ext_iff` and
Mathlib's `coeff_ofCoeffList` the statement is the identity `P = ofCoeffList [c₀, …, c_d]`,
which is proved by evaluation (`Polynomial.funext`, through `polynomialIdentityTactic`). A
single coefficient and the degree rewrite `P` to its expanded form `∑ C cₖ * X ^ k` over the
nonzero coefficients, proved the same way, and read the coefficient with `coeff_C_mul` and
`coeff_X_pow`, or the degree with `compute_degree`. When the leading coefficient involves the
other variables, the degree goes through `Polynomial.natDegree_eq_of_le_of_coeff_ne_zero` with
the hypothesis that it does not vanish.
-/

public meta section

namespace CAS.Command.Algebra

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Verified.Expr.Alg

/-- The collected form `∑ cₖ xᵏ` as text, highest power first. -/
def collectedText {n : Nat} (names : Fin n → String) (i : Fin n)
    (coefficients : Array (MvPoly n)) : String := Id.run do
  let mut out := ""
  for k in (List.range coefficients.size).reverse do
    let c := mvNormalize coefficients[k]!
    if c.isEmpty then continue
    let power := match k with
      | 0 => ""
      | 1 => names i
      | _ => s!"{names i}^{k}"
    let (negative, c) := match c with
      | [(a, m)] => if a < 0 then (true, [(-a, m)]) else (false, c)
      | _ => (false, c)
    let coefficient := polyText names c
    let term := if power.isEmpty then coefficient
      else if c.length > 1 then s!"({coefficient})*{power}"
      else if coefficient == "1" then power else s!"{coefficient}*{power}"
    out := if out.isEmpty then (if negative then s!"-{term}" else term)
      else out ++ (if negative then s!" - {term}" else s!" + {term}")
  return if out.isEmpty then "0" else out

/-- Read the input of a coefficient command: a polynomial with `x` first among its variables. -/
def polynomialInput (operation : String) (x : Name) (input : Syntax) :
    CommandElabM (Σ reified : ReifiedExpr, MvPoly reified.names.length) := do
  let reified ← parseWithLeading input [x]
  let rational ← match rationalOfExpr reified.expr with
    | .ok r => pure r
    | .error message => throwErrorAt input "{operation}: {message}"
  unless rational.value.isPoly && rational.divisors.isEmpty do
    throwErrorAt input "{operation}: the expression is not a polynomial (it divides by a term with \
      a variable)"
  let some c := constValue? rational.value.den | throwErrorAt input "{operation}: internal error"
  return ⟨reified, scalePoly (1 / c) rational.value.num⟩

/-- The index of the chosen variable, the first. -/
def leadingIndex (reified : ReifiedExpr) : Except String (Fin reified.names.length) :=
  if h : 0 < reified.names.length then .ok ⟨0, h⟩ else .error "the expression has no variable"

/-- Run `#cas [collect x] e`. -/
def logCollect (ref : Syntax) (x : Name) (input : Syntax) : CommandElabM Unit := do
  let ⟨reified, p⟩ ← polynomialInput "collect" x input
  let i ← match leadingIndex reified with
    | .ok i => pure i
    | .error message => throwErrorAt input "collect: {message}"
  let names := variableNames reified
  let coefficients := coefficientsAlong i p
  let (proposition, proof) ← liftTermElabM do
    let vars := variableTerms reified
    let mut rhs? : Option (TSyntax `term) := none
    for k in (List.range coefficients.size).reverse do
      let c := coefficients[k]!
      if (mvNormalize c).isEmpty then continue
      let cT ← polyTerm vars c
      let t ← if k = 0 then `(($cT)) else if k = 1 then `(($cT) * $(vars i))
        else `(($cT) * $(vars i) ^ $(natTerm k))
      rhs? := some <| ← match rhs? with
        | none => pure t
        | some acc => `($acc + $t)
    let rhs ← match rhs? with
      | some r => pure r
      | none => `(0)
    let lhs ← exprTerm vars reified.expr
    let statement ← realStatement (variableIdents reified.names) #[] (← `(($lhs : ℝ) = $rhs))
    let idents := variableIdents reified.names
    proveStatement "collect" statement (← `(tactic| (intro $idents*; ring1)))
  let evidence ← liftTermElabM <|
    checkedEvidence "collect" "Identity with the collected form" proposition proof
  logReport ref {
    domain := renderRealDomain reified.names
    input := reified.render
    inputType := "polynomial"
    output := collectedText names i coefficients
    outputType := s!"polynomial in {renderName x}"
  } #[evidence]

/-- What a coefficient command reports. -/
inductive CoefficientQuery where
  | coefficient (k : Nat)
  | list
  | exponent

/-- Run `#cas [coefficient x k] e`, `[coefficientList x] e` or `[exponent x] e`. -/
def logCoefficient (ref : Syntax) (x : Name) (query : CoefficientQuery) (input : Syntax) :
    CommandElabM Unit := do
  let operation := match query with
    | .coefficient _ => "coefficient" | .list => "coefficientList" | .exponent => "exponent"
  let ⟨reified, p⟩ ← polynomialInput operation x input
  let i ← match leadingIndex reified with
    | .ok i => pure i
    | .error message => throwErrorAt input "{operation}: {message}"
  let names := variableNames reified
  let parameters : Bool := decide (reified.names.length > 1)
  let coefficients := coefficientsAlong i p
  let degree := (List.range coefficients.size).foldl
    (fun d k ↦ if (mvNormalize coefficients[k]!).isEmpty then d else k) 0
  let leading := coefficients.getD degree []
  if (mvNormalize p).isEmpty && !(query matches .coefficient _) then
    throwErrorAt input "{operation}: the polynomial is zero"
  -- The proofs recurse along the expanded polynomial, and for the list along the list, so the
  -- recursion limit grows with their lengths.
  let length := match query with
    | .list => max coefficients.size p.length
    | _ => p.length
  let depth := maxRecDepth.defValue + 16 * length
  let (proposition, proof) : Lean.Expr × Lean.Expr ← liftTermElabM <|
      withAtLeastMaxRecDepth depth do
    let vars := variableTerms reified
    let parameterIdents := (variableIdents reified.names).extract 1
    let P ← polynomialRingTerm vars parameters i reified.expr
    let E ← expandedPolynomialTerm vars parameters i p
    let identity ← polynomialIdentityTactic
    let rewrite ← `(tactic| rw [show ($P) = $E by $identity:tactic])
    let read ← `(tactic| (simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_zero]; norm_num))
    let (body, script) : TSyntax `term × TSyntax `tactic ← match query with
      | .coefficient k =>
          let c := coefficients.getD k []
          let cT ← coefficientTerm vars parameters c
          pure (← `(Polynomial.coeff ($P) $(natTerm k) = $cT),
            ← `(tactic| ($rewrite:tactic; first | $read:tactic | simp)))
      | .list =>
          let entries ← coefficients.toList.mapM fun c ↦ coefficientTerm vars parameters c
          let list ← `([$(entries.toArray),*])
          let k := mkIdent `k
          -- `List.getD list k 0` is the coefficient of `ofCoeffList list`, so the statement says
          -- that `P` and `ofCoeffList list` have the same coefficients.
          pure (← `(∀ $k:ident : ℕ, Polynomial.coeff ($P) $k = List.getD $list $k 0),
            ← `(tactic| (
              simp only [← Polynomial.coeff_ofCoeffList]
              rw [← Polynomial.ext_iff]
              simp only [Polynomial.ofCoeffList_cons, Polynomial.ofCoeffList_nil]
              $identity:tactic)))
      | .exponent =>
          if isConstant leading then
            pure (← `(Polynomial.natDegree ($P) = $(natTerm degree)),
              ← `(tactic| ($rewrite:tactic; compute_degree!)))
          else
            let lT ← polyTerm vars leading
            pure (← `(($lT : ℝ) ≠ 0 → Polynomial.natDegree ($P) = $(natTerm degree)),
              ← do
                let unfold ← `(tactic| simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul,
                  Polynomial.coeff_X_pow])
                let apply ← `(tactic| apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero <;> first
                  | compute_degree
                  | ($unfold:tactic; (try norm_num); (try exact hlead); done)
                  | ($unfold:tactic; (try norm_num); grind))
                `(tactic| (intro hlead; $rewrite:tactic; $apply:tactic)))
    let statement ← if parameterIdents.isEmpty then pure body
      else `(∀ $parameterIdents* : ℝ, $body)
    let intros ← if parameterIdents.isEmpty then `(tactic| skip)
      else `(tactic| intro $parameterIdents*)
    proveStatement operation statement (← `(tactic| ($intros:tactic; $script:tactic)))
  let evidence ← liftTermElabM <| withAtLeastMaxRecDepth depth <|
    checkedEvidence operation "Statement about the polynomial" proposition proof
  let shown := match query with
    | .coefficient k => polyText names (coefficients.getD k [])
    | .list => "[" ++ ", ".intercalate (coefficients.toList.map (polyText names)) ++ "]"
    | .exponent => s!"{degree}"
  logReport ref {
    domain := if parameters then s!"{renderName x} ↦ X in ℝ[X], parameters in ℝ"
      else s!"{renderName x} ↦ X in ℚ[X]"
    input := reified.render
    inputType := "polynomial"
    output := shown
    outputType := match query with
      | .coefficient k => s!"coefficient of {renderName x}^{k}"
      | .list => "coefficients, constant term first"
      | .exponent => "degree"
    conditions? := if query matches .exponent && !isConstant leading then
      some s!"{polyText names leading} ≠ 0" else none
  } #[evidence]

end CAS.Command.Algebra

namespace CAS.Command

open Lean Elab Command

/-- `#cas [collect x] e` writes the polynomial `e` as a sum of powers of `x` whose coefficients are
expanded polynomials in the other variables.

## Theorem
For the variables `x, y, …` of `e` and the printed coefficients `cₖ`, the report proves
`∀ x y … : ℝ, e = ∑ cₖ * x ^ k` about Mathlib's real numbers, by `ring1`.

## Conditions and limits
The input is a polynomial with rational coefficients in real variables, and `x` is one of them.
A quotient by a term with a variable is refused.

## Options
None.

## Examples
```lean
#cas [collect x] ((1 + a*x)^2 + b*x)
```
```output
Output (polynomial in x): a^2*x^2 + (2*a + b)*x + 1
```
```lean
#cas [collect x] (x*y + x^2*y + x + y^2*x^2)
```
```output
Output (polynomial in x): (y^2 + y)*x^2 + (y + 1)*x
```

## In a proof
```lean
theorem collect_square (x a b : ℝ) :
    (1 + a * x) ^ 2 + b * x = a ^ 2 * x ^ 2 + (2 * a + b) * x + 1 := by
  cas
```

## See also
Mathematica `Collect`, SymPy `collect`. The modes `coefficient`, `coefficientList`, `exponent`
and `expand`.

## Possible issues
```lean
#cas [collect x] (1/x + x)
```
```output
collect: the expression is not a polynomial (it divides by a term with a variable)
```
For a rational function, `#cas [apart]` splits off the polynomial part.
-/
syntax (name := casCollectCommand) "#cas" "[" &"collect" ident "]" term : command

/-- `#cas [coefficient x k] e` prints the coefficient of `x ^ k` in the polynomial `e`.

## Theorem
With `x` read as `Polynomial.X`, `e` is a polynomial `P` in `ℚ[X]`, or in `ℝ[X]` with the other
variables `y` as constants `C y`. For the printed coefficient `c`, the report proves
`∀ y … : ℝ, P.coeff k = c`; for `(x + y)^3` and `k = 2` it is
`∀ y : ℝ, ((X + C y) ^ 3).coeff 2 = 3 * y`.

## Conditions and limits
The input is a polynomial as for `#cas [collect x]`, and `k` is a natural number literal.

## Options
None.

## Examples
```lean
#cas [coefficient x 2] ((x + y)^3)
```
```output
Output (coefficient of x^2): 3*y
```
```lean
#cas [coefficient x 3] ((1 + 2*x)^5)
```
```output
Output (coefficient of x^3): 80
```

## In a proof
```lean
open _root_.Polynomial in
theorem coefficient_binomial : ((X + 1) ^ 5 : ℚ[X]).coeff 2 = 10 := by
  cas
```

## See also
Mathematica `Coefficient`, SymPy `coeff`. The modes `coefficientList`, `collect`
and `exponent`.

## Possible issues
```lean
#cas [coefficient x 1] (1/x)
```
```output
coefficient: the expression is not a polynomial (it divides by a term with a variable)
```
The mode reads coefficients of polynomials only.
-/
syntax (name := casCoefficientCommand) "#cas" "[" &"coefficient" ident num "]" term : command

/-- `#cas [coefficientList x] e` prints the list of coefficients of the polynomial `e` in `x`,
constant term first.

## Theorem
With `e` read as a polynomial `P` as for `#cas [coefficient x k]`, and the printed list
`[c₀, …, c_d]`, the report proves `∀ k, P.coeff k = [c₀, …, c_d].getD k 0`. By
`Polynomial.ext_iff` and Mathlib's `coeff_ofCoeffList` the statement is the identity
`P = ofCoeffList [c₀, …, c_d]`, which is proved by evaluation.

## Conditions and limits
The input is a polynomial as for `#cas [collect x]`. The other variables stay symbolic in the
coefficients.

## Options
None.

## Examples
```lean
#cas [coefficientList x] ((x + 1)^3 - x/2)
```
```output
Output (coefficients, constant term first): [1, 5/2, 3, 1]
```
```lean
#cas [coefficientList x] (a*x^2 + b*x + c)
```
```output
Output (coefficients, constant term first): [c, b, a]
```

## In a proof
```lean
open _root_.Polynomial in
theorem coefficientList_cube (h : ∀ k, ((X + 1) ^ 3 : ℚ[X]).coeff k = [1, 3, 3, 1].getD k 0) :
    ((X + 1) ^ 3 : ℚ[X]).coeff 1 = 3 :=
  h 1
```

## See also
Mathematica `CoefficientList`, SymPy `Poly.all_coeffs` (highest degree first). The modes
`coefficient`, `collect` and `exponent`.

## Possible issues
```lean
#cas [coefficientList x] (x + 1/x)
```
```output
coefficientList: the expression is not a polynomial (it divides by a term with a variable)
```
The mode reads coefficients of polynomials only. The tactic `cas` does not prove the list
statement `∀ k, P.coeff k = [c₀, …, c_d].getD k 0`; it proves each single coefficient, as in
`#cas [coefficient x k]`.
-/
syntax (name := casCoefficientListCommand) "#cas" "[" &"coefficientList" ident "]" term : command

/-- `#cas [exponent x] e` prints the degree in `x` of the polynomial `e`.

## Theorem
With `e` read as a polynomial `P` as for `#cas [coefficient x k]`, and the printed degree `d`, the
report proves `P.natDegree = d`. When the leading coefficient involves the other variables, the
statement has the hypothesis that it does not vanish, as in
`∀ a : ℝ, a ≠ 0 → (C a * X ^ 2 + X + 1).natDegree = 2`.

## Conditions and limits
The input is a nonzero polynomial as for `#cas [collect x]`. The degree is computed after
expansion, so cancelling terms do not count.

## Options
None.

## Examples
```lean
#cas [exponent x] ((x + 1)^3 - x^3)
```
```output
Output (degree): 2
```
```lean
#cas [exponent x] (a*x^2 + x + 1)
```
```output
Output (degree): 2
Conditions: a ≠ 0
```

## In a proof
```lean
open _root_.Polynomial in
theorem exponent_difference : ((X + 1) ^ 3 - X ^ 3 : ℚ[X]).natDegree = 2 := by
  cas
```

## See also
Mathematica `Exponent`, SymPy `degree`. The modes `coefficient`, `coefficientList` and
`collect`.

## Possible issues
```lean
#cas [exponent x] (0)
```
```output
exponent: the polynomial is zero
```
The zero polynomial has no degree in this sense; Mathlib sets `natDegree 0 = 0` and
`degree 0 = ⊥`.
-/
syntax (name := casExponentCommand) "#cas" "[" &"exponent" ident "]" term : command

elab_rules : command
  | `(#cas [collect $x:ident] $e:term) => Algebra.logCollect e x.getId e
  | `(#cas [coefficient $x:ident $k:num] $e:term) =>
      Algebra.logCoefficient e x.getId (.coefficient k.getNat) e
  | `(#cas [coefficientList $x:ident] $e:term) => Algebra.logCoefficient e x.getId .list e
  | `(#cas [exponent $x:ident] $e:term) => Algebra.logCoefficient e x.getId .exponent e

end CAS.Command
