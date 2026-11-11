/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Series
public import CAS.Command.ParamSystems
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Symbolic sums: `#cas [sum k a n]`

`#cas [sum k a n] f` with a natural lower bound `a` and an upper bound `n` gives the closed form
of `∑ k ∈ Finset.Icc a n, f k`, as Mathematica's `Sum[f, {k, a, n}]` does, for summands that are
sums of terms `c kʲ rᵏ` with rational `c` and `r` (polynomials, geometric terms, their products,
and their quotients by a geometric term, as in `k ^ 11 / 2 ^ k`). The closed form is the
antidifference: a polynomial of one degree more for `r = 1`, `rⁿ R (n)` with `R` of the same
degree otherwise. The theorem holds for every `n` (every `n ≥ a - 1` when `a ≥ 2`) and is proved
by induction on `n`, each step by `ring`, after quotients are written as products with inverses
when `ring` alone does not close it. A numeric upper
bound gives the value; for other summands with a numeric upper bound the value is computed
term by term and checked by `norm_num`. Telescoping rational summands and hypergeometric terms
(Gosper's algorithm) are not treated.
-/

public meta section

namespace CAS.Command.Sum

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Command.SpecialFunctions
open CAS.Verified.Expr
open CAS.Command.Algebra (Dense)

/-- `∑ rᵏ P_r (k)`. -/
abbrev GeoPoly := List (ℚ × Array ℚ)

/-- `a + b` when the terms of `a` have distinct `r`: the polynomials of equal `r` are added and
zero terms dropped. -/
def gAdd (a b : GeoPoly) : GeoPoly :=
  let merged := b.foldl (fun total (r, p) ↦
    match total.find? (·.1 == r) with
    | some (_, q) => total.filter (·.1 != r) ++ [(r, Dense.add q p)]
    | none => total ++ [(r, p)]) a
  merged.filter fun (_, p) ↦ p.any (· != 0)

/-- `c a`. -/
def gScale (c : ℚ) (a : GeoPoly) : GeoPoly := a.map fun (r, p) ↦ (r, p.map (c * ·))

/-- `a b`: the products `(r₁ r₂)ᵏ P₁ P₂` of all pairs of terms, summed by `gAdd`. -/
def gMul (a b : GeoPoly) : GeoPoly :=
  a.foldl (fun total (r₁, p₁) ↦
    b.foldl (fun total (r₂, p₂) ↦ gAdd total [(r₁ * r₂, Dense.mul p₁ p₂)]) total) []

/-- The constant `c` as `1ᵏ c`, and `[]` for `c = 0`. -/
def gConst (c : ℚ) : GeoPoly := if c = 0 then [] else [(1, #[c])]

/-- The constant of a `GeoPoly` without `rᵏ` or `k`. -/
def gConstant? (a : GeoPoly) : Option ℚ :=
  match a with
  | [] => some 0
  | [(r, p)] => if r = 1 && (List.range p.size).all (fun k ↦ k == 0 || p.getD k 0 == 0) then
      some (p.getD 0 0) else none
  | _ => none

/-- The summand as `∑ c kʲ rᵏ`. A quotient is by a constant, or, with `geometricQuotients`, by a
geometric term `c rᵏ`, as in `k ^ 11 / 2 ^ k`, which is `(1 / c) (1 / r)ᵏ` times the numerator. -/
partial def toGeoPoly (f : Verified.Expr (Fin 1)) (geometricQuotients : Bool := false) :
    Option GeoPoly :=
  let go (term : Verified.Expr (Fin 1)) := toGeoPoly term geometricQuotients
  match f with
  | .nat n => some (gConst n)
  | .int n => some (gConst n)
  | .rat p q => if q = 0 then none else some (gConst ((p : ℚ) / q))
  | .var _ => some [(1, #[0, 1])]
  | .add a b => return gAdd (← go a) (← go b)
  | .sub a b => return gAdd (← go a) (gScale (-1) (← go b))
  | .neg a => return gScale (-1) (← go a)
  | .mul a b => return gMul (← go a) (← go b)
  | .pow a n => do
      let base ← go a
      return (List.range n).foldl (fun total _ ↦ gMul total base) (gConst 1)
  | .div a b => do
      let denominator ← go b
      if let some c := gConstant? denominator then
        if c = 0 then none
        return gScale (1 / c) (← go a)
      unless geometricQuotients do none
      match denominator with
      | [(r, p)] =>
          let p := Dense.trim p
          if p.size == 1 && r != 0 then return gMul (← go a) [(1 / r, #[1 / p[0]!])] else none
      | _ => none
  | .rpow a (.var _) => do
      let r ← gConstant? (← go a)
      if r = 0 then none
      return [(r, #[1])]
  | _ => none

/-- The interpolating polynomial through `(0, v₀), (1, v₁), …`. -/
def interpolate (values : Array ℚ) : Array ℚ := Id.run do
  let m := values.size
  let mut result : Array ℚ := Array.replicate m 0
  for i in [0:m] do
    -- The Lagrange basis polynomial for the node `i`.
    let mut basis : Array ℚ := #[1]
    let mut denominator : ℚ := 1
    for j in [0:m] do
      if j == i then continue
      basis := Dense.mul basis #[-(j : ℚ), 1]
      denominator := denominator * ((i : ℚ) - j)
    result := Dense.add result (basis.map (· * values.getD i 0 / denominator))
  return result

/-- `R` with `R (n) - R (n - 1) / r = P (n)`, for `r ≠ 1`. -/
def geometricPart (r : ℚ) (P : Array ℚ) : Array ℚ := Id.run do
  let d := P.size
  -- `(n - 1) ^ j = ∑ i ≤ j, C(j, i) (-1) ^ (j - i) n ^ i`.
  let shift (j : Nat) : Array ℚ := (Array.range (j + 1)).map fun i ↦
    (Nat.choose j i : ℚ) * (if (j - i) % 2 == 0 then 1 else -1)
  let mut R : Array ℚ := Array.replicate d 0
  for offset in [0:d] do
    let j := d - 1 - offset
    -- The coefficient of `n ^ j` in `R (n) - R (n - 1) / r` from the known higher terms.
    let mut known : ℚ := 0
    for i in [j + 1:d] do
      known := known - R.getD i 0 / r * (shift i).getD j 0
    R := R.set! j ((P.getD j 0 - known) / (1 - 1 / r))
  return R

/-- The antidifference `F` with `F (n) - F (n - 1) = f (n)` and `F (a - 1) = 0`, as the list of
`(r, R)` with `F (n) = ∑ rⁿ R (n)`. -/
def antidifference (f : GeoPoly) (a : ℚ) : GeoPoly := Id.run do
  let mut total : GeoPoly := []
  for (r, P) in f do
    let R := if r = 1 then
        let values := (Array.range (P.size + 1)).map fun m ↦
          (List.range (m + 1)).foldl (fun s k ↦ s + Dense.eval P k) 0
        interpolate values
      else geometricPart r P
    total := gAdd total [(r, R)]
  -- The constant fixing `F (a - 1) = 0`.
  let at₀ := total.foldl (fun s (r, R) ↦ s + r ^ ((a - 1).floor.toNat) *
    (if a = 0 then 1 / r else 1) * Dense.eval R (a - 1)) 0
  -- For `a = 0`, `r ^ (a - 1) = 1 / r`.
  return gAdd total (gConst (-at₀))

/-- Rational roots of `cs` (coefficients, constant term first) with their multiplicities, and the
exact quotient of `cs` by their linear factors, in bounded time. The integers `j` with
`|j| ≤ 2 d + 64`, `d` the degree, that divide the constant term are tried first, which finds the
roots of the denominators of closed forms. The rest has no rational root when, for a prime `ℓ`
that does not divide its leading coefficient, it has no root modulo `ℓ`, since a rational root
`p / q` has `q` dividing the leading coefficient; the first 32 primes above its degree that do not
divide it are tried, and for the numerators of closed forms the first one already succeeds. A rest
of degree at most `16` that no prime proves root-free goes to `FullSimplify.rationalRoots`, whose
root isolation is slow only for many roots close together; a larger one is returned unfactored,
so that a rational root may be left in it. -/
def rationalRoots (cs : List ℚ) : List (ℚ × Nat) × List ℚ := Id.run do
  let mut current := Dense.trim cs.toArray
  if current.size ≤ 1 then return ([], current.toList)
  let zeros := (current.toList.takeWhile (· == 0)).length
  let mut roots : List (ℚ × Nat) := []
  if zeros > 0 then
    current := current.extract zeros current.size
    roots := [(0, zeros)]
  if current.size ≤ 1 then return (roots, current.toList)
  -- `scale · current` has integer coefficients, and so has its quotient by `k - r` for an
  -- integer root `r`.
  let scale : ℕ := current.foldl (fun l c ↦ Nat.lcm l c.den) 1
  let mut integral : Array ℤ := current.map fun c ↦ (c * (scale : ℚ)).num
  let horner (p : Array ℤ) (x : ℤ) : ℤ := p.foldr (fun c total ↦ c + x * total) 0
  let mut found : List (ℚ × Nat) := []
  for j in [1:2 * (current.size - 1) + 65] do
    for r in [(j : ℤ), -(j : ℤ)] do
      let mut count := 0
      while integral.size > 1 && integral[0]! % r == 0 && horner integral r == 0 do
        -- Synthetic division by `k - r`.
        let n := integral.size - 1
        let mut quotient : Array ℤ := Array.replicate n 0
        let mut carry : ℤ := 0
        for i' in [0:n] do
          let i := n - i'
          carry := integral[i]! + r * carry
          quotient := quotient.set! (i - 1) carry
        integral := quotient
        count := count + 1
      if count > 0 then found := found ++ [((r : ℚ), count)]
  let rest : Array ℚ := integral.map fun (c : ℤ) ↦ (c : ℚ) / scale
  let degree := integral.size - 1
  let lead := integral[degree]!
  let mut rootFree := degree == 0
  let mut tried := 0
  let mut ℓ := degree
  while !rootFree && tried < 32 do
    ℓ := ℓ + 1
    if ℓ < 2 || ℓ.minFac != ℓ || lead % (ℓ : ℤ) == 0 then continue
    tried := tried + 1
    let p := integral.map (· % (ℓ : ℤ))
    rootFree := (List.range ℓ).all fun x ↦
      p.foldr (fun c total ↦ (c + x * total) % (ℓ : ℤ)) 0 != 0
  let (more, rest) := if rootFree || degree > 16 then ([], rest.toList)
    else FullSimplify.rationalRoots rest.toList
  return (roots ++ (found ++ more).mergeSort (fun a b ↦ RootIsolation.rootBefore a.1 b.1), rest)

/-- A polynomial in `n`, factored over the rationals when it has rational roots. -/
def polyExpr (P : Array ℚ) : Verified.Expr (Fin 1) := Id.run do
  let trimmed := (P.toList.reverse.dropWhile (· == 0)).reverse
  if trimmed.isEmpty then return .nat 0
  if trimmed.length == 1 then return ratExpr (trimmed.head!)
  let (roots, rest) := rationalRoots trimmed
  let mut constant : ℚ := 1
  let mut factors : List (Verified.Expr (Fin 1)) := []
  for (root, multiplicity) in roots do
    -- `n - p / q = (q n - p) / q`.
    let q := root.den
    let p := root.num
    let linear : Verified.Expr (Fin 1) :=
      let scaled : Verified.Expr (Fin 1) := if q = 1 then .var 0 else .mul (.nat q) (.var 0)
      if p = 0 then scaled
      else if p < 0 then .add scaled (.nat p.natAbs) else .sub scaled (.nat p.natAbs)
    factors := factors ++ [if multiplicity = 1 then linear else .pow linear multiplicity]
    for _ in [0:multiplicity] do
      constant := constant / q
  -- The remaining factor with its leading coefficient.
  let restPoly : Array ℚ := rest.toArray
  let restLead := restPoly.getD (restPoly.size - 1) 1
  -- The remaining factor with coprime integer coefficients and a positive leading coefficient.
  let restScale := (restPoly.map (· / restLead)).foldl (fun l c ↦ Nat.lcm l c.den) 1
  constant := constant * restLead / restScale
  let restMonic := restPoly.map (· / restLead * restScale)
  if restMonic.size > 1 then
    let terms := (List.range restMonic.size).filterMap fun k ↦
      let c := restMonic.getD k 0
      if c == 0 then none else some (k, c)
    let restExpr := terms.foldl (fun (total : Option (Verified.Expr (Fin 1))) (k, c) ↦
      let power : Verified.Expr (Fin 1) := if k = 0 then .nat 1 else if k = 1 then .var 0
        else .pow (.var 0) k
      let term := if k = 0 then ratExpr c else if c = 1 then power else .mul (ratExpr c) power
      some (match total with
        | none => term
        | some t => .add t term)) none
    if let some factor := restExpr then factors := factors ++ [factor]
  let product := factors.foldl (fun (total : Option (Verified.Expr (Fin 1))) f ↦
    some (match total with
      | none => f
      | some t => .mul t f)) none
  let some body := product | return ratExpr constant
  if constant = 1 then return body
  if constant.num = 1 then return .div body (.nat constant.den)
  if constant.den = 1 then return .mul (ratExpr constant) body
  return .div (.mul (ratExpr constant.num) body) (.nat constant.den)

/-- The closed form `∑ rⁿ R (n)` as an expression in `n`: the geometric terms first, constant
coefficients with their signs pulled out. -/
def closedExpr (F : GeoPoly) : Verified.Expr (Fin 1) :=
  let constant? (R : Array ℚ) : Option ℚ :=
    if (List.range R.size).all (fun k ↦ k == 0 || R.getD k 0 == 0) then some (R.getD 0 0)
    else none
  let signed (c : ℚ) (body : Option (Verified.Expr (Fin 1))) : Bool × Verified.Expr (Fin 1) :=
    let magnitude := if c < 0 then -c else c
    match body with
    | none => (decide (c < 0), ratExpr magnitude)
    | some body =>
        (decide (c < 0), if magnitude = 1 then body else .mul (ratExpr magnitude) body)
  let geometric := F.filterMap fun (r, R) ↦
    if r = 1 || R.all (· == 0) then none else
    let power : Verified.Expr (Fin 1) := .rpow (ratExpr r) (.var 0)
    some (match constant? R with
      | some c => signed c (some power)
      | none => (false, .mul (polyExpr R) power))
  let polynomial := F.filterMap fun (r, R) ↦
    if r ≠ 1 || R.all (· == 0) then none else
    some (match constant? R with
      | some c => signed c none
      | none => (false, polyExpr R))
  match geometric ++ polynomial with
  | [] => .nat 0
  | (negative, first) :: rest =>
      rest.foldl (fun total (negative, term) ↦
          if negative then .sub total term else .add total term)
        (if negative then .neg first else first)

/-- The right side of `… = rhs` in a statement. -/
partial def equationRhs (e : Lean.Expr) : MetaM (Option String) := do
  match e.getAppFnArgs with
  | (``Eq, #[_, _, rhs]) => return some (← renderTerm rhs)
  | _ =>
      if e.isForall then forallTelescope e fun _ body ↦ equationRhs body
      else return none

/-- The summand `input` as an expression in the summation variable `k` alone: an error names any
other variable, since sums take no parameters. -/
def parseSummand (input : Syntax) (k : Name) : CommandElabM ReifiedExpr := do
  let others := (← parseWithLeading input [k]).names.filter (· != k)
  unless others.isEmpty do
    throwErrorAt input "sum: the summand may contain only the summation variable {renderName k}; \
      sums with parameters, here {renderNames others}, are not supported"
  parseExact input [k]

/-- Run `#cas [sum k a b] f`. -/
def logSum (ref : Syntax) (k : TSyntax `ident) (aStx bStx : Syntax) (input : Syntax) :
    CommandElabM Unit := do
  let a ← parseRational "sum" aStx
  unless a.den = 1 && 0 ≤ a do throwErrorAt aStx "sum: the lower bound must be a natural number"
  let aNat := a.num.toNat
  let reified ← parseSummand input k.getId
  let f : Verified.Expr (Fin 1) ← match reified with
    | ⟨[_], expression, _⟩ => pure expression
    | _ => throwErrorAt input "sum: the summand must be an expression in {k.getId}"
  let symbolic? : Option (TSyntax `ident) := match bStx with
    | `($n:ident) => some n
    | _ => none
  let geo := toGeoPoly f (geometricQuotients := true)
  let aLit : TSyntax `num := Syntax.mkNumLit (toString aNat)
  let lemmas := Series.seriesCleanLemmas ++ [``Real.rpow_natCast, ``Nat.cast_ofNat,
    ``Matrix.cons_val_zero, ``Int.cast_ofNat, ``Int.cast_neg, ``Nat.cast_id]
  let proof ← liftTermElabM do
    let fT ← exprToSyntax (← quoteVerifiedExpr f)
    let simpEval ← `(tactic| simp only [Verified.Expr.eval, Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Real.rpow_natCast, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero,
      Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero])
    let summand ← `(fun $k:ident : ℕ ↦ Verified.Expr.eval ![($k : ℝ)] $fT)
    match symbolic? with
    | some n =>
        let some g := geo | throwError "sum: the summand is not a sum of terms c k ^ j r ^ k \
            with rational c and r"
        let F := closedExpr (antidifference g a)
        let FT ← exprToSyntax (← quoteVerifiedExpr F)
        -- `ring` keeps `(1 / 2) ^ n` and the `2⁻¹ ^ n` of `1 / 2 ^ n` apart; written with
        -- inverses of powers, a quotient by a geometric term meets the closed form.
        let step ← `(tactic| first
          | ring1
          | (simp only [div_eq_mul_inv, one_mul, mul_pow, inv_pow]; ring))
        let nT : TSyntax `term := ⟨n.raw⟩
        let body ← `(∑ $k:ident ∈ Finset.Icc $aLit $nT, $summand $k =
          Verified.Expr.eval ![($nT : ℝ)] $FT)
        if aNat ≤ 1 then
          let statement ← `(∀ $n:ident : ℕ, $body)
          let proofStx ← `(by
            intro $n:ident
            induction $n:ident with
            | zero =>
                $simpEval:tactic
                norm_num
            | succ m ih =>
                rw [Finset.sum_Icc_succ_top (by omega), ih]
                $simpEval:tactic
                push_cast
                $step:tactic)
          elabCheckedProof "sum" statement proofStx
        else
          let base : TSyntax `num := Syntax.mkNumLit (toString (aNat - 1))
          let statement ← `(∀ $n:ident : ℕ, $base ≤ $nT → $body)
          let proofStx ← `(by
            intro $n:ident h
            induction $n:ident, h using Nat.le_induction with
            | base =>
                rw [Finset.Icc_eq_empty (by omega)]
                $simpEval:tactic
                norm_num
            | succ m hm ih =>
                rw [Finset.sum_Icc_succ_top (by omega), ih]
                $simpEval:tactic
                push_cast
                $step:tactic)
          elabCheckedProof "sum" statement proofStx
    | none =>
        let b ← liftCommandElabM (parseRational "sum" bStx)
        unless b.den = 1 && 0 ≤ b do throwError "sum: the upper bound must be a natural number"
        let bNat := b.num.toNat
        let bLit : TSyntax `num := Syntax.mkNumLit (toString bNat)
        -- The value, term by term.
        let some value := (List.range (bNat + 1)).foldl (fun (total : Option ℚ) j ↦ do
            if j < aNat then return ← total
            let t ← Series.derivativeAt f 0 (j : ℚ)
            return (← total) + t) (some 0)
          | throwError "sum: the terms are not exact rational numbers"
        unless bNat + 1 - aNat ≤ 200 do
          throwError "sum: numeric sums are checked term by term, for at most 200 terms"
        let vT ← `(($(← ratSyntax value) : ℝ))
        let statement ← `(∑ $k:ident ∈ Finset.Icc ($aLit : ℕ) $bLit, $summand $k = $vT)
        let proofStx ← `(by
          $simpEval:tactic
          norm_num [Finset.sum_Icc_succ_top])
        elabCheckedProof "sum" statement proofStx
  let proof ← liftTermElabM do
    let cleaned ← Digits.cleanProof proof lemmas [``Verified.Expr.univariateEval]
      (simprocs := true)
    let cleaned ← Digits.evaluateNumerals cleaned
    let named := Digits.restoreNames (← inferType proof) (← inferType cleaned)
    let cleaned ← mkExpectedTypeHint cleaned named
    CAS.Tactic.Explanation.kernelCheckedProof "sum" named cleaned
  let report ← liftTermElabM do
    evidenceReportMessage
      #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
        (if symbolic?.isSome then "Closed form for every upper bound" else "Value of the sum")
        proof]
  let answer ← liftTermElabM do
    let some rhs ← equationRhs (← inferType proof) | pure "see the statement"
    pure s!"{rhs}"
  logReport ref {
    domain := s!"{k.getId} ∈ [{aNat}, {surfaceText bStx}]"
    input := reified.render
    inputType := "summand"
    output := answer
    outputType := if symbolic?.isSome then "closed form" else "exact value"
  } #[report]

end CAS.Command.Sum

namespace CAS.Command

open Lean Elab Command

/-- `#cas [sum k a b] e` sums `e` for `k` from the natural number `a` to `b`, in closed form when
`b` is a variable and by its exact value when `b` is a numeral.

## Theorem
For a variable upper bound `n` and the printed closed form `F`, the report proves
`∀ n : ℕ, ∑ k ∈ Finset.Icc a n, e = F` by induction on `n`, and
`∀ n : ℕ, a - 1 ≤ n → ∑ k ∈ Finset.Icc a n, e = F` when `a ≥ 2`. For a numeral `b` it proves
`∑ k ∈ Finset.Icc a b, e = v` with the exact rational `v`.

## Conditions and limits
A closed form is found for sums of terms `c * k ^ j * r ^ k` with rational `c` and `r`
(polynomials, geometric terms and their products, also divided by a geometric term, as in
`k ^ 11 / 2 ^ k`), and by Gosper's algorithm for hypergeometric terms `c ^ k * R k` with a
rational function `R` and a rational `c > 0`, such as the telescoping
`1 / (k * (k + 1))`. A summand that is undefined in the range is refused. A numeral upper bound
sums at most 200 terms one by one, and each term must be an exact rational number.
`#cas [sum k a ∞] e` sums a series.

## Options
None.

## Examples
```lean
#cas [sum k 1 n] (k^2)
```
```output
Output (closed form): n*(n + 1)*(2*n + 1)/6
```
```lean
#cas [sum k 1 n] (1 / (k * (k + 1)))
```
```output
Output (closed form (Gosper)): n/(n + 1)
```
```lean
#cas [sum k 1 ∞] (1/k^2)
```
```output
Output (sum of the series (ζ value)): pi^2/6
```

## In a proof
```lean
theorem sum_squares :
    ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, (k : ℝ) ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  cas
```

## See also
Mathematica `Sum`, SymPy `summation`. The modes `product` and `rsolve`, the call `zeta s`, and
the tactic `cas`, which proves the closed forms of finite sums. Oracle route:
`#cas [sum k a n, oracle := sympy] e`, which proves the oracle's closed form by induction.

## Possible issues
```lean
#cas [sum k 1 n] (1 / k)
```
```output
sum: Gosper's algorithm finds no closed form in hypergeometric terms for this summand
```
The harmonic numbers have no closed form in hypergeometric terms. A numeral upper bound gives the
exact value:
```lean
#cas [sum k 1 10] (1 / k)
```
```output
Output (exact value): 7381/2520
```
```lean
#cas [sum k 1 n] (sin k)
```
```output
sum: the summand is not a sum of terms c k ^ j r ^ k with rational c and r
```
The closed forms cover polynomial, geometric and hypergeometric terms only.
-/
syntax (name := casSumCommand) "#cas" "[" &"sum" ident term:max term:max "]" term : command

elab_rules : command
  | `(#cas [sum $k:ident $a:term $b:term] $f:term) => Sum.logSum f k a b f

end CAS.Command
