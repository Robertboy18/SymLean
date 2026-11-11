/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.ExpPolynomials
public meta import CAS.Command.ExpPolynomials
public import CAS.Calculus.FourierProduct
public meta import CAS.Calculus.FourierProduct
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Fourier coefficients on `[-π, π]`, and sine and cosine series on `[0, L]`

`#cas [fourier x n] f` gives the Fourier coefficients of `f` on `[-π, π]`,
`a₀ = 1/π ∫ f`, `aₙ = 1/π ∫ f (x) cos (n x)` and `bₙ = 1/π ∫ f (x) sin (n x)` for `n ≥ 1`, of the
series `a₀ / 2 + ∑ (aₙ cos (n x) + bₙ sin (n x))`, as exact functions of `n`, and proves the three
equations. The function is a sum of products of polynomials, exponentials `e ^ (a x)` with
rational `a`, sines and cosines with integer frequencies, such as `x sin x`, `x ^ 2 e ^ x` or
`sin x ^ 3 cos (2 x)`. When a term `c xʲ cos (k x)` or `c xʲ sin (k x)` has `k ≥ 1`, the
coefficients at `n = k` come out separately, as an `if`, unless the formula for general `n`
gives them too. When the proof of the coefficients fails, for instance at the heartbeat limit,
the command refuses with an error.

`#cas [fourierSin x n L] f` and `#cas [fourierCos x n L] f` give the coefficients of the sine
series `∑ bₙ sin (n π x / L)` and the cosine series `a₀ / 2 + ∑ aₙ cos (n π x / L)` of `f` on
`[0, L]`, `bₙ = 2 / L ∫_0^L f (x) sin (n π x / L)`, `aₙ = 2 / L ∫_0^L f (x) cos (n π x / L)`, for
`f` a sum of terms `c xʲ e ^ (a x)` and `L` a positive rational number or a positive rational
multiple of `π`.

## Implementation notes

The integrals are proved in `CAS/Calculus/FourierProduct.lean` by integration by parts through
the primitives `CAS.ExpTrig.primPair` of `CAS/Calculus/ExpTrigPrimitive.lean`: the recursion
`sym` gives them on `[-π, π]` and `half` on `[0, L]`. We compute the closed forms by running the
same recursions in meta code (`symP`, `halfP`) on polynomials in `n`, `π`, `(-1) ^ n` and the
values `sinh (a π)`, `cosh (a π)` or `e ^ (a L)`, with the sparse `Poly` and `FactoredFraction`
arithmetic defined here. These results are only printed; the kernel checks every equation.

For `#cas [fourier x n] f`, `toExpPoly` of `CAS/Command/ExpPolynomials.lean` gives the
exponential polynomial of `f`, and `productTerms` its terms `c xʲ e ^ (a x) cos (k x)` and
`c xʲ e ^ (a x) sin (k x)`. The proof first checks with `ring_nf` that the terms add up to `f`,
after `cos (k x)` and `sin (k x)` are written as polynomials in `cos x` and `sin x`
(`CAS.Fourier.multipleAngle`) and the powers of `sin x` are reduced by the instances of
`CAS.Fourier.sin_pow_add_two` up to the degree of `f` (`decomposition`). Then
`CAS.FourierProduct.fourier_of_eq` gives the three equations, with the closed forms
`CAS.FourierProduct.cosCoeff_cosT`, `CAS.FourierProduct.mean_cosT`, ... for the terms
`c cos (k x)` and `c sin (k x)`, and each equation is closed by unfolding the recursions, then
`field_simp` and `ring`; a special frequency `n = k` is a separate case (`by_cases`). On
`[0, L]` the terms come from `toExpPolySum` and the equations from
`CAS.FourierProduct.half_of_eq`, with `Real.sin_nat_mul_pi` and `Real.cos_nat_mul_pi` for the
frequency `n π / L`. Integration by parts and the multiple-angle formulas are classical; the
mirrored recursions, the case split and the decomposition check are ours.
-/

public meta section

namespace CAS.Command.FourierProductCmd

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Command.SpecialFunctions
open CAS.Command.ExpPolynomials
open CAS.Verified.Expr
open CAS.FourierProduct (PTerm HTerm)

/-! ## Polynomials and rational functions over `ℚ` -/

/-- Exponents of the variables `0, 1, …`, without trailing zeros. -/
abbrev Mono := List Nat

/-- The monomial without its trailing zero exponents. -/
def monoTrim (m : Mono) : Mono := (m.reverse.dropWhile (· == 0)).reverse

/-- The product of two monomials, exponents added. -/
def monoMul : Mono → Mono → Mono
  | [], b => b
  | a, [] => a
  | x :: a, y :: b => (x + y) :: monoMul a b

/-- The lexicographic order, variable `0` first. -/
partial def monoCmp : Mono → Mono → Ordering
  | [], [] => .eq
  | [], y :: b => if y > 0 then .lt else monoCmp [] b
  | x :: a, [] => if x > 0 then .gt else monoCmp a []
  | x :: a, y :: b => if x < y then .lt else if y < x then .gt else monoCmp a b

/-- `a / b` when `b` divides `a`. -/
partial def monoDiv? : Mono → Mono → Option Mono
  | a, [] => some a
  | [], y :: b => if y == 0 then monoDiv? [] b else none
  | x :: a, y :: b => if y ≤ x then (fun r ↦ (x - y) :: r) <$> monoDiv? a b else none

/-- A polynomial, its monomials in decreasing order with nonzero coefficients. -/
abbrev Poly := List (Mono × ℚ)

/-- The normal form of `p`: monomials trimmed and sorted in decreasing order (`monoCmp`),
equal monomials merged and zero coefficients dropped. -/
def pNorm (p : Poly) : Poly := Id.run do
  let sorted := (p.map fun (m, c) ↦ (monoTrim m, c)).mergeSort
    fun x y ↦ monoCmp x.1 y.1 != .lt
  let mut out : Array (Mono × ℚ) := #[]
  for (m, c) in sorted do
    match out.back? with
    | some (m', c') =>
        if m' == m then out := out.pop.push (m, c + c') else out := out.push (m, c)
    | none => out := out.push (m, c)
  return out.toList.filter fun (_, c) ↦ c != 0

/-- The constant polynomial `c`. -/
def pConst (c : ℚ) : Poly := if c == 0 then [] else [([], c)]
/-- The variable `i`. -/
def pVar (i : Nat) : Poly := [(List.replicate i 0 ++ [1], 1)]
/-- `p + q`, in normal form. -/
def pAdd (p q : Poly) : Poly := pNorm (p ++ q)
/-- `c p`. -/
def pScale (c : ℚ) (p : Poly) : Poly := if c == 0 then [] else p.map fun (m, d) ↦ (m, c * d)
/-- `-p`. -/
def pNeg (p : Poly) : Poly := pScale (-1) p
/-- `p - q`, in normal form. -/
def pSub (p q : Poly) : Poly := pAdd p (pNeg q)
/-- `p q`, in normal form. -/
def pMul (p q : Poly) : Poly :=
  pNorm (p.flatMap fun (m, c) ↦ q.map fun (m', d) ↦ (monoMul m m', c * d))
/-- `p ^ k`. -/
def pPow (p : Poly) : Nat → Poly
  | 0 => pConst 1
  | k + 1 => pMul p (pPow p k)
/-- `some c` when the normal form `p` is the constant `c` (`some 0` for `[]`), else `none`. -/
def pConst? (p : Poly) : Option ℚ :=
  match p with
  | [] => some 0
  | [([], c)] => some c
  | _ => none

/-- `p / f` when `f` divides `p`, by division with the leading terms. Each step adds one term to
the quotient, and the quotient of an exact division has degree at most `deg_i p` in each variable
`i`, so `∏ (deg_i p + 1)` steps suffice. -/
def pDiv? (p f : Poly) : Option Poly := Id.run do
  let some (fm, fc) := f.head? | return none
  let width := p.foldl (fun w (m, _) ↦ max w m.length) 0
  let steps := (List.range width).foldl
    (fun acc i ↦ acc * (p.foldl (fun d (m, _) ↦ max d (m.getD i 0)) 0 + 1)) 1
  let mut rest := p
  let mut quotient : Poly := []
  for _ in [0:steps] do
    match rest.head? with
    | none => return some quotient
    | some (m, c) =>
        match monoDiv? m fm with
        | none => return none
        | some d =>
            let t : Poly := [(monoTrim d, c / fc)]
            rest := pSub rest (pMul t f)
            quotient := pAdd quotient t
  return if rest.isEmpty then some quotient else none

/-- A factor `b` (`a2 = 0`) or `b ^ 2 + a2` of a denominator. -/
structure Fac where
  /-- The factor as a polynomial, `b` or `b ^ 2 + a2` expanded; factors are compared by it. -/
  poly : Poly
  /-- The polynomial `b`. -/
  base : Poly
  /-- The constant `a2`, `0` for the factor `b`. -/
  a2 : ℚ

/-- `num / ∏ fᵢ ^ mᵢ`. -/
structure FactoredFraction where
  /-- The numerator `num`. -/
  num : Poly
  /-- The factors `fᵢ` of the denominator with their exponents `mᵢ`. -/
  den : List (Fac × Nat)

/-- `p` as a fraction with denominator `1`. -/
def FactoredFraction.ofPoly (p : Poly) : FactoredFraction := ⟨p, []⟩

/-- The exponent of `f` in `den`, factors compared by `Fac.poly`; `0` when `f` does not
occur. -/
def multOf (den : List (Fac × Nat)) (f : Fac) : Nat :=
  ((den.find? (·.1.poly == f.poly)).map (·.2)).getD 0

/-- `a + b`, not reduced, over the denominator that takes every factor of `a` or `b` with the
larger of its two multiplicities; factors are compared as written. -/
def FactoredFraction.add (a b : FactoredFraction) : FactoredFraction := Id.run do
  if a.num.isEmpty then return b
  if b.num.isEmpty then return a
  let mut lcm := a.den
  for (f, m) in b.den do
    let m' := multOf lcm f
    if m' == 0 then lcm := lcm ++ [(f, m)]
    else if m' < m then lcm := lcm.map fun (g, k) ↦ if g.poly == f.poly then (g, m) else (g, k)
  let missing (d : List (Fac × Nat)) : Poly :=
    lcm.foldl (fun acc (f, m) ↦ pMul acc (pPow f.poly (m - multOf d f))) (pConst 1)
  return ⟨pAdd (pMul a.num (missing a.den)) (pMul b.num (missing b.den)), lcm⟩

/-- `c a`. -/
def FactoredFraction.scale (c : ℚ) (a : FactoredFraction) : FactoredFraction :=
  ⟨pScale c a.num, a.den⟩
/-- `a - b`, not reduced. -/
def FactoredFraction.sub (a b : FactoredFraction) : FactoredFraction := a.add (b.scale (-1))
/-- `p a`, the denominator kept. -/
def FactoredFraction.mulPoly (p : Poly) (a : FactoredFraction) : FactoredFraction :=
  ⟨pMul p a.num, a.den⟩

/-- Division by the factor `f`; a constant factor is a scaling. -/
def FactoredFraction.divBy (a : FactoredFraction) (f : Fac) : FactoredFraction :=
  match pConst? f.poly with
  | some c => a.scale (1 / c)
  | none =>
      if multOf a.den f == 0 then ⟨a.num, a.den ++ [(f, 1)]⟩
      else ⟨a.num, a.den.map fun (g, k) ↦ if g.poly == f.poly then (g, k + 1) else (g, k)⟩

/-- Cancel the factors of the denominator that divide the numerator. -/
def FactoredFraction.reduce (r : FactoredFraction) : FactoredFraction := Id.run do
  if r.num.isEmpty then return ⟨[], []⟩
  let mut num := r.num
  let mut den : List (Fac × Nat) := []
  for (f, m) in r.den do
    let mut k := m
    for _ in [0:m] do
      match pDiv? num f.poly with
      | some q =>
          num := q
          k := k - 1
      | none => break
    if k > 0 then den := den ++ [(f, k)]
  return ⟨num, den⟩

/-- The denominator `∏ fᵢ ^ mᵢ` expanded as a polynomial. -/
def denPoly (den : List (Fac × Nat)) : Poly :=
  den.foldl (fun acc (f, m) ↦ pMul acc (pPow f.poly m)) (pConst 1)

/-- `p` at `n = m`: the variable `0` (`n`) replaced by `m` and the variable `2` (`(-1) ^ n`) by
`(-1) ^ m`. -/
def pSubstN (p : Poly) (m : Nat) : Poly :=
  pNorm (p.map fun (mono, c) ↦
    let e0 := mono.getD 0 0
    let e2 := mono.getD 2 0
    (((mono.set 0 0).set 2 0), c * (m : ℚ) ^ e0 * (-1 : ℚ) ^ (m * e2)))

/-- Whether `r` at `n = m` is defined and equal to `s`. -/
def FactoredFraction.agreesAt (r s : FactoredFraction) (m : Nat) : Bool :=
  let den := r.den.map fun (f, k) ↦ (pPow (pSubstN f.poly m) k)
  if den.any (·.isEmpty) then false else
  let rDen := den.foldl pMul (pConst 1)
  (pSub (pMul (pSubstN r.num m) (denPoly s.den)) (pMul s.num rDen)).isEmpty

/-! ## The recursions -/

/-- Division by `a ^ 2 + b ^ 2`, kept as `b · b` when `a = 0`. -/
def divByD (a : ℚ) (b : Poly) (r : FactoredFraction) : FactoredFraction :=
  if a == 0 then
    match b with
    | [(m, c)] =>
        -- A monomial `c ∏ vᵢ ^ eᵢ`: divide by `c ^ 2` and by each variable.
        (List.range m.length).foldl (fun r i ↦
          (List.range (2 * m.getD i 0)).foldl (fun r _ ↦ r.divBy ⟨pVar i, pVar i, 0⟩) r)
          (r.scale (1 / (c * c)))
    | _ => (r.divBy ⟨b, b, 0⟩).divBy ⟨b, b, 0⟩
  else r.divBy ⟨pAdd (pMul b b) (pConst (a * a)), b, a * a⟩

/-- `CAS.FourierProduct.sym` with `wall a j = W j`. -/
def symP (W : Nat → Poly) (a : ℚ) (b σ : Poly) : Nat → FactoredFraction × FactoredFraction
  | 0 =>
      ((divByD a b (.ofPoly (pScale a (pMul σ (W 0))))).reduce,
        (divByD a b (.ofPoly (pNeg (pMul b (pMul σ (W 0)))))).reduce)
  | j + 1 =>
      let (I, J) := symP W a b σ j
      let w := W (j + 1)
      let c1 := (FactoredFraction.ofPoly (pScale a (pMul σ w))).add
        (((I.scale a).add (J.mulPoly b)).scale (-(j + 1 : ℚ)))
      let c2 := (FactoredFraction.ofPoly (pNeg (pMul b (pMul σ w)))).add
        (((J.scale a).sub (I.mulPoly b)).scale (-(j + 1 : ℚ)))
      ((divByD a b c1).reduce, (divByD a b c2).reduce)

/-- `CAS.FourierProduct.half` with `L ^ j = Lp ^ j` and `e ^ (a L) = E`. -/
def halfP (Lp E : Poly) (a : ℚ) (b σ : Poly) : Nat → FactoredFraction × FactoredFraction
  | 0 =>
      ((divByD a b (.ofPoly (pSub (pScale a (pMul σ E)) (pConst a)))).reduce,
        (divByD a b (.ofPoly (pSub b (pMul b (pMul σ E))))).reduce)
  | j + 1 =>
      let (I, J) := halfP Lp E a b σ j
      let w := pMul (pPow Lp (j + 1)) E
      let c1 := (FactoredFraction.ofPoly (pScale a (pMul σ w))).add
        (((I.scale a).add (J.mulPoly b)).scale (-(j + 1 : ℚ)))
      let c2 := (FactoredFraction.ofPoly (pNeg (pMul b (pMul σ w)))).add
        (((J.scale a).sub (I.mulPoly b)).scale (-(j + 1 : ℚ)))
      ((divByD a b c1).reduce, (divByD a b c2).reduce)

/-- The variables: `n` is `0`, `π` is `1`, `(-1) ^ n` is `2`, the values of `sinh`, `cosh` or
`exp` follow. -/
def piV : Poly := pVar 1

/-- `∫_{-π}^{π} xʲ`. -/
def polyMeanP (j : Nat) : Poly :=
  if j % 2 == 0 then pScale (2 / (j + 1 : ℚ)) (pPow piV (j + 1)) else []

/-- Where `n` is a variable or a number. -/
structure Ctx where
  /-- `n`: the variable `0`, or a constant. -/
  nP : Poly
  /-- `(-1) ^ n`: the variable `2`, or the constant `(-1) ^ m` when `n = m`. -/
  σ : Poly
  /-- The indices of `sinh (|a| π)` and `cosh (|a| π)`. -/
  atom : ℚ → Nat × Nat

/-- `CAS.FourierProduct.wall a j`, with `e ^ (± a π)` in the variables `ctx.atom |a|`
for `sinh (|a| π)` and `cosh (|a| π)`. -/
def wallP (ctx : Ctx) (a : ℚ) (j : Nat) : Poly :=
  let piJ := pPow piV j
  if a == 0 then (if j % 2 == 1 then pScale 2 piJ else [])
  else
    let (iS, iC) := ctx.atom (if a < 0 then -a else a)
    let sgn : ℚ := if a < 0 then -1 else 1
    let ep := pAdd (pVar iC) (pScale sgn (pVar iS))
    let em := pSub (pVar iC) (pScale sgn (pVar iS))
    pSub (pMul piJ ep) (pScale ((-1) ^ j) (pMul piJ em))

/-- `CAS.FourierProduct.low a j n k`, `n` from `ctx`. -/
def lowP (ctx : Ctx) (a : ℚ) (j k : Nat) : FactoredFraction × FactoredFraction :=
  let b := pSub ctx.nP (pConst k)
  if a == 0 && b.isEmpty then (.ofPoly (polyMeanP j), .ofPoly [])
  else symP (wallP ctx a) a b (pScale ((-1) ^ k) ctx.σ) j

/-- `CAS.FourierProduct.high a j n k`, `n` from `ctx`. -/
def highP (ctx : Ctx) (a : ℚ) (j k : Nat) : FactoredFraction × FactoredFraction :=
  let b := pAdd ctx.nP (pConst k)
  if a == 0 && b.isEmpty then (.ofPoly (polyMeanP j), .ofPoly [])
  else symP (wallP ctx a) a b (pScale ((-1) ^ k) ctx.σ) j

/-- `CAS.FourierProduct.PTerm.mean` of the term, for `ctx` with `n = 0`. -/
def meanP (ctx : Ctx) : PTerm → FactoredFraction
  | .cosT c j a k => (highP ctx a j k).1.scale c
  | .sinT c j a k => (highP ctx a j k).2.scale c

/-- `CAS.FourierProduct.PTerm.cosCoeff n` of the term, `n` from `ctx`. -/
def cosP (ctx : Ctx) : PTerm → FactoredFraction
  | .cosT c j a k => ((lowP ctx a j k).1.add (highP ctx a j k).1).scale (c / 2)
  | .sinT c j a k => ((highP ctx a j k).2.sub (lowP ctx a j k).2).scale (c / 2)

/-- `CAS.FourierProduct.PTerm.sinCoeff n` of the term, `n` from `ctx`. -/
def sinP (ctx : Ctx) : PTerm → FactoredFraction
  | .cosT c j a k => ((highP ctx a j k).2.add (lowP ctx a j k).2).scale (c / 2)
  | .sinT c j a k => ((lowP ctx a j k).1.sub (highP ctx a j k).1).scale (c / 2)

/-- The sum of the fractions, reduced. -/
def sumFactoredFractions (xs : List FactoredFraction) : FactoredFraction :=
  (xs.foldl FactoredFraction.add (.ofPoly [])).reduce

/-! ## Printing -/

/-- `∏ varsᵢ ^ eᵢ` for the monomial, `none` for the monomial `1`. -/
def monoSyntax (vars : Array (TSyntax `term)) (m : Mono) :
    TermElabM (Option (TSyntax `term)) := do
  let mut out : Option (TSyntax `term) := none
  for i in [0:m.length] do
    let e := m[i]!
    if e == 0 then continue
    let v := vars[i]!
    let f ← if e == 1 then pure v else `($v ^ $(Syntax.mkNumLit (toString e)))
    out := some (← match out with
      | none => pure f
      | some o => `($o * $f))
  return out

/-- The polynomial as a real term in `vars`, `(0 : ℝ)` for the zero polynomial. -/
def polySyntax (vars : Array (TSyntax `term)) (p : Poly) : TermElabM (TSyntax `term) := do
  let mut out : Option (TSyntax `term) := none
  for (m, c) in p do
    let mag := if c < 0 then -c else c
    let body ← match ← monoSyntax vars m with
      | none => real mag
      | some ms => if mag == 1 then pure ms else `($(← real mag) * $ms)
    out := some (← match out with
      | none => if c < 0 then `(-$body) else pure body
      | some o => if c < 0 then `($o - $body) else `($o + $body))
  match out with
  | some t => return t
  | none => `((0 : ℝ))

/-- The monomials in printing order: those without the variables from `2` on first, then the
others in decreasing order. -/
def printOrder (p : Poly) : Poly :=
  let plain (m : Mono) : Bool := (m.drop 2).all (· == 0)
  p.filter (plain ·.1) ++ p.filter (!plain ·.1)

/-- The numerator with the monomials grouped by the variables from `2` on. -/
def groupedSyntax (vars : Array (TSyntax `term)) (p : Poly) : TermElabM (TSyntax `term) := do
  let mut groups : List (Mono × Poly) := []
  for (m, c) in printOrder p do
    let inner := monoTrim (m.take 2)
    let outer := monoTrim (List.replicate 2 0 ++ m.drop 2)
    groups := if groups.any (·.1 == outer) then
        groups.map fun (o, q) ↦ if o == outer then (o, q ++ [(inner, c)]) else (o, q)
      else groups ++ [(outer, [(inner, c)])]
  let mut out : Option (TSyntax `term) := none
  for (outer, q) in groups do
    let q := pNorm q
    let negative := q.length == 1 && (q.head?.map fun (_, c) ↦ decide (c < 0)).getD false
    let q := if negative then pNeg q else q
    let coeff ← polySyntax vars q
    let term ← match ← monoSyntax vars outer with
      | none => pure coeff
      | some a => if q == pConst 1 then pure a else `($coeff * $a)
    out := some (← match out with
      | none => if negative then `(-$term) else pure term
      | some o => if negative then `($o - $term) else `($o + $term))
  match out with
  | some t => return t
  | none => `((0 : ℝ))

/-- The factor as a term `b` or `b ^ 2 + a2`. -/
def facSyntax (vars : Array (TSyntax `term)) (f : Fac) : TermElabM (TSyntax `term) := do
  let b ← polySyntax vars f.base
  if f.a2 == 0 then return b
  `($b ^ 2 + $(← real f.a2))

/-- The greatest common divisor `gcd (p, r) / lcm (q, s)` of `a = p / q` and `b = r / s`. -/
def ratGcd (a b : ℚ) : ℚ :=
  (Nat.gcd a.num.natAbs b.num.natAbs : ℚ) / (Nat.lcm a.den b.den : ℚ)

/-- `num / den` with the content and a common factor `(-1) ^ n` in front. -/
def factoredFractionSyntax (vars : Array (TSyntax `term)) (n : TSyntax `term)
    (r : FactoredFraction) : TermElabM (TSyntax `term) := do
  if r.num.isEmpty then return ← `((0 : ℝ))
  -- A common factor `(-1) ^ n`.
  let σPower (m : Mono) : Nat := m.getD 2 0
  let common := r.num.all fun (m, _) ↦ σPower m == 1
  let num := if common then pNorm (r.num.map fun (m, c) ↦ (m.set 2 0, c)) else r.num
  -- More negative than positive coefficients, or as many and a negative first one.
  let negatives := (num.filter fun (_, c) ↦ c < 0).length
  let positives := num.length - negatives
  let negative := negatives > positives || (negatives == positives &&
    ((printOrder num).head?.map fun (_, c) ↦ decide (c < 0)).getD false)
  let num := if negative then pNeg num else num
  let content := num.foldl (fun g (_, c) ↦ if g == 0 then (if c < 0 then -c else c)
    else ratGcd g c) 0
  let num := pScale (1 / content) num
  -- A common power of `n` and of `π` when there are several terms.
  let low (i : Nat) : Nat :=
    num.foldl (fun k (m, _) ↦ min k (m.getD i 0)) ((num.head?.map (·.1.getD i 0)).getD 0)
  let g : Mono := if num.length ≤ 1 then [] else monoTrim [low 0, low 1]
  let num := if g.isEmpty then num else
    num.map fun (m, c) ↦ (monoTrim ((List.range m.length).map fun i ↦
      m.getD i 0 - g.getD i 0), c)
  let mut factors : Array (TSyntax `term) := #[]
  if content != 1 then factors := factors.push (← real content)
  if common then
    factors := factors.push (← if negative then `((-1 : ℝ) ^ ($n + 1)) else `((-1 : ℝ) ^ $n))
  if let some gT ← monoSyntax vars g then factors := factors.push gT
  if num != pConst 1 then factors := factors.push (← groupedSyntax vars num)
  let mut top ← match factors.toList with
    | [] => `((1 : ℝ))
    | t :: rest => rest.foldlM (fun acc u ↦ `($acc * $u)) t
  if negative && !common then top ← `(-$top)
  let facs := r.den.filter (·.2 > 0)
  let facs := facs.filter (fun (f, _) ↦ f.poly.length == 1) ++
    facs.filter (fun (f, _) ↦ f.poly.length != 1)
  let mut den : Option (TSyntax `term) := none
  for (f, m) in facs do
    let fT ← facSyntax vars f
    let fT ← if m == 1 then pure fT else `($fT ^ $(Syntax.mkNumLit (toString m)))
    den := some (← match den with
      | none => pure fT
      | some d => `($d * $fT))
  match den with
  | none => return top
  | some d => `($top / $d)

/-! ## Terms -/

/-- The terms `c xʲ e ^ (a x) cos (k x)`, `c xʲ e ^ (a x) sin (k x)` of `f`; `k` is a rational
frequency, an integer on `[-π, π]`. -/
def productTerms (f : ExpPoly) : Except String (List (ℚ × Nat × ℚ × ℚ × Bool)) := do
  let mut real : List (ℚ × Nat × ℚ × ℚ × Bool) := []
  -- `(α, β, j) ↦ (p, q)`, the coefficients of `xʲ e ^ ((α ± i β) x)`.
  let mut pairs : List ((ℚ × ℚ × Nat) × GaussianRat × GaussianRat) := []
  for (l, P) in f do
    for j in [0:P.size] do
      let c := P.getD j default
      if c.re == 0 && c.im == 0 then continue
      if l.im == 0 then
        unless c.im == 0 do throw "unexpected complex coefficient"
        real := real ++ [(c.re, j, l.re, 0, false)]
      else
        let β := if l.im < 0 then -l.im else l.im
        let key := (l.re, β, j)
        let (p, q) : GaussianRat × GaussianRat := if l.im > 0 then (c, default) else (default, c)
        pairs := if pairs.any (·.1 == key) then
            pairs.map fun (k, p', q') ↦ if k == key then (k, p' + p, q' + q) else (k, p', q')
          else pairs ++ [(key, p, q)]
  let mut out := real
  for ((α, β, j), p, q) in pairs do
    -- `p e ^ (i β x) + q e ^ (-i β x) = (p + q) cos (β x) + i (p - q) sin (β x)`.
    let cc := p + q
    let ss : GaussianRat := ⟨-(p.im - q.im), p.re - q.re⟩
    unless cc.im == 0 && ss.im == 0 do throw "unexpected complex coefficient"
    if cc.re != 0 then out := out ++ [(cc.re, j, α, β, false)]
    if ss.re != 0 then out := out ++ [(ss.re, j, α, β, true)]
  return out

/-- The term as syntax `FourierProduct.PTerm.cosT c j a k` or
`FourierProduct.PTerm.sinT c j a k`. -/
def pTermSyntax : PTerm → TermElabM (TSyntax `term)
  | .cosT c j a k => do
      `(FourierProduct.PTerm.cosT $(← ratSyntax c) $(Syntax.mkNumLit (toString j))
        $(← ratSyntax a) $(Syntax.mkNumLit (toString k)))
  | .sinT c j a k => do
      `(FourierProduct.PTerm.sinT $(← ratSyntax c) $(Syntax.mkNumLit (toString j))
        $(← ratSyntax a) $(Syntax.mkNumLit (toString k)))

/-- The term as syntax `FourierProduct.HTerm.mk c p j a`. -/
def hTermSyntax (t : HTerm) : TermElabM (TSyntax `term) := do
  `(FourierProduct.HTerm.mk $(← ratSyntax t.c) $(Syntax.mkNumLit (toString t.p))
    $(Syntax.mkNumLit (toString t.j)) $(← ratSyntax t.a))

/-- Sums `∑ c πᵖ xʲ e ^ (a x)`, as `((j, a, p), c)`. -/
abbrev ExpPolySum := List ((Nat × ℚ × Nat) × ℚ)

/-- Terms with the same `(j, a, p)` merged, in order of first appearance, and zero
coefficients dropped. -/
def ExpPolySum.normalize (f : ExpPolySum) : ExpPolySum := Id.run do
  let mut out : ExpPolySum := []
  for (k, c) in f do
    out := if out.any (·.1 == k) then out.map fun (k', c') ↦ if k' == k then (k', c' + c)
      else (k', c') else out ++ [(k, c)]
  return out.filter (·.2 != 0)

/-- The product of two sums, normalized. -/
def ExpPolySum.mul (f g : ExpPolySum) : ExpPolySum :=
  ExpPolySum.normalize (f.flatMap fun ((j, a, p), c) ↦ g.map fun ((j', a', p'), c') ↦
    ((j + j', a + a', p + p'), c * c'))

/-- The constant `c`, the single term `((0, 0, 0), c)`. -/
def ExpPolySum.const (c : ℚ) : ExpPolySum := [((0, 0, 0), c)]

/-- The expression as a sum `∑ c πᵖ xʲ e ^ (a x)`, or `none`; division only by a rational
constant, `exp` only of `r x`. -/
partial def toExpPolySum : Verified.Expr (Fin 1) → Option ExpPolySum
  | .nat k => some (ExpPolySum.const k)
  | .int k => some (ExpPolySum.const k)
  | .rat p q => if q = 0 then none else some (ExpPolySum.const ((p : ℚ) / q))
  | .pi => some [((0, 0, 1), 1)]
  | .var _ => some [((1, 0, 0), 1)]
  | .add a b => return ExpPolySum.normalize ((← toExpPolySum a) ++ (← toExpPolySum b))
  | .sub a b =>
      return ExpPolySum.normalize
        ((← toExpPolySum a) ++ ExpPolySum.mul (ExpPolySum.const (-1)) (← toExpPolySum b))
  | .neg a => return ExpPolySum.mul (ExpPolySum.const (-1)) (← toExpPolySum a)
  | .mul a b => return ExpPolySum.mul (← toExpPolySum a) (← toExpPolySum b)
  | .pow a k => do
      let base ← toExpPolySum a
      return (List.range k).foldl (fun total _ ↦ ExpPolySum.mul total base) (ExpPolySum.const 1)
  | .div a b => do
      match ← toExpPolySum b with
      | [((0, 0, 0), c)] => return ExpPolySum.mul (ExpPolySum.const (1 / c)) (← toExpPolySum a)
      | _ => none
  | .exp a => do
      match ← toExpPolySum a with
      | [((1, 0, 0), r)] => return [((0, r, 0), 1)]
      | [] => return ExpPolySum.const 1
      | _ => none
  | _ => none

/-- The rates `a` of the terms, without repetitions. -/
def ratesOf (as : List ℚ) : List ℚ := as.foldl (fun acc a ↦ if acc.contains a then acc else
  acc ++ [a]) []

/-- The largest frequency of the terms `e ^ (l x)` of an exponential polynomial. -/
def maxFreq (f : ExpPoly) : Nat :=
  f.foldl (fun m (l, _) ↦ max m (if l.im < 0 then -l.im else l.im).ceil.toNat) 0

/-- A bound for the total degree in `sin x` and `cos x` after `cos (k x)` and `sin (k x)` are
written as polynomials in `cos x` and `sin x`. -/
partial def trigDegree : Verified.Expr (Fin 1) → Nat
  | .sin a | .cos a => match toExpPoly (.sin a) with
    | some f => maxFreq f
    | none => 0
  | .add a b | .sub a b => max (trigDegree a) (trigDegree b)
  | .mul a b => trigDegree a + trigDegree b
  | .div a _ => trigDegree a
  | .neg a => trigDegree a
  | .pow a m => m * trigDegree a
  | _ => 0

/-- The instances `sin x ^ (k + 2) = sin x ^ k (1 - cos x ^ 2)` of `CAS.Fourier.sin_pow_add_two`
for `k + 2 ≤ D`. As `simp` lemmas they bring a polynomial of degree at most `D` in `sin x` and
`cos x` to degree at most `1` in `sin x`. -/
def sinPowInstances (x : TSyntax `term) (D : Nat) : TermElabM (Array (TSyntax `term)) :=
  (List.range (D - 1)).toArray.mapM fun k ↦ do
    let kT := Syntax.mkNumLit (toString k)
    let k2 := Syntax.mkNumLit (toString (k + 2))
    `((show Real.sin $x ^ $k2 = Real.sin $x ^ $kT * (1 - Real.cos $x ^ 2) from
        Fourier.sin_pow_add_two $x $kT))

/-- The check `f x = ∑ tᵢ (x)` of the decomposition into terms: the terms unfolded,
`cos (k x)` and `sin (k x)` written as polynomials in `cos x` and `sin x`, then `ring_nf`, the
reduction by `sinPow` (from `sinPowInstances`) and `ring_nf` again. -/
def decomposition (x : TSyntax `ident) (evalL eval : Ident) (sinPow : Array (TSyntax `term)) :
    TermElabM (TSyntax `tactic) := do
  let simpArgs : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    sinPow.mapM fun t ↦ `(Lean.Parser.Tactic.simpLemma| $t:term)
  let args : Syntax.TSepArray [``Lean.Parser.Tactic.simpStar,
      ``Lean.Parser.Tactic.simpErase, ``Lean.Parser.Tactic.simpLemma] "," :=
    .ofElems (simpArgs.map fun l ↦ ⟨l.raw⟩)
  let reduce ← if sinPow.isEmpty then `(tactic| skip) else `(tactic| simp only [$args,*])
  `(tactic| (
      intro $x:ident
      simp only [$evalL:ident, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        $eval:ident, Verified.Expr.univariateEval, Verified.Expr.euclideanSingle_eq_const,
        Verified.Expr.eval]
      try simp only [Rat.cast_zero, zero_mul, Real.exp_zero, mul_one]
      try simp only [Fourier.cos_nat_mul_eq, Fourier.sin_nat_mul_eq, Fourier.multipleAngle]
      try simp only [Int.cast_ofNat, Int.cast_neg, Nat.cast_ofNat, Nat.cast_one,
        Nat.cast_zero, Int.cast_one, Int.cast_zero]
      try push_cast
      ring_nf <;> (try $reduce:tactic) <;> (try ring_nf)))

/-- The cleanup after unfolding, then `field_simp` and `ring`. -/
def closeTactic : TermElabM (TSyntax `tactic) :=
  `(tactic| (
      try push_cast
      try simp only [neg_mul, one_mul, neg_neg, mul_neg, Real.sinh_eq, Real.cosh_eq, zero_mul,
        mul_zero, neg_zero, Real.exp_zero, mul_one, pow_zero, zero_pow, ne_eq,
        OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_add, add_zero, sub_zero, zero_sub, zero_div, sub_self]
      all_goals first
        | ring1
        | (field_simp <;> ring1)
        | (norm_num only <;> first | ring1 | (field_simp <;> ring1))))

/-- Run the proof, clean it and check it in the kernel. -/
def finish (name : String) (statement proofT : TSyntax `term) : TermElabM Lean.Expr := do
  let proof ← elabCheckedProof name statement proofT
  let cleaned ← Digits.cleanProof proof ExpPolynomials.cleanLemmas
    [``Verified.Expr.univariateEval] (simprocs := true)
  let cleaned ← Digits.cleanProof cleaned [``one_mul, ``mul_one, ``zero_add, ``add_zero,
    ``sub_zero, ``zero_mul, ``mul_zero, ``neg_mul] (simprocs := true)
  let named := Digits.restoreNames (← inferType proof) (← inferType cleaned)
  let cleaned ← mkExpectedTypeHint cleaned named
  CAS.Tactic.Explanation.kernelCheckedProof name named cleaned

/-- Run `act`; when it fails, drop the messages it logged and refuse with `reason`, with a hint
when the failure is the heartbeat limit (thrown, or logged by a tactic). -/
def refuseOnFailure {α : Type} (reason : MessageData) (act : TermElabM α) : TermElabM α := do
  let saved := (← getThe Core.State).messages
  tryCatchRuntimeEx act fun e ↦ do
    let logged := (← getThe Core.State).messages.toList.drop saved.toList.length
    modifyThe Core.State fun s ↦ { s with messages := saved }
    let heartbeats := e.isMaxHeartbeat ||
      logged.any fun m ↦ m.data.hasTag (· == `runtime.maxHeartbeats)
    if heartbeats then throwError "{reason} (try `set_option maxHeartbeats N in`)"
    throwError reason

/-- The right sides of the equations of the statement. -/
partial def rightSides (e : Lean.Expr) : MetaM (List String) := do
  match e.getAppFnArgs with
  | (``And, #[a, b]) => return (← rightSides a) ++ (← rightSides b)
  | (``Eq, #[_, _, rhs]) => return [← renderTerm rhs]
  | _ =>
      if e.isForall then forallTelescope e fun _ body ↦ rightSides body
      else return []

/-! ## `[-π, π]` -/

/-- Run `#cas [fourier x n] f`. -/
def logProduct (ref : Syntax) (x n : TSyntax `ident) (input : Syntax) : CommandElabM Unit := do
  let reified ← parseExact input [x.getId]
  unless reified.names.length = 1 do
    throwErrorAt input "fourier: the function may depend only on {x.getId}"
  let E : Verified.Expr (Fin 1) := reified.expr.mapVars fun _ ↦ (.var 0 : Verified.Expr (Fin 1))
  let some f := toExpPoly E
    | throwErrorAt input "fourier: the function must be a sum of products of polynomials, \
        exponentials, sines and cosines"
  let raw ← match productTerms f with
    | .ok ts => pure ts
    | .error msg => throwErrorAt input "fourier: {msg}"
  unless raw.all (fun (_, _, _, k, _) ↦ k.den == 1) do
    throwErrorAt input "fourier: trigonometric frequencies must be integers on [-π, π]"
  let terms : List PTerm := raw.map fun (c, j, a, k, s) ↦
    if s then .sinT c j a k.num.natAbs else .cosT c j a k.num.natAbs
  -- The degree in `sin x` and `cos x` that the decomposition check reduces.
  let degree := max (trigDegree E) (maxFreq f)
  let rates := ratesOf (raw.filterMap fun (_, _, a, _, _) ↦
    if a == 0 then none else some (if a < 0 then -a else a))
  let specials := (ratesOf (raw.filterMap fun (_, _, a, k, _) ↦
    if a == 0 && k ≥ 1 then some k else none)).map (·.num.natAbs)
  let atomIndex (a : ℚ) : Nat × Nat :=
    match rates.findIdx? (· == a) with
    | some i => (3 + 2 * i, 4 + 2 * i)
    | none => (3, 4)
  let xT : TSyntax `term := ⟨x.raw⟩
  let nT : TSyntax `term := ⟨n.raw⟩
  let proof ← liftTermElabM do
    let mut vars : Array (TSyntax `term) := #[← `(($nT : ℝ)), ← `(Real.pi),
      ← `((-1 : ℝ) ^ $nT)]
    for a in rates do
      let arg ← if a == 1 then `(Real.pi) else `($(← real a) * Real.pi)
      vars := vars.push (← `(Real.sinh $arg))
      vars := vars.push (← `(Real.cosh $arg))
    let symbolic : Ctx := ⟨pVar 0, pVar 2, atomIndex⟩
    let numeric (m : Nat) : Ctx := ⟨pConst m, pConst ((-1) ^ m), atomIndex⟩
    let piF : Fac := ⟨piV, piV, 0⟩
    let coefficient (ctx : Ctx) (g : Ctx → PTerm → FactoredFraction) : FactoredFraction :=
      (sumFactoredFractions (terms.map (g ctx))).divBy piF |>.reduce
    let meanT ← factoredFractionSyntax vars nT (coefficient (numeric 0) meanP)
    let withSpecials (g : Ctx → PTerm → FactoredFraction) : TermElabM (TSyntax `term) := do
      let generic := coefficient symbolic g
      let mut t ← factoredFractionSyntax vars nT generic
      for m in specials.reverse do
        let special := coefficient (numeric m) g
        if generic.agreesAt special m then continue
        let v ← factoredFractionSyntax vars nT special
        t ← `(if $nT = $(Syntax.mkNumLit (toString m)) then $v else $t)
      return t
    let cosT ← withSpecials cosP
    let sinT ← withSpecials sinP
    let ET ← exprToSyntax (← quoteVerifiedExpr E)
    let D ← `([$(← terms.toArray.mapM pTermSyntax),*])
    let fT ← `(Verified.Expr.univariateEval $ET)
    let statement ← `((1 / Real.pi * ∫ $x:ident in -Real.pi..Real.pi, $fT $xT) = $meanT ∧
      (∀ $n:ident : ℕ, 0 < $nT →
        1 / Real.pi * ∫ $x:ident in -Real.pi..Real.pi, ($fT $xT) * Real.cos ($nT * $xT) =
          $cosT) ∧
      (∀ $n:ident : ℕ, 0 < $nT →
        1 / Real.pi * ∫ $x:ident in -Real.pi..Real.pi, ($fT $xT) * Real.sin ($nT * $xT) =
          $sinT))
    let mut rateFacts : Array (TSyntax `term) := #[]
    let mut rateHaves : TSyntax `tactic ← `(tactic| skip)
    for a in ratesOf (raw.map fun (_, _, a, _, _) ↦ a) do
      if a != 0 then
        let h := mkIdent (Name.mkSimple s!"hq{rateFacts.size}")
        rateFacts := rateFacts.push h
        rateHaves ← `(tactic| (have $h:ident : ($(← ratSyntax a) : ℚ) ≠ 0 := by norm_num
                               $rateHaves:tactic))
    let hfTac ← decomposition x (mkIdent ``FourierProduct.evalL)
      (mkIdent ``FourierProduct.PTerm.eval) (← sinPowInstances xT degree)
    -- The closed forms for the terms `c cos (k x)` and `c sin (k x)` first, then the recursions.
    let unfold (extra : Array (TSyntax `term)) : TermElabM (TSyntax `tactic) := do
      let lemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ← (rateFacts ++ extra).mapM
        fun t ↦ `(Lean.Parser.Tactic.simpLemma| $t:term)
      let args : Syntax.TSepArray [``Lean.Parser.Tactic.simpStar,
          ``Lean.Parser.Tactic.simpErase, ``Lean.Parser.Tactic.simpLemma] "," :=
        .ofElems (lemmas.map fun l ↦ ⟨l.raw⟩)
      `(tactic| (
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          FourierProduct.cosCoeff_cosT, FourierProduct.sinCoeff_sinT,
          FourierProduct.sinCoeff_cosT, FourierProduct.cosCoeff_sinT, FourierProduct.mean_cosT,
          FourierProduct.mean_sinT]
        try simp +decide only [List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, FourierProduct.PTerm.mean, FourierProduct.PTerm.cosCoeff,
          FourierProduct.PTerm.sinCoeff, FourierProduct.low, FourierProduct.high,
          FourierProduct.sym, FourierProduct.wall, FourierProduct.polyMean, true_and, false_and,
          and_false, add_zero, Nat.add_eq_zero_iff, ↓reduceIte, $args,*]))
    let close ← closeTactic
    -- The generic case: `n ≠ k` for the special `k`.
    let mut generic : TSyntax `tactic ← `(tactic| skip)
    let mut facts : Array (TSyntax `term) := #[]
    for m in specials do
      let h' := mkIdent (Name.mkSimple s!"hr{m}")
      let mT : TSyntax `term := Syntax.mkNumLit (toString m)
      let ne ← `(term| (‹¬ $nT = $mT›))
      facts := facts.push ne
      let fact ← `(term| sub_ne_zero.mpr (by exact_mod_cast $ne))
      generic ← `(tactic| (have $h':ident : ($nT : ℝ) - $mT ≠ 0 := $fact
                           $generic:tactic))
    let hn0 ← `(term| hn0)
    let genericUnfold ← unfold (facts.push hn0)
    let specialUnfold ← unfold #[]
    let plainUnfold ← unfold #[hn0]
    let branch (h : TSyntax `term) : TermElabM (TSyntax `tactic) := do
      if specials.isEmpty then
        `(tactic| (rw [$h:term]; $plainUnfold:tactic; $close:tactic))
      else
        -- The cases `n = k`, then the generic case.
        let mut steps : Array (TSyntax `tactic) := #[← `(tactic| rw [$h:term])]
        for m in specials do
          let mT : TSyntax `term := Syntax.mkNumLit (toString m)
          steps := steps.push (← `(tactic| by_cases hk : $nT = $mT))
          steps := steps.push (← `(tactic| · (subst hk; $specialUnfold:tactic; $close:tactic)))
        steps := steps.push (← `(tactic| ($generic:tactic; $genericUnfold:tactic; $close:tactic)))
        `(tactic| ($steps;*))
    let cosBranch ← branch (← `(hc $nT))
    let sinBranch ← branch (← `(hs $nT))
    let meanBranch ← `(tactic| (rw [h₀]; $specialUnfold:tactic; $close:tactic))
    let proofT ← `(by
      have hf : ∀ $x:ident, $fT $xT = FourierProduct.evalL $D $xT := by $hfTac:tactic
      $rateHaves:tactic
      obtain ⟨h₀, hc, hs⟩ := FourierProduct.fourier_of_eq $D hf
      refine ⟨?_, fun $n:ident hn ↦ ?_, fun $n:ident hn ↦ ?_⟩
      · $meanBranch:tactic
      · have hn0 : $nT ≠ 0 := Nat.pos_iff_ne_zero.mp hn
        $cosBranch:tactic
      · have hn0 : $nT ≠ 0 := Nat.pos_iff_ne_zero.mp hn
        $sinBranch:tactic)
    refuseOnFailure m!"fourier: the coefficients of this function could not be proved"
      (finish "fourier" statement proofT)
  let report ← liftTermElabM do
    evidenceReportMessage
      #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
        "The Fourier coefficients on [-π, π], by integration by parts" proof]
  let answer ← liftTermElabM do
    match ← rightSides (← inferType proof) with
    | [a, b, c] =>
        let (an, bn) := if n.getId == `n then ("aₙ", "bₙ")
          else (s!"a({n.getId})", s!"b({n.getId})")
        pure s!"a₀ = {a}, {an} = {b}, {bn} = {c}"
    | _ => pure "see the statement"
  logReport ref {
    domain := s!"{x.getId} ∈ [-π, π], {n.getId} ≥ 1"
    input := surfaceText input
    inputType := "scalar ℝ"
    output := answer
    outputType := "Fourier coefficients"
  } #[report]

/-! ## Sine and cosine series on `[0, L]` -/

/-- `q π ^ e` with `e ≤ 1`; the only variable is `π`. -/
partial def piMultiple? {ι : Type} : Verified.Expr ι → Option (ℚ × Nat)
  | .var _ => some (1, 1)
  | .nat k => some (k, 0)
  | .int k => some (k, 0)
  | .rat p q => if q = 0 then none else some ((p : ℚ) / q, 0)
  | .pi => some (1, 1)
  | .neg a => do
      let (q, ep) ← piMultiple? a
      return (-q, ep)
  | .mul a b => do
      let (q, ep) ← piMultiple? a
      let (q', ep') ← piMultiple? b
      if ep + ep' > 1 then none
      return (q * q', ep + ep')
  | .div a b => do
      let (q, ep) ← piMultiple? a
      let (q', ep') ← piMultiple? b
      if ep' != 0 || q' == 0 then none
      return (q / q', ep)
  | _ => none

/-- Run `#cas [fourierSin x n L] f` (`sine = true`) or `#cas [fourierCos x n L] f`. -/
def logHalf (ref : Syntax) (sine : Bool) (x n : TSyntax `ident) (Lstx : TSyntax `term)
    (input : Syntax) : CommandElabM Unit := do
  let cmd := if sine then "fourierSin" else "fourierCos"
  let Lr ← parseExact Lstx [`π]
  let some (q, ep) := piMultiple? Lr.expr
    | throwErrorAt Lstx "{cmd}: L must be a positive rational number or a rational multiple of π"
  unless q > 0 do throwErrorAt Lstx "{cmd}: L must be positive"
  let reified ← parseExact input [x.getId]
  unless reified.names.length = 1 do
    throwErrorAt input "{cmd}: the function may depend only on {x.getId}"
  let E : Verified.Expr (Fin 1) := reified.expr.mapVars fun _ ↦ (.var 0 : Verified.Expr (Fin 1))
  let some f := toExpPolySum E
    | throwErrorAt input "{cmd}: on [0, L] the function must be a sum of terms c x ^ j e ^ (a x)"
  let terms : List HTerm := f.map fun ((j, a, p), c) ↦ ⟨c, p, j, a⟩
  let rates := ratesOf (terms.filterMap fun t ↦ if t.a == 0 then none else some t.a)
  let xT : TSyntax `term := ⟨x.raw⟩
  let nT : TSyntax `term := ⟨n.raw⟩
  let proof ← liftTermElabM do
    let qT ← real q
    let LT ← if ep == 0 then pure qT else if q == 1 then `(Real.pi) else `($qT * Real.pi)
    let bT ← if ep == 1 then (if q == 1 then `(($nT : ℝ)) else `(($nT : ℝ) / $qT))
      else if q == 1 then `(($nT : ℝ) * Real.pi) else `(($nT : ℝ) * Real.pi / $qT)
    let mut vars : Array (TSyntax `term) := #[← `(($nT : ℝ)), ← `(Real.pi),
      ← `((-1 : ℝ) ^ $nT)]
    for a in rates do
      vars := vars.push (← `(Real.exp ($(← real a) * $LT)))
    let Lp : Poly := pScale q (pPow piV ep)
    let bP : Poly := pScale (1 / q) (pMul (pVar 0) (pPow piV (1 - ep)))
    let expOf (a : ℚ) : Poly :=
      if a == 0 then pConst 1 else
      match rates.findIdx? (· == a) with
      | some i => pVar (3 + i)
      | none => pConst 1
    -- `2 / L` times the sum.
    let scaled (r : FactoredFraction) : FactoredFraction :=
      let r := r.scale (2 / q)
      (if ep == 1 then r.divBy ⟨piV, piV, 0⟩ else r).reduce
    let coef (t : HTerm) (r : FactoredFraction) : FactoredFraction :=
      (r.scale t.c).mulPoly (pPow piV t.p)
    let cosAll := scaled (sumFactoredFractions (terms.map fun t ↦
      coef t (halfP Lp (expOf t.a) t.a bP (pVar 2) t.j).1))
    let sinAll := scaled (sumFactoredFractions (terms.map fun t ↦
      coef t (halfP Lp (expOf t.a) t.a bP (pVar 2) t.j).2))
    let meanAll := scaled (sumFactoredFractions (terms.map fun t ↦
      if t.a == 0 then coef t (.ofPoly (pScale (1 / (t.j + 1 : ℚ)) (pPow Lp (t.j + 1))))
      else coef t (halfP Lp (expOf t.a) t.a [] (pConst 1) t.j).1))
    let ET ← exprToSyntax (← quoteVerifiedExpr E)
    let D ← `([$(← terms.toArray.mapM hTermSyntax),*])
    let fT ← `(Verified.Expr.univariateEval $ET)
    let trig ← if sine then `(Real.sin) else `(Real.cos)
    let coeffT ← factoredFractionSyntax vars nT (if sine then sinAll else cosAll)
    let series ← `(∀ $n:ident : ℕ, 0 < $nT →
        2 / $LT * ∫ $x:ident in (0 : ℝ)..$LT, ($fT $xT) * $trig ($bT * $xT) = $coeffT)
    let statement ← if sine then pure series else
      `((2 / $LT * ∫ $x:ident in (0 : ℝ)..$LT, $fT $xT) =
          $(← factoredFractionSyntax vars nT meanAll) ∧
        $series)
    let mut rateFacts : Array (TSyntax `term) := #[]
    let mut rateHaves : TSyntax `tactic ← `(tactic| skip)
    for a in rates do
      let h := mkIdent (Name.mkSimple s!"hq{rateFacts.size}")
      rateFacts := rateFacts.push h
      rateHaves ← `(tactic| (have $h:ident : ($(← ratSyntax a) : ℚ) ≠ 0 := by norm_num
                             $rateHaves:tactic))
    let lemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ← rateFacts.mapM
      fun t ↦ `(Lean.Parser.Tactic.simpLemma| $t:term)
    let args : Syntax.TSepArray [``Lean.Parser.Tactic.simpStar,
        ``Lean.Parser.Tactic.simpErase, ``Lean.Parser.Tactic.simpLemma] "," :=
      .ofElems (lemmas.map fun l ↦ ⟨l.raw⟩)
    let unfold ← `(tactic| simp +decide only [List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, FourierProduct.HTerm.mean, FourierProduct.HTerm.cosCoeff,
        FourierProduct.HTerm.sinCoeff, FourierProduct.half, add_zero, ↓reduceIte, $args,*])
    let close ← closeTactic
    let hfTac ← decomposition x (mkIdent ``FourierProduct.hEvalL)
      (mkIdent ``FourierProduct.HTerm.eval) #[]
    let pick ← if sine then `(term| (h hb hs hc).2) else `(term| (h hb hs hc).1)
    let seriesTac ← `(tactic| (
        have hb : $bT ≠ 0 := by positivity
        have hs : Real.sin ($bT * $LT) = 0 := by
          rw [show $bT * $LT = ($nT : ℝ) * Real.pi by ring]
          exact Real.sin_nat_mul_pi $nT
        have hc : Real.cos ($bT * $LT) = (-1) ^ $nT := by
          rw [show $bT * $LT = ($nT : ℝ) * Real.pi by ring]
          exact Real.cos_nat_mul_pi $nT
        rw [$pick:term]
        $unfold:tactic
        $close:tactic))
    let proofT ← if sine then
        `(by
          have hf : ∀ $x:ident, $fT $xT = FourierProduct.hEvalL $D $xT := by $hfTac:tactic
          $rateHaves:tactic
          obtain ⟨-, h⟩ := FourierProduct.half_of_eq $D hf $LT
          intro $n:ident hn
          $seriesTac:tactic)
      else
        `(by
          have hf : ∀ $x:ident, $fT $xT = FourierProduct.hEvalL $D $xT := by $hfTac:tactic
          $rateHaves:tactic
          obtain ⟨h₀, h⟩ := FourierProduct.half_of_eq $D hf $LT
          refine ⟨?_, fun $n:ident hn ↦ ?_⟩
          · rw [h₀]
            $unfold:tactic
            $close:tactic
          · $seriesTac:tactic)
    refuseOnFailure m!"{cmd}: the coefficients of this function could not be proved"
      (finish cmd statement proofT)
  let report ← liftTermElabM do
    evidenceReportMessage
      #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
        (if sine then "The sine coefficients on [0, L]" else "The cosine coefficients on [0, L]")
        proof]
  let answer ← liftTermElabM do
    let sides ← rightSides (← inferType proof)
    let nn := if n.getId == `n then "ₙ" else s!"({n.getId})"
    match sides with
    | [b] => pure s!"b{nn} = {b}"
    | [a, b] => pure s!"a₀ = {a}, a{nn} = {b}"
    | _ => pure "see the statement"
  logReport ref {
    domain := s!"{x.getId} ∈ [0, {surfaceText Lstx.raw}], {n.getId} ≥ 1"
    input := surfaceText input
    inputType := "scalar ℝ"
    output := answer
    outputType := if sine then "sine series coefficients" else "cosine series coefficients"
  } #[report]

end CAS.Command.FourierProductCmd

namespace CAS.Command

open Lean Elab Command

/-- `#cas [fourier x n] f` computes the Fourier coefficients `a₀`, `aₙ` and `bₙ` of `f` on `[-π, π]`
as exact functions of `n ≥ 1`, and proves them.

## Theorem
For the printed coefficients, the report proves
`1 / Real.pi * ∫ x in -Real.pi..Real.pi, f = a₀`, and for every `n : ℕ` with `0 < n`,
`1 / Real.pi * ∫ x in -Real.pi..Real.pi, f * Real.cos (n * x) = aₙ` and
`1 / Real.pi * ∫ x in -Real.pi..Real.pi, f * Real.sin (n * x) = bₙ`
(`CAS.FourierProduct.fourier_of_eq`). They are the coefficients of the series
`a₀ / 2 + ∑ (aₙ * cos (n * x) + bₙ * sin (n * x))`.

## Conditions and limits
`f` is a sum of products of polynomials in `x`, exponentials `exp (a * x)` with rational `a`, and
sines and cosines with integer frequencies, such as `x * sin x`, `x ^ 2 * exp x` or
`sin x ^ 3 * cos (2 * x)`. When a term `c * x ^ j * cos (k * x)` or `c * x ^ j * sin (k * x)` has
`k ≥ 1`, the coefficients at `n = k` are given separately by an `if`, unless the formula for
general `n` covers them. When the proof of the coefficients fails, for instance at the heartbeat
limit, the command refuses with an error.

## Options
None.

## Examples
```lean
#cas [fourier x n] (x)
```
```output
Output (Fourier coefficients): a₀ = 0, aₙ = 0, bₙ = 2*(-1)^(n + 1)/n
```
```lean
#cas [fourier x n] (x^2)
```
```output
Output (Fourier coefficients): a₀ = 2/3*pi^2, aₙ = 4*(-1)^n/n^2, bₙ = 0
```
```lean
#cas [fourier x n] (x * sin x)
```
```output
Output (Fourier coefficients): a₀ = 2, aₙ = if n = 1 then -(1/2) else
2*(-1)^(n + 1)/((n + 1)*(n - 1)), bₙ = 0
```

## In a proof
```lean
theorem fourier_b_one : 1 / Real.pi * ∫ x in -Real.pi..Real.pi, x * Real.sin x = 2 := by
  cas
```

## See also
Mathematica `FourierCoefficient` and `FourierSeries`, SymPy `fourier_series`. The modes
`fourierSin`, `fourierCos`, `fourierTransform` and `integrate`.

## Possible issues
```lean
#cas [fourier x n] (exp (x ^ 2))
```
```output
fourier: the function must be a sum of products of polynomials, exponentials, sines and cosines
```
Other functions are refused; `nintegrate` encloses a single coefficient of them numerically.
```lean
#cas [fourier x n] (sin (x / 2))
```
```output
fourier: trigonometric frequencies must be integers on [-π, π]
```
The sines and cosines on `[-π, π]` have integer frequencies `k`, as in `sin (k * x)`.
-/
syntax (name := casFourierCommand) "#cas" "[" &"fourier" ident ident "]" term : command

elab_rules : command
  | `(#cas [fourier $x:ident $n:ident] $f:term) => FourierProductCmd.logProduct f x n f

/-- `#cas [fourierSin x n L] f` computes the coefficients `bₙ` of the sine series
`∑ bₙ * sin (n * π * x / L)` of `f` on `[0, L]` as exact functions of `n ≥ 1`, and proves them.

## Theorem
For the printed `bₙ`, the report proves
`∀ n : ℕ, 0 < n → 2 / L * ∫ x in 0..L, f * Real.sin (n * Real.pi * x / L) = bₙ`
(`CAS.FourierProduct.half_of_eq`), printed in simplified form, as `Real.sin (n * x)` for `L = π`.

## Conditions and limits
`f` is a sum of terms `c * x ^ j * exp (a * x)` with rational `a`, such as `x * (π - x)`, and
`L` is a positive rational number or a positive rational multiple of `π`.

## Options
None.

## Examples
```lean
#cas [fourierSin x n pi] (x * (pi - x))
```
```output
Output (sine series coefficients): bₙ = 4*(1 - (-1)^n)/(n^3*pi)
```
```lean
#cas [fourierSin x n 1] (x)
```
```output
Output (sine series coefficients): bₙ = 2*(-1)^(n + 1)/(n*pi)
```

## In a proof
```lean
theorem fourierSin_b_one : ∫ x in (0 : ℝ)..Real.pi, x * (Real.pi - x) * Real.sin x = 4 := by
  cas
```

## See also
Mathematica `FourierSinCoefficient` and `FourierSinSeries`, SymPy `fourier_series`. The modes
`fourierCos` and `fourier`.

## Possible issues
```lean
#cas [fourierSin x n 0] (x)
```
```output
fourierSin: L must be positive
```
Give a positive length `L`.
```lean
#cas [fourierSin x n pi] (exp (x ^ 2))
```
```output
fourierSin: on [0, L] the function must be a sum of terms c x ^ j e ^ (a x)
```
Sines, cosines and other functions are refused on `[0, L]`; `fourier` on `[-π, π]` accepts sines
and cosines with integer frequencies.
-/
syntax (name := casFourierSinCommand)
  "#cas" "[" &"fourierSin" ident ident term "]" term : command

/-- `#cas [fourierCos x n L] f` computes the coefficients `a₀` and `aₙ` of the cosine series
`a₀ / 2 + ∑ aₙ * cos (n * π * x / L)` of `f` on `[0, L]` as exact functions of `n ≥ 1`, and
proves them.

## Theorem
For the printed coefficients, the report proves `2 / L * ∫ x in 0..L, f = a₀` and
`∀ n : ℕ, 0 < n → 2 / L * ∫ x in 0..L, f * Real.cos (n * Real.pi * x / L) = aₙ`
(`CAS.FourierProduct.half_of_eq`), printed in simplified form, as `2 * ∫ x in 0..1, f` for
`L = 1`.

## Conditions and limits
As for `#cas [fourierSin x n L]`: `f` is a sum of terms `c * x ^ j * exp (a * x)` with rational
`a`, and `L` is a positive rational number or a positive rational multiple of `π`.

## Options
None.

## Examples
```lean
#cas [fourierCos x n 1] (x)
```
```output
Output (cosine series coefficients): a₀ = 1, aₙ = -(2*(1 - (-1)^n)/(n^2*pi^2))
```
```lean
#cas [fourierCos x n 2] (x ^ 2)
```
```output
Output (cosine series coefficients): a₀ = 8/3, aₙ = 16*(-1)^n/(n^2*pi^2)
```

## In a proof
```lean
theorem fourierCos_a_one :
    ∫ x in (0 : ℝ)..1, x * Real.cos (Real.pi * x) = -(2 / Real.pi ^ 2) := by
  cas
```

## See also
Mathematica `FourierCosCoefficient` and `FourierCosSeries`, SymPy `fourier_series`. The modes
`fourierSin` and `fourier`.

## Possible issues
```lean
#cas [fourierCos x n pi] (sin x)
```
```output
fourierCos: on [0, L] the function must be a sum of terms c x ^ j e ^ (a x)
```
Sines and cosines are refused on `[0, L]`; `fourier` on `[-π, π]` accepts them.
```lean
#cas [fourierCos x n (sqrt 2)] (x)
```
```output
fourierCos: L must be a positive rational number or a rational multiple of π
```
Give `L` as a rational number or a rational multiple of `π`, such as `2 * pi / 3`.
-/
syntax (name := casFourierCosCommand)
  "#cas" "[" &"fourierCos" ident ident term "]" term : command

elab_rules : command
  | `(#cas [fourierSin $x:ident $n:ident $L:term] $f:term) =>
      FourierProductCmd.logHalf f true x n L f
  | `(#cas [fourierCos $x:ident $n:ident $L:term] $f:term) =>
      FourierProductCmd.logHalf f false x n L f

end CAS.Command
