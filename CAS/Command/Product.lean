/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Algebra.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Factorial.Basic
public meta import CAS.Tactic.RouteRegistry

/-!
# Finite products: `#cas [product k a n]`

`#cas [product k a n] f` gives a closed form of `∏ k ∈ Finset.Icc a n, f k`, as Mathematica's
`Product[f, {k, a, n}]` does, when the rational function `f` is a constant times a product of
powers of linear factors `k + s` with integer shifts `s`:

* when the exponents add up to zero the product telescopes to `c ^ (n - a + 1)` times a rational
  function of `n`, such as `∏ (k + 1) / k = n + 1`;
* when every shift is nonnegative it is `c ^ (n - a + 1) ∏ ((n + s)! / (a + s - 1)!) ^ e`, such as
  `∏ k = n!` and `∏ 2 k (k + 1)`, written with `Nat.factorial`.

The theorem holds for every `n` (every `n ≥ a - 1` when `a ≥ 2`; the product over an empty range
is `1`) and is proved by induction on `n`, each step by `field_simp` and `ring` after
`Nat.factorial_succ`. A factor that vanishes inside the range of the product makes the command
refuse, as do rational shifts and factors irreducible of degree two or more, whose products need
Gamma functions.

`product` does not search for factors itself: factoring over `ℚ` is Hex's, through the optional
`CASHex`. Without Hex the linear factors must be written in the input: the factors are the
coprime basis of the factors written in `f`, its numerator and its denominator, refined by gcds
(`factorsOver`), so `(k - 1) * (k + 1) / k ^ 2` has a closed form and `1 - 1 / k ^ 2` is refused.
With `import CASHex.Factor` (built with `lake -R -Khex=on build CASHex`) the numerator and the
denominator are factored completely over `ℚ` by Hex's Berlekamp-Zassenhaus factorizer.
-/

public meta section

namespace CAS.Command.Algebra

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Verified.Expr.Alg

/-- The shifts `s` with exponents `e` such that `∏ fᵢ ^ eᵢ = ∏ (k + s) ^ e` for a factorization
into monic factors `fᵢ`, or `none` when a factor is not linear with an integer root. -/
def linearShifts (factors : List (Dense × Nat)) : Option (List (Int × Int)) := do
  let mut out : List (Int × Int) := []
  for (f, e) in factors do
    unless f.size = 2 do none
    let s := f.getD 0 0
    unless s.den = 1 do none
    out := out ++ [(s.num, (e : Int))]
  return out

/-- The closed form as data: a constant, the base of the power `c ^ (n - a + 1)`, the linear
factors `(n + j) ^ e` of a rational function, and factorials `(n + s)! ^ e`. -/
structure ProductForm where
  /-- The constant factor. -/
  constant : ℚ
  /-- The base `c` of `c ^ (n - a + 1)`. -/
  base : ℚ
  /-- Linear factors `(n + j) ^ e`. -/
  linear : List (Int × Int)
  /-- Factorials `(n + s)! ^ e`, with `s ≥ 0`. -/
  factorials : List (Nat × Int)

/-- Add an exponent to a list of `(key, exponent)` pairs. -/
def bump {α : Type} [BEq α] (l : List (α × Int)) (key : α) (e : Int) : List (α × Int) :=
  match l.find? (·.1 == key) with
  | some _ => (l.map fun (k, x) ↦ if k == key then (k, x + e) else (k, x)).filter (·.2 ≠ 0)
  | none => if e = 0 then l else l ++ [(key, e)]

/-- `∏_{j = lo}^{hi} j`, the product of a range of integers (`1` when empty). -/
def rangeProduct (lo hi : Int) : ℚ := Id.run do
  let mut out : ℚ := 1
  let mut j := lo
  while j ≤ hi do
    out := out * j
    j := j + 1
  return out

/-- The closed form of `∏_{k=a}^{n} c ∏ (k + s) ^ e`, or an explanation of why there is none in
this fragment. -/
def productForm (a : Nat) (c : ℚ) (shifts : List (Int × Int)) : Except String ProductForm := do
  -- A factor `k + s` vanishing for some `k ≥ a` (with a negative exponent, a division by zero).
  for (s, _) in shifts do
    if (a : Int) + s ≤ 0 then
      let factor := if s = 0 then "k" else if s > 0 then s!"k + {s}" else s!"k - {-s}"
      throw s!"the factor {factor} vanishes in the range of the product"
  let total := shifts.foldl (fun t (_, e) ↦ t + e) 0
  -- `c ^ (n - a + 1) = c ^ (1 - a) * c ^ n`.
  let constant₀ : ℚ := if c = 0 then 0 else c ^ (1 - (a : Int))
  if total = 0 then
    -- Telescoping: `∏_{k=a}^{n} (k + s) / (k + t₀) = ∏_{j = t₀ + 1}^{s} (n + j) / (a + j - 1)`.
    let t₀ := shifts.foldl (fun m (s, _) ↦ min m s) (shifts.head?.map (·.1) |>.getD 0)
    let mut linear : List (Int × Int) := []
    let mut constant := constant₀
    for (s, e) in shifts do
      let mut j := t₀ + 1
      while j ≤ s do
        linear := bump linear j e
        constant := constant / ((a : ℚ) + j - 1) ^ e
        j := j + 1
    return { constant, base := c, linear, factorials := [] }
  else
    unless shifts.all (·.1 ≥ 0) do
      throw "the product is not telescoping and has a negative shift; its closed form needs \
        Gamma functions"
    let mut constant := constant₀
    let mut factorials : List (Nat × Int) := []
    for (s, e) in shifts do
      factorials := bump factorials s.toNat e
      constant := constant / (rangeProduct 1 ((a : Int) + s - 1)) ^ e
    return { constant, base := c, linear := [], factorials }

namespace ProductForm

/-- The closed form as real term syntax in `n`. -/
def term (F : ProductForm) (n : TSyntax `ident) : TermElabM (TSyntax `term) := do
  let mut numerator : Array (TSyntax `term) := #[]
  let mut denominator : Array (TSyntax `term) := #[]
  let mag := if F.constant < 0 then -F.constant else F.constant
  if mag.num ≠ 1 then numerator := numerator.push (natTerm mag.num.natAbs)
  if mag.den ≠ 1 then denominator := denominator.push (natTerm mag.den)
  unless F.base = 1 do
    numerator := numerator.push (← `(($(← ratSyntax F.base) : ℝ) ^ $n))
  for (j, e) in F.linear do
    let base ← if j = 0 then `(($n : ℝ)) else if j > 0 then `((($n : ℝ) + $(natTerm j.toNat)))
      else `((($n : ℝ) - $(natTerm j.natAbs)))
    let factor ← if e.natAbs = 1 then pure base else `($base ^ $(natTerm e.natAbs))
    if e > 0 then numerator := numerator.push factor else denominator := denominator.push factor
  for (s, e) in F.factorials do
    let base ← if s = 0 then `((Nat.factorial $n : ℝ))
      else `((Nat.factorial ($n + $(natTerm s)) : ℝ))
    let factor ← if e.natAbs = 1 then pure base else `($base ^ $(natTerm e.natAbs))
    if e > 0 then numerator := numerator.push factor else denominator := denominator.push factor
  let product (xs : Array (TSyntax `term)) : TermElabM (TSyntax `term) := do
    if xs.isEmpty then return ← `(1)
    let mut out := xs[0]!
    for x in xs[1:] do out ← `($out * $x)
    return out
  let num ← product numerator
  let body ← if denominator.isEmpty then pure num else `($num / $(← product denominator))
  if F.constant < 0 then `(-($body)) else `(($body : ℝ))

/-- The closed form as text in `n`. -/
def text (F : ProductForm) (n : String) : String := Id.run do
  let mut numerator : List String := []
  let mut denominator : List String := []
  let mag := if F.constant < 0 then -F.constant else F.constant
  if mag.num ≠ 1 then numerator := numerator ++ [s!"{mag.num.natAbs}"]
  if mag.den ≠ 1 then denominator := denominator ++ [s!"{mag.den}"]
  unless F.base = 1 do numerator := numerator ++ [s!"{powerBaseText F.base}^{n}"]
  for (j, e) in F.linear do
    let base := if j = 0 then n else if j > 0 then s!"({n} + {j})" else s!"({n} - {j.natAbs})"
    let factor := if e.natAbs = 1 then base else s!"{base}^{e.natAbs}"
    if e > 0 then numerator := numerator ++ [factor] else denominator := denominator ++ [factor]
  for (s, e) in F.factorials do
    let base := if s = 0 then s!"{n}!" else s!"({n} + {s})!"
    let factor := if e.natAbs = 1 then base else s!"{base}^{e.natAbs}"
    if e > 0 then numerator := numerator ++ [factor] else denominator := denominator ++ [factor]
  let num := if numerator.isEmpty then "1" else "*".intercalate numerator
  let body := if denominator.isEmpty then num
    else s!"{num}/" ++ (if denominator.length > 1 then s!"({"*".intercalate denominator})"
      else denominator.head!)
  return if F.constant < 0 then s!"-{body}" else body

end ProductForm

/-- Run `#cas [product k a n] f`. The numerator and the denominator of `f` are factored by
`factorize?` when it is given (`CASHex` passes Hex's complete factorization over `ℚ`), and
otherwise over the factors written in the input (`factorsOver`). -/
def logProduct (ref : Syntax) (k : TSyntax `ident) (aStx bStx : Syntax) (input : Syntax)
    (factorize? : Option (Dense → List (Dense × Nat)) := none) : CommandElabM Unit := do
  let a ← parseRationalLiteralFor "product" "the lower bound must be a natural number" aStx
  unless a.den = 1 && 0 ≤ a do
    throwErrorAt aStx "product: the lower bound must be a natural number"
  let aNat := a.num.toNat
  let reified ← parseExact input [k.getId]
  if h : reified.names.length = 1 then
    let rational ← match rationalOfExpr reified.expr with
      | .ok r => pure r
      | .error message => throwErrorAt input "product: {message}"
    let num := toDense (h ▸ rational.value.num)
    let den := toDense (h ▸ rational.value.den)
    let (numFactors, denFactors) := match factorize? with
      | some factorize => (factorize num, factorize den)
      | none =>
          let toOne (p : MvPoly reified.names.length) : MvPoly 1 := h ▸ p
          let written := (writtenFactors reified.expr).map toOne ++
            [toOne rational.value.num, toOne rational.value.den]
          (factorsOver written num, factorsOver written den)
    unless Dense.isFactorization num numFactors && Dense.isFactorization den denFactors do
      throwErrorAt input "product: the factorization of the factor is not a product of monic, \
        pairwise coprime factors; nothing is claimed"
    let (some numShifts, some denShifts) := (linearShifts numFactors, linearShifts denFactors)
      | if factorize?.isSome || (numFactors ++ denFactors).all (·.1.size = 2) then
          throwErrorAt input "product: the factor is not a constant times powers of linear \
            factors k + s with integer s; its product needs Gamma functions or Pochhammer symbols"
        else
          throwErrorAt input "product: the factor is not, as written, a constant times powers of \
            linear factors k + s with integer s, and without Hex `product` does not factor it: \
            write it as such a product, or use CASHex (`lake -R -Khex=on build CASHex`, \
            `import CASHex.Factor`), which factors it completely over ℚ"
    let shifts := denShifts.foldl (fun acc (s, e) ↦ bump acc s (-e)) numShifts
    let form ← match productForm aNat (Dense.lead num / Dense.lead den) shifts with
      | .ok F => pure F
      | .error message => throwErrorAt input "product: {message}"
    let n := match bStx with
      | `($n:ident) => some n
      | _ => none
    let some nIdent := n | throwErrorAt bStx "product: the upper bound must be a variable"
    let (proposition, proof) ← liftTermElabM do
      let kT : TSyntax `term := ⟨(mkIdent k.getId).raw⟩
      let kReal ← `(($kT : ℝ))
      let factor ← exprTerm (fun _ ↦ kReal) (h ▸ reified.expr)
      let F ← form.term nIdent
      let aLit := natTerm aNat
      -- A binder without the source position of the command's `k`, which may be unused.
      let kBinder := mkIdent k.getId
      let body ← `(∏ $kBinder:ident ∈ Finset.Icc $aLit $nIdent, $factor = $F)
      let m := mkIdent `m
      let ih := mkIdent `ih
      let factorialRewrite ← if form.factorials.isEmpty then `(tactic| skip)
        else `(tactic| simp only [Nat.factorial_succ])
      let step ← `(tactic| (
        rw [Finset.prod_Icc_succ_top (by omega), $ih:ident]
        $factorialRewrite:tactic
        push_cast
        first
          | ring1
          | (field_simp; done)
          | (field_simp; ring1)))
      if aNat ≤ 1 then
        proveStatement "product" (← `(∀ $nIdent:ident : ℕ, $body)) (← `(tactic| (
          intro $nIdent:ident
          induction $nIdent:ident with
          | zero => norm_num [Finset.Icc_self]
          | succ $m:ident $ih:ident => $step:tactic)))
      else
        let base := natTerm (aNat - 1)
        let statement ← `(∀ $nIdent:ident : ℕ, $base ≤ $nIdent → $body)
        proveStatement "product" statement (← `(tactic| (
          intro $nIdent:ident hn
          induction $nIdent:ident, hn using Nat.le_induction with
          | base => rw [Finset.Icc_eq_empty (by omega)]; norm_num
          | succ $m:ident hm $ih:ident => $step:tactic)))
    logReport ref {
      domain := s!"{k.getId} ∈ [{aNat}, {nIdent.getId}]"
      input := reified.render
      inputType := "factor"
      output := form.text (toString nIdent.getId) ++
        (if aNat ≤ 1 then "" else s!" for {nIdent.getId} ≥ {aNat - 1}")
      outputType := "closed form"
    } #[← liftTermElabM <| checkedEvidence "product"
        (if aNat ≤ 1 then "Closed form for every upper bound"
          else s!"Closed form for every upper bound {nIdent.getId} ≥ {aNat - 1}")
        proposition proof]
  else
    throwErrorAt input "product: the factor must be an expression in {k.getId}"

end CAS.Command.Algebra

namespace CAS.Command

open Lean Elab Command

/-- `#cas [product k a n] e` computes the product of `e` for `k` from the natural number `a` to the
variable `n` in closed form.

## Theorem
For the printed closed form `P`, the report proves `∀ n : ℕ, ∏ k ∈ Finset.Icc a n, e = P`, for
every `n ≥ a - 1` when `a ≥ 2`, by induction on `n`. The factorials in `P` are `Nat.factorial`.

## Conditions and limits
`e` is a rational function of `k` that is a constant times powers of linear factors `k + s` with
integer shifts `s`. When the exponents add up to zero the product telescopes to a rational
function of `n`; when every shift is nonnegative it is a product of factorials. Without Hex the
linear factors must be written in the input; `CASHex.Factor` factors the numerator and the
denominator over `ℚ`. A factor that vanishes in the range, a rational shift, or an irreducible
factor of degree two or more is refused.

## Options
None.

## Examples
```lean
#cas [product k 1 n] ((k + 1) / k)
```
```output
Output (closed form): (n + 1)
```
```lean
#cas [product k 1 n] (2*k)
```
```output
Output (closed form): 2^n*n!
```

## In a proof
```lean
theorem product_telescoping : ∀ n : ℕ, ∏ k ∈ Finset.Icc 1 n, ((k : ℝ) + 1) / k = n + 1 := by
  cas
```

## See also
Mathematica `Product`, SymPy `product`. Hex `Hex.ZPoly.factorize` (through `CASHex.Factor`)
splits the factors of `e`. The modes `sum` and `factor`, and the call `gamma x`.

## Possible issues
```lean
#cas [product k 1 5] (k)
```
```output
product: the upper bound must be a variable
```
Use a variable upper bound and evaluate the closed form: `#cas [product k 1 n] (k)` gives `n!`.
```lean
#cas [product k 2 n] (1 - 1 / k ^ 2)
```
```output
product: the factor is not, as written, a constant times powers of linear factors k + s with
integer s, and without Hex `product` does not factor it: write it as such a product, or use
CASHex (`lake -R -Khex=on build CASHex`, `import CASHex.Factor`), which factors it completely
over ℚ
```
Write the factor as `(k - 1) * (k + 1) / k ^ 2`, or import `CASHex.Factor`.
```lean
#cas [product k 1 n] (sin k)
```
```output
product: the expression is not a rational function: it has a function other than the field
operations and natural powers
```
The factors are rational functions of `k`.
-/
syntax (name := casProductCommand) "#cas" "[" &"product" ident term:max term:max "]" term :
  command

elab_rules : command
  | `(#cas [product $k:ident $a:term $b:term] $f:term) => do
      Algebra.logProduct f k a b f (← liftCoreM Tactic.RouteRegistry.factorProvider?)

end CAS.Command
