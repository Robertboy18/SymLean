/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Expr.SmartConstructors
public import CAS.Expr.Operators

/-!
# Polynomial normalization for verified expressions

`Alg.normalize` is the unconditional algebraic normalizer of verified expressions. It expands the
polynomial fragment of an expression into a sum of monomials with rational coefficients, collects
like terms, adds two quotients only when their denominators agree, and records no side conditions.
`eval_normalize` proves that it preserves real evaluation at every valuation, and
`eval_eq_of_normalize_sub_eq_zero` makes it the side-condition-free first attempt of the exact
equality tactics.

## Main definitions

* `Monomial`, `Poly`: sparse polynomials with rational coefficients whose monomials are lists of
  symbolic factors.
* `polyOf`, `normalizePoly`, `normalizePolynomial`: reflection into sparse form, term
  collection, and reconstruction of an expression tree.
* `sameDenominator?`: syntactic equality of two normalized denominators, up to one top-level
  commuted addition.
* `normalize`: the recursive normalizer, which applies `normalizePolynomial` to every algebraic
  fragment and keeps quotients as quotients.

## Main results

* `eval_normalizePolynomial`, `eval_normalize`: both normalizers preserve real evaluation at
  every valuation, unconditionally.
* `eval_eq_zero_of_normalize_eq_zero`, `eval_eq_of_normalize_sub_eq_zero`: a normal form that is
  literally `0` proves that the input is identically zero, or that two expressions are equal.

## Implementation notes

The representation is a sparse polynomial `Poly ι = List (Rat × Monomial ι)` whose monomials are
lists of symbolic factors. Anything that is not built from `+`, `-`, `*`, natural powers, and
numeric literals (a variable, `sin a`, `exp a`, a quotient, ...) becomes an opaque factor, so
`polyOf` reflects an expression into polynomials with rational coefficients in these factors.
`normalizePoly` merges like terms (monomials equal up to a permutation of their factors) and
drops zero coefficients, but keeps the encounter order of the surviving terms, so the result is
a sparse representation rather than a canonical normal form; `sameDenominator?` compensates for
this when denominators are compared, and the ordered form is the job of `Alg.canonical`. `Poly`
is not the exponent-vector carrier `Alg.MvPoly` of the sparse arithmetic in
`CAS.Polynomial.Sparse`, whose module doc names the bridges between the two. A result other
than `0` is inconclusive, since the opaque factors may satisfy relations such as
`sin x ^ 2 + cos x ^ 2 = 1`.

Unconditional soundness rests on the fact that every rewrite used here is an identity of the
real field with totalized division: `n₁/d + n₂/d = (n₁ + n₂)/d`, `-(n/d) = (-n)/d`,
`(a/b) * (c/d) = (a*c)/(b*d)`, and `(a/b) * e = (a*e)/b` all hold with no hypothesis on the
denominators. The one identity that fails when a denominator vanishes, cross-multiplication
`a/b + c/d = (a*d + c*b)/(b*d)`, is never applied; `normalizeAdd` keeps two quotients over
different denominators as a sum. The side-aware normalizers `Alg.normalizeWithSide` and
`Alg.normalizeFractionWithSide` do apply it and consequently return denominator side conditions.
`eval_normalizePolynomial` evaluates the sparse form term by term, and `eval_normalize` follows
by induction on the expression from `eval_normalizeAdd`, `eval_normalizeSub` and
`eval_normalizeMul`.
-/

@[expose] public section

namespace CAS

open scoped BigOperators

namespace Verified.Expr

namespace Alg

/-- A monomial is a product of symbolic factors.  Factors are kept as expressions:
this lets the normalizer collect terms such as `c*x*x` even when `c` is a symbolic constant like
`-1/(4*pi)`. -/
abbrev Monomial (ι : Type*) := List (Verified.Expr ι)

/-- A sparse rational-coefficient polynomial. -/
abbrev Poly (ι : Type*) := List (Rat × Monomial ι)

/-- Reconstruct a symbolic product from a monomial factor list. -/
def monoExpr {ι : Type*} : Monomial ι → Verified.Expr ι
  | [] => .nat 1
  | hd :: tl => mkMul hd (monoExpr tl)

/-- Reconstruct one sparse term as an expression. A zero coefficient gives `0`, a coefficient of
`1` gives the bare monomial product, and any other coefficient becomes a rational constant factor
in front of the monomial. -/
def termExpr {ι : Type*} (term : Rat × Monomial ι) : Verified.Expr ι :=
  let coeff := term.1
  let mono := monoExpr term.2
  if coeff = 0 then
    .nat 0
  else if coeff = 1 then
    mono
  else
    mkMul (mkRatConst coeff) mono

/-- Reconstruct a sparse polynomial as a right-nested sum of its term expressions. The empty
polynomial is `0`. -/
def polyExpr {ι : Type*} : Poly ι → Verified.Expr ι
  | [] => .nat 0
  | hd :: tl => mkAdd (termExpr hd) (polyExpr tl)

/-- Add `coeff * mono` to a sparse polynomial, merging it into the first term whose monomial is a
permutation of `mono`. A term whose combined coefficient becomes zero is dropped, and a zero
`coeff` is never appended. -/
def insertTerm {ι : Type*} [DecidableEq ι] (coeff : Rat) (mono : Monomial ι) :
    Poly ι → Poly ι
  | [] => if coeff = 0 then [] else [(coeff, mono)]
  | (c, m) :: rest =>
      if m.Perm mono then
        if c + coeff = 0 then rest else (c + coeff, m) :: rest
      else
        (c, m) :: insertTerm coeff mono rest

/-- Combine equal monomials and remove zero coefficients from a sparse polynomial. -/
def normalizePoly {ι : Type*} [DecidableEq ι] : Poly ι → Poly ι :=
  List.foldl (fun acc term ↦ insertTerm term.1 term.2 acc) []

/-- Add two sparse polynomials by concatenating their terms and collecting like terms. -/
def addPoly {ι : Type*} [DecidableEq ι] (a b : Poly ι) : Poly ι :=
  normalizePoly (a ++ b)

/-- Negate every coefficient of a sparse polynomial, leaving the monomials unchanged. -/
def negPoly {ι : Type*} (a : Poly ι) : Poly ι :=
  a.map fun term ↦ (-term.1, term.2)

/-- Subtract sparse polynomials as `a + (-b)`, collecting like terms. -/
def subPoly {ι : Type*} [DecidableEq ι] (a b : Poly ι) : Poly ι :=
  addPoly a (negPoly b)

/-- Multiply two sparse terms: the coefficients multiply and the factor lists concatenate. -/
def mulTerm {ι : Type*} (a b : Rat × Monomial ι) : Rat × Monomial ι :=
  (a.1 * b.1, a.2 ++ b.2)

/-- Multiply two sparse polynomials term by term and collect like terms in the product. -/
def mulPoly {ι : Type*} [DecidableEq ι] (a b : Poly ι) : Poly ι :=
  normalizePoly <| a.flatMap fun ta ↦ b.map fun tb ↦ mulTerm ta tb

/-- Raise a sparse polynomial to a natural power by repeated `mulPoly`; the zeroth power is the
constant polynomial `1`. -/
def powPoly {ι : Type*} [DecidableEq ι] (a : Poly ι) : Nat → Poly ι
  | 0 => [(1, [])]
  | k + 1 => mulPoly a (powPoly a k)

/-- Expand the polynomial fragment of a symbolic expression into sparse form. Unsupported heads
are treated as opaque factors, so the normalizer remains useful around non-polynomial terms. -/
def polyOf {ι : Type*} [DecidableEq ι] : Verified.Expr ι → Poly ι
  | .nat n => if n = 0 then [] else [((n : Rat), [])]
  | .int z => if z = 0 then [] else [((z : Rat), [])]
  | .rat num den =>
      let q := Rat.divInt num (den : Int)
      if q = 0 then [] else [(q, [])]
  | .add a b => addPoly (polyOf a) (polyOf b)
  | .sub a b => subPoly (polyOf a) (polyOf b)
  | .neg a => negPoly (polyOf a)
  | .mul a b => mulPoly (polyOf a) (polyOf b)
  | .pow a k => powPoly (polyOf a) k
  | expr => [(1, [expr])]

/-- Normalize a symbolic polynomial and reconstruct its expression tree. -/
def normalizePolynomial {ι : Type*} [DecidableEq ι]
    (expr : Verified.Expr ι) : Verified.Expr ι :=
  polyExpr (normalizePoly (polyOf expr))

/-!
`normalizePolynomial` combines like terms but preserves the encounter order of additive terms.
That is enough for sound evaluation, but denominator comparison needs one extra conservative
equivalence: `1 + x*x` and `x*x + 1` should count as the same denominator after polynomial
normalization. The predicate `sameDenominator?` recognizes
syntactic equality and one top-level commuted addition; full canonical ordering is the job of
`Alg.canonical`.
-/

/-- Detect whether two symbolic denominators normalize to the same expression. -/
def sameDenominator? {ι : Type*} [DecidableEq ι]
    (a b : Verified.Expr ι) : Bool :=
  if a = b then
    true
  else
    match a, b with
    | .add a1 a2, .add b1 b2 =>
        if a1 = b2 then
          if a2 = b1 then true else false
        else
          false
    | _, _ => false

/-- Equal normalized denominators have equal real-valued semantics. -/
theorem eval_eq_of_sameDenominator? {ι : Type*} [DecidableEq ι]
    (ρ : ι → ℝ) {a b : Verified.Expr ι}
    (h : sameDenominator? a b = true) :
    a.eval ρ = b.eval ρ := by
  unfold sameDenominator? at h
  split_ifs at h with heq
  · rw [heq]
  · split at h
    · rename_i a1 a2 b1 b2
      obtain ⟨rfl, rfl⟩ : a1 = b2 ∧ a2 = b1 := by simpa using h
      simp only [eval]
      ring
    · cases h

/-! ### Recursive expression normalization

The polynomial reflector `polyOf` handles each algebraic fragment. The recursive normalizer
`normalize` applies it throughout an expression while retaining divisions whose denominator
structure carries analytic side conditions.
-/

/-- Normalize a sum whose operands are already normalized. Two quotients with the same normalized
denominator are merged into one quotient over that denominator; other quotient pairs are kept as
a plain sum, and any other pair is added and polynomial-normalized. -/
def normalizeAdd {ι : Type*} [DecidableEq ι]
    (a b : Verified.Expr ι) : Verified.Expr ι :=
  match a, b with
  | .div na da, .div nb db =>
      let daNorm := normalizePolynomial da
      let dbNorm := normalizePolynomial db
      if sameDenominator? daNorm dbNorm then
        mkDiv (normalizePolynomial (mkAdd na nb)) daNorm
      else
        mkAdd a b
  | _, _ => normalizePolynomial (mkAdd a b)

/-- Normalize a difference whose operands are already normalized. Two quotients with the same
normalized denominator are merged into one quotient over that denominator; every other pair is
subtracted and polynomial-normalized. -/
def normalizeSub {ι : Type*} [DecidableEq ι]
    (a b : Verified.Expr ι) : Verified.Expr ι :=
  match a, b with
  | .div na da, .div nb db =>
      let daNorm := normalizePolynomial da
      let dbNorm := normalizePolynomial db
      if sameDenominator? daNorm dbNorm then
        mkDiv (normalizePolynomial (mkSub na nb)) daNorm
      else
        normalizePolynomial (mkSub a b)
  | _, _ => normalizePolynomial (mkSub a b)

/-- Normalize a product while preserving compatible rational structure. -/
def normalizeMul {ι : Type*} [DecidableEq ι]
    (a b : Verified.Expr ι) : Verified.Expr ι :=
  match a, b with
  | .div na da, .div nb db =>
      mkDiv (normalizePolynomial (mkMul na nb)) (normalizePolynomial (mkMul da db))
  | .div na da, expr =>
      mkDiv (normalizePolynomial (mkMul na expr)) da
  | expr, .div nb db =>
      mkDiv (normalizePolynomial (mkMul expr nb)) db
  | _, _ => normalizePolynomial (mkMul a b)

/-- Executable algebraic normalizer for symbolic expressions. -/
def normalize {ι : Type*} [DecidableEq ι] : Verified.Expr ι → Verified.Expr ι
  | .add a b => normalizeAdd (normalize a) (normalize b)
  | .sub a b => normalizeSub (normalize a) (normalize b)
  | .neg a =>
      match normalize a with
      | .div n d => mkDiv (normalizePolynomial (mkNeg n)) d
      | expr => normalizePolynomial (mkNeg expr)
  | .mul a b => normalizeMul (normalize a) (normalize b)
  | .div a b => mkDiv (normalize a) (normalize b)
  | .pow a k => normalizePolynomial (mkPow (normalize a) k)
  | .sin a => mkSin (normalize a)
  | .cos a => mkCos (normalize a)
  | .atan a => .atan (normalize a)
  | .asin a => .asin (normalize a)
  | .acos a => .acos (normalize a)
  | .exp a => mkExp (normalize a)
  | .log a => mkLog (normalize a)
  | .sqrt a => mkSqrt (normalize a)
  | .rpow a b => mkRpow (normalize a) (normalize b)
  | expr => expr

private noncomputable def monoVal {ι : Type*} (ρ : ι → ℝ) : Monomial ι → ℝ
  | [] => 1
  | hd :: tl => hd.eval ρ * monoVal ρ tl

private theorem monoVal_eq_prod {ι : Type*} (ρ : ι → ℝ) :
    ∀ mono : Monomial ι, monoVal ρ mono = (mono.map fun factor ↦ factor.eval ρ).prod
  | [] => by simp [monoVal]
  | hd :: tl => by simp [monoVal, monoVal_eq_prod ρ tl]

private theorem monoVal_perm {ι : Type*} (ρ : ι → ℝ) {a b : Monomial ι}
    (h : a.Perm b) : monoVal ρ a = monoVal ρ b := by
  rw [monoVal_eq_prod ρ a, monoVal_eq_prod ρ b]
  exact (h.map fun factor ↦ factor.eval ρ).prod_eq

private noncomputable def termVal {ι : Type*} (ρ : ι → ℝ) (term : Rat × Monomial ι) : ℝ :=
  (term.1 : ℝ) * monoVal ρ term.2

private noncomputable def polyVal {ι : Type*} (ρ : ι → ℝ) : Poly ι → ℝ
  | [] => 0
  | hd :: tl => termVal ρ hd + polyVal ρ tl

private theorem eval_monoExpr {ι : Type*} (ρ : ι → ℝ) :
    ∀ mono : Monomial ι, (monoExpr mono).eval ρ = monoVal ρ mono
  | [] => by simp [monoExpr, monoVal]
  | hd :: tl => by simp [monoExpr, monoVal, eval_monoExpr ρ tl]

private theorem eval_termExpr {ι : Type*} (ρ : ι → ℝ) (term : Rat × Monomial ι) :
    (termExpr term).eval ρ = termVal ρ term := by
  simp only [termExpr]
  split_ifs <;> simp [termVal, eval_monoExpr, *]

private theorem eval_polyExpr {ι : Type*} (ρ : ι → ℝ) :
    ∀ poly : Poly ι, (polyExpr poly).eval ρ = polyVal ρ poly
  | [] => by simp [polyExpr, polyVal]
  | hd :: tl => by simp [polyExpr, polyVal, eval_termExpr, eval_polyExpr ρ tl]

private theorem monoVal_append {ι : Type*} (ρ : ι → ℝ) (a b : Monomial ι) :
    monoVal ρ (a ++ b) = monoVal ρ a * monoVal ρ b := by
  induction a with
  | nil => simp [monoVal]
  | cons hd tl ih =>
      simp [monoVal, ih, mul_assoc]

private theorem termVal_mulTerm {ι : Type*} (ρ : ι → ℝ)
    (a b : Rat × Monomial ι) :
    termVal ρ (mulTerm a b) = termVal ρ a * termVal ρ b := by
  rcases a with ⟨ca, ma⟩
  rcases b with ⟨cb, mb⟩
  simp [termVal, mulTerm, monoVal_append, Rat.cast_mul]
  ring

private theorem polyVal_append {ι : Type*} (ρ : ι → ℝ) (a b : Poly ι) :
    polyVal ρ (a ++ b) = polyVal ρ a + polyVal ρ b := by
  induction a with
  | nil => simp [polyVal]
  | cons hd tl ih =>
      simp [polyVal, ih, add_assoc]

private theorem polyVal_insertTerm {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (coeff : Rat) (mono : Monomial ι) :
    ∀ poly : Poly ι,
      polyVal ρ (insertTerm coeff mono poly) =
        (coeff : ℝ) * monoVal ρ mono + polyVal ρ poly
  | [] => by by_cases hcoeff : coeff = 0 <;> simp [insertTerm, polyVal, termVal, hcoeff]
  | (c, m) :: rest => by
      by_cases h : m.Perm mono
      · have hm : monoVal ρ m = monoVal ρ mono := monoVal_perm ρ h
        by_cases hcoeff : c + coeff = 0
        · have hsum : (c : ℝ) + coeff = 0 := by exact_mod_cast hcoeff
          simp only [insertTerm, h, ↓reduceIte, hcoeff, polyVal, termVal, hm]
          linear_combination -monoVal ρ mono * hsum
        · simp [insertTerm, h, hcoeff, polyVal, termVal, Rat.cast_add, hm]
          ring
      · simp [insertTerm, h, polyVal, termVal, polyVal_insertTerm ρ coeff mono rest]
        ring

private theorem polyVal_fold_insert {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (xs acc : Poly ι) :
    polyVal ρ (List.foldl (fun acc term ↦ insertTerm term.1 term.2 acc) acc xs) =
      polyVal ρ acc + polyVal ρ xs := by
  induction xs generalizing acc with
  | nil => simp [polyVal]
  | cons hd tl ih =>
      rcases hd with ⟨coeff, mono⟩
      simp [polyVal, ih, polyVal_insertTerm, termVal]
      ring_nf

private theorem polyVal_normalizePoly {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (poly : Poly ι) :
    polyVal ρ (normalizePoly poly) = polyVal ρ poly := by
  simp [normalizePoly, polyVal_fold_insert, polyVal]

private theorem polyVal_addPoly {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (a b : Poly ι) :
    polyVal ρ (addPoly a b) = polyVal ρ a + polyVal ρ b := by
  simp [addPoly, polyVal_normalizePoly, polyVal_append]

private theorem polyVal_negPoly {ι : Type*} (ρ : ι → ℝ) :
    ∀ poly : Poly ι, polyVal ρ (negPoly poly) = -polyVal ρ poly := by
  intro poly
  induction poly with
  | nil => simp [negPoly, polyVal]
  | cons hd tl ih =>
      simp only [negPoly, List.map_cons, polyVal, termVal, Rat.cast_neg, neg_mul] at ih ⊢
      rw [ih, neg_add]

private theorem polyVal_subPoly {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (a b : Poly ι) :
    polyVal ρ (subPoly a b) = polyVal ρ a - polyVal ρ b := by
  simp [subPoly, polyVal_addPoly, polyVal_negPoly, sub_eq_add_neg]

private theorem polyVal_map_mulTerm {ι : Type*} (ρ : ι → ℝ)
    (a : Rat × Monomial ι) :
    ∀ b : Poly ι,
      polyVal ρ (b.map fun tb ↦ mulTerm a tb) = termVal ρ a * polyVal ρ b
  | [] => by simp [polyVal]
  | hd :: tl => by
      simp [polyVal, termVal_mulTerm, polyVal_map_mulTerm ρ a tl]
      ring

private theorem polyVal_mulPoly {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (a b : Poly ι) :
    polyVal ρ (mulPoly a b) = polyVal ρ a * polyVal ρ b := by
  induction a with
  | nil => simp [mulPoly, polyVal, polyVal_normalizePoly]
  | cons hd tl ih =>
      simp only [mulPoly, polyVal_normalizePoly] at ih ⊢
      simp only [List.flatMap_cons, polyVal_append, polyVal_map_mulTerm, ih, polyVal, add_mul]

private theorem polyVal_powPoly {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (poly : Poly ι) :
    ∀ k : Nat, polyVal ρ (powPoly poly k) = polyVal ρ poly ^ k := by
  intro k
  induction k with
  | zero => simp [powPoly, polyVal, termVal, monoVal]
  | succ k ih => rw [powPoly, polyVal_mulPoly, ih, pow_succ']

private theorem polyVal_polyOf {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ) :
    ∀ expr : Verified.Expr ι, polyVal ρ (polyOf expr) = expr.eval ρ := by
  intro expr
  induction expr with
  | nat n => by_cases h : n = 0 <;> simp [polyOf, h, polyVal, termVal, monoVal]
  | int z => by_cases h : z = 0 <;> simp [polyOf, h, polyVal, termVal, monoVal]
  | rat num den =>
      have hqeval : ((Rat.divInt num (den : Int) : Rat) : ℝ) = (num : ℝ) / (den : ℝ) := by
        simp
      by_cases hq : Rat.divInt num (den : Int) = 0
      · simp only [polyOf, hq, ↓reduceIte, polyVal, eval]
        rw [← hqeval, hq, Rat.cast_zero]
      · simp only [polyOf, hq, ↓reduceIte, polyVal, termVal, monoVal, eval, mul_one, add_zero,
          hqeval]
  | add a b iha ihb => simp [polyOf, polyVal_addPoly, iha, ihb]
  | mul a b iha ihb => simp [polyOf, polyVal_mulPoly, iha, ihb]
  | sub a b iha ihb => simp [polyOf, polyVal_subPoly, iha, ihb]
  | neg a ih => simp [polyOf, polyVal_negPoly, ih]
  | pow a k ih => simp [polyOf, polyVal_powPoly, ih]
  | _ => simp [polyOf, polyVal, termVal, monoVal]

/-- Polynomial normalization preserves evaluation. -/
theorem eval_normalizePolynomial {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (expr : Verified.Expr ι) :
    (normalizePolynomial expr).eval ρ = expr.eval ρ := by
  simp [normalizePolynomial, eval_polyExpr, polyVal_normalizePoly, polyVal_polyOf]

/-- Normalizing a sum preserves its real value, including the shared-denominator
shortcut when that denominator evaluates to zero. -/
theorem eval_normalizeAdd {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (a b : Verified.Expr ι) :
    (normalizeAdd a b).eval ρ = a.eval ρ + b.eval ρ := by
  dsimp only [normalizeAdd]
  split
  · split
    · rename_i h
      have := eval_eq_of_sameDenominator? ρ h
      simp only [eval_normalizePolynomial] at this
      simp [eval_normalizePolynomial, this, add_div]
    · simp
  · simp [eval_normalizePolynomial]

/-- Normalizing a difference preserves its real value without denominator assumptions. -/
theorem eval_normalizeSub {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (a b : Verified.Expr ι) :
    (normalizeSub a b).eval ρ = a.eval ρ - b.eval ρ := by
  dsimp only [normalizeSub]
  split
  · split
    · rename_i h
      have := eval_eq_of_sameDenominator? ρ h
      simp only [eval_normalizePolynomial] at this
      simp [eval_normalizePolynomial, this, sub_div]
    · simp [eval_normalizePolynomial]
  · simp [eval_normalizePolynomial]

/-- Multiplicative normalization preserves evaluation. -/
theorem eval_normalizeMul {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (a b : Verified.Expr ι) :
    (normalizeMul a b).eval ρ = a.eval ρ * b.eval ρ := by
  dsimp only [normalizeMul]
  split <;> simp [eval_normalizePolynomial] <;> ring

/-- Soundness of the algebraic normalizer: `normalize expr` has the same real value as `expr`
at every valuation, with no side conditions. -/
@[simp] theorem eval_normalize {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ) :
    ∀ expr : Verified.Expr ι, (normalize expr).eval ρ = expr.eval ρ := by
  intro expr
  induction expr with
  | add a b iha ihb => simp [normalize, eval_normalizeAdd, iha, ihb]
  | sub a b iha ihb => simp [normalize, eval_normalizeSub, iha, ihb]
  | mul a b iha ihb => simp [normalize, eval_normalizeMul, iha, ihb]
  | neg a ih =>
      simp only [normalize, eval, ← ih]
      cases normalize a <;> simp [eval_normalizePolynomial, neg_div]
  | _ => simp [normalize, eval_normalizePolynomial, *]

/-- If algebraic normalization computes a symbolic expression to zero, the original expression
evaluates to zero in every environment. -/
theorem eval_eq_zero_of_normalize_eq_zero {ι : Type*} [DecidableEq ι]
    (ρ : ι → ℝ) (expr : Verified.Expr ι)
    (h : normalize expr = (0 : Verified.Expr ι)) :
    expr.eval ρ = 0 := by
  rw [← eval_normalize ρ expr, h]
  simp [Verified.Expr.eval]

/-- If the unconditional normalizer computes `lhs - rhs` to symbolic zero, the two expressions
evaluate equally at every valuation. This is the side-condition-free fast path of the exact
equality tactics. -/
theorem eval_eq_of_normalize_sub_eq_zero {ι : Type*} [DecidableEq ι]
    (ρ : ι → ℝ) (lhs rhs : Verified.Expr ι)
    (h : normalize (lhs - rhs) = (0 : Verified.Expr ι)) :
    lhs.eval ρ = rhs.eval ρ :=
  sub_eq_zero.mp (eval_eq_zero_of_normalize_eq_zero ρ (lhs - rhs) h)

end Alg

end Verified.Expr
end CAS
