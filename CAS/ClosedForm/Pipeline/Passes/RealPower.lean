/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Pipeline.BottomUp
public import CAS.ClosedForm.Pipeline.Passes.NumericLiteral
public import CAS.Expr.AutomaticSign
public import CAS.Expr.Decomposition

/-!
# Real-power and exponential normal form

The side-conditioned pass that gives the checked normalizer the algebra of real
powers `a ^ b` (`Verified.Expr.rpow`, Mathlib's `Real.rpow`) and of the exponential, which the
pass treats as the power `e ^ u`. The polynomial normalizer sees a real power as an opaque atom,
so `a ^ p * a ^ q` and `a ^ (p + q)` are unrelated to it. The pass merges such atoms into one
power per base and puts the exponent into a fixed normal form, after which the polynomial
normalizer cancels the atoms.

## Main definitions

* `exponentNormal`: the normal form of an exponent.
* `productTop`, `rpowTop`, `powTop`, `sqrtTop`: the rewrites of one product or quotient, real
  power, natural power and square root node.
* `identifyExponents`: one representative for the exponents of a base that are equal as
  polynomials.
* `realPowerDeepCleanup`, `realPowerSidePass`: the bottom-up pass and its side pass.

## Main results

* `eval_realPowerDeepCleanup`: wherever the recorded conditions hold, the normal form evaluates
  to the original expression, the same form as the soundness theorems of the other side passes.

## Implementation notes

The rewrites are Mathlib's identities for `Real.rpow`.
Inside a product or quotient we collect the powers of one base `a` (the factors `a ^ p`, `a`,
`a ^ n`, `sqrt a`, and the corresponding denominator factors) into a single `a ^ e`, whose
exponent is the sum of the numerator exponents minus that of the denominator exponents
(`Real.rpow_add`, `Real.rpow_sub`, `Real.rpow_mul_natCast`, `Real.sqrt_eq_rpow`). Collection is
triggered by a power factor `a ^ p`, `exp u`, or `e`, never by a square root or a natural power
alone, so polynomial and square-root normal forms are left to their own passes. One traversal
collects one base per product node, the first whose collection changes the node; later rounds
of the side-pass iteration reach the others, as far as the fuel allows. Nested powers flatten,
`(a ^ p) ^ q = a ^ (p * q)`, `(a ^ n) ^ q = a ^ (n * q)`, `(sqrt a) ^ q = a ^ (q / 2)`
(`Real.rpow_mul`, `Real.rpow_natCast_mul`), and so do natural powers and square roots of powers
(`powTop`, `sqrtTop`). A power of a product or quotient distributes,
`(a * b) ^ p = a ^ p * b ^ p` (`Real.mul_rpow`, `Real.div_rpow`). Exponentials are the powers of
the base `e`:
`exp a * exp b = exp (a + b)`, `x / exp a = x * exp (-a)`, `exp u ^ n = exp (n * u)`
(`Real.exp_one_rpow`, `Real.exp_mul`); these rewrites need no hypothesis.

Exponents are normalized by `exponentNormal`: quotients by numeric literals become rational
coefficients, the polynomial normalizer collects terms, and the constant term is moved last.
Exponents that are equal as polynomials but list their atoms in another order, such as `p + q`
and `q + p`, are identified after the traversal (`identifyExponents`), so that `a ^ t * a ^ s`
and `a ^ (s + t)` share one power. A literal exponent is then read off. An integer exponent is a
natural power or its reciprocal (`Real.rpow_intCast`). For a symbolic base, `a ^ (1/2)` is
`sqrt a` and `a ^ (-1/2)` is `1 / sqrt a` (`Real.sqrt_eq_rpow`, `Real.rpow_neg_eq_inv_rpow`,
`Real.sqrt_inv`), and any other literal `k + r` whose integer part `k`, rounded toward zero, is
nonzero splits as `a ^ k * a ^ r`, written as a reciprocal when `k < 0`: `a ^ (3/2) = a * sqrt a`
and `a ^ (-3/2) = 1 / (a * sqrt a)` (`Real.rpow_add`, `Real.rpow_neg`). A positive numeric base
`c` keeps the constant term of its exponent in `[0, 1)`: `c ^ (e + k)` becomes `c ^ k * c ^ e`
with the rational `c ^ k` folded into the coefficient. A natural base up to `2 ^ 16` that is a
perfect power of a smaller natural number (`perfectPower?`) is first rewritten to the smallest
such base, `4 ^ e = 2 ^ (2 * e)`, `8 ^ e = 2 ^ (3 * e)`, `9 ^ e = 3 ^ (2 * e)`
(`Real.rpow_natCast_mul`), so that `(2 ^ j) ^ 2` and `4 ^ j` share the normal form
`2 ^ (2 * j)`. A positive rational literal base `m / n` in lowest terms is split into the
quotient of two natural-base powers `m ^ e / n ^ e` (`Real.div_rpow`), so that `(1 / 4) ^ p` and
`1 / 2 ^ (2 * p)` share a normal form whether the base reaches the pass as the quotient `1 / 4`
or, after the polynomial normalizer has folded it, as the rational literal `1/4`.

Every rewrite that Mathlib states for a positive or nonnegative base records the positivity of
that base as the entry `sqrt a`, the encoding of `0 < a` used by every side-conditioned pass
(`Real.sqrt_ne_zero'`). For the lemmas that need only `0 ≤ a`, such as `Real.rpow_mul` and
`Real.mul_rpow`, this is stronger than necessary, since the list holds nonzero facts only. A
base recognized as positive by the structural checker `AutomaticSign.positive` records nothing:
positive numerals, `π`, `e`, exponentials, and sums, products, quotients, powers and square
roots of such terms. Rewrites that hold for Mathlib's total `Real.rpow` without any
hypothesis record nothing either.

The pass first scans the expression for a node it can act on (`hasPowerAtom`: a real power, an
exponential, the constant `e`, or a natural power of a square root) and returns the expression
unchanged when there is none, so an expression without such a node, a polynomial or a rational
function for instance, costs one linear scan per run of the pass.
-/

@[expose] public section

namespace CAS.Verified.Expr
namespace RealPower

open Alg

/-! ### Exponent normal form -/

/-- Whether an expression is a numeric literal accepted by `NumericLiteral.parse?`. -/
def isLiteral {ι : Type*} (expr : Verified.Expr ι) : Bool :=
  (NumericLiteral.parse? expr).isSome

/-- Replace every quotient by a nonzero numeric literal inside the arithmetic skeleton of an
exponent by multiplication with the reciprocal rational, so that `s / 2` and `(1/2) * s` share
one polynomial normal form. Other nodes are left alone. -/
def exponentCanon {ι : Type*} [DecidableEq ι] : Verified.Expr ι → Verified.Expr ι
  | .add a b => mkAdd (exponentCanon a) (exponentCanon b)
  | .sub a b => mkSub (exponentCanon a) (exponentCanon b)
  | .mul a b => mkMul (exponentCanon a) (exponentCanon b)
  | .neg a => mkNeg (exponentCanon a)
  | .pow a n => mkPow (exponentCanon a) n
  | .div a b =>
      match NumericLiteral.parse? b with
      | some q =>
          if q = 0 then mkDiv (exponentCanon a) b
          else mkMul (mkRatConst q⁻¹) (exponentCanon a)
      | none => mkDiv (exponentCanon a) (exponentCanon b)
  | expr => expr

/-- `exponentCanon` preserves evaluation; `x / q = q⁻¹ * x` holds for every real `x` and every
nonzero rational `q`. -/
theorem eval_exponentCanon {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ) :
    ∀ expr : Verified.Expr ι, (exponentCanon expr).eval ρ = expr.eval ρ := by
  intro expr
  induction expr with
  | div a b iha ihb =>
      cases hb : NumericLiteral.parse? b with
      | none => simp [exponentCanon, hb, iha, ihb]
      | some q =>
          by_cases hq : q = 0
          · simp [exponentCanon, hb, hq, iha]
          · simp [exponentCanon, hb, hq, iha, NumericLiteral.eval_parse?_eq_some ρ b q hb,
              div_eq_inv_mul]
  | _ => simp [exponentCanon, *]

/-- Move the numeric literal terms of a sum behind its symbolic terms, so that `1 + p` and
`p + 1` share one normal form. Sums without a literal term are returned unchanged. -/
def constantLast {ι : Type*} (expr : Verified.Expr ι) : Verified.Expr ι :=
  let terms := additiveTerms expr
  let literals := terms.filter isLiteral
  if literals.isEmpty then expr
  else mkAddList (terms.filter (fun term ↦ !isLiteral term) ++ literals)

/-- `constantLast` permutes the summands of a sum and therefore preserves evaluation. -/
theorem eval_constantLast {ι : Type*} (ρ : ι → ℝ) (expr : Verified.Expr ι) :
    (constantLast expr).eval ρ = expr.eval ρ := by
  dsimp only [constantLast]
  split
  · rfl
  · rw [eval_mkAddList, ← eval_mkAddList_additiveTerms ρ expr, eval_mkAddList]
    refine (List.Perm.map _ ?_).sum_eq
    simpa using List.filter_append_perm (fun term ↦ !isLiteral term) (additiveTerms expr)

/-- The exponent normal form: literal denominators are folded into rational coefficients, the
polynomial normalizer collects terms, and the constant term is moved last. -/
def exponentNormal {ι : Type*} [DecidableEq ι] (expr : Verified.Expr ι) : Verified.Expr ι :=
  constantLast (normalize (exponentCanon expr))

/-- The exponent normal form preserves evaluation. -/
@[simp] theorem eval_exponentNormal {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (expr : Verified.Expr ι) :
    (exponentNormal expr).eval ρ = expr.eval ρ := by
  simp [exponentNormal, eval_constantLast, eval_normalize, eval_exponentCanon]

/-! ### Reading factors as powers -/

/-- Read a factor as a power `base ^ exponent`: `a ^ p`, `sqrt a = a ^ (1/2)`, `exp u = e ^ u`,
`e = e ^ 1`, `x ^ n` as the `n`-fold exponent of the reading of `x`, and any other factor as its
own first power. -/
def readPower {ι : Type*} : Verified.Expr ι → Verified.Expr ι × Verified.Expr ι
  | .rpow base exponent => (base, exponent)
  | .sqrt base => (base, .rat 1 2)
  | .exp argument => (.e, argument)
  | .e => (.e, .nat 1)
  | .pow inner n => ((readPower inner).1, mkMul (.nat n) (readPower inner).2)
  | factor => (factor, .nat 1)

/-- A factor evaluates to the power it is read as, provided its base is positive. The natural
power case is `Real.rpow_mul_natCast`; the square root, exponential, and trivial cases are
`Real.sqrt_eq_rpow`, `Real.exp_one_rpow`, and `Real.rpow_one`. -/
theorem eval_readPower {ι : Type*} (ρ : ι → ℝ) :
    ∀ factor : Verified.Expr ι, 0 < (readPower factor).1.eval ρ →
      factor.eval ρ = (readPower factor).1.eval ρ ^ (readPower factor).2.eval ρ := by
  intro factor h
  induction factor with
  | sqrt base => simp [readPower, Real.sqrt_eq_rpow]
  | pow inner n ih =>
      simp only [readPower, Verified.Expr.eval, eval_mkMul] at h ih ⊢
      rw [ih h, mul_comm, Real.rpow_mul_natCast h.le]
  | _ => simp [readPower]

/-- Build the power `base ^ exponent`, writing powers of `e` as exponentials. -/
def mkPower {ι : Type*} (base exponent : Verified.Expr ι) : Verified.Expr ι :=
  match base with
  | .e => mkExp exponent
  | _ => mkRpow base exponent

/-- `mkPower` evaluates to the real power of its base (`Real.exp_one_rpow` for the base `e`). -/
@[simp] theorem eval_mkPower {ι : Type*} (ρ : ι → ℝ) (base exponent : Verified.Expr ι) :
    (mkPower base exponent).eval ρ = base.eval ρ ^ exponent.eval ρ := by
  cases base <;> simp [mkPower, Real.exp_one_rpow]

/-- The recorded positivity obligation for a base: nothing when the structural sign checker
proves `0 < base`, otherwise the entry `sqrt base`, the encoding of `0 < base` in a
`nonzero` list. -/
def positivityCondition {ι : Type*} [DecidableEq ι] (base : Verified.Expr ι) :
    List (Verified.Expr ι) :=
  if AutomaticSign.positive base then [] else [.sqrt base]

/-- A base is positive wherever its recorded positivity obligation holds. -/
theorem eval_pos_of_positivityCondition {ι : Type*} [DecidableEq ι] {ρ : ι → ℝ}
    {base : Verified.Expr ι} (h : SideHolds ρ (positivityCondition base)) :
    0 < base.eval ρ := by
  unfold positivityCondition at h
  split at h
  · exact AutomaticSign.eval_pos_of_positive_eq_true ρ base (by assumption)
  · exact Real.sqrt_ne_zero'.mp (SideHolds.of_singleton h)

/-! ### Collecting the powers of one base in a product -/

/-- Whether a factor is a power that triggers collection of its base: a real power, an
exponential, the constant `e`, or a natural power of one of these. Square roots and natural
powers of other expressions do not trigger collection. -/
def isPowerWitness {ι : Type*} : Verified.Expr ι → Bool
  | .rpow _ _ => true
  | .exp _ => true
  | .e => true
  | .pow inner _ => isPowerWitness inner
  | _ => false

/-- Split a factor list into the exponents of the factors that read as powers of `base` and
the remaining factors. Numeric literals are never read as powers of a numeric base, since the
integer part of such a power is kept in the coefficient. -/
def extractBasePowers {ι : Type*} [DecidableEq ι] (base : Verified.Expr ι) :
    List (Verified.Expr ι) → List (Verified.Expr ι) × List (Verified.Expr ι)
  | [] => ([], [])
  | factor :: rest =>
      let tail := extractBasePowers base rest
      if (readPower factor).1 = base ∧ !isLiteral factor then
        ((readPower factor).2 :: tail.1, tail.2)
      else
        (tail.1, factor :: tail.2)

/-- Extracting the powers of a positive base from a product leaves the product unchanged:
the product of the factors is the base raised to the sum of the extracted exponents times the
product of the remaining factors (`Real.rpow_add`). -/
theorem eval_extractBasePowers {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    {base : Verified.Expr ι} (hbase : 0 < base.eval ρ) :
    ∀ factors : List (Verified.Expr ι),
      (factors.map fun factor ↦ factor.eval ρ).prod =
        base.eval ρ ^ ((extractBasePowers base factors).1.map fun exponent ↦ exponent.eval ρ).sum *
          ((extractBasePowers base factors).2.map fun factor ↦ factor.eval ρ).prod
  | [] => by simp [extractBasePowers]
  | factor :: rest => by
      simp only [extractBasePowers]
      split_ifs with hmatch
      · simp only [List.map_cons, List.prod_cons, List.sum_cons,
          eval_extractBasePowers ρ hbase rest, eval_readPower ρ factor (hmatch.1 ▸ hbase),
          hmatch.1, Real.rpow_add hbase]
        ring
      · simp only [List.map_cons, List.prod_cons, eval_extractBasePowers ρ hbase rest]
        ring

/-- Collect every power of `base` in the numerator and denominator factor lists into one power
placed last in the numerator, with the normalized exponent (numerator exponents minus
denominator exponents). -/
def collectBase {ι : Type*} [DecidableEq ι] (base : Verified.Expr ι)
    (num den : List (Verified.Expr ι)) : Verified.Expr ι :=
  let numerator := extractBasePowers base num
  let denominator := extractBasePowers base den
  let exponent := exponentNormal (mkSub (mkAddList numerator.1) (mkAddList denominator.1))
  mkDiv (mkMulList (numerator.2 ++ [mkPower base exponent])) (mkMulList denominator.2)

/-- Collecting the powers of a positive base preserves the value of the quotient
(`Real.rpow_sub`). -/
theorem eval_collectBase {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    {base : Verified.Expr ι} (hbase : 0 < base.eval ρ)
    (num den : List (Verified.Expr ι)) :
    (collectBase base num den).eval ρ = (mkMulList num).eval ρ / (mkMulList den).eval ρ := by
  unfold collectBase
  simp only [eval_mkDiv, eval_mkMulList, List.map_append, List.prod_append, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, eval_mkPower, eval_exponentNormal, eval_mkSub,
    eval_mkAddList, Real.rpow_sub hbase]
  rw [eval_extractBasePowers ρ hbase num, eval_extractBasePowers ρ hbase den]
  ring

/-- Whether collecting `base` changes a product: at least two of its powers occur, or one occurs
in the denominator. -/
def isActiveBase {ι : Type*} [DecidableEq ι] (base : Verified.Expr ι)
    (num den : List (Verified.Expr ι)) : Bool :=
  let numerator := extractBasePowers base num
  let denominator := extractBasePowers base den
  !denominator.1.isEmpty || decide (2 ≤ numerator.1.length + denominator.1.length)

/-- The base of the first power witness in `candidates` whose collection changes the
product. -/
def findActiveBase {ι : Type*} [DecidableEq ι] (num den : List (Verified.Expr ι)) :
    List (Verified.Expr ι) → Option (Verified.Expr ι)
  | [] => none
  | factor :: rest =>
      if isPowerWitness factor ∧ isActiveBase (readPower factor).1 num den then
        some (readPower factor).1
      else
        findActiveBase num den rest

/-- Collect the powers of the first active base of a product `num / den`, recording the
positivity of that base. `original` is the node being rewritten and is returned unchanged when
no base is active. -/
def productTop {ι : Type*} [DecidableEq ι] (original : Verified.Expr ι)
    (num den : List (Verified.Expr ι)) : NormResult ι :=
  match findActiveBase num den (num ++ den) with
  | some base => { expr := collectBase base num den, nonzero := positivityCondition base }
  | none => { expr := original, nonzero := [] }

/-- Soundness of product collection, given that `original` is the quotient of the products of
the two factor lists. -/
theorem eval_productTop {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (original : Verified.Expr ι) (num den : List (Verified.Expr ι))
    (horiginal : (mkMulList num).eval ρ / (mkMulList den).eval ρ = original.eval ρ)
    (hside : SideHolds ρ (productTop original num den).nonzero) :
    (productTop original num den).expr.eval ρ = original.eval ρ := by
  unfold productTop at hside ⊢
  split at hside
  · rename_i base _
    simp only
    rw [eval_collectBase ρ (eval_pos_of_positivityCondition hside), horiginal]
  · rfl

/-! ### Real-power nodes -/

/-- A rational raised to an integer power, computed with natural powers and one inverse. -/
def ratZpow (q : Rat) (k : Int) : Rat :=
  if 0 ≤ k then q ^ k.toNat else (q ^ (-k).toNat)⁻¹

/-- `ratZpow` casts to the real integer power. -/
theorem cast_ratZpow (q : Rat) (k : Int) : ((ratZpow q k : Rat) : ℝ) = (q : ℝ) ^ k := by
  unfold ratZpow
  split_ifs with hk
  · rw [Rat.cast_pow, ← zpow_natCast, Int.toNat_of_nonneg hk]
  · rw [Rat.cast_inv, Rat.cast_pow, ← zpow_natCast,
      Int.toNat_of_nonneg (neg_nonneg.mpr (not_le.mp hk).le), zpow_neg, inv_inv]

/-- The fractional power `base ^ r` for a literal `r`, written as a square root when
`r = 1/2`. -/
def rootPart {ι : Type*} (base : Verified.Expr ι) (r : Rat) : Verified.Expr ι :=
  if r = 1 / 2 then mkSqrt base else .rpow base (mkRatConst r)

/-- `rootPart` evaluates to the real power with the cast literal exponent
(`Real.sqrt_eq_rpow`). -/
theorem eval_rootPart {ι : Type*} (ρ : ι → ℝ) (base : Verified.Expr ι) (r : Rat) :
    (rootPart base r).eval ρ = base.eval ρ ^ (r : ℝ) := by
  unfold rootPart
  split_ifs with hr
  · rw [eval_mkSqrt, Real.sqrt_eq_rpow, hr]
    norm_num
  · simp

/-- Rewrite `base ^ q` for a literal exponent `q`.

An integer `q` gives the natural power `base ^ n` or its reciprocal, with no hypothesis
(`Real.rpow_intCast`). For a positive numeric base the exponent splits at its floor. For a
symbolic base, `q = ±1/2` gives `sqrt base` and `1 / sqrt base` without hypothesis, and any
other non-integer `q` splits at its integer part `k` (rounded toward zero) into
`base ^ k * base ^ (q - k)`, recording `0 < base`. -/
def literalExponentTop {ι : Type*} [DecidableEq ι] (base : Verified.Expr ι) (q : Rat) :
    NormResult ι :=
  if q.den = 1 then
    if 0 ≤ q.num then { expr := mkPow base q.num.toNat, nonzero := [] }
    else { expr := mkDiv (.nat 1) (mkPow base (-q.num).toNat), nonzero := [] }
  else
    match NumericLiteral.parse? base with
    | some c =>
        if c = 1 then { expr := .nat 1, nonzero := [] }
        else if 0 < c then
          let k := Rat.floor q
          { expr := mkMul (mkRatConst (ratZpow c k)) (rootPart base (q - k)), nonzero := [] }
        else { expr := .rpow base (mkRatConst q), nonzero := [] }
    | none =>
        let k := Int.tdiv q.num q.den
        if k = 0 then
          if q = 1 / 2 then { expr := mkSqrt base, nonzero := [] }
          else if q = -(1 / 2) then { expr := mkDiv (.nat 1) (mkSqrt base), nonzero := [] }
          else { expr := .rpow base (mkRatConst q), nonzero := [] }
        else if 0 < k then
          { expr := mkMul (mkPow base k.toNat) (rootPart base (q - k))
            nonzero := positivityCondition base }
        else
          { expr := mkDiv (.nat 1) (mkMul (mkPow base (-k).toNat) (rootPart base (k - q)))
            nonzero := positivityCondition base }

/-- A real raised to an integer-valued rational is its integer power. -/
private theorem rpow_rat_of_den_eq_one (x : ℝ) {q : Rat} (hq : q.den = 1) :
    x ^ (q : ℝ) = x ^ q.num := by
  have hnum : ((q.num : Rat) : ℝ) = (q : ℝ) := by rw [Rat.coe_int_num_of_den_eq_one hq]
  rw [← hnum, Rat.cast_intCast, Real.rpow_intCast]

/-- Splitting an exponent at an integer: `x ^ q = x ^ k * x ^ (q - k)` for positive `x`. -/
private theorem rpow_split_int {x : ℝ} (hx : 0 < x) (q : Rat) (k : Int) :
    x ^ (q : ℝ) = x ^ k * x ^ ((q - k : Rat) : ℝ) := by
  rw [← Real.rpow_intCast, ← Real.rpow_add hx]
  congr 1
  push_cast
  ring

/-- Soundness of the literal-exponent rewrite. -/
theorem eval_literalExponentTop {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (base : Verified.Expr ι) (q : Rat)
    (hside : SideHolds ρ (literalExponentTop base q).nonzero) :
    (literalExponentTop base q).expr.eval ρ = base.eval ρ ^ (q : ℝ) := by
  unfold literalExponentTop at hside ⊢
  by_cases hden : q.den = 1
  · simp only [hden, ↓reduceIte, rpow_rat_of_den_eq_one _ hden]
    split_ifs with hnum
    · rw [eval_mkPow, ← zpow_natCast, Int.toNat_of_nonneg hnum]
    · rw [eval_mkDiv, eval_mkPow, Verified.Expr.eval, Nat.cast_one, one_div, ← zpow_natCast,
        Int.toNat_of_nonneg (neg_nonneg.mpr (not_le.mp hnum).le), zpow_neg, inv_inv]
  · simp only [hden, ↓reduceIte] at hside ⊢
    cases hbase : NumericLiteral.parse? base with
    | some c =>
        have hc : base.eval ρ = (c : ℝ) := NumericLiteral.eval_parse?_eq_some ρ base c hbase
        simp only
        split_ifs with hone hpos
        · simp [hc, hone]
        · simp only [eval_mkMul, eval_mkRatConst, cast_ratZpow, eval_rootPart, hc]
          exact (rpow_split_int (by exact_mod_cast hpos) q ⌊q⌋).symm
        · simp [hc]
    | none =>
        simp only [hbase] at hside ⊢
        split_ifs at hside ⊢ with hk hhalf hneghalf hkpos
        · rw [eval_mkSqrt, Real.sqrt_eq_rpow, hhalf]
          norm_num
        · simp only [eval_mkDiv, eval_mkSqrt, Verified.Expr.eval, Nat.cast_one, one_div]
          rw [← Real.sqrt_inv, Real.sqrt_eq_rpow, ← Real.rpow_neg_eq_inv_rpow, hneghalf]
          norm_num
        · simp
        · simp only [eval_mkMul, eval_mkPow, eval_rootPart]
          rw [rpow_split_int (eval_pos_of_positivityCondition hside) q (q.num.tdiv q.den),
            ← zpow_natCast, Int.toNat_of_nonneg hkpos.le]
        · have hbpos := eval_pos_of_positivityCondition hside
          simp only [eval_mkDiv, eval_mkMul, eval_mkPow, eval_rootPart, Verified.Expr.eval,
            Nat.cast_one, one_div]
          rw [rpow_split_int hbpos q (q.num.tdiv q.den), ← zpow_natCast,
            Int.toNat_of_nonneg (neg_nonneg.mpr (not_lt.mp hkpos)), zpow_neg,
            ← neg_sub q (q.num.tdiv q.den : ℚ), Rat.cast_neg, Real.rpow_neg hbpos.le, ← mul_inv,
            inv_inv]

/-- The first numeric literal summand of a sum, if any. After `exponentNormal` this is the
constant term of the exponent. -/
def constantTerm? {ι : Type*} (expr : Verified.Expr ι) : Option Rat :=
  (additiveTerms expr).findSome? NumericLiteral.parse?

/-- Rewrite `c ^ exponent` for a positive numeric base `c` and a symbolic exponent whose
constant term has a nonzero integer part `k`: the factor `c ^ k` is folded into a rational
coefficient and the exponent keeps a constant term in `[0, 1)`. Bases `c ≤ 0` are left alone
and `1 ^ exponent` is `1`. -/
def literalBaseCore {ι : Type*} [DecidableEq ι] (base : Verified.Expr ι) (c : Rat)
    (exponent : Verified.Expr ι) : NormResult ι :=
  if c = 1 then { expr := .nat 1, nonzero := [] }
  else if 0 < c then
    match constantTerm? exponent with
    | some q =>
        let k := Rat.floor q
        if k = 0 then { expr := .rpow base exponent, nonzero := [] }
        else
          { expr := mkMul (mkRatConst (ratZpow c k))
              (.rpow base (exponentNormal (mkSub exponent (mkIntConst k))))
            nonzero := [] }
    | none => { expr := .rpow base exponent, nonzero := [] }
  else { expr := .rpow base exponent, nonzero := [] }

/-- Soundness of the numeric-base rewrite; the integer part `k` is arbitrary here
(`Real.rpow_add`, `Real.rpow_intCast`). -/
theorem eval_literalBaseCore {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (base : Verified.Expr ι) (c : Rat) (exponent : Verified.Expr ι)
    (hc : base.eval ρ = (c : ℝ)) :
    (literalBaseCore base c exponent).expr.eval ρ = base.eval ρ ^ exponent.eval ρ := by
  unfold literalBaseCore
  split_ifs with hone hpos
  · simp [hc, hone]
  · cases constantTerm? exponent with
    | none => simp
    | some q =>
        simp only
        split_ifs
        · simp
        · simp only [eval_mkMul, eval_mkRatConst, cast_ratZpow, Verified.Expr.eval,
            eval_exponentNormal, eval_mkSub, eval_mkIntConst, hc]
          rw [← Real.rpow_intCast, ← Real.rpow_add (by exact_mod_cast hpos), add_sub_cancel]
  · simp

/-! ### Numeral bases that are perfect powers -/

/-- The natural number a rational literal denotes, if it is one. -/
def naturalValue? (c : Rat) : Option Nat :=
  if c.den = 1 ∧ 0 ≤ c.num then some c.num.toNat else none

/-- A rational literal recognized as a natural number casts to that natural number. -/
theorem cast_eq_of_naturalValue? {c : Rat} {k : Nat} (h : naturalValue? c = some k) :
    ((k : ℕ) : ℝ) = (c : ℝ) := by
  unfold naturalValue? at h
  split at h
  · rename_i hc
    cases h
    have : ((c.num.toNat : ℤ) : ℚ) = c := by
      rw [Int.toNat_of_nonneg hc.2, Rat.coe_int_num_of_den_eq_one hc.1]
    exact_mod_cast this
  · simp at h

/-- The exponent `m` with `b ^ m = c` among `m, m + 1, …`, searched with the given fuel and
stopping once `b ^ m` exceeds `c`. -/
def powerExponent? (b c : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, m =>
      if b ^ m = c then some m
      else if c < b ^ m then none
      else powerExponent? b c fuel (m + 1)

/-- A found exponent satisfies `b ^ m = c`; the search returns only exponents that passed the
equality test. -/
theorem pow_eq_of_powerExponent? (b c : Nat) :
    ∀ (fuel m m' : Nat), powerExponent? b c fuel m = some m' → b ^ m' = c
  | 0, _, _, h => by simp [powerExponent?] at h
  | fuel + 1, m, m', h => by
      unfold powerExponent? at h
      split_ifs at h with heq
      · exact Option.some.inj h ▸ heq
      · exact pow_eq_of_powerExponent? b c fuel (m + 1) m' h

/-- The smallest base `b, b + 1, …` with `b * b ≤ c` and `b ^ m = c` for some exponent
`m ≥ 2`, together with that exponent, searched with the given fuel. -/
def perfectPowerFrom? (c : Nat) : Nat → Nat → Option (Nat × Nat)
  | 0, _ => none
  | fuel + 1, b =>
      if c < b * b then none
      else
        match powerExponent? b c 64 2 with
        | some m => some (b, m)
        | none => perfectPowerFrom? c fuel (b + 1)

/-- A found base and exponent satisfy `b ^ m = c`. -/
theorem pow_eq_of_perfectPowerFrom? (c : Nat) :
    ∀ (fuel b b' m : Nat), perfectPowerFrom? c fuel b = some (b', m) → b' ^ m = c
  | 0, _, _, _, h => by simp [perfectPowerFrom?] at h
  | fuel + 1, b, b', m, h => by
      unfold perfectPowerFrom? at h
      split_ifs at h
      split at h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact pow_eq_of_powerExponent? b c 64 2 _ ‹_›
      · exact pow_eq_of_perfectPowerFrom? c fuel (b + 1) b' m h

/-- A natural literal `c ≤ 2 ^ 16` written as the power `b ^ m` of the smallest possible base
`b ≥ 2` with `m ≥ 2`, if it is such a power; larger literals are left alone. -/
def perfectPower? (c : Nat) : Option (Nat × Nat) :=
  if c ≤ 65536 then perfectPowerFrom? c 256 2 else none

/-- A recognized perfect power satisfies `b ^ m = c`. -/
theorem pow_eq_of_perfectPower? {c b m : Nat} (h : perfectPower? c = some (b, m)) :
    b ^ m = c := by
  unfold perfectPower? at h
  split at h
  · exact pow_eq_of_perfectPowerFrom? c 256 2 b m h
  · simp at h

/-- Rewrite `base ^ exponent` for a base that denotes the natural number `k` and a symbolic
exponent. A perfect power `k = b ^ m` of a smaller natural number is rewritten to
`b ^ (m * exponent)` (`Real.rpow_natCast_mul`), so that `4 ^ j` and `(2 ^ j) ^ 2` share the
normal form `2 ^ (2 * j)`; then the constant term of the exponent is folded into the
coefficient by `literalBaseCore`. -/
def naturalBaseTop {ι : Type*} [DecidableEq ι] (base : Verified.Expr ι) (k : Nat)
    (exponent : Verified.Expr ι) : NormResult ι :=
  match perfectPower? k with
  | some (b, m) =>
      literalBaseCore (.nat b) (b : Rat) (exponentNormal (mkMul (.nat m) exponent))
  | none => literalBaseCore base (k : Rat) exponent

/-- Soundness of the natural-base rewrite, including the perfect-power step
(`Real.rpow_natCast_mul`). -/
theorem eval_naturalBaseTop {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (base : Verified.Expr ι) (k : Nat) (exponent : Verified.Expr ι)
    (hk : base.eval ρ = (k : ℝ)) :
    (naturalBaseTop base k exponent).expr.eval ρ = base.eval ρ ^ exponent.eval ρ := by
  unfold naturalBaseTop
  rcases hp : perfectPower? k with _ | ⟨b, m⟩
  · exact eval_literalBaseCore ρ base (k : Rat) exponent (by rw [hk, Rat.cast_natCast])
  · dsimp only
    rw [eval_literalBaseCore ρ (.nat b) (b : Rat) _ (by simp)]
    simp only [Verified.Expr.eval, eval_exponentNormal, eval_mkMul]
    rw [Real.rpow_natCast_mul (Nat.cast_nonneg b), ← Nat.cast_pow, pow_eq_of_perfectPower? hp, hk]

/-- Rewrite `c ^ exponent` for a numeric base `c` and a symbolic exponent. A natural base is
rewritten by `naturalBaseTop`. A positive rational base `c = m / n` in lowest terms becomes the
quotient `m ^ exponent / n ^ exponent` of two natural-base powers (`Real.div_rpow`), so that
the perfect-power rewrite reaches both parts: `(1 / 4) ^ p` becomes `1 / 2 ^ (2 * p)` and
`(2 / 3) ^ p` becomes `2 ^ p / 3 ^ p`. Bases `c ≤ 0` are left alone. -/
def literalBaseTop {ι : Type*} [DecidableEq ι] (base : Verified.Expr ι) (c : Rat)
    (exponent : Verified.Expr ι) : NormResult ι :=
  match naturalValue? c with
  | some k => naturalBaseTop base k exponent
  | none =>
      if 0 < c then
        { expr := mkDiv (naturalBaseTop (.nat c.num.toNat) c.num.toNat exponent).expr
            (naturalBaseTop (.nat c.den) c.den exponent).expr
          nonzero := [] }
      else literalBaseCore base c exponent

/-- Soundness of the numeric-base rewrite, including the perfect-power step
(`Real.rpow_natCast_mul`) and the split of a rational base (`Real.div_rpow`). -/
theorem eval_literalBaseTop {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (base : Verified.Expr ι) (c : Rat) (exponent : Verified.Expr ι)
    (hc : base.eval ρ = (c : ℝ)) :
    (literalBaseTop base c exponent).expr.eval ρ = base.eval ρ ^ exponent.eval ρ := by
  unfold literalBaseTop
  cases hk : naturalValue? c with
  | some k =>
      exact eval_naturalBaseTop ρ base k exponent (hc.trans (cast_eq_of_naturalValue? hk).symm)
  | none =>
      dsimp only
      split_ifs with hpos
      · have hnum : (0 : ℤ) ≤ c.num := (Rat.num_pos.mpr hpos).le
        have hnumCast : ((c.num.toNat : ℕ) : ℝ) = (c.num : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hnum
        rw [eval_mkDiv, eval_naturalBaseTop ρ _ _ exponent rfl,
          eval_naturalBaseTop ρ _ _ exponent rfl]
        simp only [Verified.Expr.eval]
        rw [hnumCast, ← Real.div_rpow (by exact_mod_cast hnum) (Nat.cast_nonneg _), hc,
          Rat.cast_def]
      · exact eval_literalBaseCore ρ base c exponent hc

/-- Rewrite `base ^ exponent` when the base is itself a power or a product: `e ^ u = exp u`,
`(exp u) ^ v = exp (u * v)`, `(c ^ p) ^ q = c ^ (p * q)`, `(c ^ n) ^ q = c ^ (n * q)`,
`(sqrt c) ^ q = c ^ (q / 2)`, `(c * d) ^ q = c ^ q * d ^ q`, `(c / d) ^ q = c ^ q / d ^ q`,
recording the positivity of the inner bases. Any other base is left alone. -/
def structuralBaseTop {ι : Type*} [DecidableEq ι] (base exponent : Verified.Expr ι) :
    NormResult ι :=
  match base with
  | .e => { expr := mkExp exponent, nonzero := [] }
  | .exp u => { expr := mkExp (exponentNormal (mkMul u exponent)), nonzero := [] }
  | .rpow c p =>
      { expr := mkPower c (exponentNormal (mkMul p exponent)), nonzero := positivityCondition c }
  | .pow c n =>
      { expr := mkPower c (exponentNormal (mkMul (.nat n) exponent))
        nonzero := positivityCondition c }
  | .sqrt c =>
      { expr := mkPower c (exponentNormal (mkMul (.rat 1 2) exponent))
        nonzero := positivityCondition c }
  | .mul c d =>
      { expr := mkMul (mkRpow c exponent) (mkRpow d exponent)
        nonzero := positivityCondition c ++ positivityCondition d }
  | .div c d =>
      { expr := mkDiv (mkRpow c exponent) (mkRpow d exponent)
        nonzero := positivityCondition c ++ positivityCondition d }
  | _ => { expr := .rpow base exponent, nonzero := [] }

/-- Soundness of the structural-base rewrites (`Real.exp_one_rpow`, `Real.exp_mul`,
`Real.rpow_mul`, `Real.rpow_natCast_mul`, `Real.sqrt_eq_rpow`, `Real.mul_rpow`,
`Real.div_rpow`). -/
theorem eval_structuralBaseTop {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (base exponent : Verified.Expr ι)
    (hside : SideHolds ρ (structuralBaseTop base exponent).nonzero) :
    (structuralBaseTop base exponent).expr.eval ρ = base.eval ρ ^ exponent.eval ρ := by
  cases base with
  | e => simp [structuralBaseTop, Real.exp_one_rpow]
  | exp u => simp [structuralBaseTop, Real.exp_mul]
  | rpow c p =>
      have hc := eval_pos_of_positivityCondition (base := c) hside
      simp [structuralBaseTop, Real.rpow_mul hc.le]
  | pow c n =>
      have hc := eval_pos_of_positivityCondition (base := c) hside
      simp [structuralBaseTop, Real.rpow_natCast_mul hc.le]
  | sqrt c =>
      have hc := eval_pos_of_positivityCondition (base := c) hside
      simp [structuralBaseTop, Real.rpow_mul hc.le, Real.sqrt_eq_rpow]
  | mul c d =>
      have hc := eval_pos_of_positivityCondition (base := c) hside.append_left
      have hd := eval_pos_of_positivityCondition (base := d) hside.append_right
      simp [structuralBaseTop, Real.mul_rpow hc.le hd.le]
  | div c d =>
      have hc := eval_pos_of_positivityCondition (base := c) hside.append_left
      have hd := eval_pos_of_positivityCondition (base := d) hside.append_right
      simp [structuralBaseTop, Real.div_rpow hc.le hd.le]
  | _ => simp [structuralBaseTop]

/-- Whether a base is rewritten by `structuralBaseTop`. -/
def isStructuralBase {ι : Type*} : Verified.Expr ι → Bool
  | .e | .exp _ | .rpow _ _ | .pow _ _ | .sqrt _ | .mul _ _ | .div _ _ => true
  | _ => false

/-- Rewrite one real-power node `base ^ exponent` after normalizing the exponent. An integer
literal exponent is lowered first (no hypothesis); then a structural base is flattened or
distributed; then a literal exponent or a numeric base is put in its normal form. -/
def rpowTop {ι : Type*} [DecidableEq ι] (base exponent : Verified.Expr ι) : NormResult ι :=
  let exponent := exponentNormal exponent
  match NumericLiteral.parse? exponent with
  | some q =>
      if q.den = 1 ∨ !isStructuralBase base then literalExponentTop base q
      else structuralBaseTop base exponent
  | none =>
      if isStructuralBase base then structuralBaseTop base exponent
      else
        match NumericLiteral.parse? base with
        | some c => literalBaseTop base c exponent
        | none => { expr := .rpow base exponent, nonzero := [] }

/-- Soundness of the real-power node rewrite. -/
theorem eval_rpowTop {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ) (base exponent : Verified.Expr ι)
    (hside : SideHolds ρ (rpowTop base exponent).nonzero) :
    (rpowTop base exponent).expr.eval ρ = base.eval ρ ^ exponent.eval ρ := by
  unfold rpowTop at hside ⊢
  rw [← eval_exponentNormal ρ exponent]
  cases hq : NumericLiteral.parse? (exponentNormal exponent) with
  | some q =>
      simp only [hq] at hside ⊢
      split_ifs at hside ⊢
      · rw [eval_literalExponentTop ρ base q hside, NumericLiteral.eval_parse?_eq_some ρ _ q hq]
      · exact eval_structuralBaseTop ρ base _ hside
  | none =>
      simp only [hq] at hside ⊢
      split_ifs at hside ⊢
      · exact eval_structuralBaseTop ρ base _ hside
      · cases hbase : NumericLiteral.parse? base with
        | some c =>
            exact eval_literalBaseTop ρ base c _ (NumericLiteral.eval_parse?_eq_some ρ base c hbase)
        | none => simp

/-- Rewrite a natural power of a real power, exponential, `e`, or square root as one power of
the inner base: `(a ^ p) ^ n = a ^ (n * p)`, `exp u ^ n = exp (n * u)`,
`sqrt a ^ n = a ^ (n / 2)`. -/
def powTop {ι : Type*} [DecidableEq ι] (inner : Verified.Expr ι) (n : Nat) : NormResult ι :=
  match inner with
  | .rpow _ _ | .exp _ | .e | .sqrt _ =>
      let reading := readPower (.pow inner n)
      { expr := mkPower reading.1 (exponentNormal reading.2)
        nonzero := positivityCondition reading.1 }
  | _ => { expr := .pow inner n, nonzero := [] }

/-- Soundness of the natural-power rewrite. -/
theorem eval_powTop {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ) (inner : Verified.Expr ι) (n : Nat)
    (hside : SideHolds ρ (powTop inner n).nonzero) :
    (powTop inner n).expr.eval ρ = (Verified.Expr.pow inner n).eval ρ := by
  have hflat (h : SideHolds ρ (positivityCondition (readPower (Verified.Expr.pow inner n)).1)) :
      (mkPower (readPower (.pow inner n)).1 (exponentNormal (readPower (.pow inner n)).2)).eval ρ =
        (Verified.Expr.pow inner n).eval ρ := by
    rw [eval_mkPower, eval_exponentNormal, ← eval_readPower ρ _ (eval_pos_of_positivityCondition h)]
  cases inner with
  | rpow | exp | e | sqrt => exact hflat hside
  | _ => simp [powTop]

/-- Rewrite the square root of a real power or exponential as one power:
`sqrt (a ^ p) = a ^ (p / 2)`, `sqrt (exp u) = exp (u / 2)`. -/
def sqrtTop {ι : Type*} [DecidableEq ι] (inner : Verified.Expr ι) : NormResult ι :=
  match inner with
  | .rpow c p =>
      { expr := mkPower c (exponentNormal (mkMul (.rat 1 2) p)), nonzero := positivityCondition c }
  | .exp u => { expr := mkExp (exponentNormal (mkMul (.rat 1 2) u)), nonzero := [] }
  | _ => { expr := .sqrt inner, nonzero := [] }

/-- Soundness of the square-root rewrite (`Real.sqrt_eq_rpow`, `Real.rpow_mul`,
`Real.exp_mul`). -/
theorem eval_sqrtTop {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ) (inner : Verified.Expr ι)
    (hside : SideHolds ρ (sqrtTop inner).nonzero) :
    (sqrtTop inner).expr.eval ρ = (Verified.Expr.sqrt inner).eval ρ := by
  cases inner with
  | rpow c p =>
      have hc := eval_pos_of_positivityCondition (base := c) hside
      simp only [sqrtTop, eval_mkPower, eval_exponentNormal, eval_mkMul, Verified.Expr.eval,
        Int.cast_one, Nat.cast_ofNat]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hc.le, mul_comm]
  | exp u =>
      simp only [sqrtTop, eval_mkExp, eval_exponentNormal, eval_mkMul, Verified.Expr.eval,
        Int.cast_one, Nat.cast_ofNat]
      rw [Real.sqrt_eq_rpow, ← Real.exp_mul, mul_comm]
  | _ => simp [sqrtTop]

/-! ### Exponents equal as polynomials

The polynomial normalizer collects the terms of an exponent in the order it meets them, and the
variable type carries no order, so `p + q` and `q + p` keep two normal forms and the powers
`a ^ (p + q)` and `a ^ (q + p)` stay two atoms of the polynomial normalizer. Instead of sorting,
which would need an order on the variables, the pass identifies exponents by value: two exponents
agree when the exponent normal form of their difference is the literal zero, and every power of a
base is rewritten to the first exponent, in traversal order, that agrees with its own. Soundness
needs only `eval_exponentNormal`: agreeing exponents evaluate equally, so the two real powers are
equal without any hypothesis on the base.

The agreement test is guarded by a cheap necessary condition, the values of the two exponents at
a rational point that gives distinct variables distinct values (`mayAgree`), so that the
normalization runs only for exponents that are equal or collide at that point. The distinct
powers of the expression are tabulated once with their representatives
(`representativeTable`), each distinct exponent is compared once against the earlier ones with
the same base, and the expression is traversed again only when some power is identified with an
earlier one. -/

/-- The variables of an expression, with repetitions, in traversal order. -/
def variableOccurrences {ι : Type*} : Verified.Expr ι → List ι
  | .var i => [i]
  | .add a b | .sub a b | .mul a b | .div a b | .rpow a b =>
      variableOccurrences a ++ variableOccurrences b
  | .neg a | .pow a _ | .sin a | .cos a | .atan a | .asin a | .acos a | .exp a | .log a
  | .sqrt a => variableOccurrences a
  | _ => []

/-- The value of an expression of the polynomial fragment with numeric literals at the rational
point that assigns `k + 2` to the variable first occurring at position `k` of `vars`; `none` for
a variable outside `vars`, a quotient by zero, or a node outside the fragment. -/
def rationalValue? {ι : Type*} [DecidableEq ι] (vars : List ι) : Verified.Expr ι → Option Rat
  | .nat n => some n
  | .int z => some z
  | .rat num den => if den = 0 then none else some (Rat.divInt num den)
  | .var i => (vars.findIdx? fun j ↦ decide (j = i)).map fun k ↦ (k : Rat) + 2
  | .add a b => do pure ((← rationalValue? vars a) + (← rationalValue? vars b))
  | .sub a b => do pure ((← rationalValue? vars a) - (← rationalValue? vars b))
  | .mul a b => do pure ((← rationalValue? vars a) * (← rationalValue? vars b))
  | .div a b => do
      let divisor ← rationalValue? vars b
      if divisor = 0 then none else pure ((← rationalValue? vars a) / divisor)
  | .neg a => do pure (-(← rationalValue? vars a))
  | .pow a k => do pure ((← rationalValue? vars a) ^ k)
  | _ => none

/-- Whether two exponents may be equal as polynomials: they take the same value at the rational
point that gives their distinct variables distinct values, or one of them lies outside the
polynomial fragment. Exponents that are equal as polynomials always pass, so the test is a
filter in front of the normalization, not a decision. -/
def mayAgree {ι : Type*} [DecidableEq ι] (e₁ e₂ : Verified.Expr ι) : Bool :=
  let vars := variableOccurrences e₁ ++ variableOccurrences e₂
  match rationalValue? vars e₁, rationalValue? vars e₂ with
  | some q₁, some q₂ => decide (q₁ = q₂)
  | _, _ => true

/-- Whether two exponents are equal as polynomials in their atoms: they are the same expression,
or they pass `mayAgree` and the exponent normal form of their difference is the literal zero. -/
def exponentsAgree {ι : Type*} [DecidableEq ι] (e₁ e₂ : Verified.Expr ι) : Bool :=
  decide (e₁ = e₂) || (mayAgree e₁ e₂ && decide (exponentNormal (mkSub e₁ e₂) = .nat 0))

/-- Agreeing exponents evaluate equally. -/
theorem eval_eq_of_exponentsAgree {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    {e₁ e₂ : Verified.Expr ι} (h : exponentsAgree e₁ e₂ = true) : e₁.eval ρ = e₂.eval ρ := by
  simp only [exponentsAgree, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
  rcases h with rfl | ⟨_, hzero⟩
  · rfl
  · have hnorm := eval_exponentNormal ρ (mkSub e₁ e₂)
    simp only [hzero, Verified.Expr.eval, Nat.cast_zero, eval_mkSub] at hnorm
    linarith

/-- The powers of an expression as pairs of base and exponent, in traversal order: a real power
`a ^ e` contributes `(a, e)` and an exponential `exp u` contributes `(e, u)`, the exponential
being the power of the base `e`. -/
def powerExponents {ι : Type*} : Verified.Expr ι → List (Verified.Expr ι × Verified.Expr ι)
  | .rpow a exponent => (a, exponent) :: (powerExponents a ++ powerExponents exponent)
  | .exp u => ((.e : Verified.Expr ι), u) :: powerExponents u
  | .add a b | .sub a b | .mul a b | .div a b => powerExponents a ++ powerExponents b
  | .neg a | .pow a _ | .sin a | .cos a | .atan a | .asin a | .acos a | .log a | .sqrt a =>
      powerExponents a
  | _ => []

/-- A tabulated power: its base, its exponent, and the representative exponent standing for it. -/
abbrev PowerEntry (ι : Type*) := Verified.Expr ι × Verified.Expr ι × Verified.Expr ι

/-- Whether `table` already contains the power `base ^ exponent`, compared syntactically. -/
def tabulated {ι : Type*} [DecidableEq ι] (table : List (PowerEntry ι))
    (base exponent : Verified.Expr ι) : Bool :=
  table.any fun entry ↦ decide (entry.1 = base) && decide (entry.2.1 = exponent)

/-- The representative of `exponent` among the tabulated powers of `base`: the exponent of the
first entry that agrees with it, or `exponent` itself when there is none. -/
def representativeIn {ι : Type*} [DecidableEq ι] (table : List (PowerEntry ι))
    (base exponent : Verified.Expr ι) : Verified.Expr ι :=
  match table.find? fun entry ↦ decide (entry.1 = base) && exponentsAgree exponent entry.2.1 with
  | some entry => entry.2.1
  | none => exponent

/-- The representative of an exponent evaluates to the exponent. -/
theorem eval_representativeIn {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (table : List (PowerEntry ι)) (base exponent : Verified.Expr ι) :
    (representativeIn table base exponent).eval ρ = exponent.eval ρ := by
  unfold representativeIn
  split
  · rename_i entry hfind
    have hpred := List.find?_some hfind
    simp only [Bool.and_eq_true] at hpred
    exact (eval_eq_of_exponentsAgree ρ hpred.2).symm
  · rfl

/-- Tabulate the distinct powers of a list, in order, each with the representative among the
entries before it (`representativeIn`); a power already tabulated is skipped. -/
def representativeTableAux {ι : Type*} [DecidableEq ι] :
    List (Verified.Expr ι × Verified.Expr ι) → List (PowerEntry ι) → List (PowerEntry ι)
  | [], table => table
  | (base, exponent) :: rest, table =>
      if tabulated table base exponent then representativeTableAux rest table
      else
        representativeTableAux rest
          (table ++ [(base, exponent, representativeIn table base exponent)])

/-- The table of the distinct powers of an expression with their representatives. -/
def representativeTable {ι : Type*} [DecidableEq ι] (expr : Verified.Expr ι) :
    List (PowerEntry ι) :=
  representativeTableAux (powerExponents expr) []

/-- Every representative of a table evaluates to the exponent it stands for. -/
def TableSound {ι : Type*} (ρ : ι → ℝ) (table : List (PowerEntry ι)) : Prop :=
  ∀ entry ∈ table, entry.2.2.eval ρ = entry.2.1.eval ρ

/-- Tabulation preserves the soundness of the table. -/
theorem tableSound_representativeTableAux {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ) :
    ∀ (powers : List (Verified.Expr ι × Verified.Expr ι)) (table : List (PowerEntry ι)),
      TableSound ρ table → TableSound ρ (representativeTableAux powers table)
  | [], _, hsound => hsound
  | (base, exponent) :: rest, table, hsound => by
      unfold representativeTableAux
      split
      · exact tableSound_representativeTableAux ρ rest table hsound
      · refine tableSound_representativeTableAux ρ rest _ fun entry hentry ↦ ?_
        rcases List.mem_append.mp hentry with hold | hnew
        · exact hsound entry hold
        · exact List.mem_singleton.mp hnew ▸ eval_representativeIn ρ table base exponent

/-- The table of an expression is sound. -/
theorem tableSound_representativeTable {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (expr : Verified.Expr ι) : TableSound ρ (representativeTable expr) :=
  tableSound_representativeTableAux ρ (powerExponents expr) []
    (fun _ h ↦ absurd h List.not_mem_nil)

/-- The representative recorded for the power `base ^ exponent`, or `exponent` itself when the
power is not tabulated. -/
def lookupRepresentative {ι : Type*} [DecidableEq ι] (table : List (PowerEntry ι))
    (base exponent : Verified.Expr ι) : Verified.Expr ι :=
  match table.find? (fun entry ↦ decide (entry.1 = base) && decide (entry.2.1 = exponent)) with
  | some entry => entry.2.2
  | none => exponent

/-- In a sound table, the recorded representative evaluates to the exponent. -/
theorem eval_lookupRepresentative {ι : Type*} [DecidableEq ι] {ρ : ι → ℝ}
    {table : List (PowerEntry ι)} (hsound : TableSound ρ table)
    (base exponent : Verified.Expr ι) :
    (lookupRepresentative table base exponent).eval ρ = exponent.eval ρ := by
  unfold lookupRepresentative
  split
  · rename_i entry hfind
    have hpred := List.find?_some hfind
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hpred
    rw [hsound entry (List.mem_of_find?_eq_some hfind), hpred.2]
  · rfl

/-- Rewrite every real power and every exponential of an expression to the representative that
`table` records for it; the traversal descends into every node. -/
def unifyExponents {ι : Type*} [DecidableEq ι] (table : List (PowerEntry ι)) :
    Verified.Expr ι → Verified.Expr ι
  | .rpow a exponent =>
      .rpow (unifyExponents table a) (lookupRepresentative table a exponent)
  | .exp u => .exp (lookupRepresentative table .e u)
  | .add a b => .add (unifyExponents table a) (unifyExponents table b)
  | .sub a b => .sub (unifyExponents table a) (unifyExponents table b)
  | .mul a b => .mul (unifyExponents table a) (unifyExponents table b)
  | .div a b => .div (unifyExponents table a) (unifyExponents table b)
  | .neg a => .neg (unifyExponents table a)
  | .pow a n => .pow (unifyExponents table a) n
  | .sin a => .sin (unifyExponents table a)
  | .cos a => .cos (unifyExponents table a)
  | .atan a => .atan (unifyExponents table a)
  | .asin a => .asin (unifyExponents table a)
  | .acos a => .acos (unifyExponents table a)
  | .log a => .log (unifyExponents table a)
  | .sqrt a => .sqrt (unifyExponents table a)
  | expr => expr

/-- Unifying exponents with a sound table preserves evaluation. -/
theorem eval_unifyExponents {ι : Type*} [DecidableEq ι] {ρ : ι → ℝ}
    {table : List (PowerEntry ι)} (hsound : TableSound ρ table) :
    ∀ expr : Verified.Expr ι, (unifyExponents table expr).eval ρ = expr.eval ρ := by
  intro expr
  induction expr with
  | _ => simp [unifyExponents, eval_lookupRepresentative hsound, *]

/-- Rewrite an expression to the representatives of `table` only when some representative
differs from the exponent it stands for; otherwise the expression is returned unchanged. -/
def identifyWith {ι : Type*} [DecidableEq ι] (table : List (PowerEntry ι))
    (expr : Verified.Expr ι) : Verified.Expr ι :=
  if table.all (fun entry ↦ decide (entry.2.2 = entry.2.1)) then expr
  else unifyExponents table expr

/-- Rewriting to the representatives of a sound table preserves evaluation. -/
theorem eval_identifyWith {ι : Type*} [DecidableEq ι] {ρ : ι → ℝ}
    {table : List (PowerEntry ι)} (hsound : TableSound ρ table) (expr : Verified.Expr ι) :
    (identifyWith table expr).eval ρ = expr.eval ρ := by
  unfold identifyWith
  split
  · rfl
  · exact eval_unifyExponents hsound expr

/-- Identify the exponents of an expression that are equal as polynomials: the distinct powers
are tabulated with their representatives, and the expression is rewritten only when some
representative differs from the exponent it stands for. -/
def identifyExponents {ι : Type*} [DecidableEq ι] (expr : Verified.Expr ι) : Verified.Expr ι :=
  identifyWith (representativeTable expr) expr

/-- Identifying exponents preserves evaluation. -/
theorem eval_identifyExponents {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ) (expr : Verified.Expr ι) :
    (identifyExponents expr).eval ρ = expr.eval ρ :=
  eval_identifyWith (tableSound_representativeTable ρ expr) expr

/-! ### The pass -/

/-- The local rewrite of one rebuilt node: real-power, natural-power, and square-root nodes are
rewritten by `rpowTop`, `powTop`, and `sqrtTop`, products and quotients collect the powers of
their first active base (`productTop`), and every other node is left alone. -/
def realPowerTop {ι : Type*} [DecidableEq ι] : Verified.Expr ι → NormResult ι
  | .rpow base exponent => rpowTop base exponent
  | .pow inner n => powTop inner n
  | .sqrt inner => sqrtTop inner
  | .mul a b => productTop (.mul a b) (productFactors (.mul a b)) []
  | .div a b => productTop (.div a b) (productFactors a) (productFactors b)
  | expr => { expr := expr, nonzero := [] }

/-- Soundness of the local rewrite. -/
theorem eval_realPowerTop {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ) (expr : Verified.Expr ι)
    (hside : SideHolds ρ (realPowerTop expr).nonzero) :
    (realPowerTop expr).expr.eval ρ = expr.eval ρ := by
  cases expr with
  | rpow base exponent => exact eval_rpowTop ρ base exponent hside
  | pow inner n => exact eval_powTop ρ inner n hside
  | sqrt inner => exact eval_sqrtTop ρ inner hside
  | mul a b =>
      apply eval_productTop ρ (Verified.Expr.mul a b) _ _ _ hside
      rw [eval_mkMulList_productFactors]
      simp [mkMulList]
  | div a b =>
      apply eval_productTop ρ (Verified.Expr.div a b) _ _ _ hside
      rw [eval_mkMulList_productFactors, eval_mkMulList_productFactors]
      rfl
  | _ => rfl

end RealPower

open Alg RealPower

/-- Apply the real-power node rewrite after recursively rebuilding an expression, keeping the
side conditions inherited from the children. -/
def realPowerTopAfter {ι : Type*} [DecidableEq ι]
    (rebuilt : Verified.Expr ι) (inherited : List (Verified.Expr ι)) : NormResult ι :=
  let top := realPowerTop rebuilt
  { expr := top.expr, nonzero := cleanSide (inherited ++ top.nonzero) }

/-- The inherited side conditions are available from a `realPowerTopAfter` result. -/
theorem sideHolds_inherited_of_realPowerTopAfter {ι : Type*} [DecidableEq ι]
    {ρ : ι → ℝ} (rebuilt : Verified.Expr ι) (inherited : List (Verified.Expr ι))
    (hside : SideHolds ρ (realPowerTopAfter rebuilt inherited).nonzero) :
    SideHolds ρ inherited := by
  unfold realPowerTopAfter at hside
  exact SideHolds.append_left (sideHolds_of_cleanSide hside)

/-- Soundness of the real-power rewrite after recursive rebuilding. -/
theorem eval_realPowerTopAfter {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (rebuilt : Verified.Expr ι) (inherited : List (Verified.Expr ι))
    (hside : SideHolds ρ (realPowerTopAfter rebuilt inherited).nonzero) :
    (realPowerTopAfter rebuilt inherited).expr.eval ρ = rebuilt.eval ρ := by
  unfold realPowerTopAfter at hside ⊢
  exact eval_realPowerTop ρ rebuilt (SideHolds.append_right (sideHolds_of_cleanSide hside))

/-- Whether an expression contains a node the real-power rewrite can act on: a real power, an
exponential, the constant `e`, or a natural power of a square root. Products, quotients, and
square roots without such a node are left unchanged by every rule of `realPowerTop`, so the
traversal is skipped on expressions without one. -/
def hasPowerAtom {ι : Type*} : Verified.Expr ι → Bool
  | .rpow _ _ | .exp _ | .e => true
  | .pow (.sqrt _) _ => true
  | .pow a _ | .sqrt a | .neg a | .sin a | .cos a | .atan a | .asin a | .acos a | .log a =>
      hasPowerAtom a
  | .add a b | .mul a b | .sub a b | .div a b => hasPowerAtom a || hasPowerAtom b
  | _ => false

/-- The real-power normal form applied throughout an expression tree, after a linear scan for
a node it can act on, followed by the identification of the exponents that are equal as
polynomials (`identifyExponents`). The fixed-point side pipeline repeats it until no product,
quotient, power, or square root changes. -/
def realPowerDeepCleanup {ι : Type*} [DecidableEq ι] (expr : Verified.Expr ι) : NormResult ι :=
  if hasPowerAtom expr then
    let rebuilt := BottomUp.run realPowerTopAfter expr
    { expr := identifyExponents rebuilt.expr, nonzero := rebuilt.nonzero }
  else { expr := expr, nonzero := [] }

/-- Soundness of the real-power normal form: wherever the recorded base positivity conditions
hold, the normal form evaluates to the original expression. -/
theorem eval_realPowerDeepCleanup {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (expr : Verified.Expr ι) (hside : SideHolds ρ (realPowerDeepCleanup expr).nonzero) :
    (realPowerDeepCleanup expr).expr.eval ρ = expr.eval ρ := by
  unfold realPowerDeepCleanup at hside ⊢
  split_ifs at hside ⊢
  · exact (eval_identifyExponents ρ _).trans (BottomUp.eval_run realPowerTopAfter
      sideHolds_inherited_of_realPowerTopAfter eval_realPowerTopAfter ρ expr hside)
  · rfl

/-- Side pass for the real-power and exponential normal form. -/
def realPowerSidePass {ι : Type*} [DecidableEq ι] : SidePass ι where
  name := "real-power"
  run := realPowerDeepCleanup
  sound := by
    intro ρ expr hside
    exact eval_realPowerDeepCleanup ρ expr hside

end CAS.Verified.Expr
