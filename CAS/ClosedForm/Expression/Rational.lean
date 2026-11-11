/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Expression.Polynomial.Normalization

/-!
# Rational normalization for verified expressions

`Alg.normalizeWithSide` and `Alg.normalizeFractionWithSide` normalize rational expressions by
cross-multiplying sums of quotients. Over the reals with totalized division the identity
`a/b + c/d = (a*d + c*b)/(b*d)` fails when `b = 0` or `d = 0` (the left side is `c/d` or `a/b`,
the right side is `0`), which is why the unconditional polynomial normalizer `Alg.normalize`
never uses it. Both normalizers return a `NormResult`: a normal form together with the list
`nonzero` of expressions whose nonvanishing was assumed, and each soundness theorem takes
`SideHolds ρ nonzero` as its hypothesis.

The two normalizers differ in what they cross-multiply, and so in what they record.
`normalizeFractionWithSide` compiles the whole expression to one numerator over one denominator.
Run on the difference of the two sides of an identity, as the zero test `Alg.zeroCheck` of the
exact tactics and of `Scalar.check` does, it closes identities with lone quotients, such as
`x / x = 1` under `x ≠ 0` and `(x^2 - y^2) / (x - y) = x + y` under `x - y ≠ 0`; it is also the
`fraction-normal-form` pipeline pass. `normalizeWithSide` cross-multiplies only when both
summands of a sum or difference are syntactic quotients and leaves a quotient added to anything
else in place, so it records fewer conditions; it is the `rational-side` pipeline pass, which
runs after the fraction normal form, and it is not used as a zero test.

## Main definitions

* `NormResult`, `SideHolds`: a normal form with its nonzero obligations, and the proposition that
  all obligations hold at a valuation.
* `sideFactors`, `cleanSide`: the factor-level obligations of a denominator, and deduplication.
* `normalizeWithSide`: the conservative side-aware normalizer.
* `FractionResult`, `fractionResult`, `normalizeFractionWithSide`: the single-fraction normal
  form, in which every subexpression is compiled to a numerator over a denominator.

## Main results

* `eval_normalizeWithSide`, `eval_fractionResult`, `eval_normalizeFractionWithSide`: each normal
  form has the value of the input at every valuation where its obligations hold.
* `eval_ne_zero_of_sideFactors`: the factor-level obligations imply that the denominator is
  nonzero.
* `eval_eq_zero_of_normalizeWithSide_eq_zero`: a normal form that is literally `0` proves that
  the input vanishes wherever the obligations hold.

## Implementation notes

Only addition and subtraction create obligations. Products and quotients of fractions are
rearranged by identities (`(a/b) * (c/d) = (a*c)/(b*d)`, `(a/b) / (c/d) = (a*d)/(b*c)`) that hold
for Mathlib's total division without hypotheses, so `normalizeMulWithSide`,
`normalizeDivWithSide` and the product and quotient cases of `fractionResult` only propagate the
obligations of their arguments. A sum records the denominators of both summands, split by
`sideFactors` into the factors of products and positive powers with nonzero integer literals
dropped, and `cleanSide` removes duplicates; `normalizeWithSide` records nothing when the two
denominators agree up to `sameDenominator?`. Numerators and denominators are polynomial-normalized
separately, and no common factor is cancelled beyond what `mkDiv` folds (numeric coefficients
and quotients of exponentials): the zero test succeeds because the numerator of the difference
normalizes to `0`, and `mkDiv` turns `0 / d` into `0`. Cancelling common factors is the job of
`Alg.canonical`, which checks a gcd candidate. Both soundness theorems are
proved by induction on the expression, with `field_simp` for sums and differences under the
recorded hypotheses.
-/

@[expose] public section

namespace CAS

open scoped BigOperators

namespace Verified.Expr

namespace Alg

/-- Result of side-condition-aware rational normalization.  The expression is the normalized
closed form; every entry of `nonzero` is a denominator that must be nonzero for the stronger
cross-denominator rewrites to be semantically valid. -/
structure NormResult (ι : Type*) where
  /-- The normalized symbolic expression. -/
  expr : Verified.Expr ι
  /-- Denominators required to be nonzero for the normalization to preserve value. Later
  side-aware passes reuse this field for every nonvanishing obligation they generate; in
  particular an entry `sqrt a` stands for the positivity requirement `0 < a`. -/
  nonzero : List (Verified.Expr ι)

/-- The side conditions emitted by rational normalization hold in an environment. -/
def SideHolds {ι : Type*} (ρ : ι → ℝ) (side : List (Verified.Expr ι)) : Prop :=
  ∀ d ∈ side, d.eval ρ ≠ 0

/-- Transport side-condition proofs across a computed equality of side-condition lists.

The side-condition tactic `symbolic_assumptions` uses this when a side list can be computed by the
kernel but is not definitionally equal to the unreduced expression because named symbolic
definitions are not unfolded at that point of the proof. -/
theorem sideHolds_of_eq {ι : Type*} {ρ : ι → ℝ}
    {side side' : List (Verified.Expr ι)} (h : side = side')
    (hside : SideHolds ρ side') : SideHolds ρ side :=
  h ▸ hside

/-- Remove duplicate rational-normalization side conditions. -/
def cleanSide {ι : Type*} [DecidableEq ι] (side : List (Verified.Expr ι)) :
    List (Verified.Expr ι) :=
  side.dedup

/-- Deduplicating side conditions preserves enough information to prove the original list. -/
theorem sideHolds_of_cleanSide {ι : Type*} [DecidableEq ι] {ρ : ι → ℝ}
    {side : List (Verified.Expr ι)} (h : SideHolds ρ (cleanSide side)) :
    SideHolds ρ side :=
  fun d hd ↦ h d (List.mem_dedup.mpr hd)

/-- Factor-level nonzero obligations for a denominator.

Products and positive powers are split into their factors, nonzero integer literals are dropped,
`d ^ 0` gives no obligation, and every other expression is kept whole as one obligation. -/
def sideFactors {ι : Type*} : Verified.Expr ι → List (Verified.Expr ι)
  | .nat 0 => [.nat 0]
  | .nat (_ + 1) => []
  | .int z => if z = 0 then [.int z] else []
  | .mul a b => sideFactors a ++ sideFactors b
  | .pow _ 0 => []
  | .pow a (_ + 1) => sideFactors a
  | expr => [expr]

/-- Restrict side-condition evidence to the left side of an appended list. -/
theorem SideHolds.append_left {ι : Type*} {ρ : ι → ℝ}
    {a b : List (Verified.Expr ι)} (h : SideHolds ρ (a ++ b)) :
    SideHolds ρ a :=
  fun d hd ↦ h d (List.mem_append_left b hd)

/-- Restrict side-condition evidence to the right side of an appended list. -/
theorem SideHolds.append_right {ι : Type*} {ρ : ι → ℝ}
    {a b : List (Verified.Expr ι)} (h : SideHolds ρ (a ++ b)) :
    SideHolds ρ b :=
  fun d hd ↦ h d (List.mem_append_right a hd)

/-- Extract the nonzero fact represented by a singleton side-condition list. -/
theorem SideHolds.of_singleton {ι : Type*} {ρ : ι → ℝ}
    {d : Verified.Expr ι} (h : SideHolds ρ [d]) :
    d.eval ρ ≠ 0 :=
  h d (List.mem_singleton_self d)

/-- The factor-level side obligations imply that the original denominator is nonzero. -/
theorem eval_ne_zero_of_sideFactors {ι : Type*} (ρ : ι → ℝ) :
    ∀ d : Verified.Expr ι, SideHolds ρ (sideFactors d) → d.eval ρ ≠ 0 := by
  intro d
  induction d with
  | nat n => cases n <;> simp [sideFactors, SideHolds, Nat.cast_add_one_ne_zero]
  | int z => by_cases hz : z = 0 <;> simp [sideFactors, SideHolds, hz]
  | mul a b iha ihb => exact fun h ↦ mul_ne_zero (iha h.append_left) (ihb h.append_right)
  | pow a k ih => cases k <;> simp_all [sideFactors]
  | _ => exact SideHolds.of_singleton

/-- Add normalized results, cross-multiplying unlike denominators and recording nonzero
obligations. -/
def normalizeAddWithSide {ι : Type*} [DecidableEq ι]
    (ra rb : NormResult ι) : NormResult ι :=
  let a := ra.expr
  let b := rb.expr
  let inherited := ra.nonzero ++ rb.nonzero
  match a, b with
  | .div na da, .div nb db =>
      let daNorm := normalizePolynomial da
      let dbNorm := normalizePolynomial db
      if sameDenominator? daNorm dbNorm then
        { expr := mkDiv (normalizePolynomial (mkAdd na nb)) daNorm
          nonzero := cleanSide inherited }
      else
        { expr :=
            mkDiv
              (normalizePolynomial (mkAdd (mkMul na db) (mkMul nb da)))
              (normalizePolynomial (mkMul da db))
          nonzero := cleanSide (inherited ++ sideFactors da ++ sideFactors db) }
  | _, _ =>
      { expr := normalizePolynomial (mkAdd a b)
        nonzero := cleanSide inherited }

/-- Subtract normalized results, cross-multiplying unlike denominators and recording nonzero
obligations. -/
def normalizeSubWithSide {ι : Type*} [DecidableEq ι]
    (ra rb : NormResult ι) : NormResult ι :=
  let a := ra.expr
  let b := rb.expr
  let inherited := ra.nonzero ++ rb.nonzero
  match a, b with
  | .div na da, .div nb db =>
      let daNorm := normalizePolynomial da
      let dbNorm := normalizePolynomial db
      if sameDenominator? daNorm dbNorm then
        { expr := mkDiv (normalizePolynomial (mkSub na nb)) daNorm
          nonzero := cleanSide inherited }
      else
        { expr :=
            mkDiv
              (normalizePolynomial (mkSub (mkMul na db) (mkMul nb da)))
              (normalizePolynomial (mkMul da db))
          nonzero := cleanSide (inherited ++ sideFactors da ++ sideFactors db) }
  | _, _ =>
      { expr := normalizePolynomial (mkSub a b)
        nonzero := cleanSide inherited }

/-- Multiply normalized results while retaining their inherited side conditions. -/
def normalizeMulWithSide {ι : Type*} [DecidableEq ι]
    (ra rb : NormResult ι) : NormResult ι :=
  { expr := normalizeMul ra.expr rb.expr
    nonzero := cleanSide (ra.nonzero ++ rb.nonzero) }

/-- Divide normalized results and flatten top-level quotients using total real division. -/
def normalizeDivWithSide {ι : Type*} [DecidableEq ι]
    (ra rb : NormResult ι) : NormResult ι :=
  match ra.expr, rb.expr with
  | .div na da, .div nb db =>
      { expr :=
          mkDiv
            (normalizePolynomial (mkMul na db))
            (normalizePolynomial (mkMul da nb))
        nonzero := cleanSide (ra.nonzero ++ rb.nonzero) }
  | .div na da, expr =>
      { expr :=
          mkDiv
            (normalizePolynomial na)
            (normalizePolynomial (mkMul da expr))
        nonzero := cleanSide (ra.nonzero ++ rb.nonzero) }
  | expr, .div nb db =>
      { expr :=
          mkDiv
            (normalizePolynomial (mkMul expr db))
            (normalizePolynomial nb)
        nonzero := cleanSide (ra.nonzero ++ rb.nonzero) }
  | _, _ =>
      { expr := mkDiv ra.expr rb.expr
        nonzero := cleanSide (ra.nonzero ++ rb.nonzero) }

/-- Division introduces no new obligations: the side list of a quotient is the deduplicated
union of the operands' side lists. -/
@[simp] theorem normalizeDivWithSide_nonzero {ι : Type*} [DecidableEq ι]
    (ra rb : NormResult ι) :
    (normalizeDivWithSide ra rb).nonzero = cleanSide (ra.nonzero ++ rb.nonzero) := by
  unfold normalizeDivWithSide
  split <;> rfl

/-- Stronger rational normalizer.  Unlike `normalize`, this pass may cross-multiply unlike
denominators in sums/differences; it records the nonzero denominator side conditions needed for
those rewrites. -/
def normalizeWithSide {ι : Type*} [DecidableEq ι] : Verified.Expr ι → NormResult ι
  | .add a b => normalizeAddWithSide (normalizeWithSide a) (normalizeWithSide b)
  | .sub a b => normalizeSubWithSide (normalizeWithSide a) (normalizeWithSide b)
  | .neg a =>
      let ra := normalizeWithSide a
      { expr :=
          match ra.expr with
          | .div n d => mkDiv (mkNeg n) d
          | expr => normalizePolynomial (mkNeg expr)
        nonzero := ra.nonzero }
  | .mul a b => normalizeMulWithSide (normalizeWithSide a) (normalizeWithSide b)
  | .div a b => normalizeDivWithSide (normalizeWithSide a) (normalizeWithSide b)
  | .pow a k =>
      let ra := normalizeWithSide a
      { expr := normalizePolynomial (mkPow ra.expr k)
        nonzero := ra.nonzero }
  | .sin a =>
      let ra := normalizeWithSide a
      { expr := mkSin ra.expr
        nonzero := ra.nonzero }
  | .cos a =>
      let ra := normalizeWithSide a
      { expr := mkCos ra.expr
        nonzero := ra.nonzero }
  | .atan a =>
      let ra := normalizeWithSide a
      { expr := .atan ra.expr
        nonzero := ra.nonzero }
  | .asin a =>
      let ra := normalizeWithSide a
      { expr := .asin ra.expr
        nonzero := ra.nonzero }
  | .acos a =>
      let ra := normalizeWithSide a
      { expr := .acos ra.expr
        nonzero := ra.nonzero }
  | .exp a =>
      let ra := normalizeWithSide a
      { expr := mkExp ra.expr
        nonzero := ra.nonzero }
  | .log a =>
      let ra := normalizeWithSide a
      { expr := mkLog ra.expr
        nonzero := ra.nonzero }
  | .sqrt a =>
      let ra := normalizeWithSide a
      { expr := mkSqrt ra.expr
        nonzero := ra.nonzero }
  | .rpow a b =>
      let ra := normalizeWithSide a
      let rb := normalizeWithSide b
      { expr := mkRpow ra.expr rb.expr
        nonzero := cleanSide (ra.nonzero ++ rb.nonzero) }
  | expr => { expr := expr, nonzero := [] }

/-! #### Fraction normal form

The normalizer `normalizeWithSide` is conservative: it only cross-multiplies additions when
both summands are already syntactic divisions.  Kernel residuals usually contain mixed shapes
such as `plain + numerator/denominator`, and after one cross-multiplication they can also
contain a nested division inside a numerator.  `FractionResult` handles these at the representation
level: every subexpression is compiled to a numerator/denominator pair, so addition and subtraction
always use a common denominator.

The only emitted side conditions are the denominators needed for addition/subtraction.
Multiplication and division are sound for Lean's total real division without extra obligations.
-/

/-- A symbolic expression represented as a single numerator over a single denominator. -/
structure FractionResult (ι : Type*) where
  /-- The numerator of the compiled single fraction. -/
  num : Verified.Expr ι
  /-- The denominator of the compiled single fraction. -/
  den : Verified.Expr ι
  /-- Nonzero obligations introduced by additive cross-multiplication. -/
  nonzero : List (Verified.Expr ι)

namespace FractionResult

/-- Reassemble a fraction result as a symbolic expression. -/
def expr {ι : Type*} [DecidableEq ι] (r : FractionResult ι) : Verified.Expr ι :=
  mkDiv (normalizePolynomial r.num) (normalizePolynomial r.den)

/-- A reassembled fraction result evaluates to numerator over denominator (total real
division), since polynomial normalization of each part preserves evaluation. -/
@[simp] theorem eval_expr {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (r : FractionResult ι) :
    r.expr.eval ρ = r.num.eval ρ / r.den.eval ρ := by
  simp [expr, eval_normalizePolynomial]

end FractionResult

/-- Emit side conditions saying that both fraction denominators used in an additive
cross-multiplication are nonzero. -/
def fractionAddSide {ι : Type*} [DecidableEq ι] (ra rb : FractionResult ι) :
    List (Verified.Expr ι) :=
  cleanSide ((ra.nonzero ++ rb.nonzero) ++ (sideFactors ra.den ++ sideFactors rb.den))

/-- Compile an expression into one fraction, recursively flattening mixed and nested quotients. -/
def fractionResult {ι : Type*} [DecidableEq ι] : Verified.Expr ι → FractionResult ι
  | .add a b =>
      let ra := fractionResult a
      let rb := fractionResult b
      { num := normalizePolynomial (mkAdd (mkMul ra.num rb.den) (mkMul rb.num ra.den))
        den := normalizePolynomial (mkMul ra.den rb.den)
        nonzero := fractionAddSide ra rb }
  | .sub a b =>
      let ra := fractionResult a
      let rb := fractionResult b
      { num := normalizePolynomial (mkSub (mkMul ra.num rb.den) (mkMul rb.num ra.den))
        den := normalizePolynomial (mkMul ra.den rb.den)
        nonzero := fractionAddSide ra rb }
  | .mul a b =>
      let ra := fractionResult a
      let rb := fractionResult b
      { num := normalizePolynomial (mkMul ra.num rb.num)
        den := normalizePolynomial (mkMul ra.den rb.den)
        nonzero := cleanSide (ra.nonzero ++ rb.nonzero) }
  | .div a b =>
      let ra := fractionResult a
      let rb := fractionResult b
      { num := normalizePolynomial (mkMul ra.num rb.den)
        den := normalizePolynomial (mkMul ra.den rb.num)
        nonzero := cleanSide (ra.nonzero ++ rb.nonzero) }
  | .neg a =>
      let ra := fractionResult a
      { num := normalizePolynomial (mkNeg ra.num)
        den := ra.den
        nonzero := ra.nonzero }
  | .pow a k =>
      let ra := fractionResult a
      { num := normalizePolynomial (mkPow ra.num k)
        den := normalizePolynomial (mkPow ra.den k)
        nonzero := ra.nonzero }
  | .sin a =>
      let ra := fractionResult a
      { num := mkSin ra.expr, den := .nat 1, nonzero := ra.nonzero }
  | .cos a =>
      let ra := fractionResult a
      { num := mkCos ra.expr, den := .nat 1, nonzero := ra.nonzero }
  | .atan a =>
      let ra := fractionResult a
      { num := .atan ra.expr, den := .nat 1, nonzero := ra.nonzero }
  | .asin a =>
      let ra := fractionResult a
      { num := .asin ra.expr, den := .nat 1, nonzero := ra.nonzero }
  | .acos a =>
      let ra := fractionResult a
      { num := .acos ra.expr, den := .nat 1, nonzero := ra.nonzero }
  | .exp a =>
      let ra := fractionResult a
      { num := mkExp ra.expr, den := .nat 1, nonzero := ra.nonzero }
  | .log a =>
      let ra := fractionResult a
      { num := mkLog ra.expr, den := .nat 1, nonzero := ra.nonzero }
  | .sqrt a =>
      let ra := fractionResult a
      { num := mkSqrt ra.expr, den := .nat 1, nonzero := ra.nonzero }
  | .rpow a b =>
      let ra := fractionResult a
      let rb := fractionResult b
      { num := mkRpow ra.expr rb.expr, den := .nat 1
        nonzero := cleanSide (ra.nonzero ++ rb.nonzero) }
  | expr => { num := expr, den := .nat 1, nonzero := [] }

/-- The single-fraction normal form: `fractionResult` reassembled as one quotient of normalized
polynomials, with the denominators that additive cross-multiplication assumed nonzero. -/
def normalizeFractionWithSide {ι : Type*} [DecidableEq ι] (expr : Verified.Expr ι) :
    NormResult ι :=
  let r := fractionResult expr
  { expr := r.expr, nonzero := r.nonzero }

/-- Soundness of fraction normal form. -/
theorem eval_fractionResult {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ) :
    ∀ expr : Verified.Expr ι,
      SideHolds ρ (fractionResult expr).nonzero →
        (fractionResult expr).expr.eval ρ = expr.eval ρ := by
  intro expr
  induction expr with
  | add a b iha ihb | sub a b iha ihb =>
      intro hside
      simp only [fractionResult, fractionAddSide, SideHolds, cleanSide, List.mem_dedup,
        List.mem_append, or_imp, forall_and] at hside
      obtain ⟨⟨ha, hb⟩, hda, hdb⟩ := hside
      have hda := eval_ne_zero_of_sideFactors ρ _ hda
      have hdb := eval_ne_zero_of_sideFactors ρ _ hdb
      simp only [fractionResult, FractionResult.eval_expr, eval_normalizePolynomial, eval_mkAdd,
        eval_mkSub, eval_mkMul, eval] at iha ihb ⊢
      rw [← iha ha, ← ihb hb]
      field_simp
  | mul a b iha ihb | div a b iha ihb | rpow a b iha ihb =>
      intro hside
      simp only [fractionResult, SideHolds, cleanSide, List.mem_dedup, List.mem_append, or_imp,
        forall_and] at hside
      have ha := iha hside.1
      have hb := ihb hside.2
      simp only [FractionResult.eval_expr] at ha hb
      simp [fractionResult, eval_normalizePolynomial, ← ha, ← hb, div_mul_div_comm,
        div_div_div_eq]
  | neg a ih | pow a k ih | sin a ih | cos a ih | atan a ih | asin a ih | acos a ih
    | exp a ih | log a ih | sqrt a ih =>
      intro hside
      have ha := ih hside
      simp only [FractionResult.eval_expr] at ha
      simp [fractionResult, eval_normalizePolynomial, ← ha, neg_div, div_pow]
  | _ => simp [fractionResult, FractionResult.expr, eval_normalizePolynomial]

/-- Soundness of the single-fraction normalizer: the normal form has the same real value as the
input at every valuation where the emitted denominators are nonzero. -/
@[simp] theorem eval_normalizeFractionWithSide {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (expr : Verified.Expr ι)
    (hside : SideHolds ρ (normalizeFractionWithSide expr).nonzero) :
    (normalizeFractionWithSide expr).expr.eval ρ = expr.eval ρ := by
  simpa [normalizeFractionWithSide] using eval_fractionResult ρ expr hside

private theorem eval_normalizeAddWithSide {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (ra rb : NormResult ι)
    (hside : SideHolds ρ (normalizeAddWithSide ra rb).nonzero) :
    (normalizeAddWithSide ra rb).expr.eval ρ = ra.expr.eval ρ + rb.expr.eval ρ := by
  dsimp only [normalizeAddWithSide] at hside ⊢
  split
  · rename_i na da nb db ha hb
    rw [ha, hb]
    split
    · rename_i h
      have := eval_eq_of_sameDenominator? ρ h
      simp only [eval_normalizePolynomial] at this
      simp [eval_normalizePolynomial, this, add_div]
    · rename_i h
      simp only [ha, hb, h] at hside
      have hs := sideHolds_of_cleanSide hside
      have hda := eval_ne_zero_of_sideFactors ρ da hs.append_left.append_right
      have hdb := eval_ne_zero_of_sideFactors ρ db hs.append_right
      simp [eval_normalizePolynomial]
      field_simp
  · simp [eval_normalizePolynomial]

private theorem eval_normalizeSubWithSide {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (ra rb : NormResult ι)
    (hside : SideHolds ρ (normalizeSubWithSide ra rb).nonzero) :
    (normalizeSubWithSide ra rb).expr.eval ρ = ra.expr.eval ρ - rb.expr.eval ρ := by
  dsimp only [normalizeSubWithSide] at hside ⊢
  split
  · rename_i na da nb db ha hb
    rw [ha, hb]
    split
    · rename_i h
      have := eval_eq_of_sameDenominator? ρ h
      simp only [eval_normalizePolynomial] at this
      simp [eval_normalizePolynomial, this, sub_div]
    · rename_i h
      simp only [ha, hb, h] at hside
      have hs := sideHolds_of_cleanSide hside
      have hda := eval_ne_zero_of_sideFactors ρ da hs.append_left.append_right
      have hdb := eval_ne_zero_of_sideFactors ρ db hs.append_right
      simp [eval_normalizePolynomial]
      field_simp
  · simp [eval_normalizePolynomial]

private theorem eval_normalizeDivWithSide {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (ra rb : NormResult ι) :
    (normalizeDivWithSide ra rb).expr.eval ρ = ra.expr.eval ρ / rb.expr.eval ρ := by
  dsimp only [normalizeDivWithSide]
  split <;> simp_all [eval_normalizePolynomial, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

private theorem sideHolds_inherited_add {ι : Type*} [DecidableEq ι] {ρ : ι → ℝ}
    (ra rb : NormResult ι)
    (hside : SideHolds ρ (normalizeAddWithSide ra rb).nonzero) :
    SideHolds ρ (ra.nonzero ++ rb.nonzero) := by
  dsimp only [normalizeAddWithSide] at hside
  split at hside
  · split at hside
    · exact sideHolds_of_cleanSide hside
    · exact (sideHolds_of_cleanSide hside).append_left.append_left
  · exact sideHolds_of_cleanSide hside

private theorem sideHolds_inherited_sub {ι : Type*} [DecidableEq ι] {ρ : ι → ℝ}
    (ra rb : NormResult ι)
    (hside : SideHolds ρ (normalizeSubWithSide ra rb).nonzero) :
    SideHolds ρ (ra.nonzero ++ rb.nonzero) := by
  dsimp only [normalizeSubWithSide] at hside
  split at hside
  · split at hside
    · exact sideHolds_of_cleanSide hside
    · exact (sideHolds_of_cleanSide hside).append_left.append_left
  · exact sideHolds_of_cleanSide hside

/-- Soundness of side-condition-aware rational normalization. -/
@[simp] theorem eval_normalizeWithSide {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ) :
    ∀ expr : Verified.Expr ι,
      SideHolds ρ (normalizeWithSide expr).nonzero →
        (normalizeWithSide expr).expr.eval ρ = expr.eval ρ := by
  intro expr
  induction expr with
  | add a b iha ihb =>
      intro hside
      have h := sideHolds_inherited_add _ _ hside
      exact (eval_normalizeAddWithSide ρ _ _ hside).trans
        (congrArg₂ (· + ·) (iha h.append_left) (ihb h.append_right))
  | sub a b iha ihb =>
      intro hside
      have h := sideHolds_inherited_sub _ _ hside
      exact (eval_normalizeSubWithSide ρ _ _ hside).trans
        (congrArg₂ (· - ·) (iha h.append_left) (ihb h.append_right))
  | mul a b iha ihb =>
      intro hside
      have h := sideHolds_of_cleanSide hside
      exact (eval_normalizeMul ρ _ _).trans
        (congrArg₂ (· * ·) (iha h.append_left) (ihb h.append_right))
  | div a b iha ihb =>
      intro hside
      rw [normalizeWithSide, normalizeDivWithSide_nonzero] at hside
      have h := sideHolds_of_cleanSide hside
      exact (eval_normalizeDivWithSide ρ _ _).trans
        (congrArg₂ (· / ·) (iha h.append_left) (ihb h.append_right))
  | rpow a b iha ihb =>
      intro hside
      have h := sideHolds_of_cleanSide hside
      simp [normalizeWithSide, iha h.append_left, ihb h.append_right]
  | neg a ih =>
      intro hside
      simp only [normalizeWithSide, eval, ← ih hside]
      cases (normalizeWithSide a).expr <;> simp [eval_normalizePolynomial, neg_div]
  | pow a _ ih | sin a ih | cos a ih | atan a ih | asin a ih | acos a ih | exp a ih
    | log a ih | sqrt a ih =>
      intro hside
      simp [normalizeWithSide, eval_normalizePolynomial, ih hside]
  | _ => simp [normalizeWithSide]

/-- If side-condition-aware normalization computes symbolic zero and its emitted denominator
conditions hold, then the original expression evaluates to zero. -/
theorem eval_eq_zero_of_normalizeWithSide_eq_zero {ι : Type*} [DecidableEq ι]
    (ρ : ι → ℝ) (expr : Verified.Expr ι)
    (hside : SideHolds ρ (normalizeWithSide expr).nonzero)
    (hzero : (normalizeWithSide expr).expr = (0 : Verified.Expr ι)) :
    expr.eval ρ = 0 := by
  rw [← eval_normalizeWithSide ρ expr hside, hzero]
  simp [Verified.Expr.eval]

end Alg

end Verified.Expr
end CAS
