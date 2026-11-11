/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.Sparse.Division
public import CAS.Continuum.Interval.Rational.Basic
public import CAS.Polynomial.Sparse

/-!
# Executable rational Cauchy bounds

Root isolation needs exact rational endpoints that can be generated and checked.
`CauchyBoundCertificate` records the elementary Cauchy-bound argument for a polynomial

`scale * (x^n + lower(x))`,

where every exponent in `lower` is strictly below `n`.  The exact rational
bound

`1 + sum |lower coefficient|`

bounds the absolute value of every real root strictly (`CauchyBoundCertificate.abs_lt_bound`).
For a normalized `lower` this is Cauchy's bound [BPR, Notation 10.1 and Lemma 10.2].

## Implementation notes

The checker `valid` validates the sparse identity, the exponent condition, and the nonzero
scale. The bound is derived from the checked lower-degree tail rather than stored separately.
The generator `generate?` returns a dependent pair only after the checker accepts.

The proof of `abs_lt_bound` is that of [BPR, Lemma 10.2]: for `1 ≤ |x|`, the tail is at most
`|x| ^ (n - 1)` times the sum of its absolute coefficients
(`abs_evalReal_le_coefficientAbsSum_mul_pow`), so a root with `1 ≤ |x|` has `|x|` at most that
sum.

The root commands run `generate?` in compiled code and quote the certificate it returns into a
root certificate (`RootListCertificate`, `RootList`); the kernel then checks only `valid` of the
quoted certificate.

## References

* Saugata Basu, Richard Pollack and Marie-Françoise Roy, *Algorithms in Real Algebraic Geometry*,
  2nd ed., Algorithms and Computation in Mathematics 10, Springer, Berlin, 2006,
  <https://doi.org/10.1007/3-540-33099-2>. Notation 10.1 and Lemma 10.2, numbered as in the
  authors' online version.
-/

@[expose] public section

namespace CAS.Polynomial.RealRoot

open Sparse

/-- Sum of absolute values of all coefficients in a sparse list. -/
def coefficientAbsSum : Sparse.Univariate → Rat
  | [] => 0
  | term :: rest => |term.1| + coefficientAbsSum rest

/-- The coefficient absolute-value sum is nonnegative. -/
theorem coefficientAbsSum_nonneg (polynomial : Sparse.Univariate) :
    0 ≤ coefficientAbsSum polynomial := by
  induction polynomial with
  | nil => simp [coefficientAbsSum]
  | cons term rest ih =>
      simp only [coefficientAbsSum]
      positivity

/-- Check that every represented exponent is strictly below `degree`. -/
def allDegreesBelow (degree : Nat) (polynomial : Sparse.Univariate) : Bool :=
  polynomial.all fun term ↦
    decide (term.2 (0 : Fin 1) < degree)

/-- Soundness of the exponent check: if `allDegreesBelow degree` accepts, every term of the
sparse list has exponent strictly less than `degree`. -/
theorem degree_lt_of_mem_allDegreesBelow
    {degree : Nat} {polynomial : Sparse.Univariate}
    (hbelow : allDegreesBelow degree polynomial = true)
    {term : Rat × Verified.Expr.Alg.MvMonomial 1}
    (hterm : term ∈ polynomial) :
    term.2 (0 : Fin 1) < degree := by
  simpa [allDegreesBelow] using List.all_eq_true.mp hbelow term hterm

/-- No natural exponent is below zero, so a sparse list passing `allDegreesBelow 0` is empty. -/
theorem eq_nil_of_allDegreesBelow_zero
    {polynomial : Sparse.Univariate}
    (hbelow : allDegreesBelow 0 polynomial = true) :
    polynomial = [] := by
  cases polynomial with
  | nil => rfl
  | cons term rest =>
      exact (Nat.not_lt_zero _ (degree_lt_of_mem_allDegreesBelow hbelow List.mem_cons_self)).elim

/--
Uniform bound for a lower-degree sparse tail when `1 ≤ |x|`.
-/
theorem abs_evalReal_le_coefficientAbsSum_mul_pow
    {degree : Nat} {polynomial : Sparse.Univariate}
    (hbelow : allDegreesBelow degree polynomial = true)
    {x : ℝ} (hx : 1 ≤ |x|) :
    |Sparse.evalReal polynomial x| ≤
      (coefficientAbsSum polynomial : ℝ) * |x| ^ (degree - 1) := by
  induction polynomial with
  | nil => simp [Sparse.evalReal, coefficientAbsSum]
  | cons term rest ih =>
      have hhead := degree_lt_of_mem_allDegreesBelow hbelow List.mem_cons_self
      have htail : allDegreesBelow degree rest = true :=
        List.all_eq_true.mpr fun c hc ↦ List.all_eq_true.mp hbelow c (List.mem_cons_of_mem _ hc)
      simp only [Sparse.evalReal, coefficientAbsSum, Rat.cast_add, Rat.cast_abs, add_mul]
      refine (abs_add_le _ _).trans (add_le_add ?_ (ih htail))
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (Nat.le_sub_one_of_lt hhead))
        (abs_nonneg _)

/-- Exact evidence for one executable rational outer root bound. -/
structure CauchyBoundCertificate where
  /-- Nonzero scalar factored from the represented monic-leading polynomial. -/
  scale : Rat
  /-- Exponent of the monic leading term in the checked representation. -/
  degree : Nat
  /-- Sparse tail whose exponents must all be strictly below `degree`. -/
  lower : Sparse.Univariate
deriving DecidableEq

namespace CauchyBoundCertificate

/-- Exact rational Cauchy radius derived from the lower-degree tail. -/
def bound (certificate : CauchyBoundCertificate) : Rat :=
  1 + coefficientAbsSum certificate.lower

/-- The sparse polynomial `scale * (x ^ degree + lower)` described by the certificate. -/
def represented (certificate : CauchyBoundCertificate) :
    Sparse.Univariate :=
  Verified.Expr.Alg.mvMulPoly
    (Sparse.monomial certificate.scale 0)
    (Verified.Expr.Alg.mvAdd
      (Sparse.monomial 1 certificate.degree)
      certificate.lower)

/-- Independent exact checker for a rational Cauchy-bound certificate. -/
def valid (polynomial : Sparse.Univariate)
    (certificate : CauchyBoundCertificate) : Bool :=
  decide (certificate.scale ≠ 0) &&
    allDegreesBelow certificate.degree certificate.lower &&
    Sparse.isZero
      (Verified.Expr.Alg.mvSub polynomial certificate.represented)

private theorem valid_components
    (polynomial : Sparse.Univariate)
    (certificate : CauchyBoundCertificate)
    (hvalid : certificate.valid polynomial = true) :
    certificate.scale ≠ 0 ∧
      allDegreesBelow certificate.degree certificate.lower = true ∧
      Sparse.isZero
        (Verified.Expr.Alg.mvSub polynomial
          certificate.represented) = true := by
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  exact ⟨hvalid.1.1, hvalid.1.2, hvalid.2⟩

/-- Every derived bound is strictly positive. -/
theorem bound_pos (certificate : CauchyBoundCertificate) :
    0 < certificate.bound :=
  add_pos_of_pos_of_nonneg one_pos (coefficientAbsSum_nonneg _)

/-- Every real root lies strictly between the checked rational endpoints. -/
theorem abs_lt_bound
    {polynomial : Sparse.Univariate}
    {certificate : CauchyBoundCertificate}
    (hvalid : certificate.valid polynomial = true)
    {x : ℝ} (hroot : Sparse.evalReal polynomial x = 0) :
    |x| < (certificate.bound : ℝ) := by
  obtain ⟨hscale, hbelow, hidentity⟩ := certificate.valid_components polynomial hvalid
  have hinside : x ^ certificate.degree + Sparse.evalReal certificate.lower x = 0 := by
    simpa [represented, Sparse.evalReal_mul, Sparse.evalReal_add, Sparse.monomial,
      Sparse.evalReal, Sparse.univariateMonomial, hscale] using
      (Sparse.evalReal_eq_of_isZero_sub hidentity x).symm.trans hroot
  have hsum : (0 : ℝ) ≤ coefficientAbsSum certificate.lower := by
    exact_mod_cast coefficientAbsSum_nonneg certificate.lower
  by_contra hnot
  have hxBound : 1 + (coefficientAbsSum certificate.lower : ℝ) ≤ |x| := by
    simpa [bound] using not_lt.mp hnot
  rcases hdegree : certificate.degree with _ | degree
  · rw [hdegree] at hbelow hinside
    simp [eq_nil_of_allDegreesBelow_zero hbelow, Sparse.evalReal] at hinside
  · have hlowerBound := abs_evalReal_le_coefficientAbsSum_mul_pow hbelow
      (show 1 ≤ |x| by linarith)
    rw [hdegree, Nat.add_sub_cancel] at hlowerBound
    rw [hdegree] at hinside
    have hpower : |x| * |x| ^ degree = |Sparse.evalReal certificate.lower x| := by
      rw [← pow_succ', ← abs_pow, eq_neg_of_add_eq_zero_left hinside, abs_neg]
    have hpowPos : 0 < |x| ^ degree := pow_pos (by linarith) degree
    have hscaled := mul_le_mul_of_nonneg_right hxBound hpowPos.le
    linarith

/-- A checked degree-zero decomposition proves that the polynomial has no root. -/
theorem evalReal_ne_zero_of_degree_eq_zero
    {polynomial : Sparse.Univariate}
    {certificate : CauchyBoundCertificate}
    (hvalid : certificate.valid polynomial = true)
    (hdegree : certificate.degree = 0)
    (x : ℝ) :
    Sparse.evalReal polynomial x ≠ 0 := by
  obtain ⟨hscale, hbelow, hidentity⟩ := certificate.valid_components polynomial hvalid
  have hlower : certificate.lower = [] :=
    eq_nil_of_allDegreesBelow_zero (by simpa [hdegree] using hbelow)
  rw [Sparse.evalReal_eq_of_isZero_sub hidentity x]
  simp [represented, Sparse.evalReal_mul, Sparse.evalReal_add, Sparse.monomial, Sparse.evalReal,
    Sparse.univariateMonomial, hscale, hdegree, hlower]

/--
Candidate bound obtained by scaling the normalized polynomial to monic form and
removing its leading monomial.
-/
def candidate? (polynomial : Sparse.Univariate) :
    Option CauchyBoundCertificate :=
  let polynomial := Verified.Expr.Alg.mvNormalize polynomial
  match Verified.Expr.Alg.mvLeadingTermNormalized? polynomial with
  | none => none
  | some leading =>
      let degree := leading.2 (0 : Fin 1)
      let monic := Sparse.Univariate.monic polynomial
      let lower :=
        Verified.Expr.Alg.mvSub monic (Sparse.monomial 1 degree)
      some
        { scale := leading.1
          degree := degree
          lower := lower }

/-- Generate and independently validate a checked rational root bound. -/
def generate? (polynomial : Sparse.Univariate) :
    Option
      { certificate : CauchyBoundCertificate //
        certificate.valid polynomial = true } :=
  match candidate? polynomial with
  | none => none
  | some certificate =>
      if hvalid : certificate.valid polynomial = true then
        some ⟨certificate, hvalid⟩
      else
        none

end CauchyBoundCertificate

end CAS.Polynomial.RealRoot
