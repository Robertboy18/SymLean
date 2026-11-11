/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import CAS.Continuum.Quadrature.WeightedSum
public import CAS.Certificate.Quadrature

/-!
# Normalized quadrature rules

A quadrature rule is represented by an ordered list of weights and nodes on the reference
interval `[0,1]`. The carrier `NormalizedQuadratureRule 𝕜` is generic in the scalars:
`QuadratureRule` has real weights and nodes, and the executable `RationalQuadratureRule` of
`RationalRule` rational ones. The list fixes the order in which the terms are added.

The generic facts are proved once:

* affine transport from `[0,1]` to an arbitrary oriented interval;
* exactness on monomials from exact moments;
* exactness on every polynomial of bounded degree;
* zero-error `QuadratureCert`s for exactly integrated functions;
* transport to uniformly approximated integrands.

Concrete rules such as Simpson's rule only need to provide their nodes,
weights, and a finite moment calculation.

## Main results

* `QuadratureRule.exactFor_polynomial`: a rule whose moments through degree `d`
  agree with `∫₀¹ xᵏ dx = 1/(k+1)` integrates every polynomial of degree at most
  `d` exactly (the classical characterisation of degree of exactness).
* `QuadratureRule.valueOn_eq_integral_of_exactFor`: if the normalized rule is
  exact for the affine pullback `x ↦ f (a + x (b - a))`, the transported value
  `valueOn f a b` equals `∫ₐᵇ f` on any oriented interval.
* `QuadratureRule.exactCert`, `QuadratureRule.certOfApprox`: zero-error
  certificates for exactly integrated functions, and their transport to a
  uniformly approximated integrand.
* `QuadratureRule.valueOn_eq_integral_of_natDegree_le`: a rule exact through degree `d`
  integrates every polynomial of degree at most `d` exactly on every oriented interval.

## Implementation notes

All integrals are Mathlib's totalized interval integral, so exactness statements
never assert integrability; analytic callers supply `IntervalIntegrable` evidence
separately where it is needed.

## References

* NIST Digital Library of Mathematical Functions, §3.5 Quadrature, Version 1.2.8 (2026-09-15),
  <https://dlmf.nist.gov/3.5>. §3.5(iv): an interpolatory rule with `n` nodes integrates every
  polynomial of degree at most `n - 1` exactly.
-/

@[expose] public section

open MeasureTheory

namespace CAS.Continuum

open CAS.Certificate

/--
An ordered quadrature rule on the normalized interval `[0,1]`, over a scalar
type with zero, one, and an order relation.

The common carrier is shared by exact-real analytic rules and executable
rational rules. Scalar-specific evaluation and exactness notions remain in
their respective namespaces.
-/
structure NormalizedQuadratureRule (𝕜 : Type*) [Zero 𝕜] [One 𝕜] [Preorder 𝕜] where
  /-- Ordered `(weight, node)` pairs. -/
  terms : List (𝕜 × 𝕜)
  /-- Every node belongs to the reference interval. -/
  nodes_mem_unit : ∀ term ∈ terms, term.2 ∈ Set.Icc (0 : 𝕜) 1

/-- Exact-real normalized quadrature rule used by the analytic semantics. -/
abbrev QuadratureRule :=
  NormalizedQuadratureRule ℝ

namespace QuadratureRule

/-- Exact value of a rule on the reference interval `[0,1]`. -/
def normalizedValue (rule : QuadratureRule) (f : ℝ → ℝ) : ℝ :=
  weightedSum (rule.terms.map fun term ↦ (term.1, f term.2))

/--
Ordered exact-real terms obtained by transporting a normalized rule to the
oriented interval from `a` to `b`.
-/
def termsOn (rule : QuadratureRule) (f : ℝ → ℝ) (a b : ℝ) :
    List (ℝ × ℝ) :=
  rule.terms.map fun term ↦
    ((b - a) * term.1, f (a + term.2 * (b - a)))

/-- Exact value of a transported rule on the oriented interval `a..b`. -/
def valueOn (rule : QuadratureRule) (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  weightedSum (rule.termsOn f a b)

/-- The `k`-th normalized moment of a quadrature rule. -/
def moment (rule : QuadratureRule) (k : ℕ) : ℝ :=
  rule.normalizedValue fun x ↦ x ^ k

/--
A rule is exact through degree `d` when its first `d + 1` moments agree with
Lebesgue integration on `[0,1]`.
-/
def ExactUpTo (rule : QuadratureRule) (d : ℕ) : Prop :=
  ∀ k ≤ d, rule.moment k = 1 / (k + 1 : ℝ)

/--
A rule agrees with the totalized interval integral of `f` on `[0,1]`.

This equality does not imply interval integrability; analytic applications
must supply that evidence separately.
-/
def ExactFor (rule : QuadratureRule) (f : ℝ → ℝ) : Prop :=
  rule.normalizedValue f = ∫ x in (0 : ℝ)..1, f x

/-- The normalized value is additive in the integrand: a weighted sum of `f + g` splits into the
weighted sums of `f` and `g`. -/
theorem normalizedValue_add (rule : QuadratureRule) (f g : ℝ → ℝ) :
    rule.normalizedValue (fun x ↦ f x + g x) =
      rule.normalizedValue f + rule.normalizedValue g := by
  simp [normalizedValue, weightedSum, Function.comp_def, mul_add, List.sum_map_add]

/-- Scalars pull out of the normalized value. Together with `normalizedValue_add` this makes
`normalizedValue` a linear functional on integrands. -/
theorem normalizedValue_const_mul (rule : QuadratureRule)
    (c : ℝ) (f : ℝ → ℝ) :
    rule.normalizedValue (fun x ↦ c * f x) =
      c * rule.normalizedValue f := by
  simp [normalizedValue, weightedSum, Function.comp_def, mul_left_comm, List.sum_map_mul_left]

/-- Every rule assigns the value `0` to the zero integrand. -/
@[simp]
theorem normalizedValue_zero (rule : QuadratureRule) :
    rule.normalizedValue (fun _ ↦ 0) = 0 := by
  simpa using rule.normalizedValue_const_mul 0 (fun _ ↦ 0)

/-- The normalized value commutes with finite sums of integrands. This is the step that lets
moment exactness on monomials extend to arbitrary polynomials in `exactFor_polynomial`. -/
theorem normalizedValue_finset_sum (rule : QuadratureRule)
    {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) :
    rule.normalizedValue (fun x ↦ ∑ i ∈ s, f i x) =
      ∑ i ∈ s, rule.normalizedValue (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, normalizedValue_add, ih]

/-- Affine transport is multiplication of the normalized value by `b - a`. -/
theorem valueOn_eq_smul_normalizedValue
    (rule : QuadratureRule) (f : ℝ → ℝ) (a b : ℝ) :
    rule.valueOn f a b =
      (b - a) • rule.normalizedValue (fun x ↦ f (a + x * (b - a))) := by
  simp [valueOn, termsOn, normalizedValue, weightedSum, Function.comp_def, mul_assoc,
    List.sum_map_mul_left]

/-- Moment exactness gives exact integration of each bounded-degree monomial. -/
theorem exact_monomial {rule : QuadratureRule} {d k : ℕ}
    (hexact : rule.ExactUpTo d) (hk : k ≤ d) :
    rule.ExactFor fun x ↦ x ^ k := by
  change rule.moment k = _
  simp [hexact k hk]

/-- Exact moments through `d` imply exactness for every polynomial of degree at most `d`. -/
theorem exactFor_polynomial {rule : QuadratureRule} {d : ℕ}
    (hexact : rule.ExactUpTo d) (p : Polynomial ℝ)
    (hdegree : p.natDegree ≤ d) :
    rule.ExactFor fun x ↦ p.eval x := by
  classical
  have heval :
      p.eval =
        fun x : ℝ ↦ ∑ k ∈ p.support, p.coeff k * x ^ k := by
    funext x
    simp [Polynomial.eval_eq_sum, Polynomial.sum_def]
  rw [ExactFor, heval, normalizedValue_finset_sum, intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [normalizedValue_const_mul, intervalIntegral.integral_const_mul]
    exact congrArg _ (exact_monomial hexact
      ((Polynomial.le_natDegree_of_mem_supp k hk).trans hdegree))
  · exact fun k _ ↦ (continuous_const.mul (continuous_pow k)).intervalIntegrable 0 1

/--
An exact normalized rule integrates the corresponding affine pullback exactly
on every oriented interval.
-/
theorem valueOn_eq_integral_of_exactFor
    (rule : QuadratureRule) (f : ℝ → ℝ) (a b : ℝ)
    (hexact : rule.ExactFor fun x ↦ f (a + x * (b - a))) :
    rule.valueOn f a b = ∫ x in a..b, f x := by
  rw [valueOn_eq_smul_normalizedValue, hexact]
  simpa [mul_comm] using
    (intervalIntegral.smul_integral_comp_add_mul
      (f := f) (a := 0) (b := 1) (b - a) a)

/--
Package exactness of an affine pullback as a zero-error certificate for the
totalized interval integral. This constructor does not certify integrability.
-/
noncomputable def exactCert
    (rule : QuadratureRule) (f : ℝ → ℝ) (a b : ℝ)
    (hexact : rule.ExactFor fun x ↦ f (a + x * (b - a))) :
    QuadratureCert f a b where
  value := rule.valueOn f a b
  error := 0
  sound := by
    rw [rule.valueOn_eq_integral_of_exactFor f a b hexact]
    simp

/--
Use an exact rule for a model function and transport the certificate to a
uniformly approximated integrand.
-/
noncomputable def certOfApprox
    (rule : QuadratureRule)
    {a b : ℝ}
    (approx : ApproxCert ℝ ℝ (Set.uIcc a b))
    (hexact : rule.ExactFor fun x ↦ approx.rhs (a + x * (b - a)))
    (hlhs : IntervalIntegrable approx.lhs volume a b)
    (hrhs : IntervalIntegrable approx.rhs volume a b) :
    QuadratureCert approx.lhs a b :=
  QuadratureCert.transportApprox approx
    (rule.exactCert approx.rhs a b hexact) hlhs hrhs

end QuadratureRule

/-- Composing with the affine map `x ↦ a + (b - a) x` does not raise the degree of a polynomial. -/
theorem affinePullback_natDegree_le
    (p : Polynomial ℝ) (a b : ℝ) :
    (p.comp (Polynomial.C a + Polynomial.C (b - a) * Polynomial.X)).natDegree ≤
      p.natDegree := by
  have haffine : (Polynomial.C a + Polynomial.C (b - a) * Polynomial.X).natDegree ≤ 1 := by
    compute_degree
  exact Polynomial.natDegree_comp_le.trans
    (by simpa using Nat.mul_le_mul_left p.natDegree haffine)

namespace QuadratureRule

/-- A rule exact through degree `d` on `[0,1]` integrates every polynomial of degree at most
`d` exactly on every oriented interval, since affine pullback does not increase the degree. -/
theorem valueOn_eq_integral_of_natDegree_le {rule : QuadratureRule} {d : ℕ}
    (hexact : rule.ExactUpTo d) (p : Polynomial ℝ) (hp : p.natDegree ≤ d) (a b : ℝ) :
    rule.valueOn (fun x ↦ p.eval x) a b = ∫ x in a..b, p.eval x := by
  apply rule.valueOn_eq_integral_of_exactFor
  simpa [Polynomial.eval_comp, mul_comm] using
    exactFor_polynomial hexact _ ((affinePullback_natDegree_le p a b).trans hp)

end QuadratureRule

end CAS.Continuum
