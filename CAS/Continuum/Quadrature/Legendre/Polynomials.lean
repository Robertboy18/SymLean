/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.Gaussian.Recurrence
public import CAS.Continuum.Quadrature.Legendre.Identification

/-!
# The monic Legendre polynomials of degree at most four

`monicPolynomial n` is the monic orthogonal polynomial of degree `n` for the constant weight on
`[-1, 1]`, and `one_nodal_eq`, ..., `four_nodal_eq` identify it with the nodal polynomial of the
explicit rule with `n` nodes. Multiplying out the product of `X - C x` over the nodes of that rule
gives the coefficients of `monicPolynomial n` for `1 ≤ n ≤ 4`, and `orthogonalPolynomial_zero` of
`Recurrence` gives `monicPolynomial 0 = 1`.

## Main results

* `monicPolynomial_zero`, ..., `monicPolynomial_four`: `1`, `X`, `X ^ 2 - 1 / 3`,
  `X ^ 3 - (3 / 5) X` and `X ^ 4 - (30 / 35) X ^ 2 + 3 / 35`.
* `twoNode_eq_one_div_sqrt`: the positive two-point node is `1 / √3`.

## References

* Andrew W. Appel and David S. Bindel, `proof/quadrature.v` in the `simple_cfem` repository, <https://github.com/VeriNum/simple_cfem/blob/226b2cc7e476daf141c3b8cddfafc63c1d34d1d3/proof/quadrature.v#L2441-L2616>.
  The lemmas `Legendre_poly_0`, ..., `Legendre_poly_4` there state the same coefficients for
  the polynomials of the three-term recurrence.
-/

@[expose] public section

namespace CAS.Continuum.Legendre

open Polynomial

/-- The positive node of the two-point rule is `1 / √3`. -/
theorem twoNode_eq_one_div_sqrt : twoNode = 1 / Real.sqrt 3 := by
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hn : Real.sqrt 3 ≠ 0 := by positivity
  rw [twoNode, eq_div_iff hn, div_mul_eq_mul_div, hs, div_self (by norm_num : (3 : ℝ) ≠ 0)]

/-- The monic Legendre polynomial of degree zero is `1`. -/
theorem monicPolynomial_zero : monicPolynomial 0 = 1 := by
  rw [monicPolynomial, integralOrthogonalPolynomial, orthogonalPolynomial_zero]

/-- The monic Legendre polynomial of degree one is `X`. -/
theorem monicPolynomial_one : monicPolynomial 1 = X := by
  rw [← one_nodal_eq, Lagrange.nodal, Fin.prod_univ_one]
  change X - C 0 = X
  rw [C_0, sub_zero]

/-- The monic Legendre polynomial of degree two is `X ^ 2 - 1 / 3`. -/
theorem monicPolynomial_two : monicPolynomial 2 = X ^ 2 - C (1 / 3) := by
  rw [← two_nodal_eq, Lagrange.nodal, Fin.prod_univ_two, ← twoNode_sq]
  change (X - C (-twoNode)) * (X - C twoNode) = X ^ 2 - C (twoNode ^ 2)
  rw [C_neg, C_pow]
  ring

/-- The monic Legendre polynomial of degree three is `X ^ 3 - (3 / 5) X`. -/
theorem monicPolynomial_three : monicPolynomial 3 = X ^ 3 - C (3 / 5) * X := by
  rw [← three_nodal_eq, Lagrange.nodal, Fin.prod_univ_three, ← threeNode_sq]
  change (X - C (-threeNode)) * (X - C 0) * (X - C threeNode) = X ^ 3 - C (threeNode ^ 2) * X
  rw [C_neg, C_0, C_pow]
  ring

/-- The monic Legendre polynomial of degree four is `X ^ 4 - (30 / 35) X ^ 2 + 3 / 35`. -/
theorem monicPolynomial_four :
    monicPolynomial 4 = X ^ 4 - C (30 / 35) * X ^ 2 + C (3 / 35) := by
  have hsum : (30 / 35 : ℝ) = fourOuter ^ 2 + fourInner ^ 2 := by
    rw [fourOuter_sq, fourInner_sq]
    ring
  have hprod : (3 / 35 : ℝ) = fourOuter ^ 2 * fourInner ^ 2 := by
    rw [fourOuter_sq, fourInner_sq]
    linear_combination (4 / 1225 : ℝ) * fourRadical_sq
  rw [← four_nodal_eq, Lagrange.nodal, Fin.prod_univ_four, hsum, hprod]
  change (X - C (-fourOuter)) * (X - C (-fourInner)) * (X - C fourInner) * (X - C fourOuter) = _
  simp only [C_neg, C_add, C_mul, C_pow]
  ring

end CAS.Continuum.Legendre
