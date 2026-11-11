/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
public import CAS.Continuum.Quadrature.Subdivision

/-!
# Certified composite trapezoidal quadrature

`QuadratureCert.trapezoidal` is Mathlib's composite trapezoidal rule `trapezoidal_integral`
with `N` subintervals, with error `|b-a|^3 ζ / (12 N^2)` from Mathlib's
`trapezoidal_error_le_of_c2`, where `ζ` bounds the second derivative.

## Implementation notes

We take the rule, the error bound and its proof from Mathlib
(`Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule`, by P. Michael Kielstra) and
only package them as a `QuadratureCert`; the hypotheses are Mathlib's, including the bound on
`iteratedDerivWithin 2 f [[a,b]]` at every real point. The library's other trapezoidal
certificate, `trapezoidRule.secondOrder` in `SecondOrder`, proves its one-panel bound itself by
the Peano kernel and feeds the generic composite, planned and adaptive constructions.

## References

* The mathlib Community, "The Lean Mathematical Library", in *Proceedings of the 9th ACM SIGPLAN
  International Conference on Certified Programs and Proofs (CPP 2020)*, ACM, 2020,
  pp. 367-381, <https://doi.org/10.1145/3372885.3373824>. The declarations
  `trapezoidal_integral` and `trapezoidal_error_le_of_c2`.
* NIST Digital Library of Mathematical Functions, §3.5 Quadrature, Version 1.2.8 (2026-09-15),
  <https://dlmf.nist.gov/3.5>. Equations (3.5.2) and (3.5.3), the composite trapezoidal rule and
  its error term.
-/

@[expose] public section

open Set

namespace CAS.Continuum
namespace QuadratureCert

/--
The composite trapezoidal rule as a quadrature certificate.

The rule uses `N` subintervals and therefore `N + 1` function evaluations.
The error budget is

`|b-a|^3 * ζ / (12 * N^2)`,

where `ζ` bounds the absolute value of `iteratedDerivWithin 2 f [[a,b]]`
at every real point, as required by the underlying mathlib theorem.
-/
noncomputable def trapezoidal
    {f : ℝ → ℝ} {a b ζ : ℝ} {N : ℕ}
    (hf : ContDiffOn ℝ 2 f (Set.uIcc a b))
    (hsecond : ∀ x, |iteratedDerivWithin 2 f (Set.uIcc a b) x| ≤ ζ)
    (hN : 0 < N) :
    QuadratureCert f a b where
  value := trapezoidal_integral f N a b
  error := |b - a| ^ 3 * ζ / (12 * N ^ 2)
  sound := by
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact trapezoidal_error_le_of_c2 hf hsecond hN

end QuadratureCert

end CAS.Continuum
