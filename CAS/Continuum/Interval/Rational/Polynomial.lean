/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Arithmetic
public import CAS.Polynomial.NestedCoefficientList

/-!
# Interval evaluation of coefficient lists

`coeffRange l I` evaluates the polynomial with coefficient list `l` on the interval `I` by
Horner's rule in interval arithmetic, and `nestedRange M X Y` the polynomial
`∑ j, X ^ j m_j(Y)` of a list of coefficient lists; both contain the real values at every point
of the intervals (`coeffRange_sound`, `nestedRange_sound`).

## Main definitions

* `coeffRange`: Horner's rule for the coefficient list `l` on the interval `I`.
* `nestedRange`: Horner's rule in `X` for the nested list `M`, with the entries evaluated on `Y`.

## Main results

* `coeffRange_sound`: for `x ∈ I`, `coeffRange l I` contains the value at `x` of the polynomial
  with coefficient list `l`.
* `nestedRange_sound`: for `x ∈ X` and `y ∈ Y`, `nestedRange M X Y` contains `nestedEval M x y`.

## Implementation notes

Both evaluations are `List.foldr` over the coefficient lists with the exact operations `const`,
`add` and `mul`, so nothing is rounded. Each step mirrors one step of the real evaluations
`coeffEval` (`CAS.Polynomial.CoefficientEval`) and `nestedEval`
(`CAS.Polynomial.NestedCoefficientList`), which are the same folds, so the soundness proofs are
inductions on the list with `add_sound`, `mul_sound` and `memReal_const`; `nestedRange_sound`
uses `coeffRange_sound` for the inner lists. No module of SymLean imports this one; it serves
certificates built on the library.

## References

* Siegfried M. Rump, "Verification methods: Rigorous results using floating-point arithmetic",
  *Acta Numerica* 19 (2010), pp. 287-449, <https://doi.org/10.1017/S096249291000005X>.
  Section 5.5 for the natural interval extension of an expression and the inclusion principle
  (5.17), which the soundness theorems prove for the Horner form.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open CAS.Polynomial

/-- Horner's rule for the coefficient list `l` on the interval `I`. -/
def coeffRange (l : List ℚ) (I : RationalInterval) : RationalInterval :=
  l.foldr (fun c acc ↦ (const c).add (I.mul acc)) (const 0)

/-- For `x ∈ I`, `coeffRange l I` contains the value at `x` of the polynomial with coefficient list
`l`. -/
theorem coeffRange_sound (l : List ℚ) {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    (coeffRange l I).MemReal (coeffEval l x) := by
  induction l with
  | nil => simpa [coeffRange] using memReal_const 0
  | cons c l ih => simpa [coeffRange] using add_sound (memReal_const c) (mul_sound hx ih)

/-- Horner's rule in `X` for the nested list `M`, the entries evaluated on `Y`. -/
def nestedRange (M : List (List ℚ)) (X Y : RationalInterval) : RationalInterval :=
  M.foldr (fun m acc ↦ (coeffRange m Y).add (X.mul acc)) (const 0)

/-- For `x ∈ X` and `y ∈ Y`, `nestedRange M X Y` contains `nestedEval M x y`. -/
theorem nestedRange_sound (M : List (List ℚ)) {X Y : RationalInterval} {x y : ℝ}
    (hx : X.MemReal x) (hy : Y.MemReal y) : (nestedRange M X Y).MemReal (nestedEval M x y) := by
  induction M with
  | nil => simpa [nestedRange] using memReal_const 0
  | cons m M ih => simpa [nestedRange] using add_sound (coeffRange_sound m hy) (mul_sound hx ih)

end RationalInterval
end CAS.Continuum
