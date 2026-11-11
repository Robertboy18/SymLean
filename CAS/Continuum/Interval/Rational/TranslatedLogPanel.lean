/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Analysis.Fourier.HilbertTransform.LogPotential.TranslatedPolynomial

public import CAS.Continuum.Interval.Rational.LogPrimitive

/-!
# Logarithmic panel integrals from coefficient enclosures

If `p y = ∑ i, v i * (y - x) ^ i`, then
`polynomialLogPanel p a b x = ∫ y in a..b, p y * log |x - y|` is
`∑ i, v i * (logMonomialPrimitive i (b - x) - logMonomialPrimitive i (a - x))`, also when `x` is
an endpoint of the panel. `translatedLogPanelInterval` evaluates this sum from enclosures
`c i` of the coefficients `v i`, and `translatedLogPanelInterval_sound` shows that the result
contains the panel integral.

## Implementation notes

Term by term, `translatedLogPanelInterval` encloses two logarithms per coefficient, at `a - x`
and at `b - x`, inside `logMonomialPrimitiveInterval`. `translatedLogPanelIntervalShared`
evaluates the two logarithms once for all coefficients and none for `n = 0`. Since
`translatedLogPanelInterval_eq_shared` is a `@[csimp]` theorem, compiled code runs the shared
version, while the kernel and the proofs keep the plain sum. `translatedLogPanelInterval_sound`
rewrites the integral by the exact identity `polynomialLogPanel_eq_sum_of_eval` and encloses each
term with `sum_sound`, `mul_sound`, `sub_sound` and `logMonomialPrimitiveInterval_sound`. No
module of SymLean imports this one; it serves certificates built on the library.
-/

@[expose] public section

open MeasureTheory
open scoped Polynomial

namespace CAS.Continuum.RationalInterval

open CAS.Analysis

/-- Interval evaluation of the panel integral from coefficient enclosures `c i` in powers of
`y - x`. -/
def translatedLogPanelInterval {n : ℕ} (terms : ℕ) (c : Fin n → RationalInterval)
    (a b x : ℚ) : RationalInterval :=
  sum Finset.univ fun i ↦ (c i).mul
    ((logMonomialPrimitiveInterval terms i.val (b - x)).sub
      (logMonomialPrimitiveInterval terms i.val (a - x)))

/-- The same enclosure with endpoint logarithms shared across all coefficients.
The empty polynomial returns zero without evaluating either logarithm. -/
def translatedLogPanelIntervalShared {n : ℕ} (terms : ℕ)
    (c : Fin n → RationalInterval) (a b x : ℚ) : RationalInterval :=
  if n = 0 then const 0 else
    let left := a - x
    let right := b - x
    let leftLog := logAbsPointIntervalWith terms left
    let rightLog := logAbsPointIntervalWith terms right
    sum Finset.univ fun i ↦
      let degree : ℕ := i.val + 1
      let leftPower := left ^ degree
      let rightPower := right ^ degree
      let leftPrimitive := ((const (leftPower / degree)).mul leftLog).sub
        (const (leftPower / degree ^ 2))
      let rightPrimitive := ((const (rightPower / degree)).mul rightLog).sub
        (const (rightPower / degree ^ 2))
      (c i).mul (rightPrimitive.sub leftPrimitive)

/-- Sharing logarithms and powers preserves the exact rational endpoints.
Compiled evaluation uses this equality; kernel reduction keeps the original definition. -/
@[csimp] theorem translatedLogPanelInterval_eq_shared :
    @translatedLogPanelInterval = @translatedLogPanelIntervalShared := by
  funext n terms c a b x
  by_cases hn : n = 0
  · subst n
    apply ext <;> simp [translatedLogPanelInterval, translatedLogPanelIntervalShared, sum]
  · simp only [translatedLogPanelIntervalShared, ite_eq_right hn]
    simp only [translatedLogPanelInterval, logMonomialPrimitiveInterval,
      Nat.cast_add, Nat.cast_one]

/-- If `p y = ∑ i, v i * (y - x) ^ i` and each `v i ∈ c i`, then
`translatedLogPanelInterval terms c a b x` contains `polynomialLogPanel p a b x`. -/
theorem translatedLogPanelInterval_sound {n : ℕ} (terms : ℕ)
    (c : Fin n → RationalInterval) (a b x : ℚ) (p : ℝ[X]) (v : Fin n → ℝ)
    (hv : ∀ i, (c i).MemReal (v i))
    (hp : ∀ y, p.eval y = ∑ i : Fin n, v i * (y - (x : ℝ)) ^ i.val) :
    (translatedLogPanelInterval terms c a b x).MemReal
      (polynomialLogPanel p a b x) := by
  rw [polynomialLogPanel_eq_sum_of_eval p v a b x hp]
  refine sum_sound fun i _ ↦ mul_sound (hv i) ?_
  simpa only [Rat.cast_sub] using sub_sound (logMonomialPrimitiveInterval_sound terms i.val (b - x))
    (logMonomialPrimitiveInterval_sound terms i.val (a - x))

end CAS.Continuum.RationalInterval
