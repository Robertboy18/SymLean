/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Inclusion.Ranges
public meta import CAS.Continuum.Interval.Inclusion.Ranges
public import Mathlib.Tactic.Inclusion.ExtensionAPI.Attr
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# `cega_real` operations

We extend Mathlib's `interval_dyadic_real` family with the `cega_real` operations for
reciprocals and quotients, natural powers, `π`, `exp`, `log`, `sqrt`, `sin`, `cos`, `arctan`,
`arcsin`, `arccos`, `sinh`, `cosh` and `tanh`. For example:

```
example : Real.exp 1 < 2.7183 := by dyadic_interval [cega_real, prec := 20]
```

The reciprocal follows Lean's `0⁻¹ = 0` and the logarithm Mathlib's `log x = log |x|`, so both
use CEGA's range on an argument interval that excludes zero and the whole line on one that
contains zero.

`dyadic_interval` evaluates the interval program it builds before the kernel checks it, so the
ranges must also be available at compile time. The meta imports above make them available to
every module that imports this one.

The `prec` parameter sets the dyadic rounding of every result and also the work CEGA does
before rounding: the Taylor order of `exp`, `sinh`, `cosh` and `tanh` and the series length of
`log` are at least `prec / 2`, and the square root keeps at least `prec + 4` binary digits.
The `π` bracket and the series lengths of the trigonometric and inverse trigonometric
ranges retain their own precision policies; increasing `prec` alone does not refine them.
-/

@[expose] public section

open Inclusion

namespace CAS.Continuum.CEGAInclusion

open RationalInterval

/-! ## Global ranges -/

/-- Every real number lies in the unbounded dyadic interval `Interval.univ Dyadic`. -/
theorem mem_univ (x : ℝ) : x ∈ Interval.univ Dyadic :=
  Interval.mem_map_univ Dyadic.toReal x

/-- The dyadic `1` read as a real is `1`. -/
theorem toReal_one : (1 : Dyadic).toReal = 1 := by
  simp [Dyadic.toReal, show (1 : Dyadic).toRat = 1 from rfl]

/-- Reading dyadics as reals commutes with negation: `(-d).toReal = -d.toReal`. -/
theorem toReal_neg (d : Dyadic) : (-d).toReal = -d.toReal := by
  simp [Dyadic.toReal, Dyadic.toRat_neg]

/-- A real `x` with `-1 ≤ x ≤ 1` lies in the dyadic interval `closed (-1) 1`. -/
theorem mem_closed_neg_one_one {x : ℝ} (hlo : -1 ≤ x) (hhi : x ≤ 1) : x ∈ closed (-1) 1 :=
  mem_closed (by simpa [toReal_neg, toReal_one] using hlo) (by simpa [toReal_one] using hhi)

/-- A real `x` with `-2 ≤ x ≤ 2` lies in the dyadic interval `closed (-2) 2`. -/
theorem mem_closed_neg_two_two {x : ℝ} (hlo : -2 ≤ x) (hhi : x ≤ 2) : x ∈ closed (-2) 2 :=
  mem_closed (by simpa [toReal_neg] using hlo) (by simpa using hhi)


/-! ## Arithmetic -/

/-- If `invRange? J = some K` (so `J` lies on one side of zero) and `x` lies in `J`, then `x⁻¹` lies
in `K`. -/
theorem invRange?_sound {J K : RationalInterval} {x : ℝ} (hK : invRange? J = some K)
    (hx : J.MemReal x) : K.MemReal x⁻¹ := by
  unfold invRange? at hK
  split_ifs at hK with h h' <;> cases hK
  · exact invPositive_sound h hx
  · simpa using neg_sound (invPositive_sound h' (neg_sound hx))

/-- The reciprocal of `x ∈ I`. -/
@[inclusion_op cega_real]
theorem inv_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    x⁻¹ ∈ liftUnary invRange? (Interval.univ Dyadic) I prec :=
  mem_liftUnary invRange?_sound (fun _ ↦ mem_univ _) hx prec

/-- A quotient is the product with the reciprocal range. -/
@[inclusion_op cega_real]
theorem div_mem {x y : ℝ} {I J : Interval Dyadic} (hx : x ∈ I) (hy : y ∈ J) (prec : ℕ) :
    x / y ∈ I.mul (liftUnary invRange? (Interval.univ Dyadic) J prec) :=
  div_eq_mul_inv x y ▸ IntervalDyadicReal.mul_mem hx (inv_mem hy prec)

/-- Natural powers through FloatLib's sharp odd and even endpoint bounds. -/
@[inclusion_op cega_real]
theorem pow_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (n : ℕ) (prec : ℕ) :
    x ^ n ∈ liftUnary (fun J ↦ some (J.powNat n)) (Interval.univ Dyadic) I prec :=
  mem_liftUnary (by rintro J K y ⟨⟩ hy; exact powNat_sound hy n) (fun _ ↦ mem_univ _)
    hx prec

/-- `π` from CEGA's twenty-digit rational bracket. -/
@[inclusion_op cega_real]
theorem pi_mem (prec : ℕ) : Real.pi ∈ ofRational piInterval prec :=
  mem_ofRational piInterval_sound prec

/-! ## Exponential, logarithm, and square root -/

/-- The exponential range of `I`, with `[0, ∞)` as the unbounded-input fallback. -/
@[inclusion_op cega_real]
theorem exp_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.exp x ∈ liftUnary (fun J ↦ some (J.expRangeWith (taylorOrder prec)))
      (atLeast 0) I prec :=
  mem_liftUnary (by rintro J K y ⟨⟩ hy; exact expRangeWith_sound J _ hy)
    (fun y ↦ mem_atLeast (by simpa [Dyadic.toReal] using (Real.exp_pos y).le)) hx prec

/-- If `logRange? terms J = some K` (so `J` lies on one side of zero) and `x` lies in `J`, then
`Real.log x` (which is `log |x|` for negative `x`) lies in `K`, for every number of terms. -/
theorem logRange?_sound {terms : ℕ} {J K : RationalInterval} {x : ℝ}
    (hK : logRange? terms J = some K) (hx : J.MemReal x) : K.MemReal (Real.log x) := by
  unfold logRange? at hK
  split_ifs at hK with h h' <;> cases hK
  · exact logRangeWith_sound J terms h hx
  · simpa using logRangeWith_sound J.neg terms h' (neg_sound hx)

/-- The total logarithm range of `I`, with the whole line as the fallback across zero. -/
@[inclusion_op cega_real]
theorem log_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.log x ∈ liftUnary (logRange? (max logSeriesTerms (prec / 2))) (Interval.univ Dyadic)
      I prec :=
  mem_liftUnary logRange?_sound (fun _ ↦ mem_univ _) hx prec

/-- The total square-root range of `I`, including Mathlib's zero values below zero. -/
@[inclusion_op cega_real]
theorem sqrt_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.sqrt x ∈ liftUnary
      (fun J ↦ some (J.sqrtRangeInterval (max defaultSqrtRefinementSteps (prec + 4))))
      (atLeast 0) I prec :=
  mem_liftUnary (by rintro J K y ⟨⟩ hy; exact sqrtRangeInterval_sound J _ hy)
    (fun y ↦ mem_atLeast (by simp [Dyadic.toReal, Real.sqrt_nonneg y])) hx prec

/-! ## Trigonometric functions and their inverses -/

/-- The sine range of `I`, with the global bound `[-1, 1]` for unbounded inputs. -/
@[inclusion_op cega_real]
theorem sin_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.sin x ∈ liftUnary (fun J ↦ some J.sin) (closed (-1) 1) I prec :=
  mem_liftUnary (by rintro J K y ⟨⟩ hy; exact sin_sound hy)
    (fun y ↦ mem_closed_neg_one_one (Real.neg_one_le_sin y) (Real.sin_le_one y)) hx prec

/-- The cosine range of `I`, with the global bound `[-1, 1]` for unbounded inputs. -/
@[inclusion_op cega_real]
theorem cos_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.cos x ∈ liftUnary (fun J ↦ some J.cos) (closed (-1) 1) I prec :=
  mem_liftUnary (by rintro J K y ⟨⟩ hy; exact cos_sound hy)
    (fun y ↦ mem_closed_neg_one_one (Real.neg_one_le_cos y) (Real.cos_le_one y)) hx prec

/-- The arctangent range of `I`, with `[-2, 2]` containing every fallback value. -/
@[inclusion_op cega_real]
theorem arctan_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.arctan x ∈ liftUnary (fun J ↦ some J.atanRange) (closed (-2) 2) I prec :=
  mem_liftUnary (by rintro J K y ⟨⟩ hy; exact atanRange_sound J hy)
    (fun y ↦ mem_closed_neg_two_two
      (by linarith [Real.neg_pi_div_two_lt_arctan y, Real.pi_div_two_le_two])
      (by linarith [Real.arctan_lt_pi_div_two y, Real.pi_div_two_le_two])) hx prec

/-- The total arcsine range of `I`, with `[-2, 2]` containing every fallback value. -/
@[inclusion_op cega_real]
theorem arcsin_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.arcsin x ∈ liftUnary (fun J ↦ some J.asinRange) (closed (-2) 2) I prec :=
  mem_liftUnary (by rintro J K y ⟨⟩ hy; exact asinRange_sound J hy)
    (fun y ↦ mem_closed_neg_two_two
      (by linarith [Real.neg_pi_div_two_le_arcsin y, Real.pi_div_two_le_two])
      (by linarith [Real.arcsin_le_pi_div_two y, Real.pi_div_two_le_two])) hx prec

/-- The total arccosine range of `I`, with `[0, 4]` containing every fallback value. -/
@[inclusion_op cega_real]
theorem arccos_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.arccos x ∈ liftUnary (fun J ↦ some J.acosRange) (closed 0 4) I prec :=
  mem_liftUnary (by rintro J K y ⟨⟩ hy; exact acosRange_sound J hy)
    (fun y ↦ mem_closed (by simpa [Dyadic.toReal] using Real.arccos_nonneg y)
      (by simpa using (Real.arccos_le_pi y).trans Real.pi_le_four)) hx prec

/-! ## Hyperbolic functions -/

/-- The hyperbolic sine range of `I`, falling back to the whole line on unbounded inputs. -/
@[inclusion_op cega_real]
theorem sinh_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.sinh x ∈ liftUnary (fun J ↦ some (sinhRange (taylorOrder prec).toPNat' J))
      (Interval.univ Dyadic) I prec :=
  mem_liftUnary (by rintro J K y ⟨⟩ hy; exact sinhRange_sound _ J hy)
    (fun _ ↦ mem_univ _) hx prec

/-- The hyperbolic cosine range of `I`, with the global lower bound one as the fallback. -/
@[inclusion_op cega_real]
theorem cosh_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.cosh x ∈ liftUnary (fun J ↦ some (coshRange (taylorOrder prec).toPNat' J))
      (atLeast 1) I prec :=
  mem_liftUnary (by rintro J K y ⟨⟩ hy; exact coshRange_sound _ J hy)
    (fun y ↦ mem_atLeast (by simp [toReal_one, Real.one_le_cosh y])) hx prec

/-- The hyperbolic tangent range of `I`, with the global bound `[-1, 1]` as the fallback. -/
@[inclusion_op cega_real]
theorem tanh_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) (prec : ℕ) :
    Real.tanh x ∈ liftUnary (fun J ↦ some (tanhRange (taylorOrder prec).toPNat' J))
      (closed (-1) 1) I prec :=
  mem_liftUnary (by rintro J K y ⟨⟩ hy; exact tanhRange_sound _ J hy)
    (fun y ↦ mem_closed_neg_one_one (Real.neg_one_lt_tanh y).le (Real.tanh_lt_one y).le) hx prec

end CAS.Continuum.CEGAInclusion
