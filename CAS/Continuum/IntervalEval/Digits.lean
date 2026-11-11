/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.BinaryGridProof
public import CAS.Numerics.TrigFixedPoint
public import CAS.Continuum.Interval.Elementary.Acos
public import CAS.Continuum.Interval.Elementary.Atan
public import CAS.Continuum.Interval.Elementary.Trig
public import CAS.Continuum.IntervalEval.Callbacks
public import CAS.Continuum.Interval.Rational.RelativeHull

/-!
# Interval evaluation at a requested precision

`DigitsEval.eval` runs the shared interval evaluator `IntervalExprOps.evalWithCallbacks` with an
operation table whose precision is a parameter. Every operation is sound for every precision, so
`eval_sound` holds without conditions on the precision. The checks `lowerCheck`, `upperCheck` and
`enclosureCheck` compare the evaluated interval of a closed expression with rational bounds; they
are closed Boolean propositions for the kernel, and `of_lowerCheck_decimal` and
`of_upperCheck_decimal` state the decimal digits they certify.

## Main definitions

* `DigitsEval.Precision`, `DigitsEval.piInterval`, `DigitsEval.ops`, `DigitsEval.callbacks`,
  `DigitsEval.eval`.
* `DigitsEval.lowerCheck`, `DigitsEval.upperCheck`, `DigitsEval.enclosureCheck`.

## Main results

* `DigitsEval.piInterval_sound`, `DigitsEval.backend`, `DigitsEval.callbacks_sound`.
* `DigitsEval.eval_sound`: a successful evaluation encloses the real value.
* `DigitsEval.of_lowerCheck_decimal`, `DigitsEval.of_upperCheck_decimal`,
  `DigitsEval.of_lowerCheck_scaled`, `DigitsEval.of_upperCheck_scaled`,
  `DigitsEval.of_enclosureCheck`, `DigitsEval.of_enclosureCheck_decimal`.

## Implementation notes

`Precision.bits` is the binary grid `2 ^ (-bits)` to which products, powers and elementary
function values are rounded outward. Reciprocals and quotients are rounded relative to their
magnitude (`quotientHull`), so a small quotient such as `1 / 10 ^ 30` keeps `bits` significant
bits. The base table has no raw division: the division callback multiplies by the reciprocal of a
denominator interval that excludes zero and fails otherwise, and a real power `a ^ b` with a
positive base interval is `exp (log a * b)`. `Precision.terms` is the number of series terms
passed to the FloatLib kernels for `sin`, `cos`, `exp` and `atan`, and `Precision.logTerms` the
number for `log`. The exponential and the logarithm use FloatLib's binary-grid point kernels at
the endpoints of a monotone range. Square roots use the grid of `bits` bits. The constant `π`
comes from Machin's formula in fixed point (`CAS.Numerics.piFixed`), which uses natural-number
arithmetic only and is within `(5 w + 41) / 2 ^ w` of `π` at `w` bits. The inverse sine is
`arctan (q / sqrt (1 - q ^ 2))` at the endpoints (`Real.arcsin_eq_arctan`) and the inverse cosine
is `π / 2 - arcsin`.

Outwardly rounded interval arithmetic is classical, and the elementary kernels and their proofs
are FloatLib's; the table, the grids and the precision schedule are ours. `#cas [N d]`
(`CAS.Command.Digits`) runs the evaluator outside the kernel at up to five precisions, doubling
bits and terms each time, until the enclosure fixes the requested digits. The kernel then
decides the corresponding check instance without native code (`decideClosedCertificate`), and
`of_lowerCheck_decimal` or one of its variants turns it into the stated bounds. The precision
decides only whether a check succeeds, never whether it is sound.

## References

* Ramon E. Moore, R. Baker Kearfott and Michael J. Cloud, *Introduction to Interval Analysis*,
  SIAM, Philadelphia, 2009, <https://doi.org/10.1137/1.9780898717716>. Chapter 3 for outwardly
  rounded interval arithmetic.
* Robert Joseph George, Will Adkisson and Anima Anandkumar, *FloatLib: Verified Floating-Point
  Arithmetic in Lean*, version 3.1.0 (commit 0fe4f04), <https://github.com/lean-dojo/FloatLib>. We use its
  enclosures `Interval.sinBounds`, `Interval.cosBounds`, `Interval.atanBounds` and
  `Interval.sqrtBounds?` and its point enclosures `Enclosure.BinaryGrid.exp` and
  `Enclosure.BinaryGrid.log`.
-/

@[expose] public section

namespace CAS.Continuum
namespace DigitsEval

open CAS.Verified
open RationalInterval

/-- The working precision of the evaluator: the rounding grid and the series length. -/
structure Precision where
  /-- Results are rounded outward to the grid `2 ^ (-bits)`. -/
  bits : ℕ
  /-- Number of series terms of the sine, cosine, exponential and arctangent kernels. -/
  terms : ℕ
  /-- Number of series terms of the logarithm kernel, which gains about half a digit per term. -/
  logTerms : ℕ
  deriving Repr, DecidableEq

/-- The working precision for about `digits` decimal digits: a grid of `3.33 digits + 40`
bits and series lengths that reach it for arguments of moderate size. -/
def precisionFor (digits : ℕ) : Precision :=
  { bits := digits * 3322 / 1000 + 40, terms := digits + 24,
    logTerms := digits * 22 / 10 + 40 }

/-- `π` from Machin's formula in fixed point with `w` fractional bits. -/
def piInterval (w : ℕ) : RationalInterval :=
  ofBounds (((CAS.Numerics.piFixed w : ℚ) - (5 * w + 41)) / 2 ^ w)
    (((CAS.Numerics.piFixed w : ℚ) + (5 * w + 41)) / 2 ^ w) (by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : (0 : ℚ) ≤ 5 * w + 41 := by positivity
      linarith)

/-- The Machin interval contains `π`. -/
theorem piInterval_sound (w : ℕ) : (piInterval w).MemReal Real.pi := by
  have h := CAS.Numerics.abs_piFixed_sub_le w
  have hpos : (0 : ℝ) < 2 ^ w := by positivity
  rw [abs_le] at h
  constructor
  · change ((((CAS.Numerics.piFixed w : ℚ) - (5 * w + 41)) / 2 ^ w : ℚ) : ℝ) ≤ _
    push_cast
    exact (div_le_iff₀ hpos).mpr (by linarith [h.2])
  · change _ ≤ ((((CAS.Numerics.piFixed w : ℚ) + (5 * w + 41)) / 2 ^ w : ℚ) : ℝ)
    push_cast
    exact (le_div_iff₀ hpos).mpr (by linarith [h.1])

/-- FloatLib's sine enclosure with `p.terms` terms, rounded outward to `p.bits` bits. -/
def sin (p : Precision) (I : RationalInterval) : RationalInterval :=
  dyadicHull p.bits
    (ofFloatLib (FloatLib.Numerics.Interval.sinBounds I.toFloatLib p.terms)
      (ordered_of_containsReal (FloatLib.Numerics.Interval.containsReal_sinBounds
        I.toFloatLib p.terms ((I.toFloatLib_containsReal_iff _).mpr I.lo_memReal))))

/-- At every precision `p`, if `x` lies in `I` then `sin x` lies in `sin p I`. -/
theorem sin_sound (p : Precision) {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    (sin p I).MemReal (Real.sin x) :=
  dyadicHull_sound _ ((memReal_ofFloatLib_iff _ _ _).mpr
    (FloatLib.Numerics.Interval.containsReal_sinBounds I.toFloatLib p.terms
      ((I.toFloatLib_containsReal_iff x).mpr hx)))

/-- FloatLib's cosine enclosure with `p.terms` terms, rounded outward to `p.bits` bits. -/
def cos (p : Precision) (I : RationalInterval) : RationalInterval :=
  dyadicHull p.bits
    (ofFloatLib (FloatLib.Numerics.Interval.cosBounds I.toFloatLib p.terms)
      (ordered_of_containsReal (FloatLib.Numerics.Interval.containsReal_cosBounds
        I.toFloatLib p.terms ((I.toFloatLib_containsReal_iff _).mpr I.lo_memReal))))

/-- At every precision `p`, if `x` lies in `I` then `cos x` lies in `cos p I`. -/
theorem cos_sound (p : Precision) {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    (cos p I).MemReal (Real.cos x) :=
  dyadicHull_sound _ ((memReal_ofFloatLib_iff _ _ _).mpr
    (FloatLib.Numerics.Interval.containsReal_cosBounds I.toFloatLib p.terms
      ((I.toFloatLib_containsReal_iff x).mpr hx)))

/-- The exponential on an interval from FloatLib's binary-grid point enclosures at its
endpoints, with `p.terms` terms on the grid of `p.bits` bits. -/
def exp (p : Precision) (I : RationalInterval) : RationalInterval where
  lo := (FloatLib.Numerics.Enclosure.BinaryGrid.exp I.lo p.terms p.bits).lo
  hi := (FloatLib.Numerics.Enclosure.BinaryGrid.exp I.hi p.terms p.bits).hi
  hle := by
    have hlo := (FloatLib.Numerics.Enclosure.BinaryGrid.contains_exp I.lo p.terms p.bits).1
    have hhi := (FloatLib.Numerics.Enclosure.BinaryGrid.contains_exp I.hi p.terms p.bits).2
    have hmono := Real.exp_le_exp.mpr (show (I.lo : ℝ) ≤ I.hi by exact_mod_cast I.hle)
    exact_mod_cast hlo.trans (hmono.trans hhi)

/-- At every precision `p`, if `x` lies in `I` then `exp x` lies in `exp p I`. -/
theorem exp_sound (p : Precision) {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    (exp p I).MemReal (Real.exp x) :=
  ⟨(FloatLib.Numerics.Enclosure.BinaryGrid.contains_exp I.lo p.terms p.bits).1.trans
      (Real.exp_le_exp.mpr hx.1),
    (Real.exp_le_exp.mpr hx.2).trans
      (FloatLib.Numerics.Enclosure.BinaryGrid.contains_exp I.hi p.terms p.bits).2⟩

/-- FloatLib's arctangent enclosure with `p.terms` terms, rounded outward to `p.bits` bits. -/
def atan (p : Precision) (I : RationalInterval) : RationalInterval :=
  dyadicHull p.bits (I.atanRangeWith p.terms)

/-- At every precision `p`, if `x` lies in `I` then `arctan x` lies in `atan p I`. -/
theorem atan_sound (p : Precision) {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    (atan p I).MemReal (Real.arctan x) :=
  dyadicHull_sound _ (atanRangeWith_sound I p.terms hx)

/-- The logarithm on a positive interval from FloatLib's binary-grid point enclosures at its
endpoints, with `p.logTerms` terms on the grid of `p.bits` bits. -/
def log (p : Precision) (I : RationalInterval) : Option RationalInterval :=
  if h : 0 < I.lo then
    some {
      lo := (FloatLib.Numerics.Enclosure.BinaryGrid.log I.lo p.logTerms p.bits).lo
      hi := (FloatLib.Numerics.Enclosure.BinaryGrid.log I.hi p.logTerms p.bits).hi
      hle := by
        have hhi0 : 0 < I.hi := h.trans_le I.hle
        have hlo := (FloatLib.Numerics.Enclosure.BinaryGrid.contains_log I.lo p.logTerms p.bits
          h).1
        have hhi := (FloatLib.Numerics.Enclosure.BinaryGrid.contains_log I.hi p.logTerms p.bits
          hhi0).2
        have hmono := Real.log_le_log (by exact_mod_cast h)
          (show (I.lo : ℝ) ≤ I.hi by exact_mod_cast I.hle)
        exact_mod_cast hlo.trans (hmono.trans hhi) }
  else none

/-- At every precision `p`, if `log p I = some result` (which requires `0 < I.lo`) and `x` lies in
`I`, then `Real.log x` lies in `result`. -/
theorem log_sound (p : Precision) {I result : RationalInterval} {x : ℝ}
    (h : log p I = some result) (hx : I.MemReal x) : result.MemReal (Real.log x) := by
  unfold log at h
  split_ifs at h with hpos
  cases h
  have hhi0 : 0 < I.hi := hpos.trans_le I.hle
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (by exact_mod_cast hpos) hx.1
  exact ⟨(FloatLib.Numerics.Enclosure.BinaryGrid.contains_log I.lo p.logTerms p.bits hpos).1.trans
      (Real.log_le_log (by exact_mod_cast hpos) hx.1),
    (Real.log_le_log hxpos hx.2).trans
      (FloatLib.Numerics.Enclosure.BinaryGrid.contains_log I.hi p.logTerms p.bits hhi0).2⟩

/-- FloatLib's square-root enclosure on a nonnegative interval with the grid of `p.bits` bits. -/
def sqrt (p : Precision) (I : RationalInterval) : Option RationalInterval :=
  match h : FloatLib.Numerics.Interval.sqrtBounds? I.toFloatLib p.bits with
  | some K => some (ofFloatLib K
      (ordered_of_containsReal (FloatLib.Numerics.Interval.containsReal_sqrtBounds? h
        ((I.toFloatLib_containsReal_iff _).mpr I.lo_memReal))))
  | none => none

/-- At every precision `p`, if `sqrt p I = some result` and `x` lies in `I`, then `Real.sqrt x` lies
in `result`. -/
theorem sqrt_sound (p : Precision) {I result : RationalInterval} {x : ℝ}
    (h : sqrt p I = some result) (hx : I.MemReal x) : result.MemReal (Real.sqrt x) := by
  unfold sqrt at h
  split at h
  · rename_i K hK
    cases h
    exact (memReal_ofFloatLib_iff _ _ _).mpr
      (FloatLib.Numerics.Interval.containsReal_sqrtBounds? hK
        ((I.toFloatLib_containsReal_iff x).mpr hx))
  · cases h

/-- The reciprocal of an interval that excludes zero, rounded outward to `p.bits` significant
bits. -/
def inv (p : Precision) (I : RationalInterval) : Option RationalInterval :=
  if h : 0 < I.lo then some (quotientHull p.bits (I.invPositive h))
  else if h' : 0 < I.neg.lo then some (quotientHull p.bits (I.neg.invPositive h')).neg
  else none

/-- At every precision `p`, if `inv p I = some result` (which requires `I` to lie on one side of
zero) and `x` lies in `I`, then `x⁻¹` lies in `result`. -/
theorem inv_sound (p : Precision) {I result : RationalInterval} {x : ℝ}
    (h : inv p I = some result) (hx : I.MemReal x) : result.MemReal x⁻¹ := by
  unfold inv at h
  split_ifs at h with hpos hneg
  · cases h
    exact quotientHull_sound _ (invPositive_sound hpos hx)
  · cases h
    have hmem := neg_sound (quotientHull_sound p.bits (invPositive_sound hneg (neg_sound hx)))
    simpa [inv_neg] using hmem

/-- Half of the Machin interval, rounded outward: an enclosure of `π / 2`. -/
def halfPi (p : Precision) : RationalInterval :=
  dyadicHull p.bits ((piInterval p.bits).mul (const (1 / 2)))

/-- At every precision `p`, `π / 2` lies in `halfPi p`. -/
theorem halfPi_sound (p : Precision) : (halfPi p).MemReal (Real.pi / 2) := by
  have hhalf : (const (1 / 2)).MemReal (2 : ℝ)⁻¹ := by simpa using memReal_const (1 / 2 : ℚ)
  rw [div_eq_mul_inv]
  exact dyadicHull_sound _ (mul_sound (piInterval_sound p.bits) hhalf)

/-- `arcsin q` at a rational point: `arctan (q / sqrt (1 - q ^ 2))` inside `(-1, 1)` and
`± π / 2` outside. -/
def asinPoint (p : Precision) (q : ℚ) : Option RationalInterval :=
  if 1 ≤ q then some (halfPi p)
  else if q ≤ -1 then some (halfPi p).neg
  else
    match sqrt p (const (1 - q ^ 2)) with
    | some S =>
        match inv p S with
        | some T => some (atan p (dyadicHull p.bits ((const q).mul T)))
        | none => none
    | none => none

/-- At every precision `p` and rational `q`, if `asinPoint p q = some result`, then `Real.arcsin q`
lies in `result` (for `|q| ≥ 1` Mathlib's `arcsin` is `± π / 2`). -/
theorem asinPoint_sound (p : Precision) {q : ℚ} {result : RationalInterval}
    (h : asinPoint p q = some result) : result.MemReal (Real.arcsin q) := by
  unfold asinPoint at h
  split_ifs at h with hone hneg
  · cases h
    rw [Real.arcsin_of_one_le (by exact_mod_cast hone)]
    exact halfPi_sound p
  · cases h
    rw [Real.arcsin_of_le_neg_one (by exact_mod_cast hneg)]
    exact neg_sound (halfPi_sound p)
  · cases hS : sqrt p (const (1 - q ^ 2)) with
    | none => simp [hS] at h
    | some S =>
        cases hT : inv p S with
        | none => simp [hS, hT] at h
        | some T =>
            simp only [hS, hT, Option.some.injEq] at h
            subst h
            have hq : (q : ℝ) ∈ Set.Ioo (-1) 1 :=
              ⟨by exact_mod_cast lt_of_not_ge hneg, by exact_mod_cast lt_of_not_ge hone⟩
            rw [Real.arcsin_eq_arctan hq]
            have hc := memReal_const (1 - q ^ 2)
            push_cast at hc
            rw [div_eq_mul_inv]
            exact atan_sound p (dyadicHull_sound _
              (mul_sound (memReal_const q) (inv_sound p hT (sqrt_sound p hS hc))))

/-- The inverse sine on an interval from its endpoint values, with the CEGA range as a
fallback. -/
def asin (p : Precision) (I : RationalInterval) : RationalInterval :=
  match asinPoint p I.lo, asinPoint p I.hi with
  | some A, some B => if h : A.lo ≤ B.hi then ofBounds A.lo B.hi h else asinRange I
  | _, _ => asinRange I

/-- At every precision `p`, if `x` lies in `I` then `Real.arcsin x` lies in `asin p I`. -/
theorem asin_sound (p : Precision) {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    (asin p I).MemReal (Real.arcsin x) := by
  unfold asin
  split
  · rename_i A B hA hB
    split_ifs
    · exact ⟨(asinPoint_sound p hA).1.trans (Real.arcsin_le_arcsin hx.1),
        (Real.arcsin_le_arcsin hx.2).trans (asinPoint_sound p hB).2⟩
    · exact asinRange_sound I hx
  · exact asinRange_sound I hx

/-- The inverse cosine as `π / 2 - arcsin`. -/
def acos (p : Precision) (I : RationalInterval) : RationalInterval :=
  (halfPi p).add (asin p I).neg

/-- At every precision `p`, if `x` lies in `I` then `Real.arccos x` lies in `acos p I`. -/
theorem acos_sound (p : Precision) {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    (acos p I).MemReal (Real.arccos x) := by
  rw [Real.arccos_eq_pi_div_two_sub_arcsin, sub_eq_add_neg]
  exact add_sound (halfPi_sound p) (neg_sound (asin_sound p hx))

/-- The unary operations of the evaluator at precision `p`. -/
def unary (p : Precision) : UnaryKind → RationalInterval → Option RationalInterval
  | .inv, I => inv p I
  | .exp, I => some (exp p I)
  | .log, I => log p I
  | .atan, I => some (atan p I)
  | .asin, I => some (asin p I)
  | .acos, I => some (acos p I)
  | .sqrt, I => sqrt p I

/-- At every precision `p` and for every unary operation `op`, if `unary p op I = some result` and
`x` lies in `I`, then `op.apply x` lies in `result`. -/
theorem unary_sound (p : Precision) :
    ∀ (op : UnaryKind) (I result : RationalInterval) (x : ℝ),
      unary p op I = some result → I.MemReal x → result.MemReal (op.apply x)
  | .inv, _, _, _, h, hx => inv_sound p h hx
  | .exp, _, _, _, h, hx => Option.some.inj h ▸ exp_sound p hx
  | .log, _, _, _, h, hx => log_sound p h hx
  | .atan, _, _, _, h, hx => Option.some.inj h ▸ atan_sound p hx
  | .asin, _, _, _, h, hx => Option.some.inj h ▸ asin_sound p hx
  | .acos, _, _, _, h, hx => Option.some.inj h ▸ acos_sound p hx
  | .sqrt, _, _, _, h, hx => sqrt_sound p h hx

/-- The base operations at precision `p`. -/
def ops (p : Precision) : IntervalExprOps RationalInterval where
  const? q := some (const q)
  pi? := some (piInterval p.bits)
  e? := some (exp p (const 1))
  add? I J := some (I.add J)
  mul? I J := some (dyadicHull p.bits (I.mul J))
  pow? I k := some (dyadicHull p.bits (I.powNat k))
  div? _ _ := none
  neg? I := some I.neg
  sin? I := some (sin p I)
  cos? I := some (cos p I)

/-- Soundness of the base operations at every precision. -/
theorem backend (p : Precision) : IntervalExprBackend (ops p) where
  const_sound q result h := Option.some.inj h ▸ memReal_const q
  pi_sound result h := Option.some.inj h ▸ piInterval_sound p.bits
  e_sound result h := Option.some.inj h ▸ exp_sound p (by simpa using memReal_const 1)
  add_sound A B result x y h hx hy := Option.some.inj h ▸ add_sound hx hy
  mul_sound A B result x y h hx hy := Option.some.inj h ▸ dyadicHull_sound _ (mul_sound hx hy)
  pow_sound A k result x h hx := Option.some.inj h ▸ dyadicHull_sound _ (powNat_sound hx k)
  div_sound A B result x y h hx hy := by cases h
  neg_sound A result x h hx := Option.some.inj h ▸ RationalInterval.neg_sound hx
  sin_sound A result x h hx := Option.some.inj h ▸ DigitsEval.sin_sound p hx
  cos_sound A result x h hx := Option.some.inj h ▸ DigitsEval.cos_sound p hx

/-- Division, unary operations and real powers at precision `p`. A real power `a ^ b` is
evaluated as `exp (log a * b)` when the base interval is positive. -/
def callbacks (p : Precision) {ι : Type*} : IntervalExprCallbacks RationalInterval ι where
  div? _ _ IA IB :=
    match inv p IB with
    | some J => some (quotientHull p.bits (IA.mul J))
    | none => none
  unary? op _ IA := unary p op IA
  rpow? _ _ IA IB :=
    if 0 < IA.lo then
      match log p IA with
      | some L => some (exp p (dyadicHull p.bits (L.mul IB)))
      | none => none
    else none

/-- The callbacks satisfy the contract of the shared evaluator in every environment. -/
theorem callbacks_sound (p : Precision) {ι : Type*} (env : ι → RationalInterval) (ρ : ι → ℝ)
    (henv : ∀ i, (env i).MemReal (ρ i)) :
    IntervalExprCallbacks.Sound (ops := ops p) (callbacks := callbacks p) (env := env)
      (ρ := ρ) where
  vars := henv
  div := by
    intro a b IA IB result _ _ h ha hb
    change (match inv p IB with
      | some J => some (quotientHull p.bits (IA.mul J))
      | none => none) = some result at h
    split at h
    · cases h
      rw [div_eq_mul_inv]
      exact quotientHull_sound _ (mul_sound ha (inv_sound p ‹_› hb))
    · cases h
  unary := by
    intro op arg IA result _ h ha
    exact unary_sound p op IA result _ h ha
  rpow := by
    intro a b IA IB result _ _ h ha hb
    change (if 0 < IA.lo then
      (match log p IA with
        | some L => some (exp p (dyadicHull p.bits (L.mul IB)))
        | none => none) else none) = some result at h
    split_ifs at h with hpos
    split at h
    · cases h
      rw [Real.rpow_def_of_pos (lt_of_lt_of_le (by exact_mod_cast hpos) ha.1)]
      exact exp_sound p (dyadicHull_sound _ (mul_sound (log_sound p ‹_› ha) hb))
    · cases h

/-- Interval evaluation of a verified expression at precision `p`. -/
def eval (p : Precision) {ι : Type*} (env : ι → RationalInterval) (expr : Verified.Expr ι) :
    Option RationalInterval :=
  (ops p).evalWithCallbacks (callbacks p) env expr

/-- A successful evaluation encloses the real value whenever the environment encloses the
point. -/
theorem eval_sound (p : Precision) {ι : Type*} (env : ι → RationalInterval) (ρ : ι → ℝ)
    (henv : ∀ i, (env i).MemReal (ρ i)) (expr : Verified.Expr ι) {I : RationalInterval}
    (h : eval p env expr = some I) : I.MemReal (expr.eval ρ) :=
  IntervalExprCallbacks.evalWithCallbacks_sound (backend p) (callbacks_sound p env ρ henv) expr I h

/-- The environment of a closed expression. -/
def closedEnv : Fin 0 → RationalInterval := Fin.elim0

/-- The evaluated interval of a closed expression lies in `[lo, hi)`. -/
def lowerCheck (p : Precision) (expr : Verified.Expr (Fin 0)) (lo hi : ℚ) : Bool :=
  match eval p closedEnv expr with
  | some I => decide (lo ≤ I.lo) && decide (I.hi < hi)
  | none => false

/-- The evaluated interval of a closed expression lies in `(lo, hi]`. -/
def upperCheck (p : Precision) (expr : Verified.Expr (Fin 0)) (lo hi : ℚ) : Bool :=
  match eval p closedEnv expr with
  | some I => decide (lo < I.lo) && decide (I.hi ≤ hi)
  | none => false

/-- The evaluated interval of a closed expression lies in `[lo, hi]`. -/
def enclosureCheck (p : Precision) (expr : Verified.Expr (Fin 0)) (lo hi : ℚ) : Bool :=
  match eval p closedEnv expr with
  | some I => decide (lo ≤ I.lo) && decide (I.hi ≤ hi)
  | none => false

private theorem closedEnv_sound (ρ : Fin 0 → ℝ) : ∀ i, (closedEnv i).MemReal (ρ i) :=
  fun i ↦ i.elim0

/-- If `lowerCheck p expr lo hi = true` for a closed expression, then `lo ≤ expr.eval ρ < hi` for
the (empty) environment `ρ`. -/
theorem of_lowerCheck {p : Precision} {expr : Verified.Expr (Fin 0)} {lo hi : ℚ}
    (h : lowerCheck p expr lo hi = true) (ρ : Fin 0 → ℝ) :
    (lo : ℝ) ≤ expr.eval ρ ∧ expr.eval ρ < hi := by
  unfold lowerCheck at h
  cases hI : eval p closedEnv expr with
  | none => simp [hI] at h
  | some I =>
      simp only [hI, Bool.and_eq_true, decide_eq_true_eq] at h
      have hmem := eval_sound p closedEnv ρ (closedEnv_sound ρ) expr hI
      exact ⟨(Rat.cast_le.mpr h.1).trans hmem.1, hmem.2.trans_lt (Rat.cast_lt.mpr h.2)⟩

/-- If `upperCheck p expr lo hi = true` for a closed expression, then `lo < expr.eval ρ ≤ hi` for
the (empty) environment `ρ`. -/
theorem of_upperCheck {p : Precision} {expr : Verified.Expr (Fin 0)} {lo hi : ℚ}
    (h : upperCheck p expr lo hi = true) (ρ : Fin 0 → ℝ) :
    (lo : ℝ) < expr.eval ρ ∧ expr.eval ρ ≤ hi := by
  unfold upperCheck at h
  cases hI : eval p closedEnv expr with
  | none => simp [hI] at h
  | some I =>
      simp only [hI, Bool.and_eq_true, decide_eq_true_eq] at h
      have hmem := eval_sound p closedEnv ρ (closedEnv_sound ρ) expr hI
      exact ⟨(Rat.cast_lt.mpr h.1).trans_le hmem.1, hmem.2.trans (Rat.cast_le.mpr h.2)⟩

/-- If `enclosureCheck p expr lo hi = true` for a closed expression, then `lo ≤ expr.eval ρ ≤ hi`
for the (empty) environment `ρ`. -/
theorem of_enclosureCheck {p : Precision} {expr : Verified.Expr (Fin 0)} {lo hi : ℚ}
    (h : enclosureCheck p expr lo hi = true) (ρ : Fin 0 → ℝ) :
    (lo : ℝ) ≤ expr.eval ρ ∧ expr.eval ρ ≤ hi := by
  unfold enclosureCheck at h
  cases hI : eval p closedEnv expr with
  | none => simp [hI] at h
  | some I =>
      simp only [hI, Bool.and_eq_true, decide_eq_true_eq] at h
      have hmem := eval_sound p closedEnv ρ (closedEnv_sound ρ) expr hI
      exact ⟨(Rat.cast_le.mpr h.1).trans hmem.1, hmem.2.trans (Rat.cast_le.mpr h.2)⟩

/-- The digits of a positive value: `m / 10 ^ k ≤ x < (m + 1) / 10 ^ k`. -/
theorem of_lowerCheck_decimal {p : Precision} {expr : Verified.Expr (Fin 0)} {m k : ℕ}
    (h : lowerCheck p expr ((m : ℚ) / 10 ^ k) (((m : ℚ) + 1) / 10 ^ k) = true)
    (ρ : Fin 0 → ℝ) :
    (m : ℝ) / 10 ^ k ≤ expr.eval ρ ∧ expr.eval ρ < ((m : ℝ) + 1) / 10 ^ k := by
  simpa using of_lowerCheck h ρ

/-- The digits of a negative value: `-(m + 1) / 10 ^ k < x ≤ -m / 10 ^ k`. -/
theorem of_upperCheck_decimal {p : Precision} {expr : Verified.Expr (Fin 0)} {m k : ℕ}
    (h : upperCheck p expr (-((m : ℚ) + 1) / 10 ^ k) (-(m : ℚ) / 10 ^ k) = true)
    (ρ : Fin 0 → ℝ) :
    -((m : ℝ) + 1) / 10 ^ k < expr.eval ρ ∧ expr.eval ρ ≤ -(m : ℝ) / 10 ^ k := by
  simpa using of_upperCheck h ρ

/-- The leading digits of a large positive value: `m 10 ^ k ≤ x < (m + 1) 10 ^ k`. -/
theorem of_lowerCheck_scaled {p : Precision} {expr : Verified.Expr (Fin 0)} {m k : ℕ}
    (h : lowerCheck p expr ((m : ℚ) * 10 ^ k) (((m : ℚ) + 1) * 10 ^ k) = true)
    (ρ : Fin 0 → ℝ) :
    (m : ℝ) * 10 ^ k ≤ expr.eval ρ ∧ expr.eval ρ < ((m : ℝ) + 1) * 10 ^ k := by
  simpa using of_lowerCheck h ρ

/-- The leading digits of a large negative value: `-(m + 1) 10 ^ k < x ≤ -m 10 ^ k`. -/
theorem of_upperCheck_scaled {p : Precision} {expr : Verified.Expr (Fin 0)} {m k : ℕ}
    (h : upperCheck p expr (-((m : ℚ) + 1) * 10 ^ k) (-(m : ℚ) * 10 ^ k) = true)
    (ρ : Fin 0 → ℝ) :
    -((m : ℝ) + 1) * 10 ^ k < expr.eval ρ ∧ expr.eval ρ ≤ -(m : ℝ) * 10 ^ k := by
  simpa using of_upperCheck h ρ

/-- A decimal enclosure: `lo / 10 ^ k ≤ x ≤ hi / 10 ^ k`. -/
theorem of_enclosureCheck_decimal {p : Precision} {expr : Verified.Expr (Fin 0)} {lo hi : ℤ}
    {k : ℕ} (h : enclosureCheck p expr ((lo : ℚ) / 10 ^ k) ((hi : ℚ) / 10 ^ k) = true)
    (ρ : Fin 0 → ℝ) :
    (lo : ℝ) / 10 ^ k ≤ expr.eval ρ ∧ expr.eval ρ ≤ (hi : ℝ) / 10 ^ k := by
  simpa using of_enclosureCheck h ρ

end DigitsEval
end CAS.Continuum
