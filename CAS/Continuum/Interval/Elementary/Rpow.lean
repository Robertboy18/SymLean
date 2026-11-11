/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Elementary.Exp
public import CAS.Continuum.Interval.Elementary.Log
public import CAS.Continuum.Interval.Elementary.Sqrt
public import CAS.Continuum.Interval.Rational.Arithmetic

/-!
# Rational powers of nonnegative intervals

`rpowPoint a q p` encloses `a ^ q` (Mathlib's `Real.rpow`) for a nonnegative rational `a` and a
rational exponent `q`. When the reduced denominator of `q` is a power of two, `2 ^ m`, the
exponent is written `q = n + r / 2 ^ m` with `n = ⌊q⌋` and `0 ≤ r < 2 ^ m`, and the power is
`a ^ n` exactly times the `r`-th power of `m` iterated square roots of `a` (`dyadicPowPoint`);
the integer exponents are the case `m = 0`. Every other exponent goes through
`exp (q log a)` (`expLogPowPoint`). At `a = 0` the enclosure is Mathlib's value `0 ^ q`, which is
`1` for `q = 0` and `0` otherwise.

`rpowRat I q p` encloses `x ^ q` for every `x ∈ I` from the two endpoint enclosures, using the
monotonicity of `x ↦ x ^ q` on the nonnegative half-line; it requires `0 ≤ I.lo` for `q ≥ 0` and
`0 < I.lo` for `q < 0` (`rpowRat_sound`). Mathlib's `x ^ q` of a negative `x` is not `|x| ^ q`.

The precision is set by `PowerPrecision`: the logarithm series terms, the exponential Taylor
order and the square-root refinement steps.

## Main definitions

* `PowerPrecision`: the precision parameters of the power enclosures.
* `dyadicPowPoint`: the enclosure of `a ^ (n + r / 2 ^ m)` for a positive rational `a`.
* `expLogPowPoint`: the enclosure `exp (q log a)` of `a ^ q` for a positive rational `a`.
* `rpowPoint`: the enclosure of Mathlib's `a ^ q` for a rational `a ≥ 0`.
* `rpowRat`: the enclosure of `x ^ q` on `I`, the singleton `{0}` outside the domain
  `PowDomain I q`.

## Main results

* `sqrtIter_sound`: `sqrtIter I steps m` contains `x ^ (1 / 2 ^ m)` for every nonnegative `x ∈ I`.
* `dyadicPowPoint_sound`: `dyadicPowPoint a n r m steps` contains `a ^ (n + r / 2 ^ m)` for `a > 0`.
* `expLogPowPoint_sound`: `expLogPowPoint a q terms order ha` contains `a ^ q`.
* `rpowPoint_sound`: `rpowPoint a q p` contains `a ^ q` for every rational `a ≥ 0`.
* `rpowRat_sound`: `rpowRat I q p` contains `x ^ q` for every `x ∈ I` on the domain `PowDomain I q`.

## Implementation notes

We compose the enclosures of `Exp`, `Log` and `Sqrt` with exact rational powers, so FloatLib
enters only through them. The dyadic route needs no series: when the `2 ^ m`-th root of `a` is
rational, every square root on the way is exact and so is the power, while `exp (q log a)`
always carries the errors of both series. The identities behind the two routes,
`a ^ (n + r / 2 ^ m) = (a ^ (1 / 2 ^ m)) ^ r * a ^ n` and `a ^ q = exp (q log a)`, and the
monotonicity used by `rpowRat` come from Mathlib (`Real.rpow_add`, `Real.rpow_def_of_pos`,
`Real.rpow_le_rpow`, `Real.rpow_le_rpow_of_nonpos`).
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

/-- Precision parameters of the power enclosures: logarithm series terms, exponential Taylor
order and square-root refinement steps. -/
structure PowerPrecision where
  /-- Terms of the logarithm series, as in `logPointIntervalWith`. -/
  terms : ℕ
  /-- Taylor order of the exponential, as in `expRangeWith`. -/
  order : ℕ
  /-- Refinement steps of the square root, as in `sqrtRangeInterval`. -/
  steps : ℕ

/-! ### Iterated square roots -/

/-- `m` square roots of `I`, each by `sqrtRangeInterval` with `steps` refinement steps. -/
def sqrtIter (I : RationalInterval) (steps : ℕ) (m : ℕ) : RationalInterval :=
  Nat.rec (motive := fun _ ↦ RationalInterval) I (fun _ J ↦ sqrtRangeInterval J steps) m

/-- `sqrtIter I steps m` contains `x ^ (1 / 2 ^ m)` for every nonnegative `x ∈ I`. -/
theorem sqrtIter_sound {I : RationalInterval} (steps : ℕ) {x : ℝ} (hx : I.MemReal x)
    (hx0 : 0 ≤ x) (m : ℕ) :
    (sqrtIter I steps m).MemReal (x ^ ((1 : ℝ) / 2 ^ m)) := by
  induction m with
  | zero => simpa [sqrtIter] using hx
  | succ m ih =>
    have heq : √(x ^ ((1 : ℝ) / 2 ^ m)) = x ^ ((1 : ℝ) / 2 ^ (m + 1)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0]
      ring_nf
    exact heq ▸ sqrtRangeInterval_sound _ steps ih

/-! ### Point enclosures -/

/-- The enclosure of `a ^ (n + r / 2 ^ m)` for a positive rational `a`: the `r`-th power of `m`
square roots of `a`, times the exact rational `a ^ n`. -/
def dyadicPowPoint (a : ℚ) (n : ℤ) (r m steps : ℕ) : RationalInterval :=
  ((sqrtIter (const a) steps m).powNat r).mul (const (a ^ n))

/-- `dyadicPowPoint a n r m steps` contains `a ^ (n + r / 2 ^ m)` for `a > 0`. -/
theorem dyadicPowPoint_sound {a : ℚ} (ha : 0 < a) (n : ℤ) (r m steps : ℕ) :
    (dyadicPowPoint a n r m steps).MemReal ((a : ℝ) ^ (((n + r / 2 ^ m : ℚ)) : ℝ)) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have heq : ((a : ℝ) ^ ((1 : ℝ) / 2 ^ m)) ^ r * ((a ^ n : ℚ) : ℝ) =
      (a : ℝ) ^ (((n + r / 2 ^ m : ℚ)) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul haR.le, Rat.cast_zpow, ← Real.rpow_intCast,
      ← Real.rpow_add haR]
    push_cast
    ring_nf
  exact heq ▸ mul_sound (powNat_sound (sqrtIter_sound steps (memReal_const a) haR.le m) r)
    (memReal_const (a ^ n))

/-- The enclosure `exp (q log a)` of `a ^ q` for a positive rational `a`. -/
def expLogPowPoint (a q : ℚ) (terms order : ℕ) (ha : 0 < a) : RationalInterval :=
  expRangeWith ((logPointIntervalWith terms a ha).mul (const q)) order

/-- `expLogPowPoint a q terms order ha` contains `a ^ q`. -/
theorem expLogPowPoint_sound {a : ℚ} (q : ℚ) (terms order : ℕ) (ha : 0 < a) :
    (expLogPowPoint a q terms order ha).MemReal ((a : ℝ) ^ (q : ℝ)) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  rw [Real.rpow_def_of_pos haR]
  exact expRangeWith_sound _ order
    (mul_sound (logPointIntervalWith_sound terms a ha) (memReal_const q))

/-- The binary logarithm of the denominator of `q`. -/
def dyadicLevel (q : ℚ) : ℕ := Nat.log2 q.den

/-- The denominator of `q` is a power of two. -/
def IsDyadicExponent (q : ℚ) : Prop := 2 ^ dyadicLevel q = q.den

/-- Whether the denominator of `q` is a power of two is decided by comparing `2 ^ dyadicLevel q`
with `q.den`. -/
instance (q : ℚ) : Decidable (IsDyadicExponent q) :=
  inferInstanceAs (Decidable (2 ^ dyadicLevel q = q.den))

/-- A rational with denominator `2 ^ m` is `⌊q⌋ + r / 2 ^ m` with `r = q.num mod q.den`. -/
theorem eq_floor_add_of_isDyadicExponent {q : ℚ} (hq : IsDyadicExponent q) :
    (((q.num / q.den : ℤ) + ((q.num % q.den).toNat : ℚ) / 2 ^ dyadicLevel q : ℚ)) = q := by
  have hden : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
  have hcast : (((q.num % q.den).toNat : ℕ) : ℚ) = ((q.num % q.den : ℤ) : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Int.emod_nonneg _ hden)
  have h2 : ((2 : ℚ) ^ dyadicLevel q) = q.den := by exact_mod_cast hq
  rw [hcast, h2]
  conv_rhs => rw [← Rat.num_div_den q, ← Int.mul_ediv_add_emod q.num q.den]
  push_cast
  field_simp

/-- The enclosure of Mathlib's `a ^ q` for a rational `a ≥ 0`: Mathlib's value at `a = 0`, the
dyadic route when the denominator of `q` is a power of two, `exp (q log a)` otherwise. -/
def rpowPoint (a q : ℚ) (p : PowerPrecision) : RationalInterval :=
  if a = 0 then const (if q = 0 then 1 else 0)
  else if ha : 0 < a then
    if IsDyadicExponent q then
      dyadicPowPoint a (q.num / q.den) (q.num % q.den).toNat (dyadicLevel q) p.steps
    else expLogPowPoint a q p.terms p.order ha
  else const 0

/-- `rpowPoint a q p` contains `a ^ q` for every rational `a ≥ 0`. -/
theorem rpowPoint_sound {a : ℚ} (ha : 0 ≤ a) (q : ℚ) (p : PowerPrecision) :
    (rpowPoint a q p).MemReal ((a : ℝ) ^ (q : ℝ)) := by
  unfold rpowPoint
  split_ifs with h0 hq hpos hd
  · simpa [h0, hq] using memReal_const 1
  · simpa [h0, Real.zero_rpow (Rat.cast_ne_zero.mpr hq)] using memReal_const 0
  · simpa only [eq_floor_add_of_isDyadicExponent hd] using
      dyadicPowPoint_sound hpos (q.num / q.den) (q.num % q.den).toNat (dyadicLevel q) p.steps
  · exact expLogPowPoint_sound q p.terms p.order hpos
  · exact absurd (ha.lt_of_ne (Ne.symm h0)) hpos

/-! ### Intervals -/

/-- The sign condition of `rpowRat`: `0 ≤ I.lo` for `q ≥ 0`, `0 < I.lo` for `q < 0`. -/
def PowDomain (I : RationalInterval) (q : ℚ) : Prop := (0 ≤ q ∧ 0 ≤ I.lo) ∨ 0 < I.lo

/-- The sign condition `PowDomain I q` is decidable. -/
instance (I : RationalInterval) (q : ℚ) : Decidable (PowDomain I q) :=
  inferInstanceAs (Decidable ((0 ≤ q ∧ 0 ≤ I.lo) ∨ 0 < I.lo))

/-- On the domain `PowDomain I q` the left end of `I` is nonnegative. -/
theorem PowDomain.lo_nonneg {I : RationalInterval} {q : ℚ} (h : PowDomain I q) : 0 ≤ I.lo :=
  h.elim And.right le_of_lt

/-- On the domain, `x ↦ x ^ q` maps `I` into the interval between the powers of its endpoints. -/
theorem rpow_mem_of_powDomain {I : RationalInterval} {q : ℚ} (h : PowDomain I q) {x : ℝ}
    (hx : I.MemReal x) :
    (0 ≤ q → (I.lo : ℝ) ^ (q : ℝ) ≤ x ^ (q : ℝ) ∧ x ^ (q : ℝ) ≤ (I.hi : ℝ) ^ (q : ℝ)) ∧
      (q < 0 → (I.hi : ℝ) ^ (q : ℝ) ≤ x ^ (q : ℝ) ∧ x ^ (q : ℝ) ≤ (I.lo : ℝ) ^ (q : ℝ)) := by
  have hlo : (0 : ℝ) ≤ I.lo := by exact_mod_cast h.lo_nonneg
  refine ⟨fun hq ↦ ?_, fun hq ↦ ?_⟩
  · have hqR : (0 : ℝ) ≤ q := by exact_mod_cast hq
    exact ⟨Real.rpow_le_rpow hlo hx.1 hqR, Real.rpow_le_rpow (hlo.trans hx.1) hx.2 hqR⟩
  · have hposR : (0 : ℝ) < I.lo := by exact_mod_cast h.resolve_left fun h' ↦ not_le.mpr hq h'.1
    have hqR : (q : ℝ) ≤ 0 := by exact_mod_cast hq.le
    exact ⟨Real.rpow_le_rpow_of_nonpos (hposR.trans_le hx.1) hx.2 hqR,
      Real.rpow_le_rpow_of_nonpos hposR hx.1 hqR⟩

/-- The endpoints of `rpowRat` on its domain, in the order given by the sign of `q`. -/
def rpowEnds (I : RationalInterval) (q : ℚ) (p : PowerPrecision) : ℚ × ℚ :=
  if 0 ≤ q then ((rpowPoint I.lo q p).lo, (rpowPoint I.hi q p).hi)
  else ((rpowPoint I.hi q p).lo, (rpowPoint I.lo q p).hi)

/-- On the domain `PowDomain I q`, the two components of `rpowEnds I q p` bound `x ^ q` below and
above for every `x ∈ I`. -/
theorem rpowEnds_sound {I : RationalInterval} {q : ℚ} (h : PowDomain I q) (p : PowerPrecision)
    {x : ℝ} (hx : I.MemReal x) :
    ((rpowEnds I q p).1 : ℝ) ≤ x ^ (q : ℝ) ∧ x ^ (q : ℝ) ≤ ((rpowEnds I q p).2 : ℝ) := by
  have hl := rpowPoint_sound h.lo_nonneg q p
  have hh := rpowPoint_sound (h.lo_nonneg.trans I.hle) q p
  obtain ⟨hpos, hneg⟩ := rpow_mem_of_powDomain h hx
  unfold rpowEnds
  split_ifs with hq
  · exact ⟨hl.1.trans (hpos hq).1, (hpos hq).2.trans hh.2⟩
  · exact ⟨hh.1.trans (hneg (not_le.mp hq)).1, (hneg (not_le.mp hq)).2.trans hl.2⟩

/-- The enclosure of `x ^ q` on `I` from the endpoint enclosures; the singleton `{0}` outside
the domain `PowDomain I q`. -/
def rpowRat (I : RationalInterval) (q : ℚ) (p : PowerPrecision) : RationalInterval :=
  if h : PowDomain I q then
    ofBounds (rpowEnds I q p).1 (rpowEnds I q p).2 (by
      have hs := rpowEnds_sound h p I.lo_memReal
      exact_mod_cast hs.1.trans hs.2)
  else const 0

/-- `rpowRat I q p` contains `x ^ q` for every `x ∈ I` on the domain `PowDomain I q`. -/
theorem rpowRat_sound {I : RationalInterval} {q : ℚ} (h : PowDomain I q) (p : PowerPrecision)
    {x : ℝ} (hx : I.MemReal x) : (rpowRat I q p).MemReal (x ^ (q : ℝ)) := by
  simp only [rpowRat, h, ↓reduceDIte]
  exact rpowEnds_sound h p hx

/-- On the domain `PowDomain I q`, the left end of `rpowRat I q p` is the first component of
`rpowEnds I q p`. -/
theorem rpowRat_lo {I : RationalInterval} {q : ℚ} (h : PowDomain I q) (p : PowerPrecision) :
    (rpowRat I q p).lo = (rpowEnds I q p).1 := by
  simp only [rpowRat, h, ↓reduceDIte]; rfl

/-- On the domain `PowDomain I q`, the right end of `rpowRat I q p` is the second component of
`rpowEnds I q p`. -/
theorem rpowRat_hi {I : RationalInterval} {q : ℚ} (h : PowDomain I q) (p : PowerPrecision) :
    (rpowRat I q p).hi = (rpowEnds I q p).2 := by
  simp only [rpowRat, h, ↓reduceDIte]; rfl

end RationalInterval
end CAS.Continuum
