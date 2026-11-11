/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.Polynomial
public import Mathlib.Algebra.Order.Ring.Abs

/-!
# Exact certificates for signed polynomial products

An integer polynomial whose coefficients are smaller in absolute value than `b > 0` vanishes at
`b` only if it is zero (`intPolynomial_eq_zero_of_eval_eq_zero`): its constant term is divisible
by `b` and therefore zero, and division by `X` repeats the argument. One exact integer
multiplication thus certifies a proposed product of two signed coefficient tables
(`signedProductCheck_sound`), with no floating-point transform. `rationalPolynomial` divides
every coefficient by a supplied denominator, and exact products of rational tables use the
product of the input denominators (`rationalPolynomial_mul_eq`). These decoding identities also
hold for a zero denominator.

## Main results

* `intPolynomial_eq_of_eval_eq`: integer polynomials whose coefficients differ by less than `b`
  in absolute value are equal when they agree at `b`.
* `signedPolynomial_mul_eq_of_packed`: when the masses satisfy
  `signedMass a * signedMass b + signedMass c < 2 ^ bits`, one equation between the packed values
  `packSignedBinary bits` identifies `signedPolynomial a * signedPolynomial b` with
  `signedPolynomial c`.
* `signedProductCheck_sound`: the same statement for the Boolean check `signedProductCheck`.

## Implementation notes

The packing is the Kronecker substitution in the form Harvey describes: at `2 ^ bits`, with
`bits` large enough that the coefficients of the product do not overlap, a polynomial product
becomes one integer product. We use it to check a product, not to compute one. The product `c`
is proposed from outside, and the kernel checks only the mass inequality and one product of the
packed values, which `packSignedBinary` computes by balanced shifts over the trees; nothing is
unpacked. Harvey treats the integer case for nonnegative coefficients (Section 3 of the
preprint). For a check the signs cost nothing, since `intPolynomial_eq_of_eval_eq` needs only
that every coefficient of `a b - c` is below `2 ^ bits` in absolute value, and the mass
inequality gives this through `abs_signedPolynomial_mul_coeff_le`. A signed coefficient `v` is
stored in a natural-number leaf of a `CoefficientTree` as the zigzag code `2 |v| + s`, with
`s = 1` exactly when `v < 0` (`encodeSignedCoefficient`, decoded by `signedCoefficient`). For
tables read from packed blocks, `ZigzagBlocks` derives `signedProductCheck` from one
natural-number identity. The substitution is classical; the check and its proof are ours.

## References

* David Harvey, "Faster polynomial multiplication via multipoint Kronecker substitution",
  *Journal of Symbolic Computation* 44 (2009), pp. 1502-1510,
  <https://doi.org/10.1016/j.jsc.2009.05.004>. Section 1 of the preprint explains the
  substitution from `ℤ[x]` to `ℤ` and its origin with Kronecker and Schönhage.
-/

@[expose] public section

open Polynomial

namespace CAS.Numerics

/-- A small integer polynomial cannot vanish at the packing base unless it is zero. -/
theorem intPolynomial_eq_zero_of_eval_eq_zero {b : ℤ} (hb : 0 < b) (p : ℤ[X])
    (hbound : ∀ k, |p.coeff k| < b) (heval : p.eval b = 0) : p = 0 := by
  have constant_zero (q : ℤ[X]) (hsmall : |q.coeff 0| < b) (hzero : q.eval b = 0) :
      q.coeff 0 = 0 := by
    have hsplit := congrArg (Polynomial.eval b) q.X_mul_divX_add
    simp only [eval_add, eval_mul, eval_X, eval_C, hzero] at hsplit
    have hdvd : b ∣ q.coeff 0 := ⟨-q.divX.eval b, by linarith⟩
    exact Int.eq_zero_of_abs_lt_dvd hdvd hsmall
  have coeff_zero (k : ℕ) : ∀ q : ℤ[X],
      (∀ j, |q.coeff j| < b) → q.eval b = 0 → q.coeff k = 0 := by
    induction k with
    | zero => exact fun q hsmall hzero ↦ constant_zero q (hsmall 0) hzero
    | succ k ih =>
      intro q hsmall hzero
      have hc := constant_zero q (hsmall 0) hzero
      have hsplit := congrArg (Polynomial.eval b) q.X_mul_divX_add
      simp only [eval_add, eval_mul, eval_X, eval_C, hzero, hc, add_zero] at hsplit
      have hd : q.divX.eval b = 0 := (mul_eq_zero.mp hsplit).resolve_left hb.ne'
      simpa only [coeff_divX] using
        ih q.divX (fun j ↦ by simpa only [coeff_divX] using hsmall (j + 1)) hd
  ext k
  simpa only [Polynomial.coeff_zero] using coeff_zero k p hbound heval

/-- Equal packed values identify signed polynomials when their coefficient differences fit. -/
theorem intPolynomial_eq_of_eval_eq {b : ℤ} (hb : 0 < b) (p q : ℤ[X])
    (hbound : ∀ k, |p.coeff k - q.coeff k| < b) (heval : p.eval b = q.eval b) :
    p = q := by
  refine sub_eq_zero.mp (intPolynomial_eq_zero_of_eval_eq_zero hb _ (by simpa only [coeff_sub]) ?_)
  simpa only [eval_sub, sub_eq_zero] using heval

/-- Decode a signed magnitude stored in one natural number; padding decodes to zero. -/
def signedCoefficient (value : ℕ) : ℤ :=
  if value % 2 = 0 then (value / 2 : ℕ) else -((value / 2 : ℕ) : ℤ)

/-- Store a signed coefficient in the balanced natural-number representation. -/
def encodeSignedCoefficient (value : ℤ) : ℕ :=
  2 * value.natAbs + if value < 0 then 1 else 0

/-- Signed encoding preserves every integer, including zero. -/
@[simp]
theorem signedCoefficient_encode (value : ℤ) :
    signedCoefficient (encodeSignedCoefficient value) = value := by
  cases value with
  | ofNat n =>
    have h : ¬(n : ℤ) < 0 := not_lt.mpr (Int.natCast_nonneg n)
    simp [signedCoefficient, encodeSignedCoefficient, h]
  | negSucc n =>
    simp only [encodeSignedCoefficient, Int.natAbs_negSucc, Int.negSucc_lt_zero, ↓reduceIte]
    simpa [signedCoefficient, Nat.add_mod, Nat.add_div] using
      (show (-1 : ℤ) + -(n : ℤ) = Int.negSucc n by rw [Int.negSucc_eq]; ring)

/-- Interpret the existing balanced coefficient tree with signed coefficients. -/
noncomputable def signedPolynomial {depth : ℕ} : CoefficientTree depth → ℤ[X]
  | .leaf value => C (signedCoefficient value)
  | @CoefficientTree.branch depth left right =>
    signedPolynomial left + X ^ (2 ^ depth) * signedPolynomial right

/-- The signed polynomial has the stored coefficients and vanishes past the tree's length. -/
theorem signedPolynomial_coeff {depth : ℕ} (a : CoefficientTree depth) (i : ℕ) :
    (signedPolynomial a).coeff i =
      if i < 2 ^ depth then signedCoefficient (a.lookup i) else 0 := by
  induction a generalizing i with
  | leaf value =>
    simp only [signedPolynomial, coeff_C, CoefficientTree.lookup, pow_zero]
    split_ifs <;> omega
  | @branch depth left right ihl ihr =>
    rw [signedPolynomial, coeff_add, coeff_X_pow_mul', ihl, ihr]
    simp only [CoefficientTree.lookup, pow_succ, Nat.mul_two]
    split_ifs <;> simp_all <;> omega

/-- Compute its signed packed value by balanced shifts. -/
def packSignedBinary (bits : ℕ) {depth : ℕ} : CoefficientTree depth → ℤ
  | .leaf value => signedCoefficient value
  | @CoefficientTree.branch depth left right =>
    packSignedBinary bits left + (packSignedBinary bits right <<< (bits * 2 ^ depth))

/-- The executable signed packing is exactly polynomial evaluation. -/
theorem packSignedBinary_eq_eval (bits : ℕ) {depth : ℕ} (a : CoefficientTree depth) :
    packSignedBinary bits a = (signedPolynomial a).eval ((2 : ℤ) ^ bits) := by
  induction a with
  | leaf value => simp only [packSignedBinary, signedPolynomial, eval_C]
  | branch left right ihl ihr =>
    simp only [packSignedBinary, signedPolynomial, eval_add, eval_mul, eval_pow, eval_X,
      Int.shiftLeft_eq, ihl, ihr, pow_mul]
    ring

/-- Total absolute coefficient mass, evaluated without constructing a polynomial. -/
def signedMass {depth : ℕ} : CoefficientTree depth → ℤ
  | .leaf value => |signedCoefficient value|
  | .branch left right => signedMass left + signedMass right

/-- Every signed mass is nonnegative. -/
theorem signedMass_nonneg {depth : ℕ} (a : CoefficientTree depth) : 0 ≤ signedMass a := by
  induction a with
  | leaf value => exact abs_nonneg _
  | branch left right ihl ihr => exact add_nonneg ihl ihr

/-- A tree's absolute mass bounds every coefficient after multiplication. -/
theorem abs_signedPolynomial_mul_coeff_le {depth : ℕ} (a : CoefficientTree depth)
    (q : ℤ[X]) {B : ℤ} (hB : 0 ≤ B) (hq : ∀ k, |q.coeff k| ≤ B) (k : ℕ) :
    |(signedPolynomial a * q).coeff k| ≤ signedMass a * B := by
  induction a generalizing k with
  | leaf value =>
    simpa only [signedPolynomial, signedMass, coeff_C_mul, abs_mul] using
      mul_le_mul_of_nonneg_left (hq k) (abs_nonneg (signedCoefficient value))
  | @branch depth left right ihl ihr =>
    rw [signedPolynomial, add_mul, mul_assoc, coeff_add, coeff_X_pow_mul']
    refine (abs_add_le _ _).trans ?_
    change _ ≤ (signedMass left + signedMass right) * B
    rw [add_mul]
    apply add_le_add (ihl k)
    split
    · exact ihr _
    · simpa only [abs_zero] using mul_nonneg (signedMass_nonneg right) hB

/-- In particular, every signed coefficient is at most the tree's absolute mass. -/
theorem abs_signedPolynomial_coeff_le {depth : ℕ} (a : CoefficientTree depth) (k : ℕ) :
    |(signedPolynomial a).coeff k| ≤ signedMass a := by
  have h : ∀ j, |(1 : ℤ[X]).coeff j| ≤ (1 : ℤ) := by
    intro j
    rw [coeff_one]
    split <;> norm_num
  simpa only [mul_one] using
    abs_signedPolynomial_mul_coeff_le a 1 zero_le_one h k

/-- One exact packed product identifies all signed convolution coefficients at once. -/
theorem signedPolynomial_mul_eq_of_packed {n m l bits : ℕ}
    (a : CoefficientTree n) (b : CoefficientTree m) (c : CoefficientTree l)
    (hmass : signedMass a * signedMass b + signedMass c < (2 : ℤ) ^ bits)
    (hpacked : packSignedBinary bits a * packSignedBinary bits b = packSignedBinary bits c) :
    signedPolynomial a * signedPolynomial b = signedPolynomial c := by
  refine intPolynomial_eq_of_eval_eq (b := (2 : ℤ) ^ bits) (by positivity) _ _ (fun k ↦
    (abs_sub _ _).trans_lt ((add_le_add
      (abs_signedPolynomial_mul_coeff_le a (signedPolynomial b) (signedMass_nonneg b)
        (abs_signedPolynomial_coeff_le b) k)
      (abs_signedPolynomial_coeff_le c k)).trans_lt hmass)) ?_
  simpa only [eval_mul, ← packSignedBinary_eq_eval] using hpacked

/-- Check the digit-mass margin and exact packed multiplication together. -/
def signedProductCheck {n m l : ℕ} (bits : ℕ)
    (a : CoefficientTree n) (b : CoefficientTree m) (c : CoefficientTree l) : Bool :=
  decide (signedMass a * signedMass b + signedMass c < (2 : ℤ) ^ bits) &&
    decide (packSignedBinary bits a * packSignedBinary bits b = packSignedBinary bits c)

/-- A successful integer replay establishes the complete polynomial identity. -/
theorem signedProductCheck_sound {n m l : ℕ} (bits : ℕ)
    (a : CoefficientTree n) (b : CoefficientTree m) (c : CoefficientTree l)
    (h : signedProductCheck bits a b c = true) :
    signedPolynomial a * signedPolynomial b = signedPolynomial c := by
  simp only [signedProductCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact signedPolynomial_mul_eq_of_packed a b c h.1 h.2

/-- Decode a signed table on its common rational grid. -/
noncomputable def rationalPolynomial (denominator : ℕ) {depth : ℕ}
    (a : CoefficientTree depth) : ℚ[X] :=
  C (1 / (denominator : ℚ)) * (signedPolynomial a).map (Int.castRingHom ℚ)

/-- Each rational coefficient is the signed stored integer divided by its denominator. -/
theorem rationalPolynomial_coeff (denominator : ℕ) {depth : ℕ}
    (a : CoefficientTree depth) (i : ℕ) :
    (rationalPolynomial denominator a).coeff i =
      if i < 2 ^ depth then (signedCoefficient (a.lookup i) : ℚ) / denominator else 0 := by
  rw [rationalPolynomial, coeff_C_mul, coeff_map, signedPolynomial_coeff]
  split_ifs <;> simp [div_eq_mul_inv, mul_comm]

/-- Dividing an exact integer convolution by both input denominators preserves the product. -/
theorem rationalPolynomial_mul_eq {n m l : ℕ} (a : CoefficientTree n)
    (b : CoefficientTree m) (c : CoefficientTree l) (d e : ℕ)
    (h : signedPolynomial a * signedPolynomial b = signedPolynomial c) :
    rationalPolynomial d a * rationalPolynomial e b = rationalPolynomial (d * e) c := by
  simp only [rationalPolynomial, ← h, Polynomial.map_mul, Nat.cast_mul, one_div, mul_inv, C_mul]
  ring

end CAS.Numerics
