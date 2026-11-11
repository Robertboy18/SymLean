/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Arithmetic
public import CAS.Domain.SideConditions
public import CAS.Polynomial.CoefficientEval
public import CAS.Polynomial.Sparse.UnivariateCalculus

/-!
# Certified interval reasoning for real polynomial roots

Certificate-producing real-root checks for the shared sparse rational polynomials.
The checker is executable:

* polynomial coefficients and test points are rational;
* interval evaluation uses `Continuum.RationalInterval`;
* accepted certificates are decided by exact rational comparisons.

The semantic theorems concern ordinary real functions. A root-free interval
produces a `NonzeroOn` theorem, while an isolating bracket is proved to contain
exactly one real root using Mathlib's polynomial calculus, monotonicity theorem,
and intermediate-value theorem.

Interval monotonicity isolates one root at a time on a given interval. Exact Sturm root counts
and global Cauchy-bound coverage are proved in the Sturm and Cauchy-bound modules.

## Implementation notes

A polynomial is enclosed over an interval in two ways. The termwise extension `evalInterval`
adds the interval values of the terms `cₖ xᵏ`. The centred extension `centredInterval` shifts
the polynomial exactly to the centre `m` of the interval (`coeffShift`), `p (m + t) = ∑ bₖ tᵏ`,
and bounds the terms over `|t| ≤ r` for the radius `r` (`centredGo`). It is a centred form, a
kind of enclosure that goes back to Moore [Ratschek and Rokne 1988, Section 2.7]. Its constant
and linear terms are bounded exactly, so on a narrow interval it exceeds the range of `p` by a
term of order `r ^ 2`, while the termwise one can exceed it by a multiple of `r` that grows with
the coefficients. The checks use `enclosure`, the centred interval when it excludes zero and the
termwise one otherwise, so every interval that the termwise test accepts is still accepted.

`rootFree` and `RootBracket` are used by the root-list search `RootIsolation.generate`, and
`RootBracket` also by the Legendre quadrature certificates in `CAS/Continuum/Quadrature/Legendre`.

## References

* Ramon E. Moore, *Interval Analysis*, Prentice-Hall, Englewood Cliffs, N.J., 1966,
  <https://zbmath.org/?q=an:0176.13301>. For interval arithmetic.
* Ramon E. Moore, R. Baker Kearfott and Michael J. Cloud, *Introduction to Interval Analysis*,
  SIAM, Philadelphia, 2009, <https://doi.org/10.1137/1.9780898717716>. Chapter 5 for interval
  extensions of real functions and Chapter 6 for centered forms.
* Helmut Ratschek and Jon Rokne, *Computer Methods for the Range of Functions*, Ellis Horwood,
  Chichester, 1984, <https://zbmath.org/?q=an:0584.65019>. For centered forms.
* Helmut Ratschek and Jon Rokne, *New Computer Methods for Global Optimization*, Ellis Horwood,
  Chichester, 1988, <https://pages.cpsc.ucalgary.ca/~rokne/global_book.pdf>. Section 2.7 on
  centered forms and their introduction by Moore.
-/

@[expose] public section

namespace CAS.Polynomial.Sparse

/-- The dense coefficient list of a sparse univariate polynomial, lowest degree first. -/
def coeffs : Univariate → List ℚ
  | [] => []
  | term :: rest => coeffAddAt (term.2 0) term.1 (coeffs rest)

/-- The dense coefficient list `coeffs p` of a sparse univariate polynomial evaluates at every real
`x` to `evalReal p x`. -/
theorem coeffEval_coeffs (p : Univariate) (x : ℝ) : coeffEval (coeffs p) x = evalReal p x := by
  induction p with
  | nil => simp [coeffs, evalReal]
  | cons term rest ih => simp [coeffs, coeffEval_coeffAddAt, evalReal, ih]

/-- `acc` plus the terms `lᵢ X^(k + i)` with `lᵢ ≠ 0`, prepended in increasing degree. -/
def ofCoeffsFrom : ℕ → List ℚ → Univariate → Univariate
  | _, [], acc => acc
  | k, a :: l, acc => ofCoeffsFrom (k + 1) l (if a = 0 then acc else (a, fun _ ↦ k) :: acc)

/-- The sparse polynomial of a dense coefficient list, highest degree first. -/
def ofCoeffs (l : List ℚ) : Univariate := ofCoeffsFrom 0 l []

/-- `ofCoeffsFrom k l acc` evaluates at every real `x` to the value of `acc` plus `x ^ k` times the
value of the coefficient list `l`. -/
theorem evalReal_ofCoeffsFrom : ∀ (k : ℕ) (l : List ℚ) (acc : Univariate) (x : ℝ),
    evalReal (ofCoeffsFrom k l acc) x = evalReal acc x + x ^ k * coeffEval l x
  | _, [], acc, x => by simp [ofCoeffsFrom]
  | k, a :: l, acc, x => by
    rw [ofCoeffsFrom, evalReal_ofCoeffsFrom]
    split_ifs with ha
    · simp only [ha, coeffEval_cons, Rat.cast_zero, pow_succ]
      ring
    · simp only [evalReal, coeffEval_cons, pow_succ]
      ring

/-- The sparse polynomial `ofCoeffs l` evaluates at every real `x` to the value of the dense list
`l`. -/
theorem evalReal_ofCoeffs (l : List ℚ) (x : ℝ) : evalReal (ofCoeffs l) x = coeffEval l x := by
  simp [ofCoeffs, evalReal_ofCoeffsFrom, evalReal]

end CAS.Polynomial.Sparse

namespace CAS.Polynomial.RealRoot

open Set
open CAS.Certificate
open CAS.Continuum
open CAS.Domain

/-- The interval contribution of one sparse polynomial term. -/
def termInterval (I : RationalInterval)
    (term : Rat × Verified.Expr.Alg.MvMonomial 1) : RationalInterval :=
  RationalInterval.mul (RationalInterval.const term.1)
    (RationalInterval.powNat I (term.2 (0 : Fin 1)))

/-- Exact rational interval extension of a sparse polynomial. -/
def evalInterval : Sparse.Univariate → RationalInterval → RationalInterval
  | [], _ => RationalInterval.const 0
  | term :: rest, I =>
      RationalInterval.add (termInterval I term) (evalInterval rest I)

private theorem termInterval_sound {I : RationalInterval} {x : ℝ}
    (hx : I.MemReal x)
    (term : Rat × Verified.Expr.Alg.MvMonomial 1) :
    (termInterval I term).MemReal
      ((term.1 : ℝ) * x ^ (term.2 (0 : Fin 1))) :=
  RationalInterval.mul_sound (RationalInterval.memReal_const term.1)
    (RationalInterval.powNat_sound hx (term.2 (0 : Fin 1)))

/-- Sparse interval evaluation encloses real polynomial evaluation. -/
theorem evalInterval_sound (polynomial : Sparse.Univariate) {I : RationalInterval} {x : ℝ}
    (hx : I.MemReal x) :
    (evalInterval polynomial I).MemReal
      (Sparse.evalReal polynomial x) := by
  induction polynomial with
  | nil =>
      simp [evalInterval, Sparse.evalReal, RationalInterval.MemReal]
  | cons term rest ih =>
      simpa [evalInterval, Sparse.evalReal] using
        RationalInterval.add_sound (termInterval_sound hx term) ih

/-- Whether an interval excludes zero by one strict endpoint sign. -/
def excludesZero (I : RationalInterval) : Bool :=
  decide (I.hi < 0) || decide (0 < I.lo)

/-- Excluding zero from an interval proves every enclosed value nonzero. -/
theorem ne_zero_of_excludesZero {I : RationalInterval} {x : ℝ}
    (hcheck : excludesZero I = true) (hx : I.MemReal x) :
    x ≠ 0 := by
  simp only [excludesZero, Bool.or_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with hnegative | hpositive
  · exact (hx.2.trans_lt (Rat.cast_lt_zero.mpr hnegative)).ne
  · exact ((Rat.cast_pos.mpr hpositive).trans_le hx.1).ne'

/-- Bounds of `∑ lᵢ t^(k+i)` over `|t| ≤ r`, term by term, given `rk = r ^ k`: an even power
of `t` lies in `[0, r^k]` and an odd one in `[-r^k, r^k]`. -/
def centredGo (r : ℚ) : ℕ → ℚ → List ℚ → ℚ × ℚ
  | _, _, [] => (0, 0)
  | k, rk, a :: l =>
      let rest := centredGo r (k + 1) (rk * r) l
      if k = 0 then (a + rest.1, a + rest.2)
      else if k % 2 = 0 then (min 0 (a * rk) + rest.1, max 0 (a * rk) + rest.2)
      else (rest.1 - |a| * rk, rest.2 + |a| * rk)

/-- For `|t| ≤ r` and `rk = r ^ k` (as reals), the pair `centredGo r k rk l` bounds
`t ^ k * coeffEval l t` from below and from above, for every coefficient list `l` and every `k`. -/
theorem centredGo_sound {r : ℚ} {t : ℝ} (ht : |t| ≤ r) :
    ∀ (l : List ℚ) (k : ℕ) (rk : ℚ), (rk : ℝ) = (r : ℝ) ^ k →
      ((centredGo r k rk l).1 : ℝ) ≤ t ^ k * coeffEval l t ∧
        t ^ k * coeffEval l t ≤ (centredGo r k rk l).2
  | [], k, rk, _ => by simp [centredGo]
  | a :: l, k, rk, hrk => by
      have ih := centredGo_sound ht l (k + 1) (rk * r) (by push_cast; rw [hrk, pow_succ])
      have hsplit : t ^ k * coeffEval (a :: l) t = a * t ^ k + t ^ (k + 1) * coeffEval l t := by
        simp only [coeffEval_cons]
        ring
      have htk : |t ^ k| ≤ (r : ℝ) ^ k := by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg t) ht k
      rw [hsplit]
      by_cases hk : k = 0
      · subst hk
        simp only [zero_add, pow_one] at ih
        simp only [centredGo, ↓reduceIte, pow_zero, mul_one, zero_add, pow_one]
        push_cast
        constructor <;> linarith [ih.1, ih.2]
      · by_cases he : k % 2 = 0
        · have h0 : 0 ≤ t ^ k := (Nat.even_iff.mpr he).pow_nonneg t
          have h1 : t ^ k ≤ (r : ℝ) ^ k := (le_abs_self _).trans htk
          simp only [centredGo, hk, he, ↓reduceIte]
          push_cast
          rw [hrk]
          constructor
          · rcases le_total 0 (a : ℝ) with ha | ha
            · have : min 0 ((a : ℝ) * r ^ k) ≤ 0 := min_le_left _ _
              nlinarith [ih.1, mul_nonneg ha h0]
            · have : min 0 ((a : ℝ) * r ^ k) ≤ a * r ^ k := min_le_right _ _
              nlinarith [ih.1, mul_le_mul_of_nonpos_left h1 ha]
          · rcases le_total 0 (a : ℝ) with ha | ha
            · have : (a : ℝ) * r ^ k ≤ max 0 ((a : ℝ) * r ^ k) := le_max_right _ _
              nlinarith [ih.2, mul_le_mul_of_nonneg_left h1 ha]
            · have : (0 : ℝ) ≤ max 0 ((a : ℝ) * r ^ k) := le_max_left _ _
              nlinarith [ih.2, mul_nonpos_of_nonpos_of_nonneg ha h0]
        · simp only [centredGo, hk, he, ↓reduceIte]
          push_cast
          rw [hrk]
          have habs : |(a : ℝ) * t ^ k| ≤ |(a : ℝ)| * r ^ k := by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left htk (abs_nonneg _)
          have := abs_le.mp habs
          constructor <;> linarith [ih.1, ih.2, this.1, this.2]

/-- The bounds of the Taylor shift of `p` to the centre of `I`, over the radius of `I`. -/
def centredBounds (p : Sparse.Univariate) (I : RationalInterval) : ℚ × ℚ :=
  centredGo ((I.hi - I.lo) / 2) 0 1 (coeffShift ((I.lo + I.hi) / 2) (Sparse.coeffs p))

/-- For every `x` in `I`, the pair `centredBounds p I` bounds `Sparse.evalReal p x` from below and
from above. -/
theorem centredBounds_sound (p : Sparse.Univariate) {I : RationalInterval} {x : ℝ}
    (hx : I.MemReal x) :
    ((centredBounds p I).1 : ℝ) ≤ Sparse.evalReal p x ∧
      Sparse.evalReal p x ≤ (centredBounds p I).2 := by
  have ht : |x - (((I.lo + I.hi) / 2 : ℚ) : ℝ)| ≤ (((I.hi - I.lo) / 2 : ℚ) : ℝ) := by
    obtain ⟨h1, h2⟩ := hx
    push_cast
    rw [abs_le]
    constructor <;> linarith
  have h := centredGo_sound ht (coeffShift ((I.lo + I.hi) / 2) (Sparse.coeffs p)) 0 1 (by simp)
  simp only [pow_zero, one_mul, coeffEval_coeffShift, add_sub_cancel,
    Sparse.coeffEval_coeffs] at h
  exact h

/-- The centred interval extension of `p` over `I`: the term bounds of the exact Taylor shift
of `p` to the centre of `I`. -/
def centredInterval (p : Sparse.Univariate) (I : RationalInterval) : RationalInterval :=
  RationalInterval.ofBounds (centredBounds p I).1 (centredBounds p I).2 (by
    have h := centredBounds_sound p (RationalInterval.lo_memReal I)
    exact_mod_cast h.1.trans h.2)

/-- Centred interval evaluation encloses real polynomial evaluation. -/
theorem centredInterval_sound (p : Sparse.Univariate) {I : RationalInterval} {x : ℝ}
    (hx : I.MemReal x) : (centredInterval p I).MemReal (Sparse.evalReal p x) :=
  centredBounds_sound p hx

/-- The enclosure of the root checks: the centred interval when it excludes zero, the termwise
one otherwise. -/
def enclosure (p : Sparse.Univariate) (I : RationalInterval) : RationalInterval :=
  let c := centredInterval p I
  if excludesZero c then c else evalInterval p I

/-- The enclosure contains every value of the polynomial on the interval. -/
theorem enclosure_sound (p : Sparse.Univariate) {I : RationalInterval} {x : ℝ}
    (hx : I.MemReal x) : (enclosure p I).MemReal (Sparse.evalReal p x) := by
  unfold enclosure
  dsimp only
  split
  · exact centredInterval_sound p hx
  · exact evalInterval_sound p hx

/-- A positive termwise enclosure gives a positive enclosure. -/
theorem enclosure_lo_pos_of_evalInterval (p : Sparse.Univariate) (I : RationalInterval)
    (h : 0 < (evalInterval p I).lo) : 0 < (enclosure p I).lo := by
  unfold enclosure
  dsimp only
  split
  · rename_i hc
    simp only [excludesZero, Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with hneg | hpos
    · have h1 := (centredInterval_sound p (RationalInterval.lo_memReal I)).2
      have h2 := (evalInterval_sound p (RationalInterval.lo_memReal I)).1
      have : (evalInterval p I).lo ≤ (centredInterval p I).hi := by exact_mod_cast h2.trans h1
      linarith
    · exact hpos
  · exact h

/-- A negative termwise enclosure gives a negative enclosure. -/
theorem enclosure_hi_neg_of_evalInterval (p : Sparse.Univariate) (I : RationalInterval)
    (h : (evalInterval p I).hi < 0) : (enclosure p I).hi < 0 := by
  unfold enclosure
  dsimp only
  split
  · rename_i hc
    simp only [excludesZero, Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with hneg | hpos
    · exact hneg
    · have h1 := (centredInterval_sound p (RationalInterval.lo_memReal I)).1
      have h2 := (evalInterval_sound p (RationalInterval.lo_memReal I)).2
      have : (centredInterval p I).lo ≤ (evalInterval p I).hi := by exact_mod_cast h1.trans h2
      linarith
  · exact h

/-- Exact checker for a root-free interval proposal. -/
def rootFree (polynomial : Sparse.Univariate) (interval : RationalInterval) : Bool :=
  excludesZero (enclosure polynomial interval)

/-- An accepted root-free interval gives an ordinary pointwise nonzero theorem. -/
theorem nonzeroOn_of_rootFree_eq_true
    (polynomial : Sparse.Univariate) (interval : RationalInterval)
    (hvalid : rootFree polynomial interval = true) :
    NonzeroOn (Sparse.evalReal polynomial)
      (Icc (interval.lo : ℝ) (interval.hi : ℝ)) :=
  fun _ hx ↦ ne_zero_of_excludesZero hvalid (enclosure_sound polynomial hx)

/-- Monotonicity orientation certified on a root bracket. -/
inductive Direction where
  | increasing
  | decreasing
deriving DecidableEq, Repr

/--
Proof-free data proposing an isolating interval for one polynomial root.

The checker verifies opposite weak endpoint signs and a strict derivative sign
throughout the interval.
-/
structure RootBracket where
  /-- Rational interval whose endpoints bracket the proposed root. -/
  interval : RationalInterval
  /-- Strict monotonicity orientation checked through the derivative enclosure. -/
  direction : Direction
deriving DecidableEq

namespace RootBracket

/-- Weak endpoint sign changes and a strict derivative sign certify one root.
Degenerate intervals are accepted when their endpoint is a root. -/
def Valid (polynomial : Sparse.Univariate) (bracket : RootBracket) : Prop :=
  match bracket.direction with
    | .increasing =>
          Sparse.evalRat polynomial bracket.interval.lo ≤ 0 ∧
          0 ≤ Sparse.evalRat polynomial bracket.interval.hi ∧
          0 < (enclosure
            (Sparse.derivativeRaw polynomial)
            bracket.interval).lo
    | .decreasing =>
        0 ≤ Sparse.evalRat polynomial bracket.interval.lo ∧
          Sparse.evalRat polynomial bracket.interval.hi ≤ 0 ∧
          (enclosure
            (Sparse.derivativeRaw polynomial)
            bracket.interval).hi < 0

/-- `Decidable` for `bracket.Valid polynomial`, by unfolding `Valid`, splitting on the direction of
the bracket and inferring the instance for the rational comparisons. -/
instance (polynomial : Sparse.Univariate) (bracket : RootBracket) :
    Decidable (bracket.Valid polynomial) := by
  unfold Valid
  cases bracket.direction <;> infer_instance

/-- Exact Boolean checker for a proposed root bracket. -/
def valid (polynomial : Sparse.Univariate) (bracket : RootBracket) : Bool :=
  decide (bracket.Valid polynomial)

/-- The executable checker accepts exactly the rational validity conditions. -/
theorem valid_eq_true_iff (polynomial : Sparse.Univariate) (bracket : RootBracket) :
    bracket.valid polynomial = true ↔ bracket.Valid polynomial := by
  simp [valid]

private theorem exists_root_increasing (polynomial : Sparse.Univariate)
    (bracket : RootBracket)
    (hlo : Sparse.evalRat polynomial bracket.interval.lo ≤ 0)
    (hhi : 0 ≤ Sparse.evalRat polynomial bracket.interval.hi) :
    ∃ x ∈ Icc (bracket.interval.lo : ℝ) (bracket.interval.hi : ℝ),
      Sparse.evalReal polynomial x = 0 :=
  intermediate_value_Icc (by exact_mod_cast bracket.interval.hle)
    (Sparse.continuous_evalReal polynomial).continuousOn
    ⟨by simpa [Sparse.evalReal_ratCast] using hlo, by simpa [Sparse.evalReal_ratCast] using hhi⟩

private theorem exists_root_decreasing (polynomial : Sparse.Univariate)
    (bracket : RootBracket)
    (hlo : 0 ≤ Sparse.evalRat polynomial bracket.interval.lo)
    (hhi : Sparse.evalRat polynomial bracket.interval.hi ≤ 0) :
    ∃ x ∈ Icc (bracket.interval.lo : ℝ) (bracket.interval.hi : ℝ),
      Sparse.evalReal polynomial x = 0 :=
  intermediate_value_Icc' (by exact_mod_cast bracket.interval.hle)
    (Sparse.continuous_evalReal polynomial).continuousOn
    ⟨by simpa [Sparse.evalReal_ratCast] using hhi, by simpa [Sparse.evalReal_ratCast] using hlo⟩

private theorem strictMonoOn_of_derivative_interval
    (polynomial : Sparse.Univariate) (bracket : RootBracket)
    (hderiv :
      0 < (enclosure
        (Sparse.derivativeRaw polynomial)
        bracket.interval).lo) :
    StrictMonoOn (Sparse.evalReal polynomial)
      (Icc (bracket.interval.lo : ℝ) (bracket.interval.hi : ℝ)) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (Sparse.continuous_evalReal polynomial).continuousOn fun x hx ↦ ?_
  have hxIcc : x ∈ Icc (bracket.interval.lo : ℝ) bracket.interval.hi := interior_subset hx
  rw [(Sparse.hasDerivAt_evalRealRaw polynomial x).deriv]
  exact (Rat.cast_pos.mpr hderiv).trans_le (enclosure_sound _ hxIcc).1

private theorem strictAntiOn_of_derivative_interval
    (polynomial : Sparse.Univariate) (bracket : RootBracket)
    (hderiv :
      (enclosure
        (Sparse.derivativeRaw polynomial)
        bracket.interval).hi < 0) :
    StrictAntiOn (Sparse.evalReal polynomial)
      (Icc (bracket.interval.lo : ℝ) (bracket.interval.hi : ℝ)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (Sparse.continuous_evalReal polynomial).continuousOn fun x hx ↦ ?_
  have hxIcc : x ∈ Icc (bracket.interval.lo : ℝ) bracket.interval.hi := interior_subset hx
  rw [(Sparse.hasDerivAt_evalRealRaw polynomial x).deriv]
  exact (enclosure_sound _ hxIcc).2.trans_lt (Rat.cast_lt_zero.mpr hderiv)

/-- An accepted bracket contains exactly one real root of the polynomial. -/
theorem existsUnique_root (polynomial : Sparse.Univariate) (bracket : RootBracket)
    (hvalid : bracket.valid polynomial = true) :
    ∃! x : ℝ,
      x ∈ Icc (bracket.interval.lo : ℝ) (bracket.interval.hi : ℝ) ∧
        Sparse.evalReal polynomial x = 0 := by
  have hconditions := (valid_eq_true_iff polynomial bracket).mp hvalid
  cases hdir : bracket.direction with
  | increasing =>
      simp only [Valid, hdir] at hconditions
      obtain ⟨hlo, hhi, hderiv⟩ := hconditions
      obtain ⟨root, hrootMem, hrootZero⟩ := exists_root_increasing polynomial bracket hlo hhi
      exact ⟨root, ⟨hrootMem, hrootZero⟩, fun y hy ↦
        (strictMonoOn_of_derivative_interval polynomial bracket hderiv).injOn hy.1 hrootMem
          (hy.2.trans hrootZero.symm)⟩
  | decreasing =>
      simp only [Valid, hdir] at hconditions
      obtain ⟨hlo, hhi, hderiv⟩ := hconditions
      obtain ⟨root, hrootMem, hrootZero⟩ := exists_root_decreasing polynomial bracket hlo hhi
      exact ⟨root, ⟨hrootMem, hrootZero⟩, fun y hy ↦
        (strictAntiOn_of_derivative_interval polynomial bracket hderiv).injOn hy.1 hrootMem
          (hy.2.trans hrootZero.symm)⟩

end RootBracket

end CAS.Polynomial.RealRoot
