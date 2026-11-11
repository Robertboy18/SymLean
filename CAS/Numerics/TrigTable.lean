/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.TrigFixedPoint
public import CAS.Numerics.IntegerRounding

/-!
# Sine and cosine tables at rational multiples of π

`trigTable N p k` is a pair of integers within `1` of `2 ^ p cos (k π / (2 N))` and
`2 ^ p sin (k π / (2 N))`, for `k = 0, …, 4 N`. These are the values of the trigonometric
basis on the uniform grid of spacing `π / (2 N)`: for an integer frequency `n` and a node
`j π / (2 N)` the phase is the table index `n j` reduced modulo `4 N`. `trigPi N p k` accepts
every natural index and reduces it modulo `4 N` itself.

## Main results

* `trigPi_sound`: the bound for every natural index.
* `trigTable_sound`: the bound for the table indices `Fin (4 N + 1)`.

## Implementation notes

We compute each entry independently, so the bound `1` holds at every index for every `N` and
`p`. The rounded rotation powers of `TrigRotation` and `RotationIteration` are faster, but their
error grows linearly with the index. The index is reduced by exact symmetries: a full turn, a
quarter turn `q` (`trigQuarterTurn`) and, when the remainder `r` has `2 r > N`, the
complementary angle (`TrigApprox.swap`). The remaining angle `m π / (2 N)`, with `m = r` or
`m = N - r` and `2 m ≤ N` (`trigPiOctant`), lies in `[0, π / 4]`, below `1`, which is the
hypothesis `X ≤ 2 ^ w` of the Taylor bounds of `TrigFixedPoint`; at the degree
`trigDegree w` the Taylor remainder is at most one unit.

The working precision is `w = p + trigGuard p` bits. The argument `X`, the floor of
`m P / (2 N)` with `P = (piFixed w).toNat` and `2 m ≤ N`, clamped at `2 ^ w`, carries at most
`1 + (5 w + 41) / 4` units of `2 ^ (-w)`. Cosine and sine are `1`-Lipschitz, the floored Taylor
terms add `2 (w + 1)` and the remainder `1`, which makes `(13 w + 57) / 4` in all. This budget
grows linearly in `w`, so `log2 p + 8` guard bits keep it within half a unit at the output scale
(`trigGuard_budget`), and `roundShift` adds the other half. The symmetry reductions are
classical; the budget and the guard are ours. The bound is never checked entry by entry:
`trigTable_sound` is one theorem for all `N` and `p`, and the kernel evaluates `trigPi` only
where a proof needs the value of an entry, as when `TrigTableWords` compares a stored table with
`trigTable`.
-/

@[expose] public section

namespace CAS.Numerics

/-- A pair of integers approximates `2 ^ p cos φ` and `2 ^ p sin φ` to within `1`. -/
def TrigApprox (p : ℕ) (v : ℤ × ℤ) (φ : ℝ) : Prop :=
  |(v.1 : ℝ) - 2 ^ p * Real.cos φ| ≤ 1 ∧ |(v.2 : ℝ) - 2 ^ p * Real.sin φ| ≤ 1

/-- The scaled cosine value: `v.1 / 2 ^ p` is within `2 ^ (-p)` of `cos φ`. -/
theorem TrigApprox.abs_div_sub_cos_le {p : ℕ} {v : ℤ × ℤ} {φ : ℝ} (h : TrigApprox p v φ) :
    |(v.1 : ℝ) / 2 ^ p - Real.cos φ| ≤ 1 / 2 ^ p := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  rw [show (v.1 : ℝ) / 2 ^ p - Real.cos φ = ((v.1 : ℝ) - 2 ^ p * Real.cos φ) / 2 ^ p by
    field_simp, abs_div, abs_of_pos hp]
  exact div_le_div_of_nonneg_right h.1 hp.le

/-- The scaled sine value: `v.2 / 2 ^ p` is within `2 ^ (-p)` of `sin φ`. -/
theorem TrigApprox.abs_div_sub_sin_le {p : ℕ} {v : ℤ × ℤ} {φ : ℝ} (h : TrigApprox p v φ) :
    |(v.2 : ℝ) / 2 ^ p - Real.sin φ| ≤ 1 / 2 ^ p := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  rw [show (v.2 : ℝ) / 2 ^ p - Real.sin φ = ((v.2 : ℝ) - 2 ^ p * Real.sin φ) / 2 ^ p by
    field_simp, abs_div, abs_of_pos hp]
  exact div_le_div_of_nonneg_right h.2 hp.le

/-- Guard bits added to the output precision `p`. -/
def trigGuard (p : ℕ) : ℕ := Nat.log2 p + 8

/-- For `1 ≤ g`, `roundShift g c` lies within `1 / 2` of `c / 2 ^ g` in `ℝ`, for every integer
`c`. -/
theorem abs_roundShift_sub_le (g : ℕ) (hg : 1 ≤ g) (c : ℤ) :
    |(roundShift g c : ℝ) - c / 2 ^ g| ≤ 1 / 2 := by
  have hD : (0 : ℤ) < ((2 ^ g : ℕ) : ℤ) := by positivity
  have hlo := Int.ediv_mul_le (c + ((2 ^ (g - 1) : ℕ) : ℤ)) hD.ne'
  have hhi := Int.lt_ediv_add_one_mul_self (c + ((2 ^ (g - 1) : ℕ) : ℤ)) hD
  rw [← roundShift] at hlo hhi
  have hlo' : (roundShift g c : ℝ) * 2 ^ g ≤ c + 2 ^ (g - 1) := by exact_mod_cast hlo
  have hhi' : (c : ℝ) + 2 ^ (g - 1) < (roundShift g c + 1) * 2 ^ g := by exact_mod_cast hhi
  have hsplit : (2 : ℝ) ^ g = 2 ^ (g - 1) * 2 := (pow_sub_one_mul (by omega) 2).symm
  have hpos : (0 : ℝ) < 2 ^ (g - 1) := by positivity
  have hD' : (0 : ℝ) < 2 ^ g := by positivity
  have heq : (roundShift g c : ℝ) - c / 2 ^ g = ((roundShift g c : ℝ) * 2 ^ g - c) / 2 ^ g := by
    field_simp
  rw [heq, abs_div, abs_of_pos hD', div_le_iff₀ hD', abs_le]
  rw [hsplit] at hlo' hhi' ⊢
  constructor <;> nlinarith

/-- An integer within `2 ^ (g - 1)` of `2 ^ (p + g) f` rounds to within `1` of `2 ^ p f`. -/
theorem abs_roundShift_sub_le_one (p g : ℕ) (hg : 1 ≤ g) (c : ℤ) (f : ℝ)
    (h : |(c : ℝ) - 2 ^ (p + g) * f| ≤ 2 ^ (g - 1)) :
    |(roundShift g c : ℝ) - 2 ^ p * f| ≤ 1 := by
  have hr := abs_roundShift_sub_le g hg c
  have hg0 : (0 : ℝ) < 2 ^ g := by positivity
  have hscaled : |(c : ℝ) / 2 ^ g - 2 ^ p * f| ≤ 1 / 2 := by
    have heq : (c : ℝ) / 2 ^ g - 2 ^ p * f = ((c : ℝ) - 2 ^ (p + g) * f) / 2 ^ g := by
      rw [pow_add]
      field_simp
    rw [heq, abs_div, abs_of_pos hg0, div_le_iff₀ hg0,
      ← pow_sub_one_mul (show g ≠ 0 by omega) (2 : ℝ)]
    linarith
  exact (abs_sub_le _ ((c : ℝ) / 2 ^ g) _).trans (by linarith)

/-- The guard covers the a priori error `(13 w + 57) / 4` of the working precision `w`. -/
theorem trigGuard_budget (p : ℕ) :
    13 * (p + trigGuard p) + 57 ≤ 4 * 2 ^ (trigGuard p - 1) := by
  have hlog := Nat.log2_le_self p
  have hlt : p < 2 ^ (p.log2 + 1) := Nat.lt_log2_self
  have hg : trigGuard p - 1 = p.log2 + 7 := by unfold trigGuard; omega
  rw [hg]
  have h7 : 2 ^ (p.log2 + 7) = 64 * 2 ^ (p.log2 + 1) := by ring
  rw [h7]
  unfold trigGuard
  omega

/-- `piFixed w` truncated at zero stays within `5 w + 41` of `2 ^ w π`. -/
theorem abs_toNat_piFixed_sub_le (w : ℕ) :
    |((piFixed w).toNat : ℝ) - 2 ^ w * Real.pi| ≤ 5 * w + 41 := by
  have h := abs_piFixed_sub_le w
  have hcast : (((piFixed w).toNat : ℕ) : ℝ) = (((piFixed w).toNat : ℤ) : ℝ) := rfl
  rw [hcast, Int.toNat_eq_max]
  push_cast
  have := abs_max_sub_max_le_abs (piFixed w : ℝ) (2 ^ w * Real.pi) 0
  rw [max_eq_left (by positivity : (0 : ℝ) ≤ 2 ^ w * Real.pi)] at this
  exact this.trans h

/-- Fixed-point cosine and sine of `m π / (2 N)` at scale `2 ^ p`; accurate when `2 m ≤ N`. -/
def trigPiOctant (N p m : ℕ) : ℤ × ℤ :=
  let g := trigGuard p
  let w := p + g
  let X := min (m * (piFixed w).toNat / (2 * N)) (2 ^ w)
  (roundShift g (trigTaylorCos (2 ^ w) X (trigDegree w)),
    roundShift g (trigTaylorSin (2 ^ w) X (trigDegree w)))

/-- The octant evaluator is within `1` of both scaled values on `[0, π / 4]`. -/
theorem trigPiOctant_sound (N p m : ℕ) (hN : 0 < N) (hm : 2 * m ≤ N) :
    TrigApprox p (trigPiOctant N p m) (m * Real.pi / (2 * N)) := by
  set g := trigGuard p with hg
  set w := p + g with hw
  set P := (piFixed w).toNat with hP
  set Y := m * P / (2 * N) with hY
  set X := min Y (2 ^ w) with hX
  have hXle : X ≤ 2 ^ w := min_le_right _ _
  have hg1 : 1 ≤ g := by rw [hg, trigGuard]; omega
  have hs : (0 : ℝ) < 2 ^ w := by positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set x := (m : ℝ) * Real.pi / (2 * N) with hx
  have hmN : (m : ℝ) / (2 * N) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have : (2 * m : ℝ) ≤ N := by exact_mod_cast hm
    linarith
  have hx0 : 0 ≤ x := by positivity
  have hxle : x ≤ 1 := by
    have : x = (m : ℝ) / (2 * N) * Real.pi := by rw [hx]; ring
    rw [this]
    nlinarith [Real.pi_le_four, Real.pi_pos, show (0 : ℝ) ≤ m / (2 * N) by positivity]
  -- The fixed-point argument is within `1 + (5 w + 41) / 4` of `2 ^ w x`.
  have hYerr : |(Y : ℝ) - 2 ^ w * x| ≤ 1 + (5 * w + 41) / 4 := by
    obtain ⟨hlo, hhi⟩ := natCast_div_mem (m * P) (2 * N)
    have hπ := abs_toNat_piFixed_sub_le w
    rw [← hP] at hπ
    have heq : ((m * P : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ) - 2 ^ w * x =
        (m : ℝ) / (2 * N) * ((P : ℝ) - 2 ^ w * Real.pi) := by
      rw [hx]
      push_cast
      field_simp
    have hmid : |((m * P : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ) - 2 ^ w * x| ≤ (5 * w + 41) / 4 := by
      rw [heq, abs_mul, abs_of_nonneg (by positivity)]
      exact (mul_le_mul hmN hπ (abs_nonneg _) (by norm_num)).trans_eq (by ring)
    rw [abs_le] at hmid ⊢
    constructor <;> linarith [hmid.1, hmid.2]
  have hXerr : |(X : ℝ) - 2 ^ w * x| ≤ 1 + (5 * w + 41) / 4 := by
    have := abs_min_sub_min_le_max (Y : ℝ) (2 ^ w) (2 ^ w * x) (2 ^ w)
    rw [min_eq_left (mul_le_of_le_one_right hs.le hxle), sub_self, abs_zero,
      max_eq_left (abs_nonneg _)] at this
    rw [hX]
    push_cast
    exact this.trans hYerr
  -- The Taylor sums and the rounding.
  have hd := trigDegree_le w
  have hfac : (2 : ℝ) ^ w / (trigDegree w + 1).factorial ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast two_pow_le_factorial_trigDegree w
  have hdr : (trigDegree w : ℝ) ≤ w := by exact_mod_cast hd
  have hbudget : (13 * w + 57 : ℝ) ≤ 4 * 2 ^ (g - 1) := by exact_mod_cast trigGuard_budget p
  have harg : |2 ^ w * ((X : ℝ) / 2 ^ w) - 2 ^ w * x| = |(X : ℝ) - 2 ^ w * x| := by
    rw [mul_div_cancel₀ _ hs.ne']
  have hcos := abs_trigTaylorCos_sub_le w X (trigDegree w) hXle
  have hsin := abs_trigTaylorSin_sub_le w X (trigDegree w) hXle
  have hcos2 : |2 ^ w * Real.cos ((X : ℝ) / 2 ^ w) - 2 ^ w * Real.cos x| ≤
      |(X : ℝ) - 2 ^ w * x| := by
    rw [← mul_sub, abs_mul, abs_of_pos hs, ← harg, ← mul_sub, abs_mul, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left (Real.abs_cos_sub_cos_le _ _) hs.le
  have hsin2 : |2 ^ w * Real.sin ((X : ℝ) / 2 ^ w) - 2 ^ w * Real.sin x| ≤
      |(X : ℝ) - 2 ^ w * x| := by
    rw [← mul_sub, abs_mul, abs_of_pos hs, ← harg, ← mul_sub, abs_mul, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left (Real.abs_sin_sub_sin_le _ _) hs.le
  have key : ∀ (c : ℤ) (f fx : ℝ),
      |(c : ℝ) - 2 ^ w * fx| ≤ 2 * (trigDegree w + 1) + 2 ^ w / (trigDegree w + 1).factorial →
      |2 ^ w * fx - 2 ^ w * f| ≤ |(X : ℝ) - 2 ^ w * x| →
      |(roundShift g c : ℝ) - 2 ^ p * f| ≤ 1 := by
    intro c f fx h1 h2
    apply abs_roundShift_sub_le_one p g hg1 c f
    rw [← hw]
    linarith [abs_sub_le (c : ℝ) (2 ^ w * fx) (2 ^ w * f), h2.trans hXerr]
  change TrigApprox p (roundShift g (trigTaylorCos (2 ^ w) X (trigDegree w)),
    roundShift g (trigTaylorSin (2 ^ w) X (trigDegree w))) x
  exact ⟨key _ _ _ hcos hcos2, key _ _ _ hsin hsin2⟩

/-- Approximations of cosine and sine at `φ` give those at `π / 2 - φ` in swapped order. -/
theorem TrigApprox.swap {p : ℕ} {v : ℤ × ℤ} {φ : ℝ} (h : TrigApprox p v φ) :
    TrigApprox p v.swap (Real.pi / 2 - φ) := by
  rw [TrigApprox, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
  exact ⟨h.2, h.1⟩

/-- Cosine and sine of `q π / 2 + φ` from those of `φ`, for `q < 4`. -/
def trigQuarterTurn (q : ℕ) (v : ℤ × ℤ) : ℤ × ℤ :=
  if q = 0 then v else if q = 1 then (-v.2, v.1) else if q = 2 then (-v.1, -v.2)
  else (v.2, -v.1)

/-- For `q < 4`, if `TrigApprox p v φ`, then
`TrigApprox p (trigQuarterTurn q v) (q * (π / 2) + φ)`. -/
theorem trigQuarterTurn_sound {p q : ℕ} (hq : q < 4) {v : ℤ × ℤ} {φ : ℝ}
    (h : TrigApprox p v φ) : TrigApprox p (trigQuarterTurn q v) (q * (Real.pi / 2) + φ) := by
  obtain ⟨hc, hs⟩ := h
  have hneg : ∀ a b : ℝ, |a - b| ≤ 1 → |-a - -b| ≤ 1 := fun a b h ↦ by
    rw [← neg_sub', neg_sub, abs_sub_comm]; exact h
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl
  · simpa [trigQuarterTurn, TrigApprox] using ⟨hc, hs⟩
  · have e : ((1 : ℕ) : ℝ) * (Real.pi / 2) + φ = φ + Real.pi / 2 := by push_cast; ring
    simp only [trigQuarterTurn, TrigApprox, e, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
    push_cast
    exact ⟨by simpa using hneg _ _ hs, hc⟩
  · have e : ((2 : ℕ) : ℝ) * (Real.pi / 2) + φ = φ + Real.pi := by push_cast; ring
    simp only [trigQuarterTurn, TrigApprox, e, Real.cos_add_pi, Real.sin_add_pi]
    push_cast
    exact ⟨by simpa using hneg _ _ hc, by simpa using hneg _ _ hs⟩
  · have e : ((3 : ℕ) : ℝ) * (Real.pi / 2) + φ = (φ + Real.pi) + Real.pi / 2 := by
      push_cast; ring
    simp only [trigQuarterTurn, TrigApprox, e, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two,
      Real.cos_add_pi, Real.sin_add_pi]
    push_cast
    exact ⟨by simpa using hs, by simpa using hneg _ _ hc⟩

/-- Integers within `1` of `2 ^ p cos (k π / (2 N))` and `2 ^ p sin (k π / (2 N))`, for every
natural index `k`; the index is reduced modulo `4 N` first. -/
def trigPi (N p k : ℕ) : ℤ × ℤ :=
  trigQuarterTurn (k % (4 * N) / N)
    (if 2 * (k % (4 * N) % N) ≤ N then trigPiOctant N p (k % (4 * N) % N)
      else (trigPiOctant N p (N - k % (4 * N) % N)).swap)

/-- The value at an index depends only on its residue modulo `4 N`. -/
theorem trigPi_mod (N p k : ℕ) : trigPi N p (k % (4 * N)) = trigPi N p k := by
  simp only [trigPi, Nat.mod_mod]

/-- Every value of `trigPi N p` is within `1` of `2 ^ p cos (k π / (2 N))` and
`2 ^ p sin (k π / (2 N))`: the quarter turn and the complementary angle are exact symmetries,
and `trigPiOctant_sound` bounds the remaining angle in `[0, π / 4]`. -/
theorem trigPi_sound (N p : ℕ) (hN : 0 < N) (k : ℕ) :
    TrigApprox p (trigPi N p k) (k * Real.pi / (2 * N)) := by
  set k' := k % (4 * N) with hk'
  set r := k' % N with hr
  set q := k' / N with hq
  have hq4 : q < 4 := by
    rw [hq, Nat.div_lt_iff_lt_mul hN]
    exact Nat.mod_lt _ (by omega)
  have hrN : r < N := Nat.mod_lt _ hN
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  set φ : ℝ := r * Real.pi / (2 * N) with hφ
  have hv : TrigApprox p
      (if 2 * r ≤ N then trigPiOctant N p r else (trigPiOctant N p (N - r)).swap) φ := by
    split_ifs with h
    · exact trigPiOctant_sound N p r hN h
    · have h' := (trigPiOctant_sound N p (N - r) hN (by omega)).swap
      have e : Real.pi / 2 - ((N - r : ℕ) : ℝ) * Real.pi / (2 * N) = φ := by
        rw [hφ, Nat.cast_sub hrN.le]
        field_simp
        ring
      rwa [e] at h'
  have hturn := trigQuarterTurn_sound hq4 hv
  have hangle : (k : ℝ) * Real.pi / (2 * N) =
      (q * (Real.pi / 2) + φ) + ((k / (4 * N) : ℕ) : ℝ) * (2 * Real.pi) := by
    have h3 : (k : ℝ) = 4 * N * ((k / (4 * N) : ℕ) : ℝ) + (N * q + r) := by
      have h12 : k = 4 * N * (k / (4 * N)) + (N * q + r) := by
        rw [hq, hr, Nat.div_add_mod, hk', Nat.div_add_mod]
      exact_mod_cast h12
    rw [h3, hφ]
    field_simp
    ring
  rw [TrigApprox, hangle, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]
  exact hturn

/-- The basis function of frequency `n` at the grid node `j π / (2 N)` is the entry at the
product index `n j`. -/
theorem trigPi_sound_mul (N p : ℕ) (hN : 0 < N) (n j : ℕ) :
    TrigApprox p (trigPi N p (n * j)) (n * (j * Real.pi / (2 * N))) := by
  rw [show (n : ℝ) * (j * Real.pi / (2 * N)) = ((n * j : ℕ) : ℝ) * Real.pi / (2 * N) by
    push_cast; ring]
  exact trigPi_sound N p hN (n * j)

/-- The scaled cosine values of `trigPi N p` approximate `cos (m π / (2 N))` to within `2 ^ (-p)`
at every natural index `m`; this is the hypothesis of the approximate quadrature weights. -/
theorem abs_trigPi_div_sub_cos_le (N p : ℕ) (hN : 0 < N) (m : ℕ) :
    |((trigPi N p m).1 : ℝ) / 2 ^ p - Real.cos (m * Real.pi / (2 * N))| ≤ 1 / 2 ^ p :=
  (trigPi_sound N p hN m).abs_div_sub_cos_le

/-- The table of `2 ^ p cos (k π / (2 N))` and `2 ^ p sin (k π / (2 N))` for `k = 0, …, 4 N`,
rounded to integers. -/
def trigTable (N p : ℕ) (k : Fin (4 * N + 1)) : ℤ × ℤ := trigPi N p k

/-- Every entry of `trigTable N p` is within `1` of `2 ^ p cos (k π / (2 N))` and
`2 ^ p sin (k π / (2 N))`, for every `N > 0` and every output precision `p`. -/
theorem trigTable_sound (N p : ℕ) (hN : 0 < N) (k : Fin (4 * N + 1)) :
    |((trigTable N p k).1 : ℝ) - 2 ^ p * Real.cos (k * Real.pi / (2 * N))| ≤ 1 ∧
      |((trigTable N p k).2 : ℝ) - 2 ^ p * Real.sin (k * Real.pi / (2 * N))| ≤ 1 :=
  trigPi_sound N p hN k

end CAS.Numerics
