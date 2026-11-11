/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedSlots
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Rounded powers of a rotation

Given integers `u, v` within `1` of `2 ^ p cos φ` and `2 ^ p sin φ`, the rounded powers
`x_{k+1} = ⌊(x_k u - y_k v) / 2 ^ p⌋`, `y_{k+1} = ⌊(x_k v + y_k u) / 2 ^ p⌋` from
`(x_0, y_0) = (2 ^ p, 0)` stay within `4 k` of `2 ^ p cos (k φ)` and `2 ^ p sin (k φ)` as long as
`20 k ≤ 2 ^ p` (`rotationIterate_approx`). All numbers are stored with the bias
`b = 2 ^ (p + 2)`, so the steps use natural-number operations only (`rotationCos`,
`rotationSin`), and `rotationRows` packs the first `n` iterates into two rows of slots in one
pass (`slot_rotationRows_fst`, `slot_rotationRows_snd`). A table of `cos (k φ)` and `sin (k φ)`
for every `k < n` thus costs `n` steps, instead of one series evaluation per entry.

## Implementation notes

We prove the bound as in `TrigRotation`, in the complex plane: every step multiplies by a
number within `√2 2 ^ (-p)` of `e ^ {i φ}` and rounds each coordinate down, so the errors add up
linearly (`rotation_step_norm`, which uses the constant `3 / 2` in place of `√2`). The bias
follows the kernel rules of `PackedSlots`, which keep integers out of loops. Under
`20 k ≤ 2 ^ p` the iterate and the base have modulus at most `2 ^ (p + 1)`, so both products are
at most `4 (2 ^ p) ^ 2 = b 2 ^ p` in absolute value (`rotation_mul_bound`). Adding `b 2 ^ p` thus
keeps the natural subtraction of each step exact and leaves the result biased by `b`, and the
floor division is one `Nat.shiftRight`. `rotationIterate_approx` also shows that every biased
iterate is below `2 b`, which gives the hypothesis `hfit` of the slot lemmas for slots of width
`w` with `2 b ≤ 2 ^ w`.

`rotationRowsStrict` is the form for kernel evaluation. Its loop branches with `cond` on
`Nat.beq` of the sum of the new state against `0`, with the same recursive call in both
branches, so each step's values are forced before the next step and long runs do not nest
unevaluated iterates; `rotationRowsStrict_eq` identifies it with `rotationRows`. The kernel
evaluates the rows once, in `n` steps, and their accuracy comes from `rotationIterate_approx`, a
theorem for every `p` and `k`. The recurrence is classical; the bias, the packing and the bounds
are ours.
-/

@[expose] public section

namespace CAS.Numerics

/-- The biased cosine of one rounded rotation step: `⌊(x u - y v) / 2 ^ p⌋ + b` for
`X = x + b`, `Y = y + b`, `U = u + b`, `V = v + b`. -/
def rotationCos (p b U V X Y : ℕ) : ℕ :=
  Nat.shiftRight
    (Nat.sub (Nat.add (Nat.add (Nat.mul X U) (Nat.mul Y b)) (Nat.add (Nat.mul b V)
      (Nat.shiftLeft b p)))
      (Nat.add (Nat.add (Nat.mul X b) (Nat.mul b U)) (Nat.mul Y V))) p

/-- The biased sine of one rounded rotation step: `⌊(x v + y u) / 2 ^ p⌋ + b`. -/
def rotationSin (p b U V X Y : ℕ) : ℕ :=
  Nat.shiftRight
    (Nat.sub (Nat.add (Nat.add (Nat.mul X V) (Nat.mul Y U)) (Nat.add (Nat.mul 2 (Nat.mul b b))
      (Nat.shiftLeft b p)))
      (Nat.add (Nat.add (Nat.mul X b) (Nat.mul b V)) (Nat.add (Nat.mul Y b) (Nat.mul b U)))) p

/-- The biased iterates `(X_k, Y_k)` of the rounded rotation from `(b + 2 ^ p, b)`. -/
def rotationIterate (p b U V : ℕ) : ℕ → ℕ × ℕ
  | 0 => (b + 2 ^ p, b)
  | k + 1 => (rotationCos p b U V (rotationIterate p b U V k).1 (rotationIterate p b U V k).2,
      rotationSin p b U V (rotationIterate p b U V k).1 (rotationIterate p b U V k).2)

/-- One pass over `n` steps from step `j` with state `(X, Y)`, adding `X` and `Y` to the
packed rows `ac` and `as` at slot `j` of width `w`. -/
def rotationRowsAux (p b U V w : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ :=
  Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ) (fun _ _ _ ac as ↦ (ac, as))
    (fun _ rec j X Y ac as ↦ rec (Nat.add j 1) (rotationCos p b U V X Y)
      (rotationSin p b U V X Y) (Nat.add ac (Nat.shiftLeft X (Nat.mul w j)))
      (Nat.add as (Nat.shiftLeft Y (Nat.mul w j))))

/-- The packed rows of the biased cosines `X_j` and sines `Y_j` of the iterates, `j < n`, in
slots of width `w`. -/
def rotationRows (p b U V w n : ℕ) : ℕ × ℕ :=
  rotationRowsAux p b U V w n 0 (b + 2 ^ p) b 0 0

/-- `rotationRowsAux` with every step's values forced before the next step, so that the kernel
evaluates long runs without nesting unevaluated iterates (`rotationRowsStrictAux_eq`). -/
def rotationRowsStrictAux (p b U V w : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ :=
  Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ) (fun _ _ _ ac as ↦ (ac, as))
    (fun _ rec j X Y ac as ↦
      let X' := rotationCos p b U V X Y
      let Y' := rotationSin p b U V X Y
      let ac' := Nat.add ac (Nat.shiftLeft X (Nat.mul w j))
      let as' := Nat.add as (Nat.shiftLeft Y (Nat.mul w j))
      cond (Nat.beq (Nat.add (Nat.add X' Y') (Nat.add ac' as')) 0)
        (rec (Nat.add j 1) X' Y' ac' as') (rec (Nat.add j 1) X' Y' ac' as'))

/-- The packed rows of `rotationRows`, evaluated step by step. -/
def rotationRowsStrict (p b U V w n : ℕ) : ℕ × ℕ :=
  rotationRowsStrictAux p b U V w n 0 (b + 2 ^ p) b 0 0

/-- `rotationRowsStrictAux` equals `rotationRowsAux` for every count `n` and every start state. -/
theorem rotationRowsStrictAux_eq (p b U V w n : ℕ) : ∀ j X Y ac as,
    rotationRowsStrictAux p b U V w n j X Y ac as = rotationRowsAux p b U V w n j X Y ac as := by
  induction n with
  | zero => intro j X Y ac as; rfl
  | succ n ih =>
    intro j X Y ac as
    simp only [rotationRowsStrictAux, rotationRowsAux, Bool.cond_self] at ih ⊢

/-- `rotationRowsStrict p b U V w n` equals `rotationRows p b U V w n`, for all arguments. -/
theorem rotationRowsStrict_eq (p b U V w n : ℕ) :
    rotationRowsStrict p b U V w n = rotationRows p b U V w n :=
  rotationRowsStrictAux_eq p b U V w n _ _ _ _ _

/-- One pass from step `j` with the `j`-th iterate and the first `j` slots filled fills the
first `j + n` slots. -/
private theorem rotationRowsAux_eq (p b U V w n j : ℕ) :
    rotationRowsAux p b U V w n j (rotationIterate p b U V j).1 (rotationIterate p b U V j).2
        (packSlots w j (fun k ↦ (rotationIterate p b U V k).1))
        (packSlots w j (fun k ↦ (rotationIterate p b U V k).2)) =
      (packSlots w (j + n) (fun k ↦ (rotationIterate p b U V k).1),
        packSlots w (j + n) (fun k ↦ (rotationIterate p b U V k).2)) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    rw [show j + (n + 1) = j + 1 + n by omega, ← ih (j + 1)]
    rfl

private theorem rotationRows_eq (p b U V w n : ℕ) :
    rotationRows p b U V w n = (packSlots w n (fun k ↦ (rotationIterate p b U V k).1),
      packSlots w n (fun k ↦ (rotationIterate p b U V k).2)) := by
  have h := rotationRowsAux_eq p b U V w n 0
  rwa [Nat.zero_add] at h

/-- Slot `j` of the cosine row is the biased cosine of the `j`-th iterate. -/
theorem slot_rotationRows_fst {p b U V w n j : ℕ}
    (hfit : ∀ k < n, (rotationIterate p b U V k).1 < 2 ^ w ∧ (rotationIterate p b U V k).2 < 2 ^ w)
    (hj : j < n) : slot w j (rotationRows p b U V w n).1 = (rotationIterate p b U V j).1 := by
  rw [rotationRows_eq, slot_packed_eq (fun k hk ↦ (hfit k hk).1), ite_eq_left hj]

/-- Slot `j` of the sine row is the biased sine of the `j`-th iterate. -/
theorem slot_rotationRows_snd {p b U V w n j : ℕ}
    (hfit : ∀ k < n, (rotationIterate p b U V k).1 < 2 ^ w ∧ (rotationIterate p b U V k).2 < 2 ^ w)
    (hj : j < n) : slot w j (rotationRows p b U V w n).2 = (rotationIterate p b U V j).2 := by
  rw [rotationRows_eq, slot_packed_eq (fun k hk ↦ (hfit k hk).2), ite_eq_left hj]

/-- The cosine step in real numbers: `2 ^ p (X' - b) ≤ x u - y v < 2 ^ p (X' - b) + 2 ^ p`
for `X' = rotationCos p b U V X Y`, when the biased numerator is nonnegative. -/
private theorem rotationCos_bounds {p b U V X Y : ℕ}
    (h : 0 ≤ ((X : ℝ) - b) * ((U : ℝ) - b) - ((Y : ℝ) - b) * ((V : ℝ) - b) + b * 2 ^ p) :
    (2 : ℝ) ^ p * ((rotationCos p b U V X Y : ℝ) - b) ≤
        ((X : ℝ) - b) * ((U : ℝ) - b) - ((Y : ℝ) - b) * ((V : ℝ) - b) ∧
      ((X : ℝ) - b) * ((U : ℝ) - b) - ((Y : ℝ) - b) * ((V : ℝ) - b) <
        (2 : ℝ) ^ p * ((rotationCos p b U V X Y : ℝ) - b) + 2 ^ p := by
  have hle : X * b + b * U + Y * V ≤ X * U + Y * b + (b * V + b * 2 ^ p) :=
    (Nat.cast_le (α := ℝ)).1 (by push_cast; linarith)
  have hc : rotationCos p b U V X Y =
      (X * U + Y * b + (b * V + b * 2 ^ p) - (X * b + b * U + Y * V)) / 2 ^ p := by
    change (X * U + Y * b + (b * V + b <<< p) - (X * b + b * U + Y * V)) >>> p = _
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hN : (((X * U + Y * b + (b * V + b * 2 ^ p) - (X * b + b * U + Y * V) : ℕ)) : ℝ) =
      ((X : ℝ) - b) * ((U : ℝ) - b) - ((Y : ℝ) - b) * ((V : ℝ) - b) + b * 2 ^ p := by
    rw [Nat.cast_sub hle]
    push_cast
    ring
  have h1 := (Nat.cast_le (α := ℝ)).mpr
    (Nat.mul_div_le (X * U + Y * b + (b * V + b * 2 ^ p) - (X * b + b * U + Y * V)) (2 ^ p))
  have h2 := (Nat.cast_lt (α := ℝ)).mpr (Nat.lt_mul_div_succ
    (X * U + Y * b + (b * V + b * 2 ^ p) - (X * b + b * U + Y * V)) (Nat.two_pow_pos p))
  rw [hc]
  push_cast at h1 h2
  rw [hN] at h1 h2
  constructor <;> nlinarith

/-- The sine step in real numbers: `2 ^ p (Y' - b) ≤ x v + y u < 2 ^ p (Y' - b) + 2 ^ p`
for `Y' = rotationSin p b U V X Y`, when the biased numerator is nonnegative. -/
private theorem rotationSin_bounds {p b U V X Y : ℕ}
    (h : 0 ≤ ((X : ℝ) - b) * ((V : ℝ) - b) + ((Y : ℝ) - b) * ((U : ℝ) - b) + b * 2 ^ p) :
    (2 : ℝ) ^ p * ((rotationSin p b U V X Y : ℝ) - b) ≤
        ((X : ℝ) - b) * ((V : ℝ) - b) + ((Y : ℝ) - b) * ((U : ℝ) - b) ∧
      ((X : ℝ) - b) * ((V : ℝ) - b) + ((Y : ℝ) - b) * ((U : ℝ) - b) <
        (2 : ℝ) ^ p * ((rotationSin p b U V X Y : ℝ) - b) + 2 ^ p := by
  have hle : X * b + b * V + (Y * b + b * U) ≤ X * V + Y * U + (2 * (b * b) + b * 2 ^ p) :=
    (Nat.cast_le (α := ℝ)).1 (by push_cast; linarith)
  have hc : rotationSin p b U V X Y =
      (X * V + Y * U + (2 * (b * b) + b * 2 ^ p) - (X * b + b * V + (Y * b + b * U))) / 2 ^ p := by
    change (X * V + Y * U + (2 * (b * b) + b <<< p) - (X * b + b * V + (Y * b + b * U))) >>> p = _
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hN : (((X * V + Y * U + (2 * (b * b) + b * 2 ^ p) - (X * b + b * V + (Y * b + b * U)) :
      ℕ)) : ℝ) = ((X : ℝ) - b) * ((V : ℝ) - b) + ((Y : ℝ) - b) * ((U : ℝ) - b) + b * 2 ^ p := by
    rw [Nat.cast_sub hle]
    push_cast
    ring
  have h1 := (Nat.cast_le (α := ℝ)).mpr (Nat.mul_div_le
    (X * V + Y * U + (2 * (b * b) + b * 2 ^ p) - (X * b + b * V + (Y * b + b * U))) (2 ^ p))
  have h2 := (Nat.cast_lt (α := ℝ)).mpr (Nat.lt_mul_div_succ
    (X * V + Y * U + (2 * (b * b) + b * 2 ^ p) - (X * b + b * V + (Y * b + b * U)))
    (Nat.two_pow_pos p))
  rw [hc]
  push_cast at h1 h2
  rw [hN] at h1 h2
  constructor <;> nlinarith

/-- A complex number with both coordinates of absolute value at most `M` has norm at most
`3 / 2 * M`. -/
private theorem norm_mk_le {a c M : ℝ} (ha : |a| ≤ M) (hc : |c| ≤ M) :
    ‖(⟨a, c⟩ : ℂ)‖ ≤ 3 / 2 * M := by
  have hM : 0 ≤ M := le_trans (abs_nonneg a) ha
  have ha2 : a ^ 2 ≤ M ^ 2 := sq_le_sq' (abs_le.1 ha).1 (abs_le.1 ha).2
  have hc2 : c ^ 2 ≤ M ^ 2 := sq_le_sq' (abs_le.1 hc).1 (abs_le.1 hc).2
  have hsq : ‖(⟨a, c⟩ : ℂ)‖ ^ 2 ≤ (3 / 2 * M) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_mk]
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

/-- One rounded rotation step in the complex plane: an error of `4 κ` grows to `4 (κ + 1)`
while `20 (κ + 1) ≤ P`. -/
private theorem rotation_step_norm {P κ x y u v x' y' θ φ : ℝ} (hκ : 0 ≤ κ)
    (hP : 20 * (κ + 1) ≤ P)
    (hz : ‖(⟨x, y⟩ : ℂ) - P * Complex.exp (θ * Complex.I)‖ ≤ 4 * κ)
    (hu : |u - P * Real.cos φ| ≤ 1) (hv : |v - P * Real.sin φ| ≤ 1)
    (hx1 : P * x' ≤ x * u - y * v) (hx2 : x * u - y * v < P * x' + P)
    (hy1 : P * y' ≤ x * v + y * u) (hy2 : x * v + y * u < P * y' + P) :
    ‖(⟨x', y'⟩ : ℂ) - P * Complex.exp ((θ + φ : ℝ) * Complex.I)‖ ≤ 4 * (κ + 1) := by
  have hP0 : 0 < P := by linarith
  set Ek := Complex.exp (θ * Complex.I)
  set E := Complex.exp (φ * Complex.I)
  have hEk : ‖Ek‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hE : ‖E‖ = 1 := Complex.norm_exp_ofReal_mul_I φ
  have hPn : ‖(P : ℂ)‖ = P := Complex.norm_of_nonneg hP0.le
  have h1 : (P : ℂ) * ⟨x', y'⟩ =
      ⟨x, y⟩ * ⟨u, v⟩ - ⟨x * u - y * v - P * x', x * v + y * u - P * y'⟩ := by
    apply Complex.ext <;> simp
  have key : (P : ℂ) * ((⟨x', y'⟩ : ℂ) - P * Complex.exp ((θ + φ : ℝ) * Complex.I)) =
      ((⟨x, y⟩ : ℂ) - P * Ek) * ⟨u, v⟩ + P * Ek * ((⟨u, v⟩ : ℂ) - P * E) -
        ⟨x * u - y * v - P * x', x * v + y * u - P * y'⟩ := by
    rw [Complex.ofReal_add, add_mul, Complex.exp_add]
    linear_combination h1
  have hD : (⟨u, v⟩ : ℂ) - P * E = ⟨u - P * Real.cos φ, v - P * Real.sin φ⟩ := by
    apply Complex.ext <;> simp [E, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hDn : ‖(⟨u, v⟩ : ℂ) - P * E‖ ≤ 3 / 2 := by
    rw [hD]
    simpa using norm_mk_le hu hv
  have hWn : ‖(⟨u, v⟩ : ℂ)‖ ≤ P + 3 / 2 := by
    calc ‖(⟨u, v⟩ : ℂ)‖ = ‖(P : ℂ) * E + ((⟨u, v⟩ : ℂ) - P * E)‖ := by ring_nf
      _ ≤ ‖(P : ℂ) * E‖ + ‖(⟨u, v⟩ : ℂ) - P * E‖ := norm_add_le _ _
      _ ≤ P + 3 / 2 := by rw [norm_mul, hPn, hE, mul_one]; linarith
  have hRn : ‖(⟨x * u - y * v - P * x', x * v + y * u - P * y'⟩ : ℂ)‖ ≤ 3 / 2 * P :=
    norm_mk_le (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)
  have hbound : P * ‖(⟨x', y'⟩ : ℂ) - P * Complex.exp ((θ + φ : ℝ) * Complex.I)‖ ≤
      P * (4 * (κ + 1)) := by
    have hmul : ‖(P : ℂ) * ((⟨x', y'⟩ : ℂ) - P * Complex.exp ((θ + φ : ℝ) * Complex.I))‖ =
        P * ‖(⟨x', y'⟩ : ℂ) - P * Complex.exp ((θ + φ : ℝ) * Complex.I)‖ := by
      rw [norm_mul, hPn]
    rw [← hmul, key]
    calc _ ≤ ‖((⟨x, y⟩ : ℂ) - P * Ek) * ⟨u, v⟩ + P * Ek * ((⟨u, v⟩ : ℂ) - P * E)‖ +
          ‖(⟨x * u - y * v - P * x', x * v + y * u - P * y'⟩ : ℂ)‖ := norm_sub_le _ _
      _ ≤ ‖((⟨x, y⟩ : ℂ) - P * Ek) * ⟨u, v⟩‖ + ‖P * Ek * ((⟨u, v⟩ : ℂ) - P * E)‖ +
          ‖(⟨x * u - y * v - P * x', x * v + y * u - P * y'⟩ : ℂ)‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ 4 * κ * (P + 3 / 2) + P * (3 / 2) + 3 / 2 * P := by
        rw [norm_mul, norm_mul, norm_mul, hPn, hEk, mul_one]
        gcongr
      _ ≤ P * (4 * (κ + 1)) := by nlinarith
  exact le_of_mul_le_mul_left hbound hP0

/-- While `20 (κ + 1) ≤ P`, the products `x u - y v` and `x v + y u` of a point within `4 κ` of
the circle of radius `P` with `(u, v)` stay below `4 P ^ 2` in absolute value. -/
private theorem rotation_mul_bound {P κ x y u v θ φ : ℝ} (hκ : 0 ≤ κ)
    (hP : 20 * (κ + 1) ≤ P)
    (hz : ‖(⟨x, y⟩ : ℂ) - P * Complex.exp (θ * Complex.I)‖ ≤ 4 * κ)
    (hu : |u - P * Real.cos φ| ≤ 1) (hv : |v - P * Real.sin φ| ≤ 1) :
    |x * u - y * v| ≤ 4 * P ^ 2 ∧ |x * v + y * u| ≤ 4 * P ^ 2 := by
  have hP0 : 0 < P := by linarith
  have hPn : ‖(P : ℂ)‖ = P := Complex.norm_of_nonneg hP0.le
  have hZ : ‖(⟨x, y⟩ : ℂ)‖ ≤ 2 * P := by
    have := norm_le_norm_add_norm_sub' (⟨x, y⟩ : ℂ) (P * Complex.exp (θ * Complex.I))
    rw [norm_mul, hPn, Complex.norm_exp_ofReal_mul_I, mul_one] at this
    linarith
  have hD : (⟨u, v⟩ : ℂ) - P * Complex.exp (φ * Complex.I) =
      ⟨u - P * Real.cos φ, v - P * Real.sin φ⟩ := by
    apply Complex.ext <;> simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hW : ‖(⟨u, v⟩ : ℂ)‖ ≤ 2 * P := by
    have := norm_le_norm_add_norm_sub' (⟨u, v⟩ : ℂ) (P * Complex.exp (φ * Complex.I))
    rw [norm_mul, hPn, Complex.norm_exp_ofReal_mul_I, mul_one, hD] at this
    linarith [norm_mk_le hu hv]
  have hZW : ‖(⟨x, y⟩ : ℂ) * ⟨u, v⟩‖ ≤ 4 * P ^ 2 := by
    rw [norm_mul]
    nlinarith [norm_nonneg (⟨x, y⟩ : ℂ), norm_nonneg (⟨u, v⟩ : ℂ)]
  constructor
  · have := Complex.abs_re_le_norm ((⟨x, y⟩ : ℂ) * ⟨u, v⟩)
    simp only [Complex.mul_re] at this
    linarith
  · have := Complex.abs_im_le_norm ((⟨x, y⟩ : ℂ) * ⟨u, v⟩)
    simp only [Complex.mul_im] at this
    linarith

/-- The `k`-th iterate, unbiased and seen in the complex plane, is within `4 k` of
`2 ^ p e ^ {i k φ}` while `20 k ≤ 2 ^ p`. -/
private theorem rotationIterate_norm_le {p b U V : ℕ} {φ : ℝ} (hb : b = 2 ^ (p + 2))
    (hU : |(U : ℝ) - b - 2 ^ p * Real.cos φ| ≤ 1) (hV : |(V : ℝ) - b - 2 ^ p * Real.sin φ| ≤ 1) :
    ∀ k : ℕ, 20 * k ≤ 2 ^ p →
      ‖(⟨((rotationIterate p b U V k).1 : ℝ) - b, ((rotationIterate p b U V k).2 : ℝ) - b⟩ :
          ℂ) - ((2 ^ p : ℝ) : ℂ) * Complex.exp ((k * φ : ℝ) * Complex.I)‖ ≤ 4 * k
  | 0, _ => by simp [rotationIterate, Complex.ext_iff, -Complex.ofReal_pow]
  | k + 1, hk => by
    have ih := rotationIterate_norm_le hb hU hV k (by omega)
    have hP : 20 * ((k : ℝ) + 1) ≤ 2 ^ p := by exact_mod_cast hk
    have hb2 : (b : ℝ) * 2 ^ p = 4 * (2 ^ p) ^ 2 := by rw [hb]; push_cast; ring
    obtain ⟨hm1, hm2⟩ := rotation_mul_bound (Nat.cast_nonneg k) hP ih hU hV
    have hc := rotationCos_bounds (p := p) (b := b) (U := U) (V := V)
      (X := (rotationIterate p b U V k).1) (Y := (rotationIterate p b U V k).2)
      (by linarith [(abs_le.mp hm1).1])
    have hs := rotationSin_bounds (p := p) (b := b) (U := U) (V := V)
      (X := (rotationIterate p b U V k).1) (Y := (rotationIterate p b U V k).2)
      (by linarith [(abs_le.mp hm2).1])
    have h := rotation_step_norm (Nat.cast_nonneg k) hP ih hU hV hc.1 hc.2 hs.1 hs.2
    rw [show (((k + 1 : ℕ) : ℝ) * φ) = (k : ℝ) * φ + φ by push_cast; ring]
    exact h.trans_eq (by push_cast; ring)

/-- **Rounded powers of a rotation.** If the biased base `(U, V)` is within `1` of
`2 ^ p (cos φ, sin φ)` and `20 k ≤ 2 ^ p`, the `k`-th biased iterate is within `4 k` of
`2 ^ p (cos (k φ), sin (k φ))`, and it stays between `0` and `2 b`. -/
theorem rotationIterate_approx {p b U V : ℕ} {φ : ℝ} (hb : b = 2 ^ (p + 2))
    (hU : |(U : ℝ) - b - 2 ^ p * Real.cos φ| ≤ 1) (hV : |(V : ℝ) - b - 2 ^ p * Real.sin φ| ≤ 1)
    {k : ℕ} (hk : 20 * k ≤ 2 ^ p) :
    |((rotationIterate p b U V k).1 : ℝ) - b - 2 ^ p * Real.cos (k * φ)| ≤ 4 * k ∧
      |((rotationIterate p b U V k).2 : ℝ) - b - 2 ^ p * Real.sin (k * φ)| ≤ 4 * k ∧
      (rotationIterate p b U V k).1 < 2 * b ∧ (rotationIterate p b U V k).2 < 2 * b := by
  have h := rotationIterate_norm_le hb hU hV k hk
  have hP : 20 * (k : ℝ) ≤ 2 ^ p := by exact_mod_cast hk
  have hP0 : (0 : ℝ) < 2 ^ p := by positivity
  have hbr : (b : ℝ) = 4 * 2 ^ p := by rw [hb]; push_cast; ring
  have h1 := Complex.abs_re_le_norm
    ((⟨((rotationIterate p b U V k).1 : ℝ) - b, ((rotationIterate p b U V k).2 : ℝ) - b⟩ : ℂ) -
      ((2 ^ p : ℝ) : ℂ) * Complex.exp ((k * φ : ℝ) * Complex.I))
  have h2 := Complex.abs_im_le_norm
    ((⟨((rotationIterate p b U V k).1 : ℝ) - b, ((rotationIterate p b U V k).2 : ℝ) - b⟩ : ℂ) -
      ((2 ^ p : ℝ) : ℂ) * Complex.exp ((k * φ : ℝ) * Complex.I))
  simp only [Complex.sub_re, Complex.sub_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im] at h1 h2
  have hc := (abs_le.mp (h1.trans h)).2
  have hs := (abs_le.mp (h2.trans h)).2
  have hcos : (2 : ℝ) ^ p * Real.cos (k * φ) ≤ 2 ^ p :=
    mul_le_of_le_one_right hP0.le (Real.cos_le_one _)
  have hsin : (2 : ℝ) ^ p * Real.sin (k * φ) ≤ 2 ^ p :=
    mul_le_of_le_one_right hP0.le (Real.sin_le_one _)
  refine ⟨h1.trans h, h2.trans h, ?_, ?_⟩
  · exact_mod_cast (show ((rotationIterate p b U V k).1 : ℝ) < 2 * b by linarith)
  · exact_mod_cast (show ((rotationIterate p b U V k).2 : ℝ) < 2 * b by linarith)

end CAS.Numerics
