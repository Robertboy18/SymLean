/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.BatchSimpson

/-!
# Integrands with an algebraic singularity at `0`

An integrand such as `√x e ^ x` or `x ^ (1/3) cos x` is continuous on `[0, b]` but not smooth at
`0`, so the Simpson error bound, which needs four derivatives, does not apply. The substitution
`x = u ^ k` with `k` a common denominator of the exponents removes the singularity:
`substPower k f` is `f (u ^ k)` with `√x` written as `u ^ (k / 2)` and `x ^ (p / q)` as
`u ^ (p k / q)` (`substPower_sound`, for `u ≥ 0`), and

`∫ x in 0..c ^ k, f x = ∫ u in 0..c, f (u ^ k) k u ^ (k - 1)`

holds without any regularity of `f`, because the substitution is monotone
(`integral_eq_of_substPower`, from Mathlib's `integral_comp_mul_deriv_of_deriv_nonneg`). The
right side is smooth and the batch Simpson certificate applies to it
(`of_powerIntegralCheck`). For an upper limit `b` that is not a `k`-th power of a rational, the
interval is split at a rational `c ^ k < b`, and the part `[c ^ k, b]`, away from the
singularity, is checked directly (`of_powerSplitCheck`).

## Implementation notes

`#cas [nintegrate x in [0, b]]` (`CAS.Command.NIntegrateSingular`) proposes the root index `k`,
the substituted integrand, the split point and the panel counts and values of the batch Simpson
search. The kernel evaluates the whole Boolean hypothesis of `of_powerIntegralCheck` or
`of_powerSplitCheck`, so it recomputes `substPower k f = some G` as well as the Simpson panels.
The error bound is `of_integralCheck_abs` on the substituted integrand, and in the split case also
on `[c ^ k, b]`; the last conjunct, `|v - (v₁ + v₂)| + ε₁ + ε₂ ≤ ε`, accounts for rounding the
sum of the two values. Adding the two parts needs `f` integrable on `[0, c ^ k]`, which we get
back through the substitution (`integrable_comp_mul_deriv_iff_of_deriv_nonneg`) from the
continuity of the smooth side. The substitution `x = u ^ k` for an algebraic endpoint singularity
is classical; `substPower` and its soundness proof are ours.
-/

@[expose] public section

namespace CAS.Continuum.BatchSimpson

open CAS.Verified.Expr intervalIntegral Set MeasureTheory

/-- `√x` at `x = u ^ k`. -/
def sqrtCase (k : ℕ) (a : Verified.Expr (Fin 1)) (sa : Option (Verified.Expr (Fin 1))) :
    Option (Verified.Expr (Fin 1)) :=
  match a with
  | .var _ => if k % 2 = 0 then some (.pow (.var 0) (k / 2)) else none
  | _ => sa.map .sqrt

/-- `x ^ (p / q)` at `x = u ^ k`, with the exponent a quotient of literals or a rational
literal. -/
def rpowCase (k : ℕ) (a b : Verified.Expr (Fin 1)) (sa sb : Option (Verified.Expr (Fin 1))) :
    Option (Verified.Expr (Fin 1)) :=
  match a, b with
  | .var _, .div (.nat p) (.nat q) =>
      if q ≠ 0 ∧ (p * k) % q = 0 then some (.pow (.var 0) (p * k / q)) else none
  | .var _, .rat p q =>
      if q ≠ 0 ∧ 0 ≤ p ∧ (p.toNat * k) % q = 0 then some (.pow (.var 0) (p.toNat * k / q))
      else none
  | _, _ =>
      match sa, sb with
      | some sa, some sb => some (.rpow sa sb)
      | _, _ => none

/-- `f (u ^ k)`, with the roots of `x` written as powers of `u`. -/
def substPower (k : ℕ) : Verified.Expr (Fin 1) → Option (Verified.Expr (Fin 1))
  | .nat n => some (.nat n)
  | .int n => some (.int n)
  | .rat p q => some (.rat p q)
  | .pi => some .pi
  | .e => some .e
  | .var _ => some (.pow (.var 0) k)
  | .add a b =>
      match substPower k a, substPower k b with
      | some sa, some sb => some (.add sa sb)
      | _, _ => none
  | .mul a b =>
      match substPower k a, substPower k b with
      | some sa, some sb => some (.mul sa sb)
      | _, _ => none
  | .sub a b =>
      match substPower k a, substPower k b with
      | some sa, some sb => some (.sub sa sb)
      | _, _ => none
  | .div a b =>
      match substPower k a, substPower k b with
      | some sa, some sb => some (.div sa sb)
      | _, _ => none
  | .neg a => (substPower k a).map .neg
  | .pow a n => (substPower k a).map (.pow · n)
  | .sin a => (substPower k a).map .sin
  | .cos a => (substPower k a).map .cos
  | .atan a => (substPower k a).map .atan
  | .asin a => (substPower k a).map .asin
  | .acos a => (substPower k a).map .acos
  | .exp a => (substPower k a).map .exp
  | .log a => (substPower k a).map .log
  | .sqrt a => sqrtCase k a (substPower k a)
  | .rpow a b => rpowCase k a b (substPower k a) (substPower k b)

private theorem map_sound {f : Verified.Expr (Fin 1) → Verified.Expr (Fin 1)} {F : ℝ → ℝ}
    (hF : ∀ (expr : Verified.Expr (Fin 1)) (t : ℝ),
      (f expr).eval (fun _ ↦ t) = F (expr.eval (fun _ ↦ t)))
    {a : Verified.Expr (Fin 1)} {k : ℕ} {u : ℝ}
    (ih : ∀ {G : Verified.Expr (Fin 1)}, substPower k a = some G →
      G.eval (fun _ ↦ u) = a.eval (fun _ ↦ u ^ k))
    {G : Verified.Expr (Fin 1)} (h : (substPower k a).map f = some G) :
    G.eval (fun _ ↦ u) = F (a.eval (fun _ ↦ u ^ k)) := by
  obtain ⟨sa, hA, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [hF, ih hA]

private theorem rpow_rat_eq {u : ℝ} (hu : 0 ≤ u) {k q : ℕ} {p : ℤ} (hq : q ≠ 0) (hp : 0 ≤ p)
    (hdvd : (p.toNat * k) % q = 0) : u ^ (p.toNat * k / q) = (u ^ k) ^ ((p : ℝ) / (q : ℝ)) := by
  have hcast : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hp
  rw [← Real.rpow_natCast_mul hu, ← Real.rpow_natCast,
    Nat.cast_div (Nat.dvd_of_mod_eq_zero hdvd) (by exact_mod_cast hq), Nat.cast_mul, hcast]
  ring_nf

/-- **Soundness of the substitution.** For `u ≥ 0`, `substPower k f` at `u` is `f` at `u ^ k`. -/
theorem substPower_sound (k : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    ∀ (expr : Verified.Expr (Fin 1)) {G : Verified.Expr (Fin 1)},
      substPower k expr = some G → G.eval (fun _ ↦ u) = expr.eval (fun _ ↦ u ^ k)
  | .nat _, _, h | .int _, _, h | .rat _ _, _, h | .pi, _, h | .e, _, h => by
      cases h
      rfl
  | .var _, _, h => by
      cases h
      simp
  | .add a b, _, h | .mul a b, _, h | .sub a b, _, h | .div a b, _, h => by
      simp only [substPower] at h
      split at h <;> cases h
      simp only [eval, substPower_sound k hu a ‹_›, substPower_sound k hu b ‹_›]
  | .neg a, G, h => map_sound (F := fun t ↦ -t) (fun _ _ ↦ rfl)
      (fun hA ↦ substPower_sound k hu a hA) h
  | .pow a n, G, h => map_sound (F := fun t ↦ t ^ n) (fun _ _ ↦ rfl)
      (fun hA ↦ substPower_sound k hu a hA) h
  | .sin a, G, h => map_sound (F := Real.sin) (fun _ _ ↦ rfl)
      (fun hA ↦ substPower_sound k hu a hA) h
  | .cos a, G, h => map_sound (F := Real.cos) (fun _ _ ↦ rfl)
      (fun hA ↦ substPower_sound k hu a hA) h
  | .atan a, G, h => map_sound (F := Real.arctan) (fun _ _ ↦ rfl)
      (fun hA ↦ substPower_sound k hu a hA) h
  | .asin a, G, h => map_sound (F := Real.arcsin) (fun _ _ ↦ rfl)
      (fun hA ↦ substPower_sound k hu a hA) h
  | .acos a, G, h => map_sound (F := Real.arccos) (fun _ _ ↦ rfl)
      (fun hA ↦ substPower_sound k hu a hA) h
  | .exp a, G, h => map_sound (F := Real.exp) (fun _ _ ↦ rfl)
      (fun hA ↦ substPower_sound k hu a hA) h
  | .log a, G, h => map_sound (F := Real.log) (fun _ _ ↦ rfl)
      (fun hA ↦ substPower_sound k hu a hA) h
  | .sqrt a, G, h => by
      simp only [substPower, sqrtCase] at h
      split at h
      · split_ifs at h with hk
        cases h
        simp only [eval]
        rw [← Real.sqrt_sq (pow_nonneg hu (k / 2)), ← pow_mul,
          Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hk)]
      · exact map_sound (F := Real.sqrt) (fun _ _ ↦ rfl)
          (fun hA ↦ substPower_sound k hu a hA) h
  | .rpow a b, G, h => by
      simp only [substPower, rpowCase] at h
      split at h
      · split_ifs at h with hpq
        cases h
        simp only [eval]
        rw [← Real.rpow_natCast_mul hu, ← Real.rpow_natCast,
          Nat.cast_div (Nat.dvd_of_mod_eq_zero hpq.2) (by exact_mod_cast hpq.1), Nat.cast_mul]
        ring_nf
      · split_ifs at h with hpq
        cases h
        simp only [eval]
        exact rpow_rat_eq hu hpq.1 hpq.2.1 hpq.2.2
      · split at h <;> cases h
        simp only [eval, substPower_sound k hu a ‹_›, substPower_sound k hu b ‹_›]

/-- The integrand after the substitution `x = u ^ k`: `f (u ^ k) k u ^ (k - 1)`. -/
def powerIntegrand (k : ℕ) (G : Verified.Expr (Fin 1)) : Verified.Expr (Fin 1) :=
  .mul G (.mul (.nat k) (.pow (.var 0) (k - 1)))

private theorem univariateEval_const (expr : Verified.Expr (Fin 1)) (x : ℝ) :
    expr.univariateEval x = expr.eval (fun _ ↦ x) := by
  rw [univariateEval]
  congr 1
  funext i
  fin_cases i
  rfl

/-- **Change of variables.** `∫ x in 0..c ^ k, f x = ∫ u in 0..c, f (u ^ k) k u ^ (k - 1)`. -/
theorem integral_eq_of_substPower {f G : Verified.Expr (Fin 1)} {k : ℕ} (hk : 0 < k)
    (hG : substPower k f = some G) {c : ℝ} (hc : 0 ≤ c) :
    ∫ x in (0 : ℝ)..c ^ k, f.univariateEval x =
      ∫ u in (0 : ℝ)..c, (powerIntegrand k G).univariateEval u := by
  have hchange := integral_comp_mul_deriv_of_deriv_nonneg (a := 0) (b := c)
    (f := fun u : ℝ ↦ u ^ k) (f' := fun u ↦ k * u ^ (k - 1)) (g := f.univariateEval)
    (continuous_pow k).continuousOn
    (fun u _ ↦ by simpa using hasDerivAt_pow k u)
    fun u hu ↦ by
      have := ((min_eq_left hc).symm.trans_lt hu.1).le
      positivity
  simp only [Function.comp_def, ne_eq, hk.ne', not_false_eq_true, zero_pow] at hchange
  rw [← hchange]
  refine integral_congr fun u hu ↦ ?_
  rw [uIcc_of_le hc] at hu
  simp only [powerIntegrand, univariateEval_const, eval]
  rw [substPower_sound k hu.1 f hG]

/-- **Certified integral of an integrand with an algebraic singularity at `0`.** -/
theorem of_powerIntegralCheck {p : DigitsEval.Precision} {f G d : Verified.Expr (Fin 1)}
    {k : ℕ} {c b : ℚ} {N : ℕ} {v ε : ℚ}
    (hvalid : (powerIntegrand k G).ValidIteratesOn 5 (Icc ((0 : ℚ) : ℝ) c))
    (h : (decide (0 < k) && decide (substPower k f = some G) && decide (0 ≤ c) &&
      decide (b = c ^ k) && integralCheck p (powerIntegrand k G) d 0 c N (v - ε) (v + ε)) = true) :
    |(∫ x in (0 : ℝ)..b, f.univariateEval x) - v| ≤ ε := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hk, hG⟩, hc⟩, rfl⟩, hcheck⟩ := h
  rw [Rat.cast_pow, integral_eq_of_substPower hk hG (by exact_mod_cast hc)]
  simpa only [Rat.cast_zero] using of_integralCheck_abs hvalid hcheck

private theorem continuousOn_of_valid {F : Verified.Expr (Fin 1)} {n : ℕ} (hn : 0 < n)
    {s : Set ℝ} (hvalid : F.ValidIteratesOn n s) : ContinuousOn F.univariateEval s :=
  fun u hu ↦ (hasDerivAt_univariateEval F u (by simpa using hvalid 0 hn u hu)).continuousAt
    |>.continuousWithinAt

/-- The same with the interval split at `s = c ^ k < b`: the substitution on `[0, s]` and the
direct check on `[s, b]`, the value `v` within `ε` of the sum of the two parts. -/
theorem of_powerSplitCheck {p : DigitsEval.Precision} {f G d d₂ : Verified.Expr (Fin 1)}
    {k : ℕ} {c s b : ℚ} {N N₂ : ℕ} {v₁ v₂ ε₁ ε₂ v ε : ℚ}
    (hvalid : (powerIntegrand k G).ValidIteratesOn 5 (Icc ((0 : ℚ) : ℝ) c))
    (hvalid₂ : f.ValidIteratesOn 5 (Icc (s : ℝ) b))
    (h : (decide (0 < k) && decide (substPower k f = some G) && decide (0 ≤ c) &&
      decide (s = c ^ k) && decide (s < b) &&
      integralCheck p (powerIntegrand k G) d 0 c N (v₁ - ε₁) (v₁ + ε₁) &&
      integralCheck p f d₂ s b N₂ (v₂ - ε₂) (v₂ + ε₂) &&
      decide (|v - (v₁ + v₂)| + ε₁ + ε₂ ≤ ε)) = true) :
    |(∫ x in (0 : ℝ)..b, f.univariateEval x) - v| ≤ ε := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hk, hG⟩, hc⟩, rfl⟩, hcb⟩, hcheck₁⟩, hcheck₂⟩, hround⟩ := h
  have h₁ := of_integralCheck_abs hvalid hcheck₁
  have h₂ := of_integralCheck_abs hvalid₂ hcheck₂
  rw [Rat.cast_zero] at h₁ hvalid
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  have hcb' : ((c ^ k : ℚ) : ℝ) ≤ b := by exact_mod_cast hcb.le
  have hsplit : (∫ x in (0 : ℝ)..b, f.univariateEval x) =
      (∫ x in (0 : ℝ)..((c ^ k : ℚ) : ℝ), f.univariateEval x) +
        ∫ x in ((c ^ k : ℚ) : ℝ)..b, f.univariateEval x := by
    refine (integral_add_adjacent_intervals ?_
      ((continuousOn_of_valid (by norm_num) hvalid₂).intervalIntegrable_of_Icc hcb')).symm
    -- Integrable on `[0, c ^ k]` through the substitution.
    have hcont : ContinuousOn
        (fun u : ℝ ↦ (f.univariateEval ∘ fun u ↦ u ^ k) u * ((k : ℝ) * u ^ (k - 1)))
        (Icc 0 (c : ℝ)) := (continuousOn_of_valid (by norm_num) hvalid).congr fun u hu ↦ by
      simp only [Function.comp_def, powerIntegrand, univariateEval_const, eval,
        substPower_sound k hu.1 f hG]
    have htransfer := (integrable_comp_mul_deriv_iff_of_deriv_nonneg (a := 0) (b := (c : ℝ))
      (f := fun u : ℝ ↦ u ^ k) (f' := fun u ↦ (k : ℝ) * u ^ (k - 1))
      (g := f.univariateEval) (continuous_pow k).continuousOn
      (fun u _ ↦ by simpa using hasDerivAt_pow k u)
      fun u hu ↦ by
        have := ((min_eq_left hc').symm.trans_lt hu.1).le
        positivity).mp (hcont.intervalIntegrable_of_Icc hc')
    simpa [zero_pow hk.ne', Rat.cast_pow] using htransfer
  have hfirst : (∫ x in (0 : ℝ)..((c ^ k : ℚ) : ℝ), f.univariateEval x) =
      ∫ u in (0 : ℝ)..(c : ℝ), (powerIntegrand k G).univariateEval u := by
    rw [Rat.cast_pow]
    exact integral_eq_of_substPower hk hG hc'
  have hround' : |(v : ℝ) - (v₁ + v₂)| + ε₁ + ε₂ ≤ ε := by exact_mod_cast hround
  rw [hsplit, hfirst]
  rw [abs_le] at h₁ h₂ ⊢
  have hv := abs_le.mp (le_refl |(v : ℝ) - (v₁ + v₂)|)
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2, hv.1, hv.2]

end CAS.Continuum.BatchSimpson
