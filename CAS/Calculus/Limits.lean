/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.Series

/-!
# One-sided limits, poles, and limits at infinity

A quotient `g / h` whose numerator and denominator have the leading terms `c (x - a) ^ k` and
`d (x - a) ^ m` at `a`, with `k < m`, has a pole of order `m - k`: it is asymptotically
equivalent to `(c / d) ((x - a) ^ (m - k))⁻¹` (`isEquivalent_div_of_isLittleO`), so it tends to
`+∞` or `-∞` on each side of `a`, with the sign of `c / d` on the right and of
`(c / d) (-1) ^ (m - k)` on the left (`tendsto_div_pole_of_check`). For `k ≥ m` the limit is
finite, and the two-sided limit of `tendsto_div_of_check` restricts to either side
(`tendsto_div_side_of_check`).

For limits at `±∞`, `inversion e` writes `e (1 / t)` as `N (t) / t ^ j` with `N` an expression
in `t`, built through field operations from `x ↦ 1 / t` and from functions of arguments that
stay finite (`inversion_sound`). The limit of `e` at `+∞` (`-∞`) is then the limit of
`N (t) / t ^ j` as `t → 0` from the right (left), `tendsto_of_inversion`, which the one-sided
results give.

## Main definitions

* `poleUp`, `side`: the sign of `q ((x - a) ^ j)⁻¹` on a side of `a`, and that side as a filter.
* `inversion`: the substitution `x = 1 / t`, as an expression `N` and a power `j`.

## Main results

* `tendsto_div_pole_of_check`, `tendsto_div_pole_two_sided_of_check`: infinite limits at a
  pole.
* `tendsto_div_side_of_check`, `tendsto_side_of_validIteratesOn`: one-sided finite limits.
* `inversion_sound`, `tendsto_of_inversion`: limits at `±∞`.
* `tendsto_of_univariateEval`, `tendsto_div_of_univariateEval`: transport of a limit of a
  checked expression to the ordinary function it denotes, along any source and target filters,
  for the tactic `cas`.

## Implementation notes

The search of `CAS.Command.Limits` proposes the orders `k` and `m` and the coefficients `c` and
`d`, from the exact values of the symbolic derivatives at `a` as in `CAS.Calculus.Series`, and
the side's sign `poleUp`. The kernel decides the hypothesis of `tendsto_div_pole_of_check` (the
two `leadingCheck`s, `c ≠ 0`, `d ≠ 0`, `k < m` and the sign), so neither the orders nor the sign
is trusted. Validity is needed at `a` only and comes from the CEGA domain checker on `[a, a]`.
We need it because the symbolic derivatives are evaluated with `y / 0 = 0`, as in Lean, and
describe the function only where it is valid.

A pole is a comparison with the model `q ((x - a) ^ j)⁻¹` (`tendsto_pole_model`, built on
Mathlib's `tendsto_inv_nhdsGT_zero` and `tendsto_inv_nhdsLT_zero`), and the asymptotic
equivalence `isEquivalent_div_of_isLittleO` (Mathlib's `IsEquivalent`) carries the model's limit
over to the quotient. Everything rests on leading terms of Taylor expansions, with no comparison
of growth classes. At infinity `inversion` reduces the question to one-sided leading terms at
`0`; it is a structural recursion proved sound once (`inversion_sound`), and the kernel
evaluates it on the input. It fails on functions of unbounded arguments such as `exp x` or
`log x`, whose limits come from the fixed scale of `CAS.Calculus.AsymptoticScale` instead.
-/

@[expose] public section

namespace CAS.Verified.Expr

open Filter Asymptotics Topology Set

/-! ## Poles -/

private theorem tendsto_pow_sub_zero {a : ℝ} {j : ℕ} (hj : 0 < j) (l : Filter ℝ)
    (hl : l ≤ 𝓝 a) : Tendsto (fun x ↦ (x - a) ^ j) l (𝓝 0) :=
  ((by fun_prop : Continuous fun x : ℝ ↦ (x - a) ^ j).tendsto' a 0 (by simp [hj.ne'])).mono_left hl

/-- `((x - a) ^ j)⁻¹ → +∞` as `x → a` from the right. -/
theorem tendsto_inv_pow_sub_nhdsGT {a : ℝ} {j : ℕ} (hj : 0 < j) :
    Tendsto (fun x ↦ ((x - a) ^ j)⁻¹) (𝓝[>] a) atTop := by
  have hpos : Tendsto (fun x ↦ (x - a) ^ j) (𝓝[>] a) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_pow_sub_zero hj _ nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact Set.mem_Ioi.mpr (pow_pos (sub_pos.mpr hx) j)
  exact tendsto_inv_nhdsGT_zero.comp hpos

/-- `((x - a) ^ j)⁻¹` as `x → a` from the left: `+∞` for even `j`, `-∞` for odd `j`. -/
theorem tendsto_inv_pow_sub_nhdsLT {a : ℝ} {j : ℕ} (hj : 0 < j) :
    Tendsto (fun x ↦ ((x - a) ^ j)⁻¹) (𝓝[<] a) (if j % 2 = 0 then atTop else atBot) := by
  have hzero := tendsto_pow_sub_zero hj (𝓝[<] a) nhdsWithin_le_nhds
  split_ifs with heven
  · have hpos : Tendsto (fun x ↦ (x - a) ^ j) (𝓝[<] a) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hzero, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact Set.mem_Ioi.mpr ((Nat.even_iff.mpr heven).pow_pos (sub_ne_zero.mpr (ne_of_lt hx)))
    exact tendsto_inv_nhdsGT_zero.comp hpos
  · have hneg : Tendsto (fun x ↦ (x - a) ^ j) (𝓝[<] a) (𝓝[<] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hzero, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact Set.mem_Iio.mpr ((Nat.odd_iff.mpr (by omega)).pow_neg (sub_neg.mpr hx))
    exact tendsto_inv_nhdsLT_zero.comp hneg

/-- `true` when `q ((x - a) ^ j)⁻¹ → +∞` on the side: the sign of `q` from the right, the sign
of `q (-1) ^ j` from the left. -/
def poleUp (q : ℚ) (j : ℕ) (above : Bool) : Bool :=
  if above then decide (0 < q) else decide (0 < q) == decide (j % 2 = 0)

/-- The side of `a`: from the right when `above`, from the left otherwise. -/
def side (a : ℝ) (above : Bool) : Filter ℝ := if above then 𝓝[>] a else 𝓝[<] a

/-- Either side `side a above` of `a` is finer than the punctured neighbourhood filter `𝓝[≠] a`. -/
theorem side_le_nhdsNE (a : ℝ) (above : Bool) : side a above ≤ 𝓝[≠] a := by
  cases above
  · exact nhdsWithin_mono a fun x hx ↦ ne_of_lt (Set.mem_Iio.mp hx)
  · exact nhdsWithin_mono a fun x hx ↦ ne_of_gt (Set.mem_Ioi.mp hx)

/-- Either side `side a above` of `a` is finer than the neighbourhood filter `𝓝 a`. -/
theorem side_le_nhds (a : ℝ) (above : Bool) : side a above ≤ 𝓝 a :=
  (side_le_nhdsNE a above).trans nhdsWithin_le_nhds

/-- The model of a pole: `q ((x - a) ^ j)⁻¹` on either side of `a`. -/
theorem tendsto_pole_model {a : ℝ} {q : ℚ} {j : ℕ} (hj : 0 < j) (hq : q ≠ 0) (above : Bool) :
    Tendsto (fun x ↦ (q : ℝ) * ((x - a) ^ j)⁻¹) (side a above)
      (if poleUp q j above then atTop else atBot) := by
  rcases lt_or_gt_of_ne hq with hneg | hpos
  · have hq' : (q : ℝ) < 0 := by exact_mod_cast hneg
    have hnot : ¬ 0 < q := not_lt.mpr hneg.le
    cases above
    · have hlim := tendsto_inv_pow_sub_nhdsLT (a := a) hj
      split_ifs at hlim with heven
      · simpa [side, poleUp, hnot, heven] using hlim.const_mul_atTop_of_neg hq'
      · simpa [side, poleUp, hnot, heven] using hlim.const_mul_atBot_of_neg hq'
    · simpa [side, poleUp, hnot] using
        (tendsto_inv_pow_sub_nhdsGT (a := a) hj).const_mul_atTop_of_neg hq'
  · have hq' : (0 : ℝ) < q := by exact_mod_cast hpos
    cases above
    · have hlim := tendsto_inv_pow_sub_nhdsLT (a := a) hj
      split_ifs at hlim with heven
      · simpa [side, poleUp, hpos, heven] using hlim.const_mul_atTop hq'
      · simpa [side, poleUp, hpos, heven] using hlim.const_mul_atBot hq'
    · simpa [side, poleUp, hpos] using
        (tendsto_inv_pow_sub_nhdsGT (a := a) hj).const_mul_atTop hq'

/-- **Poles.** If `g (x) = c (x - a) ^ k + o ((x - a) ^ k)` and
`h (x) = d (x - a) ^ m + o ((x - a) ^ m)` with `c, d ≠ 0` and `k ≤ m`, then `g / h` is
equivalent to `(c / d) ((x - a) ^ (m - k))⁻¹` as `x → a`, `x ≠ a`. -/
theorem isEquivalent_div_of_isLittleO {g h : ℝ → ℝ} {a c d : ℝ} {k m : ℕ}
    (hg : (fun x ↦ g x - c * (x - a) ^ k) =o[𝓝 a] fun x ↦ (x - a) ^ k)
    (hh : (fun x ↦ h x - d * (x - a) ^ m) =o[𝓝 a] fun x ↦ (x - a) ^ m)
    (hc : c ≠ 0) (hd : d ≠ 0) (hkm : k ≤ m) :
    (fun x ↦ g x / h x) ~[𝓝[≠] a] fun x ↦ c / d * ((x - a) ^ (m - k))⁻¹ := by
  have hge : g ~[𝓝[≠] a] fun x ↦ c * (x - a) ^ k :=
    ((isLittleO_const_mul_right_iff hc).mpr hg).mono nhdsWithin_le_nhds
  have hhe : h ~[𝓝[≠] a] fun x ↦ d * (x - a) ^ m :=
    ((isLittleO_const_mul_right_iff hd).mpr hh).mono nhdsWithin_le_nhds
  refine (hge.div hhe).congr_right ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : x - a ≠ 0 := sub_ne_zero.mpr hx
  rw [Pi.div_apply, ← pow_mul_pow_sub _ hkm]
  field_simp

/-- The infinite limit of a quotient at a pole, on one side. -/
theorem tendsto_div_pole_of_check (num den : Verified.Expr (Fin 1)) (k m : ℕ) (a : ℚ)
    (hnum : num.ValidIteratesOn (k + 1) {(a : ℝ)}) (hden : den.ValidIteratesOn (m + 1) {(a : ℝ)})
    (c d : ℚ) (above up : Bool)
    (h : (leadingCheck num k a c && leadingCheck den m a d && decide (c ≠ 0) &&
      decide (d ≠ 0) && decide (k < m) && (up == poleUp (c / d) (m - k) above)) = true) :
    Tendsto (fun x ↦ num.univariateEval x / den.univariateEval x) (side (a : ℝ) above)
      (if up then atTop else atBot) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hcn, hdn⟩, hc0⟩, hd0⟩, hkm⟩, rfl⟩ := h
  have hequiv := isEquivalent_div_of_isLittleO (leading_of_check num k a hnum c hcn)
    (leading_of_check den m a hden d hdn) (by exact_mod_cast hc0) (by exact_mod_cast hd0)
    hkm.le
  have hmodel := tendsto_pole_model (a := (a : ℝ)) (q := c / d) (j := m - k) (by omega)
    (div_ne_zero hc0 hd0) above
  rw [Rat.cast_div] at hmodel
  have hsym := (hequiv.mono (side_le_nhdsNE (a : ℝ) above)).symm
  split_ifs at hmodel ⊢
  · exact hsym.tendsto_atTop hmodel
  · exact hsym.tendsto_atBot hmodel

/-- The infinite limit of a quotient at a pole of even order, from both sides. -/
theorem tendsto_div_pole_two_sided_of_check (num den : Verified.Expr (Fin 1)) (k m : ℕ)
    (a : ℚ)
    (hnum : num.ValidIteratesOn (k + 1) {(a : ℝ)}) (hden : den.ValidIteratesOn (m + 1) {(a : ℝ)})
    (c d : ℚ) (up : Bool)
    (h : (leadingCheck num k a c && leadingCheck den m a d && decide (c ≠ 0) &&
      decide (d ≠ 0) && decide (k < m) && decide ((m - k) % 2 = 0) &&
      (up == decide (0 < c / d))) = true) :
    Tendsto (fun x ↦ num.univariateEval x / den.univariateEval x) (𝓝[≠] (a : ℝ))
      (if up then atTop else atBot) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hcn, hdn⟩, hc0⟩, hd0⟩, hkm⟩, heven⟩, hup⟩ := h
  have hside (above : Bool) := tendsto_div_pole_of_check num den k m a hnum hden c d
    above up (by simp [hcn, hdn, hc0, hd0, hkm, hup, poleUp, heven])
  rw [← nhdsLT_sup_nhdsGT]
  exact (hside false).sup (hside true)

/-- A finite limit of a quotient, on one side. -/
theorem tendsto_div_side_of_check (num den : Verified.Expr (Fin 1)) (m : ℕ) (a : ℚ)
    (hnum : num.ValidIteratesOn (m + 1) {(a : ℝ)}) (hden : den.ValidIteratesOn (m + 1) {(a : ℝ)})
    (c d L : ℚ) (above : Bool)
    (h : (leadingCheck num m a c && leadingCheck den m a d && decide (d ≠ 0) &&
      decide (L = c / d)) = true) :
    Tendsto (fun x ↦ num.univariateEval x / den.univariateEval x) (side (a : ℝ) above)
      (𝓝 (L : ℝ)) :=
  (tendsto_div_of_check num den m a hnum hden c d L h).mono_left
    (side_le_nhdsNE (a : ℝ) above)

/-- An expression tends to its value on either side of a point where it is valid. -/
theorem tendsto_side_of_validIteratesOn (expr : Verified.Expr (Fin 1)) (a : ℚ)
    (hvalid : expr.ValidIteratesOn 1 {(a : ℝ)}) (above : Bool) :
    Tendsto (fun x ↦ expr.univariateEval x) (side (a : ℝ) above)
      (𝓝 (expr.univariateEval a)) :=
  (tendsto_of_validIteratesOn expr a hvalid).mono_left (side_le_nhds (a : ℝ) above)

/-! ## Limits at infinity -/

/-- `e t ^ k`, written without a factor when `k = 0`. -/
def mulTPow (expr : Verified.Expr (Fin 1)) (k : ℕ) : Verified.Expr (Fin 1) :=
  if k = 0 then expr else .mul expr (.pow (.var 0) k)

/-- At the constant environment `t`, `mulTPow expr k` evaluates to `expr` at `t` times `t ^ k`, for
every `k` (including `k = 0`, where no factor is written). -/
theorem eval_mulTPow (expr : Verified.Expr (Fin 1)) (k : ℕ) (t : ℝ) :
    (mulTPow expr k).eval (fun _ ↦ t) = expr.eval (fun _ ↦ t) * t ^ k := by
  rw [mulTPow]
  split_ifs with hk <;> simp [hk]

/-- A function of an argument that stays finite at `t = 0`. -/
def inversionUnary (f : Verified.Expr (Fin 1) → Verified.Expr (Fin 1)) :
    Option (Verified.Expr (Fin 1) × ℕ) → Option (Verified.Expr (Fin 1) × ℕ)
  | some (n, 0) => some (f n, 0)
  | _ => none

/-- `expr (1 / t) = N (t) / t ^ j`: the expression `N` and the power `j`. -/
def inversion : Verified.Expr (Fin 1) → Option (Verified.Expr (Fin 1) × ℕ)
  | .nat n => some (.nat n, 0)
  | .int n => some (.int n, 0)
  | .rat p q => some (.rat p q, 0)
  | .pi => some (.pi, 0)
  | .e => some (.e, 0)
  | .var _ => some (.nat 1, 1)
  | .add a b =>
      match inversion a, inversion b with
      | some (na, ja), some (nb, jb) =>
          some (.add (mulTPow na (max ja jb - ja)) (mulTPow nb (max ja jb - jb)), max ja jb)
      | _, _ => none
  | .sub a b =>
      match inversion a, inversion b with
      | some (na, ja), some (nb, jb) =>
          some (.sub (mulTPow na (max ja jb - ja)) (mulTPow nb (max ja jb - jb)), max ja jb)
      | _, _ => none
  | .mul a b =>
      match inversion a, inversion b with
      | some (na, ja), some (nb, jb) => some (.mul na nb, ja + jb)
      | _, _ => none
  | .div a b =>
      match inversion a, inversion b with
      | some (na, ja), some (nb, jb) =>
          if jb ≤ ja then some (.div na nb, ja - jb)
          else some (.div (mulTPow na (jb - ja)) nb, 0)
      | _, _ => none
  | .neg a =>
      match inversion a with
      | some (na, ja) => some (.neg na, ja)
      | none => none
  | .pow a n =>
      match inversion a with
      | some (na, ja) => some (.pow na n, ja * n)
      | none => none
  | .sin a => inversionUnary .sin (inversion a)
  | .cos a => inversionUnary .cos (inversion a)
  | .atan a => inversionUnary .atan (inversion a)
  | .asin a => inversionUnary .asin (inversion a)
  | .acos a => inversionUnary .acos (inversion a)
  | .exp a => inversionUnary .exp (inversion a)
  | .log a => inversionUnary .log (inversion a)
  | .sqrt a => inversionUnary .sqrt (inversion a)
  | .rpow a b =>
      match inversion a, inversion b with
      | some (na, 0), some (nb, 0) => some (.rpow na nb, 0)
      | _, _ => none

private theorem div_pow_eq_mul_pow_div {x t : ℝ} (ht : t ≠ 0) {k j : ℕ} (hk : k ≤ j) :
    x / t ^ k = x * t ^ (j - k) / t ^ j := by
  rw [← pow_sub_mul_pow t hk]
  field_simp

private theorem inversionUnary_sound {f : Verified.Expr (Fin 1) → Verified.Expr (Fin 1)}
    {F : ℝ → ℝ} (hF : ∀ (n : Verified.Expr (Fin 1)) (t : ℝ),
      (f n).eval (fun _ ↦ t) = F (n.eval (fun _ ↦ t)))
    {a : Verified.Expr (Fin 1)} {s : ℝ}
    (ih : ∀ {N : Verified.Expr (Fin 1)} {j : ℕ}, inversion a = some (N, j) →
      a.eval (fun _ ↦ s) = N.eval (fun _ ↦ s⁻¹) / s⁻¹ ^ j)
    {N : Verified.Expr (Fin 1)} {j : ℕ} (h : inversionUnary f (inversion a) = some (N, j)) :
    F (a.eval (fun _ ↦ s)) = N.eval (fun _ ↦ s⁻¹) / s⁻¹ ^ j := by
  unfold inversionUnary at h
  split at h
  · rename_i n hn
    cases h
    simp [ih hn, hF]
  · cases h

/-- **Soundness of the inversion.** For `t ≠ 0`, `expr (1 / t) = N (t) / t ^ j`, written with
`s = 1 / t`. -/
theorem inversion_sound : ∀ (expr : Verified.Expr (Fin 1)) {N : Verified.Expr (Fin 1)} {j : ℕ},
    inversion expr = some (N, j) → ∀ {s : ℝ}, s ≠ 0 →
      expr.eval (fun _ ↦ s) = N.eval (fun _ ↦ s⁻¹) / s⁻¹ ^ j := by
  intro expr
  induction expr with
  | nat | int | rat | pi | e | var =>
    rintro N j ⟨⟩ s _
    simp
  | add a b iha ihb | sub a b iha ihb =>
    intro N j h s hs
    simp only [inversion] at h
    split at h
    · rename_i na ja nb jb hA hB
      cases h
      simp only [eval, eval_mulTPow]
      rw [iha hA hs, ihb hB hs, div_pow_eq_mul_pow_div (inv_ne_zero hs) (le_max_left ja jb),
        div_pow_eq_mul_pow_div (inv_ne_zero hs) (le_max_right ja jb)]
      ring
    · cases h
  | mul a b iha ihb =>
    intro N j h s hs
    simp only [inversion] at h
    split at h
    · rename_i na ja nb jb hA hB
      cases h
      simp only [eval, iha hA hs, ihb hB hs, pow_add, div_mul_div_comm]
    · cases h
  | div a b iha ihb =>
    intro N j h s hs
    have ht (n : ℕ) : s⁻¹ ^ n ≠ 0 := pow_ne_zero _ (inv_ne_zero hs)
    simp only [inversion] at h
    split at h
    · rename_i na ja nb jb hA hB
      rw [eval, iha hA hs, ihb hB hs]
      split_ifs at h with hle
      · cases h
        rw [eval, ← pow_sub_mul_pow _ hle, div_mul_eq_div_div, div_div_div_cancel_right₀ (ht _),
          div_right_comm]
      · cases h
        rw [eval, eval_mulTPow, ← pow_sub_mul_pow _ (le_of_not_ge hle), div_mul_eq_div_div,
          div_div_div_cancel_right₀ (ht _), div_div_eq_mul_div, pow_zero, div_one]
    · cases h
  | neg a ih | pow a n ih =>
    intro N j h s hs
    simp only [inversion] at h
    split at h
    · rename_i na ja hA
      cases h
      simp only [eval, ih hA hs, neg_div, div_pow, pow_mul]
    · cases h
  | sin a ih | cos a ih | atan a ih | asin a ih | acos a ih | exp a ih | log a ih | sqrt a ih =>
    intro N j h s hs
    simp only [eval]
    exact inversionUnary_sound (fun _ _ ↦ rfl) (fun hA ↦ ih hA hs) h
  | rpow a b iha ihb =>
    intro N j h s hs
    simp only [inversion] at h
    split at h
    · rename_i na nb hA hB
      cases h
      simp [iha hA hs, ihb hB hs]
    · cases h

/-- **Limits at infinity.** The limit of `expr` at `+∞` (`above`) or `-∞` is the limit of
`N (t) / t ^ j` as `t → 0` from the right or the left. -/
theorem tendsto_of_inversion (expr N : Verified.Expr (Fin 1)) (j : ℕ)
    (h : inversion expr = some (N, j)) (above : Bool) {l : Filter ℝ}
    (hlim : Tendsto (fun t ↦ N.univariateEval t / (Verified.Expr.pow (.var 0) j).univariateEval t)
      (side ((0 : ℚ) : ℝ) above) l) :
    Tendsto (fun x ↦ expr.univariateEval x) (if above then atTop else atBot) l := by
  rw [Rat.cast_zero] at hlim
  have heq : ∀ x : ℝ, x ≠ 0 → expr.univariateEval x =
      N.univariateEval x⁻¹ / (Verified.Expr.pow (.var 0) j).univariateEval x⁻¹ := by
    intro x hx
    simp only [univariateEval, eval, Matrix.vec_single_eq_const]
    exact inversion_sound expr h hx
  cases above
  · refine (hlim.comp tendsto_inv_atBot_nhdsLT_zero).congr' ?_
    filter_upwards [eventually_lt_atBot 0] with x hx
    exact (heq x hx.ne).symm
  · refine (hlim.comp tendsto_inv_atTop_nhdsGT_zero).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact (heq x hx.ne').symm

/-! ## Transport to ordinary functions -/

/-- The univariate evaluation of an expression at `x` is its evaluation `expr.eval ![x]` at the
one-entry environment `![x]`. -/
theorem univariateEval_eq_eval (expr : Verified.Expr (Fin 1)) (x : ℝ) :
    expr.univariateEval x = expr.eval ![x] := by
  rw [univariateEval, euclideanSingle_eq_const, Matrix.vec_single_eq_const]

/-- A limit of a checked expression is a limit of the function it denotes, along the stated
source and target filters. -/
theorem tendsto_of_univariateEval {expr : Verified.Expr (Fin 1)} {f : ℝ → ℝ}
    {l l' m m' : Filter ℝ} (h : Tendsto (fun x ↦ expr.univariateEval x) l m)
    (hf : ∀ x, expr.eval ![x] = f x) (hl : l = l') (hm : m = m') : Tendsto f l' m' := by
  subst hl hm
  exact h.congr fun x ↦ by rw [univariateEval_eq_eval, hf]

/-- `tendsto_of_univariateEval` for the quotient form of `tendsto_div_of_check`. -/
theorem tendsto_div_of_univariateEval {num den : Verified.Expr (Fin 1)} {f : ℝ → ℝ}
    {l l' m m' : Filter ℝ}
    (h : Tendsto (fun x ↦ num.univariateEval x / den.univariateEval x) l m)
    (hf : ∀ x, (num.div den).eval ![x] = f x) (hl : l = l') (hm : m = m') :
    Tendsto f l' m' := by
  subst hl hm
  exact h.congr fun x ↦ by rw [univariateEval_eq_eval, univariateEval_eq_eval, ← hf]; rfl

end CAS.Verified.Expr
