/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalEval.Digits
public import CAS.Continuum.Quadrature.CompositeSimpson
public import CAS.Continuum.SymbolicDerivativeBounds

/-!
# Composite Simpson enclosures in one kernel check

`panels (panel p f d) a h n` encloses `∫ x in a..a + n h, f x` by `n` Simpson panels of width
`h`. `panels` and its soundness `panels_sound` are stated once for every panel enclosure, so the
range panels of `BatchRange` use them too. On
each panel the fourth derivative is bounded by evaluating the expression `d` on the panel with
the precision-parametric interval evaluator `DigitsEval.eval`, where `d` is the simplified
fourth symbolic derivative `f.symbolicDerivative 4`; the three samples are interval values of
`f`. The whole composite enclosure is one closed computation, so a single kernel evaluation of
`integralCheck` checks every panel, instead of one proof term per panel.

`of_integralCheck` gives `lo ≤ ∫ x in a..b, f x ≤ hi` from a passing check and the validity of
`f` and its first four symbolic derivatives on `[a, b]`; `of_integralCheck_abs` states
`|∫ x in a..b, f x - c| ≤ ε`.

## Implementation notes

The search is compiled code in the command and tactic layers. `#cas [nintegrate]`
(`CAS.Command.NIntegrate.batchSearch`) runs `panels` with `N = 4, 8, …, 1024` panels until the
enclosure fixes the requested decimals, and bare `cega` (`CAS.CEGA.Integration`) doubles `N`
from one. Both hand only `N`, the precision and the bounds to the kernel, which evaluates
`integralCheck`: it decides the syntactic equality `f.symbolicDerivative 4 = d`, computes the
`2 N + 1` samples and the `N` derivative enclosures of `sharedPanels`, and compares the sum with
`[lo, hi]`.

Every panel rests on `simpsonRule.enclosure_sound`, that is, on the Peano-kernel estimate
`norm_integral_sub_simpsonRule_valueOn_le` of `CAS.Continuum.Quadrature.SimpsonPeano`, with the
bound `M = D.absMax` for the interval `D` that `DigitsEval.eval` returns for `d` on the panel;
`intervalIntegral.integral_add_adjacent_intervals` glues the panels together. Enclosing a Simpson
sum and its remainder in interval arithmetic is classical (Rump, Section 12). We bound the fourth
derivative on each panel rather than once on `[a, b]`, and the reduction of the whole composite
rule to one Boolean that the kernel evaluates is ours.

## References

* Siegfried M. Rump, "Verification methods: Rigorous results using floating-point arithmetic",
  *Acta Numerica* 19 (2010), pp. 287-449, <https://doi.org/10.1017/S096249291000005X>.
  Theorem 12.1 is the composite Simpson rule with the remainder `h⁴ (b - a) f⁽⁴⁾(ξ) / 180`, `h`
  the node spacing (half our panel width), and Algorithm 12.2 encloses the integral by
  evaluating the sum and that remainder in interval arithmetic.
-/

@[expose] public section

namespace CAS.Continuum

open Set RationalInterval CAS.Verified

/-- `n` panels of width `h` from `a`: the sum of the enclosures `panel l r` of the panels
`[a + k h, a + (k + 1) h]` for `k < n`, or `none` once one of them is `none`. -/
def panels (panel : ℚ → ℚ → Option RationalInterval) (a h : ℚ) : ℕ → Option RationalInterval
  | 0 => some (const 0)
  | n + 1 => do
      let rest ← panels panel a h n
      let I ← panel (a + n * h) (a + (n + 1) * h)
      some (rest.add I)

/-- For `0 < h` and `n < N`, panel `n` of width `h` from `a` lies in `[a, a + N h]`. -/
theorem Icc_panel_subset {a h : ℚ} (hh : 0 < h) {n N : ℕ} (hn : n < N) :
    Icc ((a + n * h : ℚ) : ℝ) ((a + (n + 1) * h : ℚ) : ℝ) ⊆ Icc (a : ℝ) ((a + N * h : ℚ) : ℝ) := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hN : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn
  apply Icc_subset_Icc <;> push_cast <;> nlinarith

/-- **Panel sums.** If `g` is interval integrable on `[a, a + N h]` with `0 < h`, and each of the
first `N` panels encloses the integral of `g` over its interval whenever it returns, then the
first `n ≤ N` panels enclose `∫ x in a..a + n h, g x`. This holds for every panel enclosure
`panel`. -/
theorem panels_sound {panel : ℚ → ℚ → Option RationalInterval} {g : ℝ → ℝ} {a h : ℚ}
    (hh : 0 < h) {N : ℕ} (hg : IntervalIntegrable g MeasureTheory.volume a ((a + N * h : ℚ) : ℝ))
    (hpanel : ∀ n < N, ∀ I, panel (a + n * h) (a + (n + 1) * h) = some I →
      I.MemReal (∫ x in ((a + n * h : ℚ) : ℝ)..((a + (n + 1) * h : ℚ) : ℝ), g x)) :
    ∀ n ≤ N, ∀ I, panels panel a h n = some I →
      I.MemReal (∫ x in (a : ℝ)..((a + n * h : ℚ) : ℝ), g x)
  | 0, _, I, hI => by
      cases hI
      simpa using memReal_const 0
  | n + 1, hn, I, hI => by
      simp only [panels, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hI
      obtain ⟨rest, hrest, J, hJ, rfl⟩ := hI
      have hh' : (0 : ℝ) < h := by exact_mod_cast hh
      have hN : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn
      have hab : (a : ℝ) ≤ ((a + N * h : ℚ) : ℝ) := by push_cast; nlinarith
      have hint (u v : ℝ) (hu : (a : ℝ) ≤ u) (huv : u ≤ v)
          (hv : v ≤ ((a + N * h : ℚ) : ℝ)) :
          IntervalIntegrable g MeasureTheory.volume u v :=
        hg.mono_set (by
          rw [uIcc_of_le huv, uIcc_of_le hab]
          exact Icc_subset_Icc hu hv)
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hint (a : ℝ) ((a + n * h : ℚ) : ℝ) le_rfl (by push_cast; nlinarith)
          (by push_cast; nlinarith))
        (hint ((a + n * h : ℚ) : ℝ) ((a + (n + 1) * h : ℚ) : ℝ) (by push_cast; nlinarith)
          (by push_cast; nlinarith) (by push_cast; nlinarith))
      have hcast : ((a + ((n + 1 : ℕ) : ℚ) * h : ℚ) : ℝ) = ((a + (n + 1) * h : ℚ) : ℝ) := by
        push_cast
        ring
      rw [hcast, ← hsplit]
      exact add_sound (panels_sound hh hg hpanel n (Nat.le_of_succ_le hn) rest hrest)
        (hpanel n hn J hJ)

/-- Once `panels` fails, it fails for every larger panel count. -/
theorem panels_add_eq_none {panel : ℚ → ℚ → Option RationalInterval} {a h : ℚ} {m : ℕ}
    (hm : panels panel a h m = none) : ∀ j, panels panel a h (m + j) = none
  | 0 => hm
  | j + 1 => by
      rw [← Nat.add_assoc, panels, panels_add_eq_none hm j]
      rfl

namespace BatchSimpson

/-- The one-coordinate environment with value interval `I`. -/
def env (I : RationalInterval) : Fin 1 → RationalInterval := fun _ ↦ I

/-- If `x` lies in `I`, the environment `env I` encloses the one-coordinate point `!₂[x]` in every
coordinate. -/
theorem env_sound {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) :
    ∀ i, (env I i).MemReal ((!₂[x] : EuclideanSpace ℝ (Fin 1)) i) := by
  intro i
  fin_cases i
  simpa [env] using hx

/-- The Simpson enclosure of one panel `[l, r]`. -/
def panel (p : DigitsEval.Precision) (f d : Verified.Expr (Fin 1)) (l r : ℚ) :
    Option RationalInterval :=
  if hlr : l < r then do
    let D ← DigitsEval.eval p (env (ofBounds l r hlr.le)) d
    let fl ← DigitsEval.eval p (env (const l)) f
    let fm ← DigitsEval.eval p (env (const ((l + r) / 2))) f
    let fr ← DigitsEval.eval p (env (const r)) f
    some (simpsonRule.enclosure l r D.absMax hlr.le (absMax_nonneg D) fl fm fr)
  else none

private theorem sample_sound {p : DigitsEval.Precision} {f : Verified.Expr (Fin 1)} {q : ℚ}
    {I : RationalInterval} (h : DigitsEval.eval p (env (const q)) f = some I) :
    I.MemReal (f.univariateEval q) :=
  DigitsEval.eval_sound p _ _ (env_sound (memReal_const q)) f h

/-- One panel encloses its integral. -/
theorem panel_sound {p : DigitsEval.Precision} {f d : Verified.Expr (Fin 1)} {l r : ℚ}
    {I : RationalInterval} (hd : f.symbolicDerivative 4 = d)
    (hvalid : f.ValidIteratesOn 5 (Icc (l : ℝ) r)) (h : panel p f d l r = some I) :
    I.MemReal (∫ x in (l : ℝ)..r, f.univariateEval x) := by
  unfold panel at h
  split at h
  · rename_i hlr
    have hlr' : (l : ℝ) < r := by exact_mod_cast hlr
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨D, hD, fl, hl, fm, hm, fr, hr, rfl⟩ := h
    refine simpsonRule.enclosure_sound l r D.absMax hlr (absMax_nonneg D) fl fm fr
      (Verified.Expr.contDiffOn_univariateEval f 4 (uniqueDiffOn_Icc hlr') hvalid) ?_
      (sample_sound hl) (sample_sound hm) (sample_sound hr)
    intro x hx
    rw [Verified.Expr.iteratedDerivWithin_univariateEval_eq_symbolicDerivative f 4
      (uniqueDiffOn_Icc hlr') (hvalid.mono (by norm_num)) hx, hd, Real.norm_eq_abs]
    exact abs_le_absMax
      (DigitsEval.eval_sound p _ _ (env_sound (memReal_ofBounds hlr.le hx)) d hD)
  · cases h

/-! ## Shared endpoint samples

Adjacent panels share an endpoint, and `panels` samples `f` there twice: once as the right
endpoint `a + (n + 1) * h` of panel `n` and once as the left endpoint `a + ↑(n + 1) * h` of panel
`n + 1`. The two points are equal rationals but different terms, so the kernel, which caches
evaluations by term, evaluates both. `sharedPanels` computes the same enclosure with the sample at
every grid point taken once, `2 N + 1` samples of `f` instead of `3 N`, by handing the right sample
of each panel to the next (`panelStep`, `panelsFrom`); `sharedPanels_eq_panels` shows that it
returns exactly what `panels` returns, so `integralCheck` uses it. On `exp (-x ^ 2)` with 16
panels the kernel evaluation drops from 9.0 s to 6.7 s. -/

/-- The Simpson panel `[l, r]` from the sample `fl` of `f` at `l`: its enclosure and the sample of
`f` at `r`, which is the left sample of the next panel. -/
def panelStep (p : DigitsEval.Precision) (f d : Verified.Expr (Fin 1)) (l r : ℚ)
    (fl : RationalInterval) : Option (RationalInterval × RationalInterval) :=
  if hlr : l < r then do
    let D ← DigitsEval.eval p (env (ofBounds l r hlr.le)) d
    let fm ← DigitsEval.eval p (env (const ((l + r) / 2))) f
    let fr ← DigitsEval.eval p (env (const r)) f
    some (simpsonRule.enclosure l r D.absMax hlr.le (absMax_nonneg D) fl fm fr, fr)
  else none

/-- `panel` is `panelStep` after sampling the left endpoint. -/
theorem panel_eq_bind_panelStep (p : DigitsEval.Precision) (f d : Verified.Expr (Fin 1))
    (l r : ℚ) :
    panel p f d l r = (DigitsEval.eval p (env (const l)) f).bind fun fl ↦
      (panelStep p f d l r fl).map Prod.fst := by
  unfold panel panelStep
  split
  · rename_i hlr
    cases DigitsEval.eval p (env (ofBounds l r hlr.le)) d <;>
      cases DigitsEval.eval p (env (const l)) f <;>
      cases DigitsEval.eval p (env (const ((l + r) / 2))) f <;>
      cases DigitsEval.eval p (env (const r)) f <;> rfl
  · cases DigitsEval.eval p (env (const l)) f <;> rfl

/-- The second component of `panelStep` is the sample of `f` at the right endpoint. -/
theorem eval_right_of_panelStep {p : DigitsEval.Precision} {f d : Verified.Expr (Fin 1)}
    {l r : ℚ} {fl I fr : RationalInterval} (h : panelStep p f d l r fl = some (I, fr)) :
    DigitsEval.eval p (env (const r)) f = some fr := by
  unfold panelStep at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨_, _, _, _, right, hright, _, rfl⟩ := h
    exact hright
  · cases h

/-- The panels `k, …, k + n - 1` of width `h` from `a`, added in order to `acc`, where `left` is
the sample of `f` at the left endpoint `a + k * h` of panel `k`. -/
def panelsFrom (p : DigitsEval.Precision) (f d : Verified.Expr (Fin 1)) (a h : ℚ) :
    ℕ → ℕ → RationalInterval → RationalInterval → Option RationalInterval
  | _, 0, acc, _ => some acc
  | k, n + 1, acc, left => do
      let (I, right) ← panelStep p f d (a + k * h) (a + (k + 1) * h) left
      panelsFrom p f d a h (k + 1) n (acc.add I) right

/-- `panels` with every grid point sampled once: the same enclosure (`sharedPanels_eq_panels`). -/
def sharedPanels (p : DigitsEval.Precision) (f d : Verified.Expr (Fin 1)) (a h : ℚ) :
    ℕ → Option RationalInterval
  | 0 => some (const 0)
  | n + 1 => do
      let left ← DigitsEval.eval p (env (const a)) f
      panelsFrom p f d a h 0 (n + 1) (const 0) left

/-- `panelsFrom` continues `panels`: from the enclosure of the first `k` panels and the sample at
`a + k * h`, it computes the enclosure of the first `k + n`. -/
theorem panelsFrom_eq_panels {p : DigitsEval.Precision} {f d : Verified.Expr (Fin 1)}
    {a h : ℚ} : ∀ (n k : ℕ) (acc left : RationalInterval),
      panels (panel p f d) a h k = some acc →
      DigitsEval.eval p (env (const (a + k * h))) f = some left →
      panelsFrom p f d a h k n acc left = panels (panel p f d) a h (k + n)
  | 0, k, acc, left, hacc, _ => by simp [panelsFrom, hacc]
  | n + 1, k, acc, left, hacc, hleft => by
      have hstep : panels (panel p f d) a h (k + 1) =
          (panelStep p f d (a + k * h) (a + (k + 1) * h) left).map fun step ↦ acc.add step.1 := by
        rw [panels, hacc, panel_eq_bind_panelStep, hleft]
        simp only [Option.bind_eq_bind, Option.bind_some]
        cases panelStep p f d (a + k * h) (a + (k + 1) * h) left <;> rfl
      rw [show k + (n + 1) = k + 1 + n by omega]
      cases hcase : panelStep p f d (a + k * h) (a + (k + 1) * h) left with
      | none =>
          rw [hcase] at hstep
          simp only [panelsFrom, hcase, Option.bind_eq_bind, Option.bind_none]
          exact (panels_add_eq_none hstep n).symm
      | some step =>
          obtain ⟨I, right⟩ := step
          rw [hcase] at hstep
          have hright : DigitsEval.eval p (env (const (a + ((k + 1 : ℕ) : ℚ) * h))) f =
              some right := by
            push_cast
            exact eval_right_of_panelStep hcase
          simp only [panelsFrom, hcase, Option.bind_eq_bind, Option.bind_some]
          exact panelsFrom_eq_panels n (k + 1) (acc.add I) right hstep hright

/-- `sharedPanels` computes exactly the enclosure of `panels`. -/
theorem sharedPanels_eq_panels (p : DigitsEval.Precision) (f d : Verified.Expr (Fin 1))
    (a h : ℚ) : ∀ N, sharedPanels p f d a h N = panels (panel p f d) a h N
  | 0 => rfl
  | n + 1 => by
      have hzero : a + ((0 : ℕ) : ℚ) * h = a := by simp
      cases hleft : DigitsEval.eval p (env (const a)) f with
      | none =>
          have hfirst : panels (panel p f d) a h 1 = none := by
            rw [panels, panels, panel_eq_bind_panelStep]
            simp [hleft]
          simp only [sharedPanels, hleft, Option.bind_eq_bind, Option.bind_none]
          rw [show n + 1 = 1 + n by omega]
          exact (panels_add_eq_none hfirst n).symm
      | some left =>
          simp only [sharedPanels, hleft, Option.bind_eq_bind, Option.bind_some]
          rw [panelsFrom_eq_panels (n + 1) 0 (const 0) left rfl (by rw [hzero]; exact hleft),
            Nat.zero_add]

/-- The enclosure of `∫ x in a..b, f x` by `N` panels lies in `[lo, hi]`, and `d` is the
fourth symbolic derivative of `f`. -/
def integralCheck (p : DigitsEval.Precision) (f d : Verified.Expr (Fin 1)) (a b : ℚ) (N : ℕ)
    (lo hi : ℚ) : Bool :=
  decide (f.symbolicDerivative 4 = d) && decide (0 < N) && decide (a < b) &&
    match sharedPanels p f d a ((b - a) / N) N with
    | some I => decide (lo ≤ I.lo) && decide (I.hi ≤ hi)
    | none => false

/-- **Batch Simpson certificate.** -/
theorem of_integralCheck {p : DigitsEval.Precision} {f d : Verified.Expr (Fin 1)} {a b : ℚ}
    {N : ℕ} {lo hi : ℚ} (hvalid : f.ValidIteratesOn 5 (Icc (a : ℝ) b))
    (h : integralCheck p f d a b N lo hi = true) :
    (lo : ℝ) ≤ ∫ x in (a : ℝ)..b, f.univariateEval x ∧
      ∫ x in (a : ℝ)..b, f.univariateEval x ≤ hi := by
  unfold integralCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hd, hN⟩, hab⟩, hrest⟩ := h
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hend : a + N * ((b - a) / N) = b := by field_simp; ring
  have hh : 0 < (b - a) / N := div_pos (sub_pos.mpr hab) (by exact_mod_cast hN)
  split at hrest
  · rename_i I hI
    rw [sharedPanels_eq_panels] at hI
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hrest
    have hab' : (a : ℝ) < b := by exact_mod_cast hab
    have hvalid' : f.ValidIteratesOn 5 (Icc (a : ℝ) ((a + N * ((b - a) / N) : ℚ) : ℝ)) := by
      rwa [hend]
    have hint : IntervalIntegrable f.univariateEval MeasureTheory.volume (a : ℝ)
        ((a + N * ((b - a) / N) : ℚ) : ℝ) := by
      rw [hend]
      exact (Verified.Expr.contDiffOn_univariateEval f 0 (uniqueDiffOn_Icc hab')
        (hvalid.mono (by norm_num))).continuousOn.intervalIntegrable_of_Icc hab'.le
    have hmem := panels_sound hh hint (fun n hn J hJ ↦ panel_sound hd
      (fun k hk x hx ↦ hvalid' k hk x (Icc_panel_subset hh hn hx)) hJ) N le_rfl I hI
    rw [hend] at hmem
    exact ⟨(Rat.cast_le.mpr hrest.1).trans hmem.1, hmem.2.trans (Rat.cast_le.mpr hrest.2)⟩
  · cases hrest

/-- The integral within `ε` of `c`, from a check on `[c - ε, c + ε]`. -/
theorem of_integralCheck_abs {p : DigitsEval.Precision} {f d : Verified.Expr (Fin 1)} {a b : ℚ}
    {N : ℕ} {c ε : ℚ} (hvalid : f.ValidIteratesOn 5 (Icc (a : ℝ) b))
    (h : integralCheck p f d a b N (c - ε) (c + ε) = true) :
    |(∫ x in (a : ℝ)..b, f.univariateEval x) - c| ≤ ε := by
  have hb := of_integralCheck hvalid h
  push_cast at hb
  rw [abs_sub_le_iff]
  constructor <;> linarith [hb.1, hb.2]

end BatchSimpson
end CAS.Continuum
