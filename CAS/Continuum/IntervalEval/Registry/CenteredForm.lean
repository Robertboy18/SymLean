/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalEval.Registry.Monotonicity

/-!
# Centered-form interval evaluation on boxes

For a rational box `B` with midpoint `m` and an expression valid on `B`, the mean
value theorem along the segment from `m` to a point `x` of the box gives

`f x = f m + Σᵢ ∂ᵢf(c) · (xᵢ - mᵢ)` for some `c` on the segment,

so `f(B) ⊆ f(m) + Σᵢ ∂ᵢf(B) · (Bᵢ - mᵢ)`. Enclose `f m` by an interval `C`
and each partial derivative on the whole box by an interval `Dᵢ`. Using
`Bᵢ - mᵢ` for the coordinate displacement yields a centered enclosure of width
`width(C) + 2 Σᵢ radius(Bᵢ) · max |Dᵢ|`. The rational midpoint is exact, but
`C` need not be a singleton. This can sharpen the range even when the
derivatives change sign. In one dimension it is the classical form
`f(m) + f'(I) · (I - m)`.

## Main definitions

* `CertifiedEvalRegistry.PartialEnclosures`, `partialAttemptsOn?`: the labelled
  derivative enclosures along the non-degenerate coordinates of the box.
* `CertifiedEvalRegistry.centeredFormEnclosureAttempt?`: the checked
  centered-form enclosure of a box, with
  `CertifiedEvalRegistry.centeredFormEnclosurePreview?` as its proof-free width
  preview.

## Main results

* `CertifiedEvalRegistry.exists_eq_add_deriv_mul_sub`: the one-dimensional mean
  value theorem in centered form.
* `exists_mem_boxDomain_eval_eq_add_sum`: its multivariate consequence along the
  midpoint segment, with the symbolic partial derivatives.

## Implementation notes

The mean value form with the midpoint as center is classical: centered forms go back to Moore,
and Ratschek and Rokne give the inclusion property of `f(c) + (Y - c)ᵀ F'(Y)` with
`c = mid Y`. We prove that inclusion along the segment `t ↦ m + t • (x - m)`. Mathlib's
`exists_hasDerivAt_eq_slope` applied to the composite with `Verified.Expr.hasFDerivAt_eval`
gives the point `c`, and `symbolicFDeriv_apply_eq_sum` writes the derivative there as the sum
of the symbolic partials `expr.diff i`. The partials are symbolic expressions, enclosed by the
same registry as any other expression; there is no automatic differentiation.

`centeredFormAttempt` combines three independently checked ingredients: analytic validity of
the expression on the box (`validOn?`), which the derivative theorem requires; one derivative
enclosure per non-degenerate coordinate from the ordinary registry planner, after the same
optional normalizations as the monotonicity route; and an enclosure of `f m` from the registry
of the degenerate midpoint box. A degenerate coordinate has `xᵢ - mᵢ = 0` and needs no
derivative. The route fails closed when a partial derivative cannot be enclosed, and the caller
keeps the natural, affine or monotonicity route. The mean value form can be wider than the
natural extension, in particular on wide boxes, so the box planner compares the proof-free
previews of the routes and builds the certificate of the sharpest one first.

## References

* Ramon E. Moore, *Interval Analysis*, Prentice-Hall, Englewood Cliffs, N.J., 1966,
  <https://zbmath.org/?q=an:0176.13301>. Cited for interval mean value theorems.
* Ramon E. Moore, R. Baker Kearfott and Michael J. Cloud, *Introduction to Interval Analysis*,
  SIAM, Philadelphia, 2009, <https://doi.org/10.1137/1.9780898717716>. Chapter 6 for centered
  forms.
* Helmut Ratschek and Jon Rokne, *Computer Methods for the Range of Functions*, Ellis Horwood,
  Chichester, 1984, <https://zbmath.org/?q=an:0584.65019>.
* Helmut Ratschek and Jon Rokne, *New Computer Methods for Global Optimization*, Ellis Horwood,
  Chichester, 1988, <https://pages.cpsc.ucalgary.ca/~rokne/global_book.pdf>. Section 2.7 for
  the mean value form and its inclusion property.
-/

@[expose] public section

namespace CAS.Continuum
namespace RationalInterval

open Set
open CAS.Certificate
open CAS.Verified

namespace CertifiedEvalRegistry

/--
The mean value theorem in centered form: on a closed interval, a differentiable
function satisfies `f x = f m + f' c · (x - m)` for some `c` in the interval.
-/
theorem exists_eq_add_deriv_mul_sub {f f' : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    {m x : ℝ} (hm : m ∈ Icc a b) (hx : x ∈ Icc a b) :
    ∃ c ∈ Icc a b, f x = f m + f' c * (x - m) := by
  rcases lt_trichotomy x m with hlt | rfl | hgt
  · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f f' hlt
      (hcont.mono (Icc_subset_Icc hx.1 hm.2))
      (fun y hy ↦ hderiv y ⟨hx.1.trans hy.1.le, hy.2.le.trans hm.2⟩)
    refine ⟨c, ⟨hx.1.trans hc.1.le, hc.2.le.trans hm.2⟩, ?_⟩
    rw [hslope, ← neg_sub m x, mul_neg, div_mul_cancel₀ _ (sub_ne_zero.mpr hlt.ne')]
    ring
  · exact ⟨x, hx, by ring⟩
  · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f f' hgt
      (hcont.mono (Icc_subset_Icc hm.1 hx.2))
      (fun y hy ↦ hderiv y ⟨hm.1.trans hy.1.le, hy.2.le.trans hx.2⟩)
    refine ⟨c, ⟨hm.1.trans hc.1.le, hc.2.le.trans hx.2⟩, ?_⟩
    rw [hslope, div_mul_cancel₀ _ (sub_ne_zero.mpr hgt.ne')]
    ring

end CertifiedEvalRegistry

/-! ## The midpoint of a box -/

/-- The degenerate box consisting of the midpoint of every coordinate interval. -/
def centerBox {n : ℕ} (box : Fin n → RationalInterval) : Fin n → RationalInterval :=
  fun i ↦ const (box i).center

/-- The midpoint of a rational box as a Euclidean point. -/
noncomputable def boxCenter {n : ℕ} (box : Fin n → RationalInterval) : ℝ^n :=
  WithLp.toLp 2 fun i ↦ ((box i).center : ℝ)

/-- The coordinates of the box midpoint are the coordinate midpoints. -/
@[simp] theorem boxCenter_apply {n : ℕ} (box : Fin n → RationalInterval) (i : Fin n) :
    boxCenter box i = ((box i).center : ℝ) :=
  rfl

/-- The midpoint of a box lies in the box. -/
theorem boxCenter_mem_boxDomain {n : ℕ} (box : Fin n → RationalInterval) :
    boxCenter box ∈ boxDomain box :=
  fun i ↦ RationalInterval.center_memReal (box i)

/-- The midpoint of a box is the unique point of its midpoint box. -/
theorem boxCenter_mem_centerBox {n : ℕ} (box : Fin n → RationalInterval) :
    boxCenter box ∈ boxDomain (centerBox box) :=
  fun i ↦ memReal_const (box i).center

/-! ## The mean value theorem along the midpoint segment -/

/--
The formal Fréchet derivative applied to a vector is the coordinate-weighted sum
of the evaluated symbolic partial derivatives.
-/
theorem symbolicFDeriv_apply_eq_sum {n : ℕ} (expr : Verified.Expr (Fin n)) (p : ℝ^n)
    (v : ℝ^n) :
    Verified.Expr.symbolicFDeriv expr p v = ∑ i, v i * (expr.diff i).eval p := by
  have hv : ∑ i, v i • EuclideanSpace.single i (1 : ℝ) = v := by
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  conv_lhs => rw [← hv]
  simp [map_sum, Verified.Expr.symbolicFDeriv_apply_single_eq_diff_eval expr p _]

/--
The mean value theorem along the segment from `m` to `x` inside a box, in
centered form with the symbolic partial derivatives: some point `c` of the box
satisfies `f x = f m + Σᵢ ∂ᵢf(c) · (xᵢ - mᵢ)`.
-/
theorem exists_mem_boxDomain_eval_eq_add_sum {n : ℕ} (box : Fin n → RationalInterval)
    (expr : Verified.Expr (Fin n))
    (hvalid : ∀ y ∈ boxDomain box, expr.ValidAt fun j ↦ y j)
    {m x : ℝ^n} (hm : m ∈ boxDomain box) (hx : x ∈ boxDomain box) :
    ∃ c ∈ boxDomain box,
      expr.eval (fun j ↦ x j) =
        expr.eval (fun j ↦ m j) + ∑ i, (expr.diff i).eval (fun j ↦ c j) * (x i - m i) := by
  let segment : ℝ → ℝ^n := fun t ↦ m + t • (x - m)
  have hsegment : ∀ t, HasDerivAt segment (x - m) t := fun t ↦ by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const (x - m)).const_add m
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, segment t ∈ boxDomain box := fun t ht j ↦ by
    simpa [segment, MemReal, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply] using
      (convex_Icc ((box j).lo : ℝ) ((box j).hi : ℝ)).add_smul_sub_mem (hm j) (hx j) ht
  let g : ℝ → ℝ := fun t ↦ expr.eval (segment t)
  let g' : ℝ → ℝ := fun t ↦ Verified.Expr.symbolicFDeriv expr (segment t) (x - m)
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g (g' t) t := fun t ht ↦ by
    simpa [Function.comp_def, g, g'] using
      (Verified.Expr.hasFDerivAt_eval expr (segment t) (hvalid _ (hmem t ht))).comp_hasDerivAt
        t (hsegment t)
  obtain ⟨c, hc, hvalue⟩ := CertifiedEvalRegistry.exists_eq_add_deriv_mul_sub
    (HasDerivAt.continuousOn hderiv) hderiv (left_mem_Icc.mpr zero_le_one)
    (right_mem_Icc.mpr zero_le_one)
  refine ⟨segment c, hmem c hc, ?_⟩
  simp only [g, g', show segment 1 = x by simp [segment], show segment 0 = m by simp [segment],
    sub_zero, mul_one] at hvalue
  rw [hvalue, symbolicFDeriv_apply_eq_sum expr (segment c) (x - m)]
  simp [PiLp.sub_apply, mul_comm]

/-! ## Degenerate coordinates -/

/-- The coordinates of a box whose intervals are not degenerate. -/
def wideCoordinates {n : ℕ} (box : Fin n → RationalInterval) : List (Fin n) :=
  (List.finRange n).filter fun i ↦ decide ((box i).lo < (box i).hi)

/-- On a degenerate coordinate every box point coincides with the midpoint. -/
theorem sub_boxCenter_eq_zero_of_not_lt {n : ℕ} (box : Fin n → RationalInterval) {x : ℝ^n}
    (hx : x ∈ boxDomain box) {i : Fin n} (hdegenerate : ¬ (box i).lo < (box i).hi) :
    x i - boxCenter box i = 0 := by
  have heq : ((box i).lo : ℝ) = (box i).hi := by
    exact_mod_cast le_antisymm (box i).hle (not_lt.mp hdegenerate)
  push_cast [boxCenter_apply, RationalInterval.center]
  linarith [(hx i).1, (hx i).2]

/-- Terms that vanish outside a filter may be dropped from a list sum. -/
theorem sum_map_filter_eq_of_eq_zero {β : Type*} (p : β → Bool) (t : β → ℝ) :
    ∀ l : List β, (∀ i ∈ l, p i = false → t i = 0) →
      (l.map t).sum = ((l.filter p).map t).sum
  | [], _ => rfl
  | i :: rest, h => by
      have ih := sum_map_filter_eq_of_eq_zero p t rest fun j hj hp ↦ h j (by simp [hj]) hp
      cases hp : p i <;> simp [hp, ih, h i (by simp)]

/-! ## Interval assembly -/

/-- The exact interval sum of a list of intervals. -/
def sumList : List RationalInterval → RationalInterval
  | [] => const 0
  | I :: rest => I.add (sumList rest)

/-- The interval sum over a list contains the corresponding real sum. -/
theorem memReal_sumList_map {β : Type*} (f : β → RationalInterval) (g : β → ℝ) :
    ∀ l : List β, (∀ i ∈ l, (f i).MemReal (g i)) →
      (sumList (l.map f)).MemReal (l.map g).sum
  | [], _ => by simpa [sumList] using memReal_const 0
  | i :: rest, h =>
      add_sound (h i (by simp)) (memReal_sumList_map f g rest fun j hj ↦ h j (by simp [hj]))

/--
The centered remainder `Σᵢ Dᵢ · (boxᵢ - mᵢ)` of a box with midpoint `m`, from
partial-derivative intervals `Dᵢ` labelled by their coordinates.
-/
def centeredRemainder {n : ℕ} (box : Fin n → RationalInterval)
    (partials : List (Fin n × RationalInterval)) : RationalInterval :=
  sumList (partials.map fun term ↦ term.2.mul ((box term.1).sub (const (box term.1).center)))

namespace CertifiedEvalRegistry

variable {α : Type*} {n : ℕ} {s : Set α} {ρ : α → Fin n → ℝ}

/--
Checked enclosures of the partial derivatives along a list of coordinates, one
labelled entry per coordinate in the order of the list.
-/
structure PartialEnclosures {α : Type*} {n : ℕ} (s : Set α) (ρ : α → Fin n → ℝ)
    (expr : Verified.Expr (Fin n)) (coordinates : List (Fin n)) where
  /-- The labelled derivative enclosures. -/
  attempts : List (Σ i : Fin n, EnclosureAttempt α s (fun x ↦ (expr.diff i).eval (ρ x)))
  /-- The labels are the requested coordinates, in order. -/
  labels : attempts.map Sigma.fst = coordinates

/--
Checked enclosures of the partial derivatives along the listed coordinates, or
`none` as soon as one of them cannot be enclosed.
-/
noncomputable def partialAttemptsOn? (r : CertifiedEvalRegistry s ρ)
    (expr : Verified.Expr (Fin n)) :
    (coordinates : List (Fin n)) → Option (PartialEnclosures s ρ expr coordinates)
  | [] => some ⟨[], rfl⟩
  | i :: rest => do
      let head ← partialAttempt? r expr i
      let tail ← partialAttemptsOn? r expr rest
      some ⟨⟨i, head⟩ :: tail.attempts, by rw [List.map_cons, tail.labels]⟩

/--
Assemble the centered form from its checked ingredients.

The interval is `center + Σᵢ ∂ᵢ · (boxᵢ - mᵢ)` over the non-degenerate
coordinates of the box; on a degenerate coordinate the factor `xᵢ - mᵢ` is
exactly zero, so no derivative enclosure is needed there. The mean value
theorem along the midpoint segment, the derivative theorem for the symbolic
partial derivatives, and the interval arithmetic soundness theorems establish
the enclosure.
-/
noncomputable def centeredFormAttempt {n : ℕ} (box : Fin n → RationalInterval)
    (expr : Verified.Expr (Fin n))
    (validity : CertificateRoute (∀ x, x ∈ boxDomain box → expr.ValidAt fun j ↦ x j))
    (partials : PartialEnclosures (boxDomain box) (fun x : ℝ^n ↦ fun j ↦ x j) expr
      (wideCoordinates box))
    (center : EnclosureAttempt (ℝ^n) (boxDomain (centerBox box))
      (fun x ↦ expr.eval fun j ↦ x j)) :
    EnclosureAttempt (ℝ^n) (boxDomain box) (fun x ↦ expr.eval fun j ↦ x j) where
  interval :=
    center.interval.add
      (centeredRemainder box (partials.attempts.map fun entry ↦ (entry.1, entry.2.interval)))
  sound := by
    intro x hx
    obtain ⟨c, hc, hvalue⟩ :=
      exists_mem_boxDomain_eval_eq_add_sum box expr validity.cert (boxCenter_mem_boxDomain box) hx
    change (center.interval.add _).MemReal (expr.eval fun j ↦ x j)
    rw [hvalue, Fin.sum_univ_def,
      sum_map_filter_eq_of_eq_zero (fun i ↦ decide ((box i).lo < (box i).hi)) _ (List.finRange n)
        fun i _ hdegenerate ↦ by
          rw [sub_boxCenter_eq_zero_of_not_lt box hx (by simpa using hdegenerate), mul_zero]]
    refine add_sound (center.memReal (boxCenter_mem_centerBox box)) ?_
    have hlabels :
        ((List.finRange n).filter fun i ↦ decide ((box i).lo < (box i).hi)) =
          partials.attempts.map Sigma.fst :=
      partials.labels.symm
    rw [hlabels, List.map_map]
    unfold centeredRemainder
    rw [List.map_map]
    exact memReal_sumList_map _ _ partials.attempts fun entry _ ↦
      mul_sound (entry.2.memReal hc)
        (sub_sound (hx entry.1) (memReal_const (box entry.1).center))
  steps := .centeredForm ::
    (validity.steps ++ partials.attempts.flatMap (fun entry ↦ entry.2.steps) ++ center.steps)

/--
Whether the centered form may sharpen a simplified expression on a box: the
derivative routes apply and no partial derivative retains a square root.
-/
def centeredFormApplies {n : ℕ} (box : Fin n → RationalInterval)
    (expr : Verified.Expr (Fin n)) : Bool :=
  derivativeRoutesApply box expr &&
    (List.finRange n).all fun i ↦ !expr.containsVar i || !containsSquareRoot (expr.diff i)

/--
Preview the centered-form enclosure without constructing a proof object.

The preview lets a caller compare this route with the natural, affine, and
monotonicity routes before constructing the selected certificate.
-/
noncomputable def centeredFormEnclosurePreview? {n : ℕ} (precision : Precision)
    (box : Fin n → RationalInterval) (expr : Verified.Expr (Fin n)) :
    Option PlannerSummary := do
  let registry := boxRegistry box precision
  let partials ← (wideCoordinates box).mapM fun i ↦
    (partialPlan? registry expr i).map fun plan ↦ (i, plan.2)
  let center ← (boxRegistry (centerBox box) precision).selectFiniteEnclosurePreview? expr
  pure {
    kind := .easy
    interval :=
      center.interval.add
        (centeredRemainder box (partials.map fun term ↦ (term.1, term.2.interval)))
    stepCount :=
      partials.foldl (fun count term ↦ count + term.2.stepCount) center.stepCount + 1 }

/--
Try to certify a box range by the centered form
`f(B) ⊆ f(m) + Σᵢ ∂ᵢf(B) · (Bᵢ - mᵢ)`.

Every ingredient is a checked certificate; the route selection inside the
derivative planner is untrusted and only decides which certificates are built.
-/
noncomputable def centeredFormEnclosureAttempt? {n : ℕ} (precision : Precision)
    (box : Fin n → RationalInterval) (expr : Verified.Expr (Fin n)) :
    Option (EnclosureAttempt (ℝ^n) (boxDomain box) (fun x ↦ expr.eval fun j ↦ x j)) := do
  let registry := boxRegistry box precision
  let validity ← registry.validOn? expr
  let partials ← partialAttemptsOn? registry expr (wideCoordinates box)
  let center ← (boxRegistry (centerBox box) precision).selectFiniteEnclosureAttempt? expr
  some (centeredFormAttempt box expr validity partials center)

end CertifiedEvalRegistry
end RationalInterval
end CAS.Continuum
