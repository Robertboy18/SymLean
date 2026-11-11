/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.AffineArithmetic
public import CAS.Expr.Syntax

/-!
# Affine-arithmetic evaluation of expressions

`compileAffine? box` compiles the polynomial fragment of `Verified.Expr` into an `AffineModel`
over a rational box. Each variable `xᵢ` becomes `center + radius * εᵢ`, with one unit noise
symbol `εᵢ` per variable, so repeated occurrences of a variable stay correlated, which ordinary
interval evaluation forgets. Rational constants with nonzero denominator, variables, addition,
subtraction, negation, multiplication and natural powers (by binary exponentiation) are
accepted. Every other operation, including division and the transcendental functions, makes the
compiler return `none`. `affineRange?` returns the range of the compiled model, and the registry
planner turns it into an `EnclosureAttempt`.

## Main results

* `represents_recenter_of_compileAffine?_eq_some`: the compiled model represents the value of the
  expression at `recenter box ε` for every `ε` with `|εᵢ| ≤ 1`.
* `mem_affineRange_of_memBox`: a successful `affineRange?` contains `expr.eval x` for every point
  `x` of the box.

## Implementation notes

Replacing each input interval by an affine form `center + radius * εᵢ` with its own noise symbol and
evaluating the expression in affine arithmetic is the classical use of affine arithmetic (Andrade,
Comba and Stolfi); the forms and their product are in `CAS.Continuum.AffineArithmetic`. Sums and
negations keep the affine part exact, while products and powers move their nonlinear terms into the
interval remainder, where correlations are lost. The soundness proof goes from the box to the noise
box: for a point `x` of the box, `unitNoise` takes `εᵢ = (xᵢ - cᵢ) / rᵢ` with the center `cᵢ` and
radius `rᵢ` of the `i`-th interval, or `0` when `rᵢ = 0`, `recenter_unitNoise_eq` shows that
recentering gives back `x`, and `AffineModel.mem_range` puts `expr.eval x` in the range. The
registry planner previews this range next to its other finite-chart routes; when it wins,
`affineEnclosureAttempt?` returns an attempt whose `sound` field is `mem_affineRange_of_memBox`.

## References

* Marcus Vinicius Alvim Andrade, João Luiz Dihl Comba and Jorge Stolfi, "Affine Arithmetic",
  Interval'94, St. Petersburg, Russia, March 1994; authors' draft at
  <https://graphics.stanford.edu/~comba/papers/aa-93-12-petersburg-paper.pdf>. Section 3.1 for
  the affine form of an input interval, Section 4.1 for the exact affine operations.
-/

@[expose] public section

namespace CAS.Continuum

open CAS.Verified

namespace RationalInterval

/-- Recenter unit noises into the original rational variable box. -/
def recenter {ι : Type*} (box : ι → RationalInterval) (ε : ι → ℝ) (i : ι) : ℝ :=
  (box i).center + (box i).radius * ε i

/-- The affine form assigned to one reflected variable in a rational box. -/
def variableAffineForm {ι : Type*} [DecidableEq ι]
    (box : ι → RationalInterval) (i : ι) : AffineForm ι :=
  (AffineForm.const (box i).center).add
    ((AffineForm.noise i).scale (box i).radius)

/-- The variable form evaluates to the recentered coordinate `center + radius * ε i`. -/
@[simp] theorem eval_variableAffineForm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (box : ι → RationalInterval) (i : ι) (ε : ι → ℝ) :
    (variableAffineForm box i).eval ε = recenter box ε i := by
  simp [variableAffineForm, recenter]

/-- The exact affine model assigned to one reflected variable. -/
def variableAffineModel {ι : Type*} [DecidableEq ι]
    (box : ι → RationalInterval) (i : ι) : AffineModel ι :=
  .ofAffine (variableAffineForm box i)

/-- Compile the polynomial fragment of a reflected expression over a rational box. -/
def compileAffine? {ι : Type*} [Fintype ι] [DecidableEq ι]
    (box : ι → RationalInterval) : Verified.Expr ι → Option (AffineModel ι)
  | .nat n => some (.const n)
  | .int n => some (.const n)
  | .rat num den =>
      if den = 0 then none else some (.const ((num : ℚ) / (den : ℚ)))
  | .var i => some (variableAffineModel box i)
  | .add a b => do
      let ca ← compileAffine? box a
      let cb ← compileAffine? box b
      pure (ca.add cb)
  | .mul a b => do
      let ca ← compileAffine? box a
      let cb ← compileAffine? box b
      pure (ca.mul cb)
  | .sub a b => do
      let ca ← compileAffine? box a
      let cb ← compileAffine? box b
      pure (ca.sub cb)
  | .neg a => AffineModel.neg <$> compileAffine? box a
  | .pow a n => do
      let ca ← compileAffine? box a
      pure (ca.pow n)
  | .pi | .e | .div _ _ | .sin _ | .cos _ | .atan _ | .asin _ | .acos _ | .exp _ |
      .log _ | .sqrt _ => none
  | .rpow _ _ => none

/-- Successful compilation represents evaluation on every recentered unit-noise assignment. -/
theorem represents_recenter_of_compileAffine?_eq_some
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (box : ι → RationalInterval) (expr : Verified.Expr ι)
    (result : AffineModel ι) (ε : ι → ℝ) (hε : ∀ i, |ε i| ≤ 1)
    (h : compileAffine? box expr = some result) :
    result.Represents ε (expr.eval (recenter box ε)) := by
  induction expr generalizing result <;>
    simp only [compileAffine?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Option.map_eq_map, Option.map_eq_some_iff, reduceCtorEq] at h
  case nat n =>
    subst h
    exact AffineModel.represents_const n ε
  case int n =>
    subst h
    exact AffineModel.represents_const n ε
  case rat num den =>
    split_ifs at h
    obtain rfl := Option.some.inj h
    simpa using AffineModel.represents_const ((num : ℚ) / (den : ℚ)) ε
  case var i =>
    subst h
    change (variableAffineModel box i).Represents ε (recenter box ε i)
    rw [← eval_variableAffineForm box i ε]
    exact AffineModel.represents_ofAffine (variableAffineForm box i) ε
  case add a b ha hb =>
    obtain ⟨ca, hca, cb, hcb, rfl⟩ := h
    exact (ha ca hca).add (hb cb hcb)
  case mul a b ha hb =>
    obtain ⟨ca, hca, cb, hcb, rfl⟩ := h
    exact (ha ca hca).mul (hb cb hcb) hε
  case sub a b ha hb =>
    obtain ⟨ca, hca, cb, hcb, rfl⟩ := h
    exact (ha ca hca).sub (hb cb hcb)
  case neg a ha =>
    obtain ⟨ca, hca, rfl⟩ := h
    exact (ha ca hca).neg
  case pow a n ha =>
    obtain ⟨ca, hca, rfl⟩ := h
    exact (ha ca hca).pow n hε

/-- Unit noise recovered from a point in the original rational box. -/
noncomputable def unitNoise {ι : Type*}
    (box : ι → RationalInterval) (x : ι → ℝ) (i : ι) : ℝ :=
  if (box i).radius = 0 then 0
  else (x i - (box i).center) / (box i).radius

/-- Recentering the recovered unit noise returns the original boxed point. -/
theorem recenter_unitNoise_eq {ι : Type*} (box : ι → RationalInterval)
    (x : ι → ℝ) (hx : AffineForm.MemBox box x) :
    recenter box (unitNoise box x) = x := by
  funext i
  obtain ⟨hlo, hhi⟩ := hx i
  rw [← (box i).center_sub_radius_eq_lo] at hlo
  rw [← (box i).center_add_radius_eq_hi] at hhi
  push_cast at hlo hhi
  by_cases hradius : (box i).radius = 0
  · simp only [recenter, unitNoise, hradius, ↓reduceIte, Rat.cast_zero, zero_mul, add_zero,
      sub_zero] at hlo hhi ⊢
    exact le_antisymm hlo hhi
  · have hradiusReal : ((box i).radius : ℝ) ≠ 0 := by exact_mod_cast hradius
    rw [recenter, unitNoise, ite_eq_right hradius, mul_div_cancel₀ _ hradiusReal, add_sub_cancel]

/-- Recovered noises from a boxed point all lie in the unit interval. -/
theorem abs_unitNoise_le_one {ι : Type*} (box : ι → RationalInterval)
    (x : ι → ℝ) (hx : AffineForm.MemBox box x) (i : ι) :
    |unitNoise box x i| ≤ 1 := by
  by_cases hradius : (box i).radius = 0
  · simp [unitNoise, hradius]
  · have hpos : (0 : ℝ) < (box i).radius := by
      exact_mod_cast (box i).radius_nonneg.lt_of_ne' hradius
    obtain ⟨hlo, hhi⟩ := hx i
    rw [← (box i).center_sub_radius_eq_lo] at hlo
    rw [← (box i).center_add_radius_eq_hi] at hhi
    push_cast at hlo hhi
    rw [unitNoise, ite_eq_right hradius, abs_div, abs_of_pos hpos, div_le_one hpos, abs_le]
    constructor <;> linarith

/-- Successful affine compilation represents evaluation at every point of the variable box. -/
theorem represents_unitNoise_of_compileAffine?_eq_some
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (box : ι → RationalInterval) (expr : Verified.Expr ι)
    (result : AffineModel ι) (x : ι → ℝ) (hx : AffineForm.MemBox box x)
    (h : compileAffine? box expr = some result) :
    result.Represents (unitNoise box x) (expr.eval x) := by
  simpa only [recenter_unitNoise_eq box x hx] using represents_recenter_of_compileAffine?_eq_some
    box expr result (unitNoise box x) (abs_unitNoise_le_one box x hx) h

/-- Compute an affine enclosure of a reflected expression over a rational variable box. -/
def affineRange? {ι : Type*} [Fintype ι] [DecidableEq ι]
    (box : ι → RationalInterval) (expr : Verified.Expr ι) : Option RationalInterval :=
  (compileAffine? box expr).map AffineModel.range

/-- A successful affine range contains every evaluation on the original variable box. -/
theorem mem_affineRange_of_memBox
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (box : ι → RationalInterval) (expr : Verified.Expr ι)
    (range : RationalInterval) (x : ι → ℝ) (hx : AffineForm.MemBox box x)
    (h : affineRange? box expr = some range) :
    range.MemReal (expr.eval x) := by
  simp only [affineRange?, Option.map_eq_some_iff] at h
  obtain ⟨result, hcompile, rfl⟩ := h
  exact AffineModel.mem_range
    (represents_unitNoise_of_compileAffine?_eq_some box expr result x hx hcompile)
    (abs_unitNoise_le_one box x hx)

end RationalInterval
end CAS.Continuum
