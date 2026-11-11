/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Certificate.Atlas.Residual

/-!
# Weighted residual assembly on a cover

A variable coefficient contributes its certified magnitude times the residual budget.
Finite sums accumulate these products on each patch before the atlas compares them with
the requested global tolerance. This retains the correlation between small coefficients
and small residuals on the same patch.

On one patch, `ResidualCert.smulOfEnclosure` multiplies a residual certificate by an
enclosed coefficient and `ResidualCert.weightedSum` sums such products. Over a cover,
`ResidualAtlasCert.weightedSumOfCover` assembles the patchwise sums into one global
`ResidualAtlasCert`; its local formulas need only agree with the global weights and
residuals on their own patches. The residuals may take values in any normed real vector
space, so derivative residuals fit once a derivative identity and an enclosure are proved.

## Implementation notes

The kernel checks the `sound` proof of each certificate as it is built; the coefficient
enclosures, the residual budgets and the global tolerance are proposals, for example CEGA
enclosures on each patch. One product costs `max |lo| |hi| * eps`, the magnitude bound of
`BoundCert.absOfEnclosure` times the residual budget. Bounding the coefficients and the
residuals over the whole domain and multiplying the two maxima would also be sound, but larger
whenever the large coefficients and the large residuals sit on different patches.
-/

@[expose] public section

namespace CAS.Certificate

open CAS.Domain

namespace ResidualCert

variable {α E : Type*} [NormedAddCommGroup E] {s : Set α}

/-- Replace a residual by a function equal to it on the certified domain. -/
def replaceResidual (c : ResidualCert α E s) (residual : α → E)
    (hresidual : Set.EqOn residual c.residual s) : ResidualCert α E s where
  residual := residual
  eps := c.eps
  sound := approxOn_congr c.sound (Set.Subset.refl s) hresidual (Set.eqOn_refl _ _)

/-- Turn a real enclosure into a residual certificate using its largest endpoint magnitude. -/
def ofEnclosure (c : EnclosureCert α s) : ResidualCert α ℝ s where
  residual := c.fn
  eps := max |c.lo| |c.hi|
  sound := by
    intro x hx
    simpa only [BoundCert.absOfEnclosure, sub_zero, Real.norm_eq_abs] using
      (BoundCert.absOfEnclosure c).sound x hx

/-- Enclosure conversion retains the enclosed function as its residual. -/
@[simp]
theorem ofEnclosure_residual (c : EnclosureCert α s) :
    (ofEnclosure c).residual = c.fn :=
  rfl

/-- Enclosure conversion uses the larger absolute endpoint as its budget. -/
@[simp]
theorem ofEnclosure_eps (c : EnclosureCert α s) :
    (ofEnclosure c).eps = max |c.lo| |c.hi| :=
  rfl

/-- Sum finitely many residuals, adding their error budgets by the triangle inequality. -/
def sum {κ : Type*} (indices : Finset κ) (c : κ → ResidualCert α E s) :
    ResidualCert α E s where
  residual := fun x ↦ ∑ j ∈ indices, (c j).residual x
  eps := ∑ j ∈ indices, (c j).eps
  sound := by
    intro x hx
    simp only [sub_zero]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _hj ↦ by
      simpa only [sub_zero] using (c j).sound x hx)

/-- Multiply a residual by a variable real coefficient with a certified absolute bound.

No sign assumption on the coefficient or the stored budgets is needed. At a point of the
domain, soundness supplies nonnegativity of both magnitude bounds; an empty patch is harmless. -/
def smulOfBoundCert [NormedSpace ℝ E] (c : ResidualCert α E s) (weight : α → ℝ)
    (bound : BoundCert α s) (hbound : Set.EqOn bound.fn (fun x ↦ |weight x|) s) :
    ResidualCert α E s where
  residual := fun x ↦ weight x • c.residual x
  eps := bound.upper * c.eps
  sound := by
    intro x hx
    have hw : |weight x| ≤ bound.upper := by
      simpa only [hbound hx] using bound.sound x hx
    have hc : ‖c.residual x‖ ≤ c.eps := by
      simpa only [sub_zero] using c.sound x hx
    simp only [sub_zero, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hw hc (norm_nonneg _) ((abs_nonneg _).trans hw)

/-- An enclosed variable coefficient supplies the magnitude bound for scalar multiplication. -/
def smulOfEnclosure [NormedSpace ℝ E] (c : ResidualCert α E s)
    (weight : EnclosureCert α s) : ResidualCert α E s :=
  c.smulOfBoundCert weight.fn (BoundCert.absOfEnclosure weight) (Set.eqOn_refl _ _)

/-- The weighted residual multiplies by the enclosed coefficient pointwise. -/
@[simp]
theorem smulOfEnclosure_residual [NormedSpace ℝ E] (c : ResidualCert α E s)
    (weight : EnclosureCert α s) :
    (c.smulOfEnclosure weight).residual = fun x ↦ weight.fn x • c.residual x :=
  rfl

/-- Multiplication scales the budget by the largest absolute coefficient endpoint. -/
@[simp]
theorem smulOfEnclosure_eps [NormedSpace ℝ E] (c : ResidualCert α E s)
    (weight : EnclosureCert α s) :
    (c.smulOfEnclosure weight).eps = max |weight.lo| |weight.hi| * c.eps :=
  rfl

/-- Compose a finite family of variable-weight residuals on one patch. -/
def weightedSum {κ : Type*} [NormedSpace ℝ E] (indices : Finset κ)
    (weights : κ → EnclosureCert α s) (residuals : κ → ResidualCert α E s) :
    ResidualCert α E s :=
  sum indices fun j ↦ (residuals j).smulOfEnclosure (weights j)

/-- The assembled function is the pointwise weighted sum. -/
@[simp]
theorem weightedSum_residual {κ : Type*} [NormedSpace ℝ E] (indices : Finset κ)
    (weights : κ → EnclosureCert α s) (residuals : κ → ResidualCert α E s) :
    (weightedSum indices weights residuals).residual =
      fun x ↦ ∑ j ∈ indices, (weights j).fn x • (residuals j).residual x :=
  rfl

/-- The budget sums coefficient magnitudes times component budgets. -/
@[simp]
theorem weightedSum_eps {κ : Type*} [NormedSpace ℝ E] (indices : Finset κ)
    (weights : κ → EnclosureCert α s) (residuals : κ → ResidualCert α E s) :
    (weightedSum indices weights residuals).eps =
      ∑ j ∈ indices, max |(weights j).lo| |(weights j).hi| * (residuals j).eps :=
  rfl

end ResidualCert

namespace ResidualAtlasCert

variable {α E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {domain : Set α}

/-- Assemble weighted residuals patchwise with a symbolic global tolerance.

Only the selected components must agree with the global formulas. Each patch compares its
own sum of products with `eps`, so coefficient and residual budgets are never maximized
independently across patches. The index type of the cover need not be finite. -/
def weightedSumOfCover (cover : PatchCover α ι domain) (indices : Finset κ)
    (weights : κ → α → ℝ) (residuals : κ → α → E)
    (weightCert : (i : ι) → κ → EnclosureCert α (cover.patch i))
    (residualCert : (i : ι) → κ → ResidualCert α E (cover.patch i))
    (hweights : ∀ i j, j ∈ indices →
      Set.EqOn (weights j) (weightCert i j).fn (cover.patch i))
    (hresiduals : ∀ i j, j ∈ indices →
      Set.EqOn (residuals j) (residualCert i j).residual (cover.patch i))
    (eps : ℝ)
    (hbudget : ∀ i, (∑ j ∈ indices,
      max |(weightCert i j).lo| |(weightCert i j).hi| * (residualCert i j).eps) ≤ eps) :
    ResidualAtlasCert α E ι domain :=
  ofCover cover (fun x ↦ ∑ j ∈ indices, weights j x • residuals j x) eps
    (fun i ↦ (ResidualCert.weightedSum indices (weightCert i) (residualCert i)).replaceResidual
      (fun x ↦ ∑ j ∈ indices, weights j x • residuals j x) (by
        intro x hx
        change (∑ j ∈ indices, weights j x • residuals j x) =
          ∑ j ∈ indices, (weightCert i j).fn x • (residualCert i j).residual x
        apply Finset.sum_congr rfl
        intro j hj
        rw [hweights i j hj hx, hresiduals i j hj hx]))
    (fun _ ↦ rfl) hbudget

end ResidualAtlasCert

end CAS.Certificate
