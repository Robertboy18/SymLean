/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import CAS.Certificate.WeightedResidual
import CAS.CEGA

/-!
# A weighted ODE defect and its derivative

For `p(x) = 1 + x + x²/2`, the computer algebra system proves that the defect `p′ - p` is `-x²/2`
and its derivative is `-x`. CEGA encloses both functions on the two halves of
`[0, 1]`. The atlas then certifies a weighted combination with arbitrary real
amplitudes `a`, `b` and a symbolic tolerance.

The two patch budgets are `|a|/16 + |b|/2` and `|a|/2 + |b|/2`.
Their coefficients follow from the polynomial ranges and the weights `x`, `1-x`.
-/

@[expose] public section

noncomputable section

namespace CAS.Examples.Numerics.WeightedResidual

open CAS.Certificate CAS.Domain

/-- The quadratic Taylor polynomial for the equation `u′ = u` with initial value one. -/
def profile (x : ℝ) : ℝ :=
  1 + x + x ^ 2 / 2

/-- The differential defect of the polynomial. -/
def defect (x : ℝ) : ℝ :=
  deriv profile x - profile x

/-- The actual differential defect agrees with the polynomial used by the enclosures. -/
theorem defect_eq (x : ℝ) : defect x = -x ^ 2 / 2 := by
  unfold defect
  have hd : deriv profile x = 1 + x := by
    unfold profile
    cas
  rw [hd]
  unfold profile
  cas

/-- The derivative enclosure concerns the derivative of the actual differential defect. -/
theorem deriv_defect (x : ℝ) : deriv defect x = -x := by
  rw [show defect = (fun y : ℝ ↦ -y ^ 2 / 2) from funext defect_eq]
  cas

/-- The left and right half intervals, with their shared endpoint included in both. -/
def patch : Bool → Set ℝ
  | true => Set.Icc 0 (1 / 2)
  | false => Set.Icc (1 / 2) 1

/-- Both closed patches cover the whole requested interval. -/
def cover : PatchCover ℝ Bool (Set.Icc 0 1) where
  patch := patch
  covers := by
    intro x hx
    rcases le_total x (1 / 2) with hleft | hright
    · exact ⟨true, hx.1, hleft⟩
    · exact ⟨false, hright, hx.2⟩

/-- The coefficient of the defect is `x`; that of its derivative is `1-x`. -/
def weights : Bool → ℝ → ℝ
  | true => fun x ↦ x
  | false => fun x ↦ 1 - x

/-- The two residual components retain arbitrary signed amplitudes. -/
def residuals (a b : ℝ) : Bool → ℝ → ℝ
  | true => fun x ↦ a * defect x
  | false => fun x ↦ b * deriv defect x

/-- The weight range is tighter on the patch where that weight is small. -/
def weightCert (i j : Bool) : EnclosureCert ℝ (patch i) where
  fn := weights j
  lo := if i = j then 0 else 1 / 2
  hi := if i = j then 1 / 2 else 1
  sound := by
    cases i <;> cases j <;> intro x hx
    all_goals
      rcases hx with ⟨h0, h1⟩
      simp only [weights, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
      constructor <;> cas

/-- Checked polynomial ranges for the defect on each patch. -/
def defectEnclosure (i : Bool) : EnclosureCert ℝ (patch i) where
  fn := fun x ↦ -x ^ 2 / 2
  lo := if i then -(1 / 8) else -(1 / 2)
  hi := 0
  sound := by
    cases i <;> intro x hx
    all_goals
      rcases hx with ⟨h0, h1⟩
      dsimp only
      constructor <;> cega

/-- Checked polynomial ranges for the derivative of the defect. -/
def derivativeEnclosure (i : Bool) : EnclosureCert ℝ (patch i) where
  fn := fun x ↦ -x
  lo := if i then -(1 / 2) else -1
  hi := 0
  sound := by
    cases i <;> intro x hx
    all_goals
      rcases hx with ⟨h0, h1⟩
      dsimp only
      constructor <;> cega

/-- Scale the checked residual components by symbolic amplitudes without assuming their signs. -/
def residualCert (a b : ℝ) (i : Bool) : Bool → ResidualCert ℝ ℝ (patch i)
  | true => (ResidualCert.ofEnclosure (defectEnclosure i)).smulOfEnclosure
      (EnclosureCert.const a (patch i))
  | false => (ResidualCert.ofEnclosure (derivativeEnclosure i)).smulOfEnclosure
      (EnclosureCert.const b (patch i))

/-- The analytic identities connect actual derivatives to the enclosed local formulas. -/
theorem residualCert_eqOn (a b : ℝ) (i j : Bool) :
    Set.EqOn (residuals a b j) (residualCert a b i j).residual (patch i) := by
  intro x _hx
  cases j
  · change b * deriv defect x = b * (-x)
    rw [deriv_defect]
  · change a * defect x = a * (-x ^ 2 / 2)
    rw [defect_eq]

/-- Assemble the actual defect and its derivative, comparing local sums to the tolerance. -/
def weightedAtlas (a b eps : ℝ)
    (hleft : |a| / 16 + |b| / 2 ≤ eps)
    (hright : |a| / 2 + |b| / 2 ≤ eps) :
    ResidualAtlasCert ℝ ℝ Bool (Set.Icc 0 1) :=
  ResidualAtlasCert.weightedSumOfCover cover Finset.univ weights (residuals a b)
    weightCert (residualCert a b)
    (fun _ _ _ ↦ Set.eqOn_refl _ _) (fun i j _ ↦ residualCert_eqOn a b i j) eps (by
      intro i
      cases i
      · norm_num [weightCert, residualCert, EnclosureCert.const, defectEnclosure,
          derivativeEnclosure, Fintype.sum_bool]
        convert hright using 1
        cas
      · norm_num [weightCert, residualCert, EnclosureCert.const, defectEnclosure,
          derivativeEnclosure, Fintype.sum_bool]
        convert hleft using 1
        cas)

/-- CEGA turns the assembled atlas into a residual bound with symbolic tolerance `eps`. -/
theorem weighted_defect_bound (a b eps : ℝ)
    (hright : |a| / 2 + |b| / 2 ≤ eps) :
    ResidualBound
      (fun x ↦ x * (a * defect x) + (1 - x) * (b * deriv defect x))
      (Set.Icc 0 1) eps := by
  have hleft : |a| / 16 + |b| / 2 ≤ eps := by linarith [abs_nonneg a]
  have h : ResidualBound (fun x ↦ ∑ j : Bool, weights j x • residuals a b j x)
      (Set.Icc 0 1) eps := by
    cega using (weightedAtlas a b eps hleft hright).toResidualCert
  simpa only [Fintype.sum_bool, weights, residuals, smul_eq_mul] using h

/-- An explicit symbolic bound needs no certificate or residual estimate as an input. -/
theorem weighted_defect_bound_explicit (a b : ℝ) :
    ResidualBound
      (fun x ↦ x * (a * defect x) + (1 - x) * (b * deriv defect x))
      (Set.Icc 0 1) (|a| / 2 + |b| / 2) := by
  exact weighted_defect_bound a b _ le_rfl

end CAS.Examples.Numerics.WeightedResidual
