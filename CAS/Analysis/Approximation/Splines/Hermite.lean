/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Analysis.Approximation.Splines.PiecewisePolynomial
import CAS.ExactTactic

/-!
# Cubic Hermite interpolation on a strict knot mesh

For `h ≠ 0`, `hermitePolynomial left h a b da db` is the cubic on the panel `[left, left + h]`
with the values `a`, `b` and the physical slopes `da`, `db` at its two ends
(`hermitePolynomial_left`, `hermitePolynomial_right`, `hermitePolynomial_slope_left`,
`hermitePolynomial_slope_right`).
`HermiteData.toSpline` places nodal values and slopes on a `StrictKnotMesh`, which may be
nonuniform. Adjacent panels share these data, so their value and first derivative jets match and
the panels form a `PolynomialSpline mesh 3 1`. All lengths and nodal data are exact real values;
an evaluation at a rounded local coordinate needs its own comparison with the exact endpoint.

## References

* Jiajie Chen, Thomas Y. Hou and De Huang, "On the Finite Time Blowup of the De Gregorio Model
  for the 3D Euler Equations", *Communications on Pure and Applied Mathematics* 74 (2021),
  no. 6, pp. 1282-1350, <https://doi.org/10.1002/cpa.21991>. The supplementary material of the
  arXiv version, <https://arxiv.org/abs/1905.06387v3>, represents its approximate profile in this
  piecewise cubic Hermite basis (§7.3.1).
-/

@[expose] public section

noncomputable section

namespace CAS.Splines

open _root_.Polynomial

/-- The cubic Hermite basis on a unit panel, with slopes scaled by its physical length. -/
def hermiteValue (h a b da db z : ℝ) : ℝ :=
  a * (1 - 3 * z ^ 2 + 2 * z ^ 3) + b * (3 * z ^ 2 - 2 * z ^ 3) +
    h * (da * (z - 2 * z ^ 2 + z ^ 3) + db * (-z ^ 2 + z ^ 3))

/-- Interpolation at the left local endpoint. -/
@[simp] theorem hermiteValue_zero (h a b da db : ℝ) :
    hermiteValue h a b da db 0 = a := by
  simp [hermiteValue]

/-- Interpolation at the right local endpoint, independently of the slopes. -/
@[simp] theorem hermiteValue_one (h a b da db : ℝ) :
    hermiteValue h a b da db 1 = b := by
  norm_num [hermiteValue]

/-- The physical polynomial on a panel starting at `left`, of length `h`. -/
def hermitePolynomial (left h a b da db : ℝ) : ℝ[X] :=
  let z := (X - C left) * C (1 / h)
  C a + C (h * da) * z + C (-3 * a + 3 * b - h * (2 * da + db)) * z ^ 2 +
    C (2 * a - 2 * b + h * (da + db)) * z ^ 3

/-- The reconstruction is cubic even when some of its leading coefficients vanish. -/
theorem hermitePolynomial_degree (left h a b da db : ℝ) :
    (hermitePolynomial left h a b da db).natDegree ≤ 3 := by
  have hz : ((X - C left) * C (1 / h)).natDegree ≤ 1 := by
    simpa using (natDegree_mul_le (p := (X : ℝ[X]) - C left) (q := C (1 / h)))
  apply natDegree_add_le_of_degree_le
  · apply natDegree_add_le_of_degree_le
    · apply natDegree_add_le_of_degree_le
      · simp
      · exact (natDegree_C_mul_le _ _).trans (hz.trans (by decide))
    · exact (natDegree_C_mul_le _ _).trans
        ((natDegree_pow_le_of_le 2 hz).trans (by decide))
  · exact (natDegree_C_mul_le _ _).trans (natDegree_pow_le_of_le 3 hz)

/-- The physical polynomial agrees with the normalized Hermite formula. -/
theorem hermitePolynomial_eval (left h a b da db x : ℝ) :
    (hermitePolynomial left h a b da db).eval x =
      hermiteValue h a b da db ((x - left) / h) := by
  simp only [hermitePolynomial, eval_add, eval_mul, eval_C, eval_sub, eval_X, eval_pow]
  unfold hermiteValue
  cas

/-- The polynomial interpolates the left value. -/
theorem hermitePolynomial_left (left h a b da db : ℝ) :
    polynomialJet 0 (hermitePolynomial left h a b da db) left = a := by
  simp [hermitePolynomial_eval]

/-- The polynomial interpolates the right value on a nondegenerate panel. -/
theorem hermitePolynomial_right (left h a b da db : ℝ) (hh : h ≠ 0) :
    polynomialJet 0 (hermitePolynomial left h a b da db) (left + h) = b := by
  simp [hermitePolynomial_eval, hh]

/-- The first jet interpolates the left physical slope. -/
theorem hermitePolynomial_slope_left (left h a b da db : ℝ) (hh : h ≠ 0) :
    polynomialJet 1 (hermitePolynomial left h a b da db) left = da := by
  simp only [polynomialJet, hermitePolynomial, map_mul, one_div, neg_mul, map_sub,
    map_add, map_neg, Function.iterate_one, derivative_C, derivative_mul,
    zero_mul, mul_zero, add_zero, derivative_X, sub_zero, one_mul, zero_add,
    neg_zero, sub_self, derivative_pow, Nat.cast_ofNat, Nat.add_one_sub_one,
    pow_one, eval_add, eval_mul, eval_C, eval_sub, eval_neg, eval_X, eval_pow, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  cas using hh

/-- The first jet interpolates the right physical slope. -/
theorem hermitePolynomial_slope_right (left h a b da db : ℝ) (hh : h ≠ 0) :
    polynomialJet 1 (hermitePolynomial left h a b da db) (left + h) = db := by
  simp only [polynomialJet, hermitePolynomial, map_mul, one_div, neg_mul, map_sub,
    map_add, map_neg, Function.iterate_one, derivative_C, derivative_mul,
    zero_mul, mul_zero, add_zero, derivative_X, sub_zero, one_mul, zero_add,
    neg_zero, sub_self, derivative_pow, Nat.cast_ofNat, Nat.add_one_sub_one,
    pow_one, eval_add, eval_mul, eval_C, eval_sub, eval_neg, eval_X, add_sub_cancel_left, eval_pow]
  cas using hh

/-- Nodal values and shared physical slopes for cubic Hermite interpolation. -/
structure HermiteData (panels : ℕ) where
  /-- Values at all `panels + 1` nodes. -/
  value : Fin (panels + 1) → ℝ
  /-- Shared physical slopes at those same nodes. -/
  slope : Fin (panels + 1) → ℝ

namespace HermiteData

variable {panels : ℕ}

/-- Place the nodal data on a strict mesh using its exact panel lengths. -/
def polynomialData (data : HermiteData panels) (mesh : StrictKnotMesh panels) :
    PolynomialSplineData mesh 3 where
  piece i := hermitePolynomial (mesh.panelLeft i) (mesh.panelRight i - mesh.panelLeft i)
    (data.value i.castSucc) (data.value i.succ) (data.slope i.castSucc) (data.slope i.succ)
  degree_le _ := hermitePolynomial_degree _ _ _ _ _ _

/-- The left value jet of every panel is its supplied nodal value. -/
theorem value_left (data : HermiteData panels) (mesh : StrictKnotMesh panels)
    (i : Fin panels) :
    polynomialJet 0 ((data.polynomialData mesh).piece i) (mesh.panelLeft i) =
      data.value i.castSucc :=
  hermitePolynomial_left _ _ _ _ _ _

/-- The right value jet of every panel is its supplied nodal value. -/
theorem value_right (data : HermiteData panels) (mesh : StrictKnotMesh panels)
    (i : Fin panels) :
    polynomialJet 0 ((data.polynomialData mesh).piece i) (mesh.panelRight i) =
      data.value i.succ := by
  have hh := (sub_pos.mpr (mesh.panelLeft_lt_panelRight i)).ne'
  simpa [polynomialData] using hermitePolynomial_right (mesh.panelLeft i) _ (data.value i.castSucc)
    (data.value i.succ) (data.slope i.castSucc) (data.slope i.succ) hh

/-- The left slope jet of every panel is its supplied nodal slope. -/
theorem slope_left (data : HermiteData panels) (mesh : StrictKnotMesh panels)
    (i : Fin panels) :
    polynomialJet 1 ((data.polynomialData mesh).piece i) (mesh.panelLeft i) =
      data.slope i.castSucc :=
  hermitePolynomial_slope_left _ _ _ _ _ _
    (sub_pos.mpr (mesh.panelLeft_lt_panelRight i)).ne'

/-- The right slope jet of every panel is its supplied nodal slope. -/
theorem slope_right (data : HermiteData panels) (mesh : StrictKnotMesh panels)
    (i : Fin panels) :
    polynomialJet 1 ((data.polynomialData mesh).piece i) (mesh.panelRight i) =
      data.slope i.succ := by
  have hh := (sub_pos.mpr (mesh.panelLeft_lt_panelRight i)).ne'
  simpa [polynomialData] using hermitePolynomial_slope_right (mesh.panelLeft i) _
    (data.value i.castSucc)
    (data.value i.succ) (data.slope i.castSucc) (data.slope i.succ) hh

/-- Shared values and slopes certify all interior value and first derivative matches. -/
def toSpline (data : HermiteData panels) (mesh : StrictKnotMesh panels) :
    PolynomialSpline mesh 3 1 where
  toPolynomialSplineData := data.polynomialData mesh
  matchesJets := by
    intro i hi order horder
    have hnode : i.succ = (StrictKnotMesh.rightNeighbor i hi).castSucc := by
      apply Fin.ext
      rfl
    interval_cases order
    · rw [data.value_right, mesh.panelRight_eq_panelLeft_rightNeighbor i hi,
        data.value_left, hnode]
    · rw [data.slope_right, mesh.panelRight_eq_panelLeft_rightNeighbor i hi,
        data.slope_left, hnode]

end HermiteData

end CAS.Splines
