/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.AffineArithmetic

/-!
# Squaring an affine form

For a noise symbol `ε` with `|ε| ≤ 1`, the square of the affine form `1 + ε / 2` is
`1 + ε + ε² / 4`. The affine linearization keeps `1 + ε` and the checked interval
remainder encloses `ε² / 4`. `shiftedNoise_square_mem` gets the enclosure from
`AffineForm.mulRange`, and `shiftedNoiseModel_square_mem` gets it from the general
multiplication of `AffineModel`.
-/

@[expose] public section

namespace CAS.Examples.Numerics.AffineArithmetic

open CAS.Continuum

/-- The one-noise affine form `1 + ε / 2`. -/
def shiftedNoise : AffineForm (Fin 1) :=
  ⟨1, fun _ ↦ 1 / 2⟩

/-- The exact affine evaluation is `1 + ε / 2`. -/
theorem shiftedNoise_eval (ε : Fin 1 → ℝ) :
    shiftedNoise.eval ε = 1 + ε 0 / 2 := by
  simp [shiftedNoise, AffineForm.eval]
  ring

/-- The checked multiplication enclosure contains every unit-noise square. -/
theorem shiftedNoise_square_mem (ε : Fin 1 → ℝ)
    (hε : ∀ i, |ε i| ≤ 1) :
    (shiftedNoise.mulRange shiftedNoise).MemReal
      ((1 + ε 0 / 2) ^ 2) := by
  rw [← shiftedNoise_eval]
  simpa [pow_two] using AffineForm.mul_mem_mulRange shiftedNoise shiftedNoise hε

/-- The shifted noise as an exact model with zero remainder. -/
def shiftedNoiseModel : AffineModel (Fin 1) :=
  .ofAffine shiftedNoise

/-- General model multiplication represents the square of the represented value. -/
theorem shiftedNoiseModel_square_represents (ε : Fin 1 → ℝ)
    (hε : ∀ i, |ε i| ≤ 1) :
    (shiftedNoiseModel.mul shiftedNoiseModel).Represents ε
      ((1 + ε 0 / 2) ^ 2) := by
  have hsource : shiftedNoiseModel.Represents ε (1 + ε 0 / 2) := by
    rw [← shiftedNoise_eval]
    exact AffineModel.represents_ofAffine shiftedNoise ε
  simpa [pow_two] using hsource.mul hsource hε

/-- The reported model range contains every represented square. -/
theorem shiftedNoiseModel_square_mem (ε : Fin 1 → ℝ)
    (hε : ∀ i, |ε i| ≤ 1) :
    (shiftedNoiseModel.mul shiftedNoiseModel).range.MemReal
      ((1 + ε 0 / 2) ^ 2) :=
  AffineModel.mem_range (shiftedNoiseModel_square_represents ε hε) hε

end CAS.Examples.Numerics.AffineArithmetic
