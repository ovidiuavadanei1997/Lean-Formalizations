/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.EuclideanMatrix
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Euclidean deformation bounds for an axis-shaped derivative -/

public section

namespace ClockBarrier.Geometry

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The standard matrix determines the action of the actual Euclidean linear operator. -/
theorem axis_diagonal_apply {A : E₃ →L[ℝ] E₃} {J : ℝ}
    (hA : euclideanMatrix A = Matrix.diagonal ![J⁻¹, J⁻¹, J ^ 2]) (η : E₃) :
    A η = !₂[J⁻¹ * η 0, J⁻¹ * η 1, J ^ 2 * η 2] := by
  have hrepr : A.toLinearMap = Matrix.toEuclideanLin (Matrix.diagonal ![J⁻¹, J⁻¹, J ^ 2]) := by
    rw [← hA, toEuclideanLin_euclideanMatrix]
  change A.toLinearMap η = _
  rw [hrepr]
  change WithLp.toLp 2 (Matrix.mulVec (Matrix.diagonal ![J⁻¹, J⁻¹, J ^ 2]) (WithLp.ofLp η)) = _
  ext i
  change (Matrix.diagonal ![J⁻¹, J⁻¹, J ^ 2]).mulVec (WithLp.ofLp η) i = _
  rw [Matrix.mulVec_diagonal]
  fin_cases i <;> rfl

/-- The exact Euclidean squared norm separates transverse and axial deformation. -/
theorem norm_sq_of_axis_diagonal {A : E₃ →L[ℝ] E₃} {J : ℝ}
    (hA : euclideanMatrix A = Matrix.diagonal ![J⁻¹, J⁻¹, J ^ 2]) (η : E₃) :
    ‖A η‖ ^ 2 = (Real.sqrt ((η 0)^2 + (η 1)^2) / J)^2 + (J ^ 2 * |η 2|)^2 := by
  rw [axis_diagonal_apply hA η, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_three]
  change (J⁻¹ * η 0)^2 + (J⁻¹ * η 1)^2 + (J ^ 2 * η 2)^2 = _
  rw [div_pow, Real.sq_sqrt (by positivity)]
  simp only [mul_pow, sq_abs]
  ring

/-- Lower radial and axial shell bounds force the anisotropic distance scale.
This holds for every positive clock, without a collapse-regime restriction. -/
theorem clock_scale_le_norm_of_axis_diagonal
    {A : E₃ →L[ℝ] E₃} {J l Λ : ℝ} {η : E₃}
    (hJ : 0 < J) (hl : 0 ≤ l) (hΛ : 0 ≤ Λ)
    (hA : euclideanMatrix A = Matrix.diagonal ![J⁻¹, J⁻¹, J ^ 2])
    (hR : l * J ^ 3 * Λ ≤ Real.sqrt ((η 0)^2 + (η 1)^2)) (hZ : Λ ≤ |η 2|) :
    J ^ 2 * Λ * Real.sqrt (1 + l ^ 2) ≤ ‖A η‖ := by
  have hr : l * J ^ 2 * Λ ≤ Real.sqrt ((η 0)^2 + (η 1)^2) / J := by
    apply (le_div_iff₀ hJ).2
    calc
      l * J ^ 2 * Λ * J = l * J ^ 3 * Λ := by ring
      _ ≤ _ := hR
  have hz : J ^ 2 * Λ ≤ J ^ 2 * |η 2| :=
    mul_le_mul_of_nonneg_left hZ (sq_nonneg J)
  apply (sq_le_sq₀ (by positivity) (norm_nonneg (A η))).mp
  calc
    (J ^ 2 * Λ * Real.sqrt (1 + l ^ 2)) ^ 2 =
        (l * J ^ 2 * Λ) ^ 2 + (J ^ 2 * Λ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      ring
    _ ≤ (Real.sqrt ((η 0)^2 + (η 1)^2) / J)^2 + (J ^ 2 * |η 2|)^2 :=
      add_le_add (pow_le_pow_left₀ (by positivity) hr 2) (pow_le_pow_left₀ (by positivity) hz 2)
    _ = ‖A η‖ ^ 2 := (norm_sq_of_axis_diagonal hA η).symm

end ClockBarrier.Geometry
