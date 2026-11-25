/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.EuclideanMatrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity

/-! # Operator bounds for the axis deformation in the collapse regime -/

public section

namespace ClockBarrier.Geometry

open scoped Matrix.Norms.L2Operator

/-- For 0 < J ≤ 1, the actual Euclidean operator norm of the axis matrix is J⁻¹. -/
theorem norm_axis_diagonal_eq_inv {J : ℝ} (hJ : 0 < J) (hJ₁ : J ≤ 1) :
    ‖(Matrix.toEuclideanLin (Matrix.diagonal ![J⁻¹, J⁻¹, J ^ 2])).toContinuousLinearMap‖ = J⁻¹ := by
  change ‖(Matrix.diagonal ![J⁻¹, J⁻¹, J ^ 2] : Matrix (Fin 3) (Fin 3) ℝ)‖ = J⁻¹
  rw [Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr hJ.le)).2
    intro i
    fin_cases i
    · simp [abs_of_pos hJ]
    · simp [abs_of_pos hJ]
    · change ‖J ^ 2‖ ≤ J⁻¹
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg J)] using
        (pow_le_one₀ hJ.le hJ₁ (n := 2)).trans ((one_le_inv₀ hJ).2 hJ₁)
  · simpa [abs_of_pos hJ] using norm_le_pi_norm ![J⁻¹, J⁻¹, J ^ 2] (0 : Fin 3)

/-- Comparison with the actual axis derivative gives the vector stretching bound.
Applying this to vorticity still requires proving the Cauchy transport identity. -/
theorem norm_apply_le_of_axis_comparison
    {A F : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {J C : ℝ} (hJ : 0 < J) (hJ₁ : J ≤ 1)
    (hA : euclideanMatrix A = Matrix.diagonal ![J⁻¹, J⁻¹, J ^ 2])
    (hF : ‖F‖ ≤ C * ‖A‖) (w : EuclideanSpace ℝ (Fin 3)) :
    ‖F w‖ ≤ C * J⁻¹ * ‖w‖ := by
  have hrepr : (Matrix.toEuclideanLin (Matrix.diagonal ![J⁻¹, J⁻¹, J ^ 2])).toContinuousLinearMap = A := by
    rw [← hA, toEuclideanLin_euclideanMatrix]
    rfl
  calc
    ‖F w‖ ≤ ‖F‖ * ‖w‖ := F.le_opNorm w
    _ ≤ (C * ‖A‖) * ‖w‖ := mul_le_mul_of_nonneg_right hF (norm_nonneg w)
    _ = C * J⁻¹ * ‖w‖ := by rw [← hrepr, norm_axis_diagonal_eq_inv hJ hJ₁]

end ClockBarrier.Geometry
