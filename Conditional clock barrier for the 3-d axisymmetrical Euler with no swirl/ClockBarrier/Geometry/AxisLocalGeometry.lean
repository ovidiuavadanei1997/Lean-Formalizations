/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.NearIdentity
public import ClockBarrier.Geometry.AxisDeformation
import Mathlib.Tactic.NormNum

/-! # Radial and operator comparisons near the identity -/

public section
namespace ClockBarrier.Geometry
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The distance to the half-turn image is twice the cylindrical radius. -/
theorem norm_sub_axis_halfTurn (a : E₃) :
    ‖a - !₂[-a 0, -a 1, a 2]‖ = 2 * Real.sqrt ((a 0)^2 + (a 1)^2) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  nlinarith [Real.sq_sqrt (show 0 ≤ (a 0)^2 + (a 1)^2 by positivity)]

/-- A half-size perturbation controls the operator norm itself. -/
theorem opNorm_bounds_of_half_perturbation {F : E₃ →L[ℝ] E₃}
    (hF : ‖F - ContinuousLinearMap.id ℝ E₃‖ ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ ‖F‖ ∧ ‖F‖ ≤ 3 / 2 := by
  have hn := abs_le.mp ((abs_norm_sub_norm_le F (ContinuousLinearMap.id ℝ E₃)).trans hF)
  rw [ContinuousLinearMap.norm_id] at hn
  exact ⟨by linarith [hn.1], by linarith [hn.2]⟩

/-- The positive axis clock stays uniformly comparable to one near identity. -/
theorem axis_clock_bounds_of_half_perturbation {F : E₃ →L[ℝ] E₃} {J : ℝ}
    (hJ : 0 < J) (hdiag : euclideanMatrix F = Matrix.diagonal ![J⁻¹, J⁻¹, J^2])
    (hF : ‖F - ContinuousLinearMap.id ℝ E₃‖ ≤ 1 / 2) :
    (2 / 3 : ℝ) ≤ J ∧ J ≤ 2 := by
  have hb := norm_bounds_of_norm_sub_id_le hF (!₂[1, 0, 0] : E₃)
  norm_num [axis_diagonal_apply hdiag, EuclideanSpace.norm_eq, Fin.sum_univ_three,
    Matrix.cons_val_two, Real.sqrt_inv, Real.sqrt_sq_eq_abs, abs_of_pos hJ] at hb
  rw [inv_eq_one_div, le_div_iff₀ hJ, div_le_iff₀ hJ] at hb
  exact ⟨by linarith [hb.2], by linarith [hb.1]⟩

/-- Global distance bounds and half-turn covariance give radial bounds, even on the axis. -/
theorem radius_bounds_of_halfTurn {f : E₃ → E₃}
    (hhalf : ∀ a, f !₂[-a 0, -a 1, a 2] = !₂[-f a 0, -f a 1, f a 2])
    (hdist : ∀ a b, (1 / 2 : ℝ) * ‖a - b‖ ≤ ‖f a - f b‖ ∧
      ‖f a - f b‖ ≤ (3 / 2 : ℝ) * ‖a - b‖) (a : E₃) :
    (1 / 2 : ℝ) * Real.sqrt ((a 0)^2 + (a 1)^2) ≤
        Real.sqrt ((f a 0)^2 + (f a 1)^2) ∧
    Real.sqrt ((f a 0)^2 + (f a 1)^2) ≤
      (3 / 2 : ℝ) * Real.sqrt ((a 0)^2 + (a 1)^2) := by
  have hb := hdist a !₂[-a 0, -a 1, a 2]
  rw [hhalf, norm_sub_axis_halfTurn, norm_sub_axis_halfTurn] at hb
  exact ⟨by linarith [hb.1], by linarith [hb.2]⟩

end ClockBarrier.Geometry
