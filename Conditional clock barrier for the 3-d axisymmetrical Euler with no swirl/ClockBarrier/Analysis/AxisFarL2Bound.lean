/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.AxisFarIntegration
public import ClockBarrier.Analysis.L2Pairing
public import ClockBarrier.Geometry.CurlLinear
import Mathlib.Tactic.Ring

/-! # Energy bounds for the complete smooth far-field integral -/

public section

namespace ClockBarrier.Analysis

open MeasureTheory Geometry
open scoped Topology ContDiff NNReal

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Each integrated velocity derivative is controlled by kinetic energy and
the `L²` norm of the full differentiated cutoff coefficient. -/
theorem abs_integral_axis_far_mul_velocity_derivative_le
    {χ : E₃ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : χ =ᶠ[𝓝 (0 : E₃)] 0)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1)
    {u : E₃ → E₃} {H α : ℝ≥0} (hu : Differentiable ℝ u)
    (hα : 0 < α) (hD : HolderWith H α (fderiv ℝ u))
    (henergy : Integrable (fun x => ‖u x‖ ^ 2) volume)
    (i j k : Fin 3) (v : E₃) (hv : ‖v‖ = 1) :
    |∫ x : E₃, χ x * (x i * x j / ‖x‖ ^ 5) * fderiv ℝ u x v k| ≤
      Real.sqrt (∫ x : E₃, ‖fderiv ℝ
        (fun y : E₃ => χ y * (y i * y j / ‖y‖ ^ 5)) x v‖ ^ 2) *
      Real.sqrt (∫ x : E₃, ‖u x‖ ^ 2) := by
  rw [integral_axis_far_mul_velocity_derivative hχ hzero hχ₀ hχ₁ houter
    hu hα hD henergy i j k v hv, abs_neg]
  exact abs_integral_mul_coordinate_le_sqrt_energy
    (memLp_fderiv_axis_far_coefficient hχ hzero houter i j v)
    ((memLp_two_iff_integrable_sq_norm hu.continuous.aestronglyMeasurable).mpr henergy) k

/-- Expansion of the signed axis kernel into its four Cartesian derivative terms. -/
theorem axis_far_curl_expansion (χ : E₃ → ℝ) (u : E₃ → E₃) (x : E₃) :
    χ x * (x 2 * (x 0 * curlLinearMap (fderiv ℝ u x) 1 -
      x 1 * curlLinearMap (fderiv ℝ u x) 0) / ‖x‖ ^ 5) =
    (χ x * (x 2 * x 0 / ‖x‖ ^ 5) * fderiv ℝ u x !₂[0, 0, 1] 0 -
      χ x * (x 2 * x 0 / ‖x‖ ^ 5) * fderiv ℝ u x !₂[1, 0, 0] 2) -
    (χ x * (x 2 * x 1 / ‖x‖ ^ 5) * fderiv ℝ u x !₂[0, 1, 0] 2 -
      χ x * (x 2 * x 1 / ‖x‖ ^ 5) * fderiv ℝ u x !₂[0, 0, 1] 1) := by
  simp only [curlLinearMap_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- For a fixed smooth cutoff the complete unit-scale far field is a bounded
functional of the velocity in `L²`. The constant is independent of the velocity
and of its Hölder bound; the transition annulus is included. -/
theorem exists_axis_far_energy_constant
    {χ : E₃ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : χ =ᶠ[𝓝 (0 : E₃)] 0)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : E₃ → E₃} {H α : ℝ≥0},
      Differentiable ℝ u → 0 < α → HolderWith H α (fderiv ℝ u) →
      Integrable (fun x => ‖u x‖ ^ 2) volume →
      Integrable (fun x : E₃ => χ x * (x 2 *
        (x 0 * curlLinearMap (fderiv ℝ u x) 1 -
          x 1 * curlLinearMap (fderiv ℝ u x) 0) / ‖x‖ ^ 5)) volume ∧
      |∫ x : E₃, χ x * (x 2 * (x 0 * curlLinearMap (fderiv ℝ u x) 1 -
        x 1 * curlLinearMap (fderiv ℝ u x) 0) / ‖x‖ ^ 5)| ≤
        C * Real.sqrt (∫ x : E₃, ‖u x‖ ^ 2) := by
  let B (i j : Fin 3) (v : E₃) : ℝ := Real.sqrt (∫ x : E₃,
    ‖fderiv ℝ (fun y : E₃ => χ y * (y i * y j / ‖y‖ ^ 5)) x v‖ ^ 2)
  refine ⟨B 2 0 !₂[0, 0, 1] + B 2 0 !₂[1, 0, 0] +
    (B 2 1 !₂[0, 1, 0] + B 2 1 !₂[0, 0, 1]), by dsimp [B]; positivity, ?_⟩
  intro u H α hu hα hD henergy
  have hi := integrable_axis_far_mul_velocity_derivative hχ hzero hχ₀ hχ₁ hu hα hD henergy
  have hiA := hi 2 0 0 !₂[0, 0, 1] (by simp [EuclideanSpace.norm_eq, Fin.sum_univ_three])
  have hiB := hi 2 0 2 !₂[1, 0, 0] (by simp [EuclideanSpace.norm_eq, Fin.sum_univ_three])
  have hiC := hi 2 1 2 !₂[0, 1, 0] (by simp [EuclideanSpace.norm_eq, Fin.sum_univ_three])
  have hiD := hi 2 1 1 !₂[0, 0, 1] (by simp [EuclideanSpace.norm_eq, Fin.sum_univ_three])
  refine ⟨by simpa only [axis_far_curl_expansion, Pi.sub_def] using
    (hiA.sub hiB).sub (hiC.sub hiD), ?_⟩
  simp_rw [axis_far_curl_expansion]
  have hsplit := integral_sub (hiA.sub hiB) (hiC.sub hiD)
  simp only [Pi.sub_apply, integral_sub hiA hiB, integral_sub hiC hiD] at hsplit
  rw [hsplit]
  have hb := abs_integral_axis_far_mul_velocity_derivative_le hχ hzero hχ₀ hχ₁ houter
    hu hα hD henergy
  refine (abs_sub _ _).trans ?_
  refine (add_le_add (abs_sub _ _) (abs_sub _ _)).trans ?_
  simpa only [add_mul, B] using add_le_add
    (add_le_add
      (hb 2 0 0 !₂[0, 0, 1] (by simp [EuclideanSpace.norm_eq, Fin.sum_univ_three]))
      (hb 2 0 2 !₂[1, 0, 0] (by simp [EuclideanSpace.norm_eq, Fin.sum_univ_three])))
    (add_le_add
      (hb 2 1 2 !₂[0, 1, 0] (by simp [EuclideanSpace.norm_eq, Fin.sum_univ_three]))
      (hb 2 1 1 !₂[0, 0, 1] (by simp [EuclideanSpace.norm_eq, Fin.sum_univ_three])))

end ClockBarrier.Analysis
