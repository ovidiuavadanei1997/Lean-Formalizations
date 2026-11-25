/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.AxisFarCutoff
public import ClockBarrier.Analysis.NewtonianIntegrationByParts
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Tactic.GCongr

/-! # Integration by parts for the smooth far-field kernel

The cutoff is retained on the whole space. Its differentiated coefficients
therefore include the transition annulus.
-/

public section

namespace ClockBarrier.Analysis

open Set Metric MeasureTheory
open scoped Topology ContDiff NNReal

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The cutoff coefficient times a velocity derivative is integrable under the
finite-energy and spatial Hölder hypotheses used by the Euler interface. -/
theorem integrable_axis_far_mul_velocity_derivative
    {χ : E₃ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : χ =ᶠ[𝓝 (0 : E₃)] 0)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    {u : E₃ → E₃} {H α : ℝ≥0} (hu : Differentiable ℝ u)
    (hα : 0 < α) (hD : HolderWith H α (fderiv ℝ u))
    (henergy : Integrable (fun x => ‖u x‖ ^ 2) volume)
    (i j k : Fin 3) (v : E₃) (hv : ‖v‖ = 1) :
    Integrable (fun x : E₃ => χ x * (x i * x j / ‖x‖ ^ 5) *
      fderiv ℝ u x v k) volume := by
  have hcD := hD.continuous hα
  have hc : Continuous (fun x : E₃ => χ x * (x i * x j / ‖x‖ ^ 5) *
      fderiv ℝ u x v k) :=
    (contDiff_axis_far_coefficient hχ hzero i j).continuous.mul
      ((EuclideanSpace.proj k).continuous.comp (hcD.clm_apply continuous_const))
  have hnear := hc.continuousOn.integrableOn_compact (μ := volume)
    (isCompact_closedBall (0 : E₃) 1)
  have ht := integrableOn_norm_fderiv_apply_div_cube_compl_ball hu hα hD henergy v hv
  have hfar : IntegrableOn (fun x : E₃ => χ x * (x i * x j / ‖x‖ ^ 5) *
      fderiv ℝ u x v k) (ball 0 1)ᶜ volume := by
    refine ht.mono' hc.aestronglyMeasurable.restrict (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hχ₀ x)]
    simpa only [one_mul, one_div, div_eq_mul_inv, mul_comm] using
      mul_le_mul (mul_le_mul (hχ₁ x) (abs_axis_strain_coefficient_le i j x)
        (abs_nonneg _) (by positivity))
        (abs_euclidean_coordinate_le_norm _ k) (abs_nonneg _) (by positivity)
  simpa only [union_compl_self, integrableOn_univ] using
    (hnear.mono_set ball_subset_closedBall).union hfar

/-- Moving a velocity derivative onto the full cutoff coefficient retains
every transition-annulus contribution. -/
theorem integral_axis_far_mul_velocity_derivative
    {χ : E₃ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : χ =ᶠ[𝓝 (0 : E₃)] 0)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1)
    {u : E₃ → E₃} {H α : ℝ≥0} (hu : Differentiable ℝ u)
    (hα : 0 < α) (hD : HolderWith H α (fderiv ℝ u))
    (henergy : Integrable (fun x => ‖u x‖ ^ 2) volume)
    (i j k : Fin 3) (v : E₃) (hv : ‖v‖ = 1) :
    (∫ x : E₃, χ x * (x i * x j / ‖x‖ ^ 5) * fderiv ℝ u x v k) =
      -(∫ x : E₃, fderiv ℝ (fun y : E₃ => χ y * (y i * y j / ‖y‖ ^ 5)) x v * u x k) := by
  have hL2 : MemLp (fun x => u x k) 2 volume :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).comp_memLp'
      ((memLp_two_iff_integrable_sq_norm hu.continuous.aestronglyMeasurable).mpr henergy)
  have hi := integrable_axis_far_mul_velocity_derivative hχ hzero hχ₀ hχ₁ hu hα hD henergy
    i j k v hv
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((memLp_fderiv_axis_far_coefficient hχ hzero houter i j v).integrable_mul hL2)
    (by simpa only [fderiv_component_apply (hu _)] using hi)
    ((memLp_axis_far_coefficient hχ hzero houter i j).integrable_mul hL2)
    (fun x _ => (contDiff_axis_far_coefficient hχ hzero i j).differentiable (by simp) x)
    (fun x _ => (EuclideanSpace.proj (𝕜 := ℝ) k).differentiableAt.comp x (hu x))
  simpa only [fderiv_component_apply (hu _)] using hibp

end ClockBarrier.Analysis
