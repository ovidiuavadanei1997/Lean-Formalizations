/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.NewtonianIntegrability
public import ClockBarrier.Analysis.MixedIntegration
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! # Global integration by parts for the regularized Newtonian kernel -/

public section

namespace ClockBarrier.Analysis

open MeasureTheory
open scoped NNReal ContDiff

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Taking a scalar component commutes with an actual spatial derivative. -/
theorem fderiv_component_apply {u : E₃ → E₃} {x : E₃}
    (hu : DifferentiableAt ℝ u x) (j : Fin 3) (v : E₃) :
    fderiv ℝ (fun y => u y j) x v = fderiv ℝ u x v j := by
  have hd : HasFDerivAt (fun y => u y j)
      ((EuclideanSpace.proj (𝕜 := ℝ) j).comp (fderiv ℝ u x)) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp x hu.hasFDerivAt
  rw [hd.fderiv]
  rfl

/-- The two derivative directions can be exchanged inside the whole-space
integral. All integrability obligations follow from the stated velocity regularity. -/
theorem integral_newtonian_derivative_swap
    {u : E₃ → E₃} {H α : ℝ≥0} (hu : Differentiable ℝ u)
    (hα : 0 < α) (hD : HolderWith H α (fderiv ℝ u))
    (henergy : Integrable (fun x => ‖u x‖ ^ 2) volume)
    {B : ℝ} (hbound : ∀ x, ‖u x‖ ≤ B)
    (i j : Fin 3) (v w : E₃) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    (∫ x : E₃, fderiv ℝ
      (fun y : E₃ => -(y i * (1 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2))) x v * fderiv ℝ u x w j) =
    ∫ x : E₃, fderiv ℝ
      (fun y : E₃ => -(y i * (1 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2))) x w * fderiv ℝ u x v j := by
  have huc : Differentiable ℝ (fun x => u x j) :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).differentiable.comp hu
  have hL2 : MemLp (fun x => u x j) 2 volume :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).comp_memLp'
      ((memLp_two_iff_integrable_sq_norm hu.continuous.aestronglyMeasurable).mpr henergy)
  have hk : ContDiff ℝ 2 (fun y : E₃ => -(y i * (1 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2))) :=
    (contDiff_newtonian_gradient i).of_le (by decide)
  suffices (∫ x : E₃, fderiv ℝ
      (fun y : E₃ => -(y i * (1 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2))) x v *
        fderiv ℝ (fun y => u y j) x w) =
      ∫ x : E₃, fderiv ℝ
        (fun y : E₃ => -(y i * (1 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2))) x w *
          fderiv ℝ (fun y => u y j) x v by
    simpa only [fderiv_component_apply (hu _)] using this
  apply integral_fderiv_mul_fderiv_swap hk huc v w
  · simpa only [fderiv_component_apply (hu _)] using
      integrable_newtonian_hessian_mul_velocity_derivative hu hα hD henergy i j v w hw
  · simpa only [fderiv_component_apply (hu _)] using
      integrable_newtonian_hessian_mul_velocity_derivative hu hα hD henergy i j w v hv
  · exact (memLp_fderiv_newtonian_gradient i v).integrable_mul hL2
  · exact (memLp_fderiv_newtonian_gradient i w).integrable_mul hL2
  · have hi := (integrable_fderiv_newtonian_hessian i v w).mul_bdd
      huc.continuous.aestronglyMeasurable
      (ae_of_all _ fun x => (abs_euclidean_coordinate_le_norm (u x) j).trans (hbound x))
    have hd := (hk.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    simpa only [fderiv_clm_apply (hd _) (differentiableAt_const v), fderiv_const_apply,
      ContinuousLinearMap.comp_zero, add_apply, zero_apply, zero_add,
      ContinuousLinearMap.flip_apply] using hi

end ClockBarrier.Analysis
