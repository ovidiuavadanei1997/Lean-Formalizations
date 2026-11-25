/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.NewtonianBounds
public import ClockBarrier.Analysis.DerivativeTail
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-! # Integrability needed for Newtonian integration by parts -/

public section

namespace ClockBarrier.Analysis

open MeasureTheory Set Metric
open scoped ContDiff NNReal

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The inverse-cube regularized weight is square integrable. -/
theorem memLp_newtonian_hessian_weight :
    MemLp (fun x : E₃ => (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2)) 2 volume := by
  apply (memLp_two_iff_integrable_sq
    (contDiff_newtonian_power _).continuous.aestronglyMeasurable).mpr
  have hi := integrable_rpow_neg_one_add_norm_sq (μ := volume) (E := E₃)
    (r := 6) (by norm_num)
  refine hi.congr (ae_of_all _ fun x => ?_)
  change (1 + ‖x‖ ^ 2) ^ (-(6 : ℝ) / 2) = ((1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2)) ^ 2
  rw [← Real.rpow_natCast ((1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2)) 2,
    ← Real.rpow_mul (by positivity)]
  norm_num

/-- Regularized Hessian entries are square integrable. -/
theorem memLp_fderiv_newtonian_gradient (i : Fin 3) (v : E₃) :
    MemLp (fun x : E₃ => fderiv ℝ
      (fun y : E₃ => -(y i * (1 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2))) x v) 2 volume := by
  have hc := ((contDiff_newtonian_gradient i).fderiv_right (m := 0) (by simp)).continuous
  refine (memLp_newtonian_hessian_weight.const_mul (4 * ‖v‖)).mono' ?_ ?_
  · exact (hc.clm_apply continuous_const).aestronglyMeasurable
  · exact ae_of_all _ fun x => by
      simpa only [Real.norm_eq_abs, mul_right_comm] using abs_fderiv_newtonian_gradient_le i x v

/-- Derivatives of the regularized Hessian entries are integrable. -/
theorem integrable_fderiv_newtonian_hessian (i : Fin 3) (v w : E₃) :
    Integrable (fun x : E₃ => fderiv ℝ (fun y : E₃ => fderiv ℝ
      (fun a : E₃ => -(a i * (1 + ‖a‖ ^ 2) ^ (-(3 : ℝ) / 2))) y v) x w) volume := by
  have hc : ContDiff ℝ 1 (fun y : E₃ => fderiv ℝ
      (fun a : E₃ => -(a i * (1 + ‖a‖ ^ 2) ^ (-(3 : ℝ) / 2))) y v) :=
    ((contDiff_newtonian_gradient i).fderiv_right (m := 1) (by decide)).clm_apply contDiff_const
  have hm := (((hc.fderiv_right (m := 0) (by norm_num)).continuous).clm_apply
    (continuous_const (y := w))).aestronglyMeasurable (μ := volume)
  have hi : Integrable (fun x : E₃ => (1 + ‖x‖ ^ 2) ^ (-2 : ℝ)) volume := by
    convert! integrable_rpow_neg_one_add_norm_sq (μ := volume) (E := E₃)
      (r := 4) (by norm_num) using 1
    norm_num
  refine (hi.const_mul (24 * ‖v‖ * ‖w‖)).mono' hm (ae_of_all _ fun x => ?_)
  convert! abs_fderiv_newtonian_hessian_le i x v w using 1
  ring

/-- A regularized Hessian times a velocity derivative is integrable, using the
finite-energy derivative-tail theorem for the part outside the unit ball. -/
theorem integrable_newtonian_hessian_mul_velocity_derivative
    {u : E₃ → E₃} {H α : ℝ≥0} (hu : Differentiable ℝ u)
    (hα : 0 < α) (hD : HolderWith H α (fderiv ℝ u))
    (henergy : Integrable (fun x => ‖u x‖ ^ 2) volume)
    (i j : Fin 3) (v w : E₃) (hw : ‖w‖ = 1) :
    Integrable (fun x : E₃ => fderiv ℝ
      (fun y : E₃ => -(y i * (1 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2))) x v *
        fderiv ℝ u x w j) volume := by
  have hcK := ((contDiff_newtonian_gradient i).fderiv_right (m := 0) (by simp)).continuous
  have hcD := hD.continuous hα
  have hc : Continuous (fun x : E₃ => fderiv ℝ
      (fun y : E₃ => -(y i * (1 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2))) x v *
        fderiv ℝ u x w j) := by fun_prop
  have hnear := hc.continuousOn.integrableOn_compact (μ := volume)
    (isCompact_closedBall (0 : E₃) 1)
  have ht := integrableOn_norm_fderiv_apply_div_cube_compl_ball hu hα hD henergy w hw
  have hfar : IntegrableOn (fun x : E₃ => fderiv ℝ
      (fun y : E₃ => -(y i * (1 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2))) x v *
        fderiv ℝ u x w j) (ball 0 1)ᶜ volume := by
    refine (ht.const_mul (4 * ‖v‖)).mono' hc.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with x hx
    have hx0 : x ≠ 0 := by
      intro heq
      subst x
      simp at hx
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ (4 * (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) * ‖v‖) * ‖fderiv ℝ u x w‖ :=
        mul_le_mul (abs_fderiv_newtonian_gradient_le i x v)
          (abs_euclidean_coordinate_le_norm _ j) (abs_nonneg _) (by positivity)
      _ ≤ (4 * (1 / ‖x‖ ^ 3) * ‖v‖) * ‖fderiv ℝ u x w‖ := by
        gcongr
        exact newtonian_hessian_weight_le_inv_cube hx0
      _ = _ := by ring
  simpa only [union_compl_self, integrableOn_univ] using
    (hnear.mono_set ball_subset_closedBall).union hfar

end ClockBarrier.Analysis
