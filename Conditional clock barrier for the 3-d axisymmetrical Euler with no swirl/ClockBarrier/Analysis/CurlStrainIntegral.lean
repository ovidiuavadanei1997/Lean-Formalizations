/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.DerivativeTail
public import ClockBarrier.Geometry.CurlBounds
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Group.Integral

/-! # Absolute integrability of the Cartesian curl strain kernel -/

public section

namespace ClockBarrier.Analysis

open Set Metric MeasureTheory Geometry
open scoped NNReal

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- At a zero of the curl, the strain integral is absolutely convergent. The
infinite tail is derived from finite energy and Hölder regularity of the derivative. -/
theorem integrable_axis_strain_curl_fderiv
    {u : E₃ → E₃} {H α : ℝ≥0} (hu : Differentiable ℝ u)
    (hα : 0 < α) (hD : HolderWith H α (fderiv ℝ u))
    (henergy : Integrable (fun x => ‖u x‖ ^ 2) volume)
    (hzero : curlLinearMap (fderiv ℝ u 0) = 0) :
    Integrable (fun x => x 2 *
      (x 0 * curlLinearMap (fderiv ℝ u x) 1 - x 1 * curlLinearMap (fderiv ℝ u x) 0) /
        ‖x‖ ^ 5) volume := by
  let ω : E₃ → E₃ := fun x => curlLinearMap (fderiv ℝ u x)
  have hω : HolderWith (‖curlLinearMap‖₊ * H) α ω := holderWith_curlLinearMap hD
  have hnear := integrableOn_axis_strain_kernel_ball hα hω hzero 1
  have hi (v : E₃) (hv : ‖v‖ = 1) :=
    integrableOn_norm_fderiv_apply_div_cube_compl_ball hu hα hD henergy v hv
  have hi₀ := hi !₂[1, 0, 0] (by simp [EuclideanSpace.norm_eq, Fin.sum_univ_three])
  have hi₁ := hi !₂[0, 1, 0] (by simp [EuclideanSpace.norm_eq, Fin.sum_univ_three])
  have hi₂ := hi !₂[0, 0, 1] (by simp [EuclideanSpace.norm_eq, Fin.sum_univ_three])
  have hmajor : IntegrableOn (fun x =>
      ((‖fderiv ℝ u x !₂[0, 1, 0]‖ + ‖fderiv ℝ u x !₂[0, 0, 1]‖) +
        (‖fderiv ℝ u x !₂[0, 0, 1]‖ + ‖fderiv ℝ u x !₂[1, 0, 0]‖)) / ‖x‖ ^ 3)
      (ball 0 1)ᶜ volume := by
    simpa only [IntegrableOn, Pi.add_def, add_div] using (hi₁.add hi₂).add (hi₂.add hi₀)
  have hc := hω.continuous hα
  have hm : Measurable (fun x => x 2 * (x 0 * ω x 1 - x 1 * ω x 0) / ‖x‖ ^ 5) := by
    fun_prop
  have hfar : IntegrableOn (fun x => x 2 * (x 0 * ω x 1 - x 1 * ω x 0) / ‖x‖ ^ 5)
      (ball 0 1)ᶜ volume := hmajor.mono' hm.aestronglyMeasurable.restrict (ae_of_all _ fun x =>
        (abs_axis_strain_kernel_le x (ω x)).trans
          (div_le_div_of_nonneg_right (abs_curlLinearMap_transverse_le _) (by positivity)))
  simpa only [union_compl_self, integrableOn_univ] using hnear.union hfar

/-- Translation gives absolute convergence at any point where the curl vanishes. -/
theorem integrable_axis_strain_curl_fderiv_sub
    {u : E₃ → E₃} {H α : ℝ≥0} (hu : Differentiable ℝ u)
    (hα : 0 < α) (hD : HolderWith H α (fderiv ℝ u))
    (henergy : Integrable (fun x => ‖u x‖ ^ 2) volume)
    (a : E₃) (hzero : curlLinearMap (fderiv ℝ u a) = 0) :
    Integrable (fun x => (x - a) 2 *
      ((x - a) 0 * curlLinearMap (fderiv ℝ u x) 1 -
        (x - a) 1 * curlLinearMap (fderiv ℝ u x) 0) / ‖x - a‖ ^ 5) volume := by
  have hdiff : Differentiable ℝ (fun x => u (x + a)) :=
    fun x => (differentiableAt_comp_add_right a).mpr (hu (x + a))
  have hDa : HolderWith H α (fderiv ℝ (fun x => u (x + a))) := by
    intro x y
    simpa only [fderiv_comp_add_right, edist_add_right] using hD (x + a) (y + a)
  have hi := integrable_axis_strain_curl_fderiv hdiff hα hDa (henergy.comp_add_right a)
    (by simpa only [fderiv_comp_add_right, zero_add] using hzero)
  simpa only [fderiv_comp_add_right, ← sub_eq_add_neg, sub_add_cancel] using
    hi.comp_add_right (-a)

end ClockBarrier.Analysis
