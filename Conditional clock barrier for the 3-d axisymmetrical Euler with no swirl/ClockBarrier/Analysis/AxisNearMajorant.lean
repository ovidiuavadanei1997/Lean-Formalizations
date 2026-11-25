/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.AxisStrainMajorant
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! # Local convergence of the nonnegative axis-strain majorant

Positive Hölder decay at an axis point makes the full norm-vorticity majorant
locally integrable. This is stronger than convergence of the signed kernel.
-/

public section

namespace ClockBarrier.Analysis

open Set Metric MeasureTheory
open scoped NNReal

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Cylindrical radius is at most the Euclidean norm. -/
theorem radius_le_norm (x : E₃) :
    Real.sqrt ((x 0)^2 + (x 1)^2) ≤ ‖x‖ := by
  simpa [EuclideanSpace.norm_eq, Fin.sum_univ_three, Real.norm_eq_abs, add_assoc] using
    Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg (x 2)) :
      (x 0)^2 + (x 1)^2 ≤ (x 0)^2 + (x 1)^2 + (x 2)^2)

/-- Hölder vanishing controls the full nonnegative cylindrical majorant. -/
theorem axis_near_majorant_le_rpow
    {ω : E₃ → E₃} {H α : ℝ≥0} (hω : HolderWith H α ω) (hzero : ω 0 = 0) (x : E₃) :
    Real.sqrt ((x 0)^2 + (x 1)^2) * |x 2| / ‖x‖ ^ 5 * ‖ω x‖ ≤
      H * ‖x‖ ^ ((α : ℝ) - 3) := by
  have hd : ‖ω x‖ ≤ H * ‖x‖ ^ (α : ℝ) := by
    simpa only [hzero, dist_zero_right] using hω.dist_le x 0
  by_cases hx : x = 0
  · simp only [hx, norm_zero, zero_pow (by decide : 5 ≠ 0), div_zero, zero_mul]
    positivity
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    refine (mul_le_mul
      (div_le_div_of_nonneg_right
        (mul_le_mul (radius_le_norm x) (abs_euclidean_coordinate_le_norm x 2)
          (abs_nonneg _) (norm_nonneg _)) (pow_nonneg hn.le 5))
      hd (norm_nonneg _) (by positivity)).trans_eq ?_
    rw [Real.rpow_sub hn, Real.rpow_ofNat]
    field_simp

/-- The norm-vorticity majorant is integrable on every ball about its zero. -/
theorem integrableOn_axis_near_majorant_ball
    {ω : E₃ → E₃} {H α : ℝ≥0} (hα : 0 < α)
    (hω : HolderWith H α ω) (hzero : ω 0 = 0) (r : ℝ) :
    IntegrableOn (fun x => Real.sqrt ((x 0)^2 + (x 1)^2) * |x 2| / ‖x‖ ^ 5 * ‖ω x‖)
      (ball 0 r) volume := by
  have hc := hω.continuous hα
  have hm : Measurable
      (fun x => Real.sqrt ((x 0)^2 + (x 1)^2) * |x 2| / ‖x‖ ^ 5 * ‖ω x‖) := by fun_prop
  apply integrableOn_ball_of_norm_le_rpow (by simp : 1 ≤ Module.finrank ℝ E₃)
    (α := 3 - (α : ℝ)) (C := H) (by simpa using sub_lt_self (3 : ℝ) hα)
    _ hm.aestronglyMeasurable
  filter_upwards with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ Real.sqrt ((x 0)^2 + (x 1)^2) * |x 2| / ‖x‖ ^ 5 * ‖ω x‖), neg_sub]
    using axis_near_majorant_le_rpow hω hzero x

/-- Translation and enlargement of the ball give convergence on the source's
closed physical near region about any axis height. -/
theorem integrableOn_axis_near_majorant_closedBall
    {ω : E₃ → E₃} {H α : ℝ≥0} (hα : 0 < α)
    (hω : HolderWith H α ω) (z : ℝ) (hzero : ω !₂[0, 0, z] = 0) (L : ℝ) :
    IntegrableOn (fun x => Real.sqrt ((x 0)^2 + (x 1)^2) * |x 2 - z| /
      ‖x - !₂[0, 0, z]‖ ^ 5 * ‖ω x‖) (closedBall !₂[0, 0, z] L) volume := by
  have hω' : HolderWith H α (fun x => ω (x + !₂[0, 0, z])) := by
    intro x y
    simpa only [edist_add_right] using hω (x + !₂[0, 0, z]) (y + !₂[0, 0, z])
  have hi := (integrableOn_axis_near_majorant_ball hα hω'
    (by simpa only [zero_add] using hzero) (L + 1)).mono_set
      (closedBall_subset_ball (lt_add_one L))
  have ht := ((measurePreserving_add_right volume (-(!₂[0, 0, z] : E₃))).integrableOn_comp_preimage
    (Homeomorph.addRight (-(!₂[0, 0, z] : E₃))).measurableEmbedding).mpr hi
  simpa [Function.comp_def, ← sub_eq_add_neg, PiLp.sub_apply, Metric.closedBall, dist_eq_norm]
    using ht

end ClockBarrier.Analysis
