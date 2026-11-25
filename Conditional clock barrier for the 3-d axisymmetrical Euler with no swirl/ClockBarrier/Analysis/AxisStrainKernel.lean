/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Absolute convergence near the on-axis strain singularity

The Cartesian numerator retains the orientation of the curl. Values at
the single singular point do not affect the Lebesgue integral.
-/

public section

namespace ClockBarrier.Analysis

open Set Metric MeasureTheory
open scoped NNReal

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Each Cartesian coordinate is bounded by the Euclidean norm. -/
theorem abs_euclidean_coordinate_le_norm (x : E₃) (i : Fin 3) : |x i| ≤ ‖x‖ :=
  PiLp.norm_apply_le x i

/-- The azimuthal Cartesian numerator is controlled by the first two components. -/
theorem abs_axis_curl_numerator_le (x w : E₃) :
    |x 0 * w 1 - x 1 * w 0| ≤ ‖x‖ * (|w 0| + |w 1|) := by
  have hb := abs_sub (x 0 * w 1) (x 1 * w 0)
  calc
    _ ≤ |x 0 * w 1| + |x 1 * w 0| := hb
    _ ≤ ‖x‖ * |w 1| + ‖x‖ * |w 0| := by
      simpa only [abs_mul] using (add_le_add
        (mul_le_mul_of_nonneg_right (abs_euclidean_coordinate_le_norm x 0) (abs_nonneg (w 1)))
        (mul_le_mul_of_nonneg_right (abs_euclidean_coordinate_le_norm x 1) (abs_nonneg (w 0))))
    _ = _ := by ring

/-- The signed strain integrand is bounded by the two transverse curl components
times the order-three radial kernel. -/
theorem abs_axis_strain_kernel_le (x w : E₃) :
    |x 2 * (x 0 * w 1 - x 1 * w 0) / ‖x‖ ^ 5| ≤ (|w 0| + |w 1|) / ‖x‖ ^ 3 := by
  by_cases hx : x = 0
  · simp [hx]
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    rw [abs_div, abs_mul, abs_of_pos (pow_pos hn 5)]
    refine (div_le_div_of_nonneg_right
      (mul_le_mul (abs_euclidean_coordinate_le_norm x 2) (abs_axis_curl_numerator_le x w)
        (abs_nonneg _) (norm_nonneg _)) (pow_nonneg hn.le 5)).trans_eq ?_
    field_simp

/-- Hölder decay of the curl cancels the local order-three singularity. -/
theorem abs_axis_strain_kernel_le_rpow
    {ω : E₃ → E₃} {H α : ℝ≥0} (hω : HolderWith H α ω) (hzero : ω 0 = 0) (x : E₃) :
    |x 2 * (x 0 * ω x 1 - x 1 * ω x 0) / ‖x‖ ^ 5| ≤
      (2 * H) * ‖x‖ ^ ((α : ℝ) - 3) := by
  have hd : ‖ω x‖ ≤ H * ‖x‖ ^ (α : ℝ) := by
    simpa only [hzero, dist_zero_right] using hω.dist_le x 0
  by_cases hx : x = 0
  · simp only [hx, norm_zero, zero_pow (by decide : 5 ≠ 0), div_zero, abs_zero]
    positivity
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hb := add_le_add ((abs_euclidean_coordinate_le_norm (ω x) 0).trans hd)
      ((abs_euclidean_coordinate_le_norm (ω x) 1).trans hd)
    refine ((abs_axis_strain_kernel_le x (ω x)).trans
      (div_le_div_of_nonneg_right hb (pow_nonneg hn.le 3))).trans_eq ?_
    rw [Real.rpow_sub hn, Real.rpow_ofNat]
    ring

/-- No principal value is needed near a zero of a positive-exponent Hölder curl. -/
theorem integrableOn_axis_strain_kernel_ball
    {ω : E₃ → E₃} {H α : ℝ≥0} (hα : 0 < α)
    (hω : HolderWith H α ω) (hzero : ω 0 = 0) (r : ℝ) :
    IntegrableOn (fun x => x 2 * (x 0 * ω x 1 - x 1 * ω x 0) / ‖x‖ ^ 5)
      (ball 0 r) volume := by
  have hc := hω.continuous hα
  have hm : Measurable (fun x => x 2 * (x 0 * ω x 1 - x 1 * ω x 0) / ‖x‖ ^ 5) := by
    fun_prop
  apply integrableOn_ball_of_norm_le_rpow (by simp : 1 ≤ Module.finrank ℝ E₃)
    (α := 3 - (α : ℝ)) (C := 2 * H) (by simpa using sub_lt_self (3 : ℝ) hα)
    _ hm.aestronglyMeasurable
  filter_upwards with x
  simpa only [Real.norm_eq_abs, neg_sub] using abs_axis_strain_kernel_le_rpow hω hzero x

end ClockBarrier.Analysis
