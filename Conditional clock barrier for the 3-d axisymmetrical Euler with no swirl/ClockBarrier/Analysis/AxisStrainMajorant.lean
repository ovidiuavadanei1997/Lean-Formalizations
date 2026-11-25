/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.AxisStrainKernel
import Mathlib.Tactic.Ring

/-! # The sharp cylindrical majorant of the signed Cartesian strain kernel -/

public section

namespace ClockBarrier.Analysis

open MeasureTheory

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The Cartesian azimuthal numerator is bounded by radius times vorticity norm,
with no loss in the constant. -/
theorem abs_axis_curl_numerator_le_radius (x w : E₃) :
    |x 0 * w 1 - x 1 * w 0| ≤ Real.sqrt ((x 0)^2 + (x 1)^2) * ‖w‖ := by
  have h := abs_real_inner_le_norm (!₂[-x 1, x 0, 0] : E₃) w
  simpa [PiLp.inner_apply, EuclideanSpace.norm_eq, Fin.sum_univ_three,
    Real.inner_apply, sub_eq_add_neg, add_comm, mul_comm] using h

/-- Reversing the axial difference changes only the sign. The same cylindrical
majorant controls the signed integrand even at a zero denominator. -/
theorem abs_signed_axis_kernel_le (x w : E₃) (z d : ℝ) :
    |(z - x 2) * (x 0 * w 1 - x 1 * w 0) / d| ≤
      |(Real.sqrt ((x 0)^2 + (x 1)^2) * (x 2 - z) / d) * ‖w‖| := by
  have h := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (abs_axis_curl_numerator_le_radius x w)
      (abs_nonneg (z - x 2))) (abs_nonneg d)
  simpa only [abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (norm_nonneg _), abs_sub_comm (x 2) z,
    div_eq_mul_inv, abs_inv, mul_assoc, mul_comm, mul_left_comm] using h

end ClockBarrier.Analysis
