/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Pointwise kernel bounds and clock scaling in the axis-driver estimate -/

public section

namespace ClockBarrier.Analysis

/-- The axial coordinate is bounded by the distance, removing one singular power. -/
theorem abs_axis_kernel_le {r z d : ℝ} (hr : 0 ≤ r) (hd : 0 < d) (hz : |z| ≤ d) :
    |r * z / d ^ 5| ≤ r / d ^ 4 := by
  rw [abs_div, abs_mul, abs_of_nonneg hr, abs_of_pos (pow_pos hd 5),
    div_le_iff₀ (pow_pos hd 5)]
  calc
    r * |z| ≤ r * d := mul_le_mul_of_nonneg_left hz hr
    _ = r / d ^ 4 * d ^ 5 := by field_simp

/-- Upper radial and lower distance comparisons give a uniform block kernel bound. -/
theorem abs_axis_kernel_le_of_comparisons {r z d R D : ℝ}
    (hr : 0 ≤ r) (hD : 0 < D) (hDd : D ≤ d) (hrR : r ≤ R) (hz : |z| ≤ d) :
    |r * z / d ^ 5| ≤ R / D ^ 4 := by
  calc
    |r * z / d ^ 5| ≤ r / d ^ 4 := abs_axis_kernel_le hr (hD.trans_le hDd) hz
    _ ≤ R / d ^ 4 := div_le_div_of_nonneg_right hrR (by positivity)
    _ ≤ R / D ^ 4 := div_le_div_of_nonneg_left (hr.trans hrR) (pow_pos hD 4)
      (pow_le_pow_left₀ hD.le hDd 4)

/-- The anisotropic clock geometry produces the axis kernel's J⁻⁶ scaling. -/
theorem abs_axis_kernel_le_clock_scale {r z d l J Λ cR cd : ℝ}
    (hr : 0 ≤ r) (hl : 0 < l) (hJ : 0 < J) (hΛ : 0 < Λ) (hcd : 0 < cd)
    (hrR : r ≤ cR * l * J ^ 2 * Λ)
    (hDd : cd * J ^ 2 * Λ * Real.sqrt (1 + l ^ 2) ≤ d) (hz : |z| ≤ d) :
    |r * z / d ^ 5| ≤ (cR / cd ^ 4) * (l / (J ^ 6 * Λ ^ 3 * (1 + l ^ 2) ^ 2)) := by
  have h := abs_axis_kernel_le_of_comparisons hr
    (by positivity : 0 < cd * J ^ 2 * Λ * Real.sqrt (1 + l ^ 2)) hDd hrR hz
  convert h using 1
  have hsqrt : (Real.sqrt (1 + l ^ 2)) ^ 4 = (1 + l ^ 2) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by positivity)]
  simp only [mul_pow, hsqrt]
  field_simp

/-- Kernel, stretching, and cusp mass combine into the exact clock power 3α−1. -/
theorem axis_kernel_cusp_scaling {l J Λ α : ℝ}
    (hl : 0 < l) (hJ : 0 < J) (hΛ : 0 < Λ) :
    (l / (J ^ 6 * Λ ^ 3 * (1 + l ^ 2) ^ 2)) *
        (J⁻¹ * (l ^ (α + 2) * J ^ (3 * α + 6) * Λ ^ (α + 3))) =
      J ^ (3 * α - 1) * (l ^ (α + 3) / (1 + l ^ 2) ^ 2) * Λ ^ α := by
  rw [Real.rpow_add hΛ α 3, Real.rpow_ofNat]
  rw [show 3 * α + 6 = (3 * α - 1) + 7 by ring, Real.rpow_add hJ, Real.rpow_ofNat]
  rw [show α + 3 = (α + 2) + 1 by ring, Real.rpow_add hl (α + 2) 1, Real.rpow_one]
  field_simp

end ClockBarrier.Analysis
