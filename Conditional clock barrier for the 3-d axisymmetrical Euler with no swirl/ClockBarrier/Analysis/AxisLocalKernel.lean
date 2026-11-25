/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.AxisNearMajorant

/-! # The elementary inverse-cube majorant for the axis kernel -/

public section
namespace ClockBarrier.Analysis

/-- Two coordinate factors remove two powers from the axis kernel. -/
theorem axis_weight_mul_le_div_cube {r z d N : ℝ}
    (hz : 0 ≤ z) (hd : 0 ≤ d) (hN : 0 ≤ N)
    (hrd : r ≤ d) (hzd : z ≤ d) : r * z / d^5 * N ≤ N / d^3 := by
  by_cases he : d = 0
  · simp [he]
  · have hp : 0 < d := lt_of_le_of_ne hd (fun hc => he hc.symm)
    refine (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
      (mul_le_mul hrd hzd hz hd) (pow_nonneg hd 5)) hN).trans_eq ?_
    field_simp

end ClockBarrier.Analysis
