/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.Scalar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Passing from an axis strain bound to a uniform clock barrier -/

public section

namespace ClockBarrier.Analysis

open Set MeasureTheory

/-- Keep the factor one-half when passing from the strain estimate to the clock inequality. -/
theorem neg_linear_power_le_axis_clock_driver {J W B C α : ℝ} (hJ : 0 < J)
    (hW : |W| ≤ B + C * J ^ (3 * α - 1)) :
    -(B / 2) * J - (C / 2) * J ^ (3 * α) ≤ (1 / 2 : ℝ) * J * W := by
  have hpow : J * J ^ (3 * α - 1) = J ^ (3 * α) := by
    simpa only [Real.rpow_one, show 1 + (3 * α - 1) = 3 * α by ring] using
      (Real.rpow_add hJ 1 (3 * α - 1)).symm
  rw [← hpow]
  nlinarith [mul_le_mul_of_nonneg_left ((neg_le_abs W).trans hW) hJ.le]

/-- A common integrable axis-strain estimate prevents collapse uniformly over all clocks.
Continuity of each clock follows from its actual evolution equation. -/
theorem exists_pos_lower_bound_of_axis_driver
    {B : ℝ → ℝ} {T C α : ℝ} (hC : 0 ≤ C) (hα : (1 / 3 : ℝ) ≤ α)
    (hB : IntegrableOn B (Ico 0 T)) (hB₀ : ∀ t ∈ Ico 0 T, 0 ≤ B t) :
    ∃ c : ℝ, 0 < c ∧ ∀ (J W : ℝ → ℝ), J 0 = 1 →
      (∀ t ∈ Ico 0 T, 0 < J t) →
      (∀ t ∈ Ico 0 T, HasDerivWithinAt J ((1 / 2 : ℝ) * J t * W t) (Ico 0 T) t) →
      (∀ t ∈ Ioo 0 T, J t ≤ 1 → |W t| ≤ B t + C * (J t) ^ (3 * α - 1)) →
      ∀ t ∈ Ico 0 T, c ≤ J t := by
  obtain ⟨c, hc₀, hc⟩ := exists_pos_lower_bound_of_power_deriv_ge
    (B := fun t => B t / 2) (T := T) (C := C / 2) (p := 3 * α)
    (by positivity) (by linarith) (hB.div_const 2)
    (fun t ht => div_nonneg (hB₀ t ht) (by norm_num))
  refine ⟨c, hc₀, fun J W hinit hpos hode hdriver =>
    hc J (fun t => (1 / 2 : ℝ) * J t * W t)
      (fun t ht => (hode t ht).continuousWithinAt) hinit hpos ?_ ?_⟩
  · intro t ht
    exact ((hode t ⟨ht.1.le, ht.2⟩).hasDerivAt (Ico_mem_nhds ht.1 ht.2)).hasDerivWithinAt
  · exact fun t ht hsmall => neg_linear_power_le_axis_clock_driver
      (hpos t ⟨ht.1.le, ht.2⟩) (hdriver t ht hsmall)

end ClockBarrier.Analysis
