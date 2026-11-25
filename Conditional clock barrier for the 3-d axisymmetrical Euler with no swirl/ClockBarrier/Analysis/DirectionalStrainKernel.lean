/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.AxisStrainKernel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The directional strain kernel and its local absolute convergence -/

public section
namespace ClockBarrier.Analysis
open Set Metric MeasureTheory
open scoped NNReal InnerProductSpace
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The Cartesian cross-product vector obeys the Euclidean area bound. -/
theorem norm_cartesian_cross_le (x w : E₃) :
    ‖(!₂[x 1 * w 2 - x 2 * w 1, x 2 * w 0 - x 0 * w 2,
      x 0 * w 1 - x 1 * w 0] : E₃)‖ ≤ ‖x‖ * ‖w‖ := by
  let v : E₃ := !₂[x 1 * w 2 - x 2 * w 1, x 2 * w 0 - x 0 * w 2,
    x 0 * w 1 - x 1 * w 0]
  have hsq : ‖v‖ ^ 2 + ⟪x, w⟫_ℝ ^ 2 = (‖x‖ * ‖w‖) ^ 2 := by
    simp only [mul_pow, EuclideanSpace.real_norm_sq_eq,
      EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct, Fin.sum_univ_three]
    simp [v]
    ring
  change ‖v‖ ≤ ‖x‖ * ‖w‖
  nlinarith [sq_nonneg ⟪x, w⟫_ℝ, norm_nonneg v, mul_nonneg (norm_nonneg x) (norm_nonneg w)]

/-- The directional kernel has inverse-cube size, uniformly in a unit direction. -/
theorem abs_directional_strain_kernel_le (x w e : E₃) (he : ‖e‖ = 1) :
    |⟪e, x⟫_ℝ *
      ⟪e, (!₂[x 1 * w 2 - x 2 * w 1, x 2 * w 0 - x 0 * w 2,
        x 0 * w 1 - x 1 * w 0] : E₃)⟫_ℝ / ‖x‖ ^ 5| ≤ ‖w‖ / ‖x‖ ^ 3 := by
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hfirst : |⟪e, x⟫_ℝ| ≤ ‖x‖ := by
    simpa only [he, one_mul] using abs_real_inner_le_norm e x
  have hsecond :
      |⟪e, (!₂[x 1 * w 2 - x 2 * w 1, x 2 * w 0 - x 0 * w 2,
        x 0 * w 1 - x 1 * w 0] : E₃)⟫_ℝ| ≤ ‖x‖ * ‖w‖ := by
    have hi := abs_real_inner_le_norm e
      (!₂[x 1 * w 2 - x 2 * w 1, x 2 * w 0 - x 0 * w 2,
        x 0 * w 1 - x 1 * w 0] : E₃)
    simp only [he, one_mul] at hi
    exact hi.trans (norm_cartesian_cross_le x w)
  rw [abs_div, abs_mul, abs_of_pos (pow_pos hn 5)]
  refine (div_le_div_of_nonneg_right
    (mul_le_mul hfirst hsecond (abs_nonneg _) (norm_nonneg x))
    (pow_nonneg hn.le 5)).trans_eq ?_
  field_simp

/-- Subtracting the value at the center gives a locally integrable power bound. -/
theorem abs_directional_strain_increment_le_rpow
    {ω : E₃ → E₃} {H α : ℝ≥0} (hω : HolderWith H α ω) (e : E₃) (he : ‖e‖ = 1)
    (x : E₃) :
    let w := ω x - ω 0
    |⟪e, x⟫_ℝ *
      ⟪e, (!₂[x 1 * w 2 - x 2 * w 1, x 2 * w 0 - x 0 * w 2,
        x 0 * w 1 - x 1 * w 0] : E₃)⟫_ℝ / ‖x‖ ^ 5| ≤
      H * ‖x‖ ^ ((α : ℝ) - 3) := by
  intro w
  have hd : ‖w‖ ≤ H * ‖x‖ ^ (α : ℝ) := by
    simpa only [dist_eq_norm, sub_zero] using hω.dist_le x 0
  by_cases hx : x = 0
  · simp only [hx, norm_zero, zero_pow (by decide : 5 ≠ 0), div_zero, abs_zero]
    positivity
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  refine ((abs_directional_strain_kernel_le x w e he).trans
    (div_le_div_of_nonneg_right hd (pow_nonneg hn.le 3))).trans_eq ?_
  rw [Real.rpow_sub hn, Real.rpow_ofNat]
  ring

/-- The subtracted directional strain integral is absolutely convergent on
every ball, for any positive Hölder exponent. -/
theorem integrableOn_directional_strain_increment_ball
    {ω : E₃ → E₃} {H α : ℝ≥0} (hα : 0 < α)
    (hω : HolderWith H α ω) (e : E₃) (he : ‖e‖ = 1) (r : ℝ) :
    IntegrableOn (fun x : E₃ =>
      let w := ω x - ω 0
      ⟪e, x⟫_ℝ *
        ⟪e, (!₂[x 1 * w 2 - x 2 * w 1, x 2 * w 0 - x 0 * w 2,
          x 0 * w 1 - x 1 * w 0] : E₃)⟫_ℝ / ‖x‖ ^ 5) (ball 0 r) volume := by
  have hc := hω.continuous hα
  have hm : Measurable (fun x : E₃ =>
      let w := ω x - ω 0
      ⟪e, x⟫_ℝ *
        ⟪e, (!₂[x 1 * w 2 - x 2 * w 1, x 2 * w 0 - x 0 * w 2,
          x 0 * w 1 - x 1 * w 0] : E₃)⟫_ℝ / ‖x‖ ^ 5) := by fun_prop
  apply integrableOn_ball_of_norm_le_rpow (by simp : 1 ≤ Module.finrank ℝ E₃)
    (α := 3 - (α : ℝ)) (C := H) (by simpa using sub_lt_self (3 : ℝ) hα)
    _ hm.aestronglyMeasurable
  filter_upwards with x
  simpa only [Real.norm_eq_abs, neg_sub] using abs_directional_strain_increment_le_rpow hω e he x

end ClockBarrier.Analysis
