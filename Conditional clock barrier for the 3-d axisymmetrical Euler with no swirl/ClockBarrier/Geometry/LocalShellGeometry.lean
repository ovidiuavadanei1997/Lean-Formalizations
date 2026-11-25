/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Label distances within a general dyadic shell -/

public section
namespace ClockBarrier.Geometry
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Coordinatewise absolute bounds control the Euclidean norm. -/
theorem norm_le_mul_of_coordinate_bounds {x y : E₃} {C : ℝ} (hC : 0 ≤ C)
    (hxy : ∀ i, |x i| ≤ C * |y i|) : ‖x‖ ≤ C * ‖y‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => by
    simpa only [mul_pow, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hxy i) 2)

/-- Two points in the same half-open coordinate shell have comparable label norms. -/
theorem norm_le_two_mul_of_shell_bounds {r : Fin 3 → ℝ} {x y : E₃}
    (hx : ∀ i, |x i| ≤ 2 * r i) (hy : ∀ i, r i ≤ |y i|) : ‖x‖ ≤ 2 * ‖y‖ := by
  exact norm_le_mul_of_coordinate_bounds (by norm_num) (fun i =>
    (hx i).trans (mul_le_mul_of_nonneg_left (hy i) (by norm_num)))

/-- The Euclidean transverse scale separates its common radial factor. -/
theorem norm_transverse_shell_scale {r : ℝ} (hr : 0 ≤ r) (l₀ l₁ : ℝ) :
    ‖(!₂[l₀ * r, l₁ * r, 0] : E₃)‖ = r * Real.sqrt (l₀ ^ 2 + l₁ ^ 2) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, mul_pow,
    Real.sq_sqrt (by positivity)]
  change (l₀ * r) ^ 2 + (l₁ * r) ^ 2 + 0 ^ 2 = _
  ring

/-- A fixed-height slice of the transverse box has diameter at most four times
its Euclidean transverse scale. -/
theorem norm_sub_le_transverse_shell_diameter {x y : E₃} {r l₀ l₁ : ℝ}
    (hr : 0 ≤ r) (hl₀ : 0 ≤ l₀) (hl₁ : 0 ≤ l₁) (hxy : x 2 = y 2)
    (hx₀ : |x 0| ≤ 2 * (l₀ * r)) (hx₁ : |x 1| ≤ 2 * (l₁ * r))
    (hy₀ : |y 0| ≤ 2 * (l₀ * r)) (hy₁ : |y 1| ≤ 2 * (l₁ * r)) :
    ‖x - y‖ ≤ 4 * (r * Real.sqrt (l₀ ^ 2 + l₁ ^ 2)) := by
  rw [← norm_transverse_shell_scale hr]
  apply norm_le_mul_of_coordinate_bounds (by norm_num)
  intro i
  fin_cases i
  · change |x 0 - y 0| ≤ 4 * |l₀ * r|
    rw [abs_of_nonneg (mul_nonneg hl₀ hr)]
    nlinarith only [abs_sub (x 0) (y 0), hx₀, hy₀]
  · change |x 1 - y 1| ≤ 4 * |l₁ * r|
    rw [abs_of_nonneg (mul_nonneg hl₁ hr)]
    nlinarith only [abs_sub (x 1) (y 1), hx₁, hy₁]
  · change |x 2 - y 2| ≤ 4 * |(0 : ℝ)|
    simp only [hxy, sub_self, abs_zero, mul_zero, le_refl]

end ClockBarrier.Geometry
