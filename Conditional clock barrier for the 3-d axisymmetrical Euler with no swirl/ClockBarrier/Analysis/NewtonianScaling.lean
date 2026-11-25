/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.NewtonianLimit
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Scaling of the regularized signed strain integral -/

public section

namespace ClockBarrier.Analysis

open MeasureTheory

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- A positive spatial dilation rescales the regularizing length. -/
theorem newtonian_power_smul {ε : ℝ} (hε : 0 < ε) (x : E₃) :
    (ε ^ 2 + ‖ε • x‖ ^ 2) ^ (-(5 : ℝ) / 2) =
      (ε ^ 5)⁻¹ * (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) := by
  rw [norm_smul, Real.norm_of_nonneg hε.le]
  rw [show ε ^ 2 + (ε * ‖x‖) ^ 2 = ε ^ 2 * (1 + ‖x‖ ^ 2) by ring,
    Real.mul_rpow (sq_nonneg ε) (by positivity)]
  rw [← Real.rpow_natCast ε 2, ← Real.rpow_mul hε.le]
  norm_num [Real.rpow_neg hε.le]

/-- Whole-space change of variables carries the unit-scale curl integral to any
positive regularizing length. -/
theorem integral_regularized_axis_kernel_scaling (ω : E₃ → E₃)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ x : E₃, 3 * x 2 * (x 0 * ω (ε • x) 1 - x 1 * ω (ε • x) 0) *
      (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)) =
    ∫ x : E₃, 3 * x 2 * (x 0 * ω x 1 - x 1 * ω x 0) *
      (ε ^ 2 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) := by
  let f (x : E₃) : ℝ := 3 * x 2 * (x 0 * ω x 1 - x 1 * ω x 0) *
    (ε ^ 2 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)
  have hscale (x : E₃) : f (ε • x) = (ε ^ 3)⁻¹ *
      (3 * x 2 * (x 0 * ω (ε • x) 1 - x 1 * ω (ε • x) 0) *
        (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)) := by
    simp only [f, newtonian_power_smul hε, PiLp.smul_apply, smul_eq_mul]
    field_simp
  apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 hε.ne'))
  calc
    _ = ∫ x : E₃, f (ε • x) := by simp_rw [hscale]; rw [integral_const_mul]
    _ = _ := by
      simpa only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] using
        Measure.integral_comp_smul_of_nonneg (volume : Measure E₃) f ε (hR := hε.le)

end ClockBarrier.Analysis
