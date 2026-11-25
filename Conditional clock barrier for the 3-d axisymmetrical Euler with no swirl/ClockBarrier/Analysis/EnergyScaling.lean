/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.VelocityScaling
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Exact kinetic-energy scaling for the strain normalization -/

public section

namespace ClockBarrier.Analysis

open MeasureTheory

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Spatial dilation and inverse amplitude give the fifth inverse power in energy. -/
theorem integral_sq_norm_rescaled_velocity (u : E₃ → E₃) {L : ℝ} (hL : 0 < L) :
    (∫ x : E₃, ‖L⁻¹ • u (L • x)‖ ^ 2) = (L ^ 5)⁻¹ * ∫ x : E₃, ‖u x‖ ^ 2 := by
  simp_rw [norm_smul, mul_pow]
  rw [integral_const_mul]
  have hs := Measure.integral_comp_smul_of_nonneg (volume : Measure E₃)
    (fun x => ‖u x‖ ^ 2) L (hR := hL.le)
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at hs
  rw [hs, norm_inv, Real.norm_of_nonneg hL.le]
  ring

/-- The `L²` scaling exponent is exactly `-5 / 2`. -/
theorem sqrt_energy_rescaled_velocity (u : E₃ → E₃) {L : ℝ} (hL : 0 < L) :
    Real.sqrt (∫ x : E₃, ‖L⁻¹ • u (L • x)‖ ^ 2) =
      L ^ (-(5 : ℝ) / 2) * Real.sqrt (∫ x : E₃, ‖u x‖ ^ 2) := by
  rw [integral_sq_norm_rescaled_velocity u hL, Real.sqrt_mul (by positivity)]
  have hp : (L ^ 5)⁻¹ = L ^ (-(5 : ℝ)) := by simp [Real.rpow_neg hL.le]
  rw [hp, Real.sqrt_eq_rpow, ← Real.rpow_mul hL.le]
  congr 2
  ring

end ClockBarrier.Analysis
