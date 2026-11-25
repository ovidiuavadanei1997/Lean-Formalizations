/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Integrable pairings with Schwartz test functions -/

public section

namespace ClockBarrier.Analysis

open MeasureTheory SchwartzMap

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- A function of at most linear growth can be paired integrably with a
Schwartz test. No smoothness of the multiplier is required. -/
theorem integrable_schwartz_mul_of_linear_growth (φ : 𝓢(E₃, ℂ))
    {q : E₃ → ℂ} (hq : AEStronglyMeasurable q volume) {A B : ℝ}
    (hb : ∀ x, ‖q x‖ ≤ A + B * ‖x‖) :
    Integrable (fun x => φ x * q x) volume := by
  have hi : Integrable (fun x : E₃ => A * ‖φ x‖ + B * (‖x‖ * ‖φ x‖)) volume := by
    convert!
      ((φ.integrable (μ := (volume : Measure E₃))).norm.const_mul A).add ((φ.integrable_pow_mul volume 1).const_mul B) using 1
    simp only [pow_one]
    rfl
  apply hi.mono' (φ.continuous.aestronglyMeasurable.mul hq)
  filter_upwards [] with x
  calc
    ‖φ x * q x‖ = ‖φ x‖ * ‖q x‖ := norm_mul _ _
    _ ≤ ‖φ x‖ * (A + B * ‖x‖) := mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)
    _ = A * ‖φ x‖ + B * (‖x‖ * ‖φ x‖) := by ring

/-- A bounded measurable multiplier has an integrable Schwartz pairing. -/
theorem integrable_schwartz_mul_of_bounded (φ : 𝓢(E₃, ℂ))
    {q : E₃ → ℂ} (hq : AEStronglyMeasurable q volume) {A : ℝ}
    (hb : ∀ x, ‖q x‖ ≤ A) : Integrable (fun x => φ x * q x) volume := by
  apply integrable_schwartz_mul_of_linear_growth φ hq (A := A) (B := 0)
  simpa only [zero_mul, add_zero] using hb

end ClockBarrier.Analysis
