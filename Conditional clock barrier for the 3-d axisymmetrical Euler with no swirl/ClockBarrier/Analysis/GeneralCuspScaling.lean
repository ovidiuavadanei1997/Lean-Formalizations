/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The general cusp estimate's clock exponent -/

public section
namespace ClockBarrier.Analysis

/-- Determinant one converts the transverse stretch factor into the clock and distortion powers. -/
theorem general_clock_distortion_scaling {τ₁ τ₂ ν α : ℝ}
    (hτ₂ : 0 < τ₂) (hν : 0 < ν) (hdet : τ₁ * τ₂ * ν = 1) :
    ν ^ (α - 1) * τ₂ ^ (-1 - α) =
      ν ^ ((3 * α - 1) / 2) * (τ₁ / τ₂) ^ ((α + 1) / 2) := by
  have hκ : τ₁ / τ₂ = (ν * τ₂ ^ 2)⁻¹ := by
    apply (mul_eq_one_iff_eq_inv₀ (by positivity : ν * τ₂ ^ 2 ≠ 0)).mp
    calc
      τ₁ / τ₂ * (ν * τ₂ ^ 2) = τ₁ * τ₂ * ν := by field_simp
      _ = 1 := hdet
  rw [hκ, ← Real.rpow_neg_eq_inv_rpow, Real.mul_rpow hν.le (sq_nonneg τ₂)]
  rw [← Real.rpow_natCast τ₂ 2, ← Real.rpow_mul hτ₂.le, ← mul_assoc, ← Real.rpow_add hν]
  congr 2 <;> ring

/-- The inverse-cube kernel and the integrated cusp mass have the required clock scaling. -/
theorem general_kernel_cusp_scaling {τ₁ τ₂ ν Λ c q l l₁ l₂ α M b : ℝ}
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) (hν : 0 < ν) (hΛ : 0 < Λ)
    (hc : 0 < c) (hq : 0 < q) (hl : 0 ≤ l) (hdet : τ₁ * τ₂ * ν = 1) :
    (τ₁ / (c * ν * Λ * q) ^ 3) *
      ((M * b) * (l * ν * Λ / τ₂) ^ α * (l₁ * l₂ * ν ^ 2 * Λ ^ 3 / (τ₁ * τ₂))) =
      (M * b / c ^ 3) * Λ ^ α * ν ^ ((3 * α - 1) / 2) *
        (τ₁ / τ₂) ^ ((α + 1) / 2) * (l ^ α * l₁ * l₂ / q ^ 3) := by
  have hmass : (l * ν * Λ / τ₂) ^ α = l ^ α * ν ^ α * Λ ^ α / τ₂ ^ α := by
    rw [Real.div_rpow (by positivity) hτ₂.le, Real.mul_rpow (by positivity) hΛ.le,
      Real.mul_rpow hl hν.le]
  have hτ : τ₂ ^ (-1 - α) = (τ₂ ^ α * τ₂)⁻¹ := by
    rw [show -1 - α = -(α + 1) by ring, Real.rpow_neg hτ₂.le,
      Real.rpow_add hτ₂, Real.rpow_one]
  rw [mul_assoc (M * b / c ^ 3 * Λ ^ α),
    ← general_clock_distortion_scaling hτ₂ hν hdet]
  have hνpow : ν ^ (α - 1) = ν ^ α / ν := by
    simpa only [Nat.cast_one, pow_one] using Real.rpow_sub_natCast hν.ne' α 1
  rw [hmass, hτ, hνpow]
  field_simp

end ClockBarrier.Analysis
