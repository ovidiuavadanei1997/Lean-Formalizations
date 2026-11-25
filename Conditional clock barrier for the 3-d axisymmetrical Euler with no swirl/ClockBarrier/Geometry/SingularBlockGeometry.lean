/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.SingularFrame
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-! # The anisotropic distance scale of a singular-coordinate block -/

public section
namespace ClockBarrier.Geometry
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The Euclidean norm of the three lower shell scales. -/
theorem norm_singular_shell_scale {r : ℝ} (hr : 0 ≤ r) (l₁ l₂ : ℝ) :
    ‖(!₂[l₁ * r, l₂ * r, r] : E₃)‖ = r * Real.sqrt (1 + l₁ ^ 2 + l₂ ^ 2) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, mul_pow,
    Real.sq_sqrt (by positivity)]
  change (l₁ * r) ^ 2 + (l₂ * r) ^ 2 + r ^ 2 = _
  ring

/-- Half-open shells give the anisotropic norm scale, uniformly in their indices. -/
theorem norm_bounds_of_singular_shell {F : E₃ →L[ℝ] E₃}
    {U V : E₃ ≃ₗᵢ[ℝ] E₃} {σ : Fin 3 → ℝ} {x : E₃} {l₁ l₂ Λ : ℝ}
    (hF : ∀ η : E₃, F (V η) = U !₂[σ 0 * η 0, σ 1 * η 1, σ 2 * η 2])
    (hσ : ∀ i, 0 < σ i) (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂) (hΛ : 0 ≤ Λ)
    (h₀ : l₁ * σ 2 * Λ / σ 0 ≤ |V.symm x 0| ∧
      |V.symm x 0| < 2 * (l₁ * σ 2 * Λ / σ 0))
    (h₁ : l₂ * σ 2 * Λ / σ 1 ≤ |V.symm x 1| ∧
      |V.symm x 1| < 2 * (l₂ * σ 2 * Λ / σ 1))
    (h₂ : Λ ≤ |V.symm x 2| ∧ |V.symm x 2| < 2 * Λ) :
    σ 2 * Λ * Real.sqrt (1 + l₁ ^ 2 + l₂ ^ 2) ≤ ‖F x‖ ∧
      ‖F x‖ ≤ 2 * (σ 2 * Λ * Real.sqrt (1 + l₁ ^ 2 + l₂ ^ 2)) := by
  have hscale {s A z : ℝ} (hs : 0 < s)
      (hz : A / s ≤ |z| ∧ |z| < 2 * (A / s)) :
      A ≤ s * |z| ∧ s * |z| ≤ 2 * A := by
    constructor
    · simpa only [mul_comm] using (div_le_iff₀ hs).mp hz.1
    · have h := (lt_div_iff₀ hs).mp (show |z| < (2 * A) / s by
        simpa only [mul_div_assoc] using hz.2)
      simpa only [mul_comm] using h.le
  have hnorm := norm_bounds_of_singular_frame_shell (x := x) (γ := !₂[l₁ * (σ 2 * Λ),
    l₂ * (σ 2 * Λ), σ 2 * Λ]) hF (fun i => (hσ i).le)
  rw [norm_singular_shell_scale (mul_nonneg (hσ 2).le hΛ)] at hnorm
  apply hnorm
  · intro i
    fin_cases i
    · exact mul_nonneg hl₁ (mul_nonneg (hσ 2).le hΛ)
    · exact mul_nonneg hl₂ (mul_nonneg (hσ 2).le hΛ)
    · exact mul_nonneg (hσ 2).le hΛ
  · intro i
    fin_cases i
    · change l₁ * (σ 2 * Λ) ≤ σ 0 * |V.symm x 0| ∧
        σ 0 * |V.symm x 0| ≤ 2 * (l₁ * (σ 2 * Λ))
      simpa only [mul_assoc] using hscale (hσ 0) h₀
    · change l₂ * (σ 2 * Λ) ≤ σ 1 * |V.symm x 1| ∧
        σ 1 * |V.symm x 1| ≤ 2 * (l₂ * (σ 2 * Λ))
      simpa only [mul_assoc] using hscale (hσ 1) h₁
    · change σ 2 * Λ ≤ σ 2 * |V.symm x 2| ∧ σ 2 * |V.symm x 2| ≤ 2 * (σ 2 * Λ)
      exact ⟨mul_le_mul_of_nonneg_left h₂.1 (hσ 2).le,
        (mul_le_mul_of_nonneg_left h₂.2.le (hσ 2).le).trans_eq (by ring)⟩

/-- Strict clock localization excludes every axial scale at or above the clock radius. -/
theorem axial_shell_lt_clock_radius {a aStar : E₃} (V : E₃ ≃ₗᵢ[ℝ] E₃) {Λ ℓ : ℝ}
    (hΛ : Λ ≤ |V.symm (a - aStar) 2|) (hclock : ‖a - aStar‖ < ℓ) : Λ < ℓ := by
  have hc : |V.symm (a - aStar) 2| ≤ ‖a - aStar‖ := by
    simpa only [Real.norm_eq_abs, V.symm.norm_map] using
      PiLp.norm_apply_le (V.symm (a - aStar)) (2 : Fin 3)
  exact (hΛ.trans hc).trans_lt hclock

end ClockBarrier.Geometry
