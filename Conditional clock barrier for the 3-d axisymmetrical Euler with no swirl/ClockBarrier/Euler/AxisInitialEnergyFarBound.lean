/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisSmoothFarBound
public import ClockBarrier.Euler.EnergyConservation

/-! # The smooth far-field estimate in terms of initial energy

Energy conservation supplies a time-independent right side. The smooth far
integral retains the entire transition annulus.
-/

public section

namespace ClockBarrier.Euler

open Set MeasureTheory Geometry
open scoped NNReal BoundedContinuousFunction Topology ContDiff

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The actual signed, normalized smooth far field has the energy
bound in terms of initial energy, uniformly in time, axis point and cutoff radius. -/
theorem exists_axis_smooth_far_initial_energy_bound
    {χ : E₃ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : χ =ᶠ[𝓝 (0 : E₃)] 0)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ},
      ∀ h : classical_euler_on α T u p, ∀ t, ∀ ht : t ∈ Ico 0 T, ∀ z : ℝ, ∀ {L : ℝ}, 0 < L →
      Integrable (fun y : E₃ => χ (L⁻¹ • (y - !₂[0, 0, z])) * ((z - y 2) *
        (y 0 * vorticity (u t) (h.cartesian_partials t ht) y 1 -
          y 1 * vorticity (u t) (h.cartesian_partials t ht) y 0) / ‖y - !₂[0, 0, z]‖ ^ 5)) volume ∧
      |-(3 / (4 * Real.pi)) * ∫ y : E₃, χ (L⁻¹ • (y - !₂[0, 0, z])) * ((z - y 2) *
        (y 0 * vorticity (u t) (h.cartesian_partials t ht) y 1 -
          y 1 * vorticity (u t) (h.cartesian_partials t ht) y 0) / ‖y - !₂[0, 0, z]‖ ^ 5)| ≤
        C * L ^ (-(5 : ℝ) / 2) * Real.sqrt (∫ y : E₃, ‖u 0 y‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_axis_smooth_far_energy_bound hχ hzero hχ₀ hχ₁ houter
  refine ⟨C, hC, ?_⟩
  intro α T u p h t ht z L hL
  simpa only [h.energy_eq_initial ht] using hbound h t ht z hL

end ClockBarrier.Euler
