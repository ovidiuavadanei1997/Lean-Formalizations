/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.DirectionalFarTranslation
public import ClockBarrier.Euler.VorticityRegularity
public import ClockBarrier.Euler.EnergyConservation
import Mathlib.Tactic.Positivity

/-! # The directional far field bounded by the initial energy -/

public section
namespace ClockBarrier.Euler
open Set Filter MeasureTheory Geometry
open scoped Topology ContDiff NNReal InnerProductSpace BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The complete normalized smooth far field has a cutoff-only constant,
uniform in the solution, time, center, radius and unit direction. -/
theorem exists_directional_smooth_far_initial_energy_bound
    {χ : E₃ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : χ =ᶠ[𝓝 (0 : E₃)] 0)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ},
      ∀ h : classical_euler_on α T u p, ∀ t, ∀ ht : t ∈ Ico 0 T,
      ∀ (a e : E₃), ‖e‖ = 1 → ∀ {L : ℝ}, 0 < L →
      let f := fun x : E₃ =>
        let w := vorticity (u t) (h.cartesian_partials t ht) x
        let y := x - a
        χ (L⁻¹ • y) * (⟪e, y⟫_ℝ *
          ⟪e, (!₂[y 1 * w 2 - y 2 * w 1, y 2 * w 0 - y 0 * w 2,
            y 0 * w 1 - y 1 * w 0] : E₃)⟫_ℝ / ‖y‖ ^ 5)
      Integrable f volume ∧ |(3 / (4 * Real.pi)) * ∫ x, f x| ≤
        C * L ^ (-(5 : ℝ) / 2) * Real.sqrt (∫ x : E₃, ‖u 0 x‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := Analysis.exists_translated_directional_far_energy_constant
    hχ hzero hχ₀ hχ₁ houter
  refine ⟨(3 / (4 * Real.pi)) * C, by positivity, ?_⟩
  intro α T u p h t ht a e he L hL f
  obtain ⟨D, _, hd, hHolder⟩ := h.2.2.2.2.1
  obtain ⟨H, hH⟩ := hHolder t ht
  have hD : HolderWith H α (fderiv ℝ (u t)) := by
    simpa only [show fderiv ℝ (u t) = D t from funext (fun x => (hd t ht x).fderiv)]
      using hH t ⟨ht.1, le_rfl⟩
  have hL2 := h.2.2.2.2.2.1 t ht
  obtain ⟨hi, hb⟩ := hbound (fun x => (hd t ht x).differentiableAt) h.2.1 hD
    ((memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).mp hL2) a hL e he
  have hfi : Integrable f volume := by
    simpa only [f, h.vorticity_eq_curlLinearMap t ht] using hi
  refine ⟨hfi, ?_⟩
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 3 / (4 * Real.pi))]
  simpa only [f, h.vorticity_eq_curlLinearMap t ht, mul_assoc, h.energy_eq_initial ht] using
    mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 3 / (4 * Real.pi))

end ClockBarrier.Euler
