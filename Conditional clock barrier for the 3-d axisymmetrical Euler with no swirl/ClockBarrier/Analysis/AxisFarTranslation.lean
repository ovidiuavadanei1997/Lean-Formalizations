/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.AxisFarScaling
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Group.Integral

/-! # Uniformity of the smooth far-field estimate in its center -/

public section

namespace ClockBarrier.Analysis

open MeasureTheory Geometry
open scoped Topology ContDiff NNReal

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Translation does not change the energy constant or the cutoff scale. -/
theorem exists_translated_axis_far_energy_constant
    {χ : E₃ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : χ =ᶠ[𝓝 (0 : E₃)] 0)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : E₃ → E₃} {H α : ℝ≥0},
      Differentiable ℝ u → 0 < α → HolderWith H α (fderiv ℝ u) →
      Integrable (fun x => ‖u x‖ ^ 2) volume → ∀ (a : E₃) {L : ℝ}, 0 < L →
      Integrable (fun x : E₃ => χ (L⁻¹ • (x - a)) * ((x - a) 2 *
        ((x - a) 0 * curlLinearMap (fderiv ℝ u x) 1 -
          (x - a) 1 * curlLinearMap (fderiv ℝ u x) 0) / ‖x - a‖ ^ 5)) volume ∧
      |∫ x : E₃, χ (L⁻¹ • (x - a)) * ((x - a) 2 *
        ((x - a) 0 * curlLinearMap (fderiv ℝ u x) 1 -
          (x - a) 1 * curlLinearMap (fderiv ℝ u x) 0) / ‖x - a‖ ^ 5)| ≤
        C * L ^ (-(5 : ℝ) / 2) * Real.sqrt (∫ x : E₃, ‖u x‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_scaled_axis_far_energy_constant hχ hzero hχ₀ hχ₁ houter
  refine ⟨C, hC, ?_⟩
  intro u H α hu hα hD henergy a L hL
  have hd : Differentiable ℝ (fun x => u (x + a)) :=
    fun x => (differentiableAt_comp_add_right a).mpr (hu (x + a))
  have hDa : HolderWith H α (fderiv ℝ (fun x => u (x + a))) := by
    exact fun x y => by
      simpa only [fderiv_comp_add_right, edist_add_right] using hD (x + a) (y + a)
  obtain ⟨hi, hb⟩ := hbound hd hα hDa (henergy.comp_add_right a) hL
  simp only [fderiv_comp_add_right] at hi hb
  refine ⟨by simpa only [← sub_eq_add_neg, sub_add_cancel] using hi.comp_add_right (-a), ?_⟩
  rw [integral_add_right_eq_self (fun x : E₃ => ‖u x‖ ^ 2) a] at hb
  have ht := integral_add_right_eq_self (μ := volume) (fun x : E₃ => χ (L⁻¹ • (x - a)) *
    ((x - a) 2 * ((x - a) 0 * curlLinearMap (fderiv ℝ u x) 1 -
      (x - a) 1 * curlLinearMap (fderiv ℝ u x) 0) / ‖x - a‖ ^ 5)) a
  simp only [add_sub_cancel_right] at ht
  rwa [ht] at hb

end ClockBarrier.Analysis
