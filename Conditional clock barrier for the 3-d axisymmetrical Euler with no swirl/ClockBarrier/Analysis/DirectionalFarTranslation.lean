/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.DirectionalFarScaling
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Group.Integral

/-! # Uniformity of the directional far field in its center -/

public section
namespace ClockBarrier.Analysis
open MeasureTheory Geometry
open scoped Topology ContDiff NNReal InnerProductSpace
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Translation preserves the energy constant, uniformly in the center, radius
and unit direction. The full smooth far-field integral is absolutely convergent. -/
theorem exists_translated_directional_far_energy_constant
    {χ : E₃ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : χ =ᶠ[𝓝 (0 : E₃)] 0)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : E₃ → E₃} {H α : ℝ≥0},
      Differentiable ℝ u → 0 < α → HolderWith H α (fderiv ℝ u) →
      Integrable (fun x => ‖u x‖ ^ 2) volume → ∀ (a : E₃) {L : ℝ}, 0 < L →
      ∀ e : E₃, ‖e‖ = 1 →
      let f := fun x : E₃ =>
        let w := curlLinearMap (fderiv ℝ u x)
        let y := x - a
        χ (L⁻¹ • y) * (⟪e, y⟫_ℝ *
          ⟪e, (!₂[y 1 * w 2 - y 2 * w 1, y 2 * w 0 - y 0 * w 2,
            y 0 * w 1 - y 1 * w 0] : E₃)⟫_ℝ / ‖y‖ ^ 5)
      Integrable f volume ∧ |∫ x, f x| ≤
        C * L ^ (-(5 : ℝ) / 2) * Real.sqrt (∫ x : E₃, ‖u x‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_scaled_directional_far_energy_constant
    hχ hzero hχ₀ hχ₁ houter
  refine ⟨C, hC, ?_⟩
  intro u H α hu hα hD henergy a L hL e he f
  have hd : Differentiable ℝ (fun x => u (x + a)) :=
    fun x => (differentiableAt_comp_add_right a).mpr (hu (x + a))
  have hDa : HolderWith H α (fderiv ℝ (fun x => u (x + a))) := by
    exact fun x y => by
      simpa only [fderiv_comp_add_right, edist_add_right] using hD (x + a) (y + a)
  obtain ⟨hi, hb⟩ := hbound hd hα hDa (henergy.comp_add_right a) hL e he
  simp only [fderiv_comp_add_right] at hi hb
  refine ⟨by simpa only [← sub_eq_add_neg, sub_add_cancel] using hi.comp_add_right (-a), ?_⟩
  rw [integral_add_right_eq_self (fun x : E₃ => ‖u x‖ ^ 2) a] at hb
  have ht := integral_add_right_eq_self (μ := volume) f a
  simp only [f, add_sub_cancel_right] at ht
  rwa [ht] at hb

end ClockBarrier.Analysis
