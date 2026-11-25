/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.DirectionalBiotSavart
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Group.Integral

/-! # The signed directional representation at every spatial center -/

public section
namespace ClockBarrier.Analysis
open Set Filter MeasureTheory Geometry
open scoped Topology ContDiff NNReal InnerProductSpace
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Translation gives the actual signed strain formula at every center, with
absolute convergence of both smooth pieces and no curl-zero assumption. -/
theorem directional_strain_eq_smooth_near_add_far_sub
    {u : E₃ → E₃} {H α : ℝ≥0} (hu : Differentiable ℝ u)
    (hα : 0 < α) (hD : HolderWith H α (fderiv ℝ u))
    (henergy : Integrable (fun x => ‖u x‖ ^ 2) volume)
    {B C : ℝ} (hbound : ∀ x, ‖u x‖ ≤ B) (hDbound : ∀ x, ‖fderiv ℝ u x‖ ≤ C)
    (hdiv : ∀ x, ∑ i : Fin 3, fderiv ℝ u x (EuclideanSpace.single i 1) i = 0)
    {χ : E₃ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : χ =ᶠ[𝓝 (0 : E₃)] 0)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1)
    (hradial : ∀ x y, ‖x‖ = ‖y‖ → χ x = χ y) {L : ℝ} (hL : 0 < L)
    (a e : E₃) (he : ‖e‖ = 1) :
    let w := fun x => curlLinearMap (fderiv ℝ u x)
    let N := fun (x v : E₃) => ⟪e, x⟫_ℝ *
      ⟪e, (!₂[x 1 * v 2 - x 2 * v 1, x 2 * v 0 - x 0 * v 2,
        x 0 * v 1 - x 1 * v 0] : E₃)⟫_ℝ
    let η := fun x => χ (L⁻¹ • (x - a))
    Integrable (fun x => (1 - η x) * (N (x - a) (w x - w a) / ‖x - a‖ ^ 5)) volume ∧
    Integrable (fun x => η x * (N (x - a) (w x) / ‖x - a‖ ^ 5)) volume ∧
      ⟪e, fderiv ℝ u a e⟫_ℝ = (3 / (4 * Real.pi)) *
        ((∫ x, (1 - η x) * (N (x - a) (w x - w a) / ‖x - a‖ ^ 5)) +
          ∫ x, η x * (N (x - a) (w x) / ‖x - a‖ ^ 5)) := by
  intro w N η
  have hd : Differentiable ℝ (fun x => u (x + a)) :=
    fun x => (differentiableAt_comp_add_right a).mpr (hu (x + a))
  have hDa : HolderWith H α (fderiv ℝ (fun x => u (x + a))) := fun x y => by
    simpa only [fderiv_comp_add_right, edist_add_right] using hD (x + a) (y + a)
  obtain ⟨hn, hf, hid⟩ := directional_strain_eq_smooth_near_add_far hd hα hDa
    (henergy.comp_add_right a) (fun x => hbound (x + a))
    (fun x => by simpa only [fderiv_comp_add_right] using hDbound (x + a))
    (fun x => by simpa only [fderiv_comp_add_right] using hdiv (x + a))
    hχ hzero hχ₀ hχ₁ houter hradial hL e he
  simp only [fderiv_comp_add_right, zero_add] at hn hf hid
  refine ⟨by simpa only [← sub_eq_add_neg, sub_add_cancel] using hn.comp_add_right (-a),
    by simpa only [← sub_eq_add_neg, sub_add_cancel] using hf.comp_add_right (-a), ?_⟩
  have hnshift := integral_add_right_eq_self (μ := volume)
    (fun x => (1 - η x) * (N (x - a) (w x - w a) / ‖x - a‖ ^ 5)) a
  have hfshift := integral_add_right_eq_self (μ := volume)
    (fun x => η x * (N (x - a) (w x) / ‖x - a‖ ^ 5)) a
  simp only [η, add_sub_cancel_right] at hnshift hfshift
  exact hid.trans (congrArg (fun z => (3 / (4 * Real.pi)) * z)
    (congrArg₂ (fun x y : ℝ => x + y) hnshift hfshift))

end ClockBarrier.Analysis
