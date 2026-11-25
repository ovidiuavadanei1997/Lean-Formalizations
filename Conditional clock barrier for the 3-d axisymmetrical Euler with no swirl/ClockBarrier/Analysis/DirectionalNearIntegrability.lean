/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.DirectionalStrainKernel
public import ClockBarrier.Analysis.WeightedDecomposition
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.Positivity

/-! # Absolute convergence of the complementary directional near field -/

public section
namespace ClockBarrier.Analysis
open Set Metric MeasureTheory
open scoped NNReal InnerProductSpace
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- A complementary cutoff supported in a ball converts local integrability
into whole-space integrability by extending the weighted integrand by zero. -/
theorem integrable_near_cutoff_mul {f χ : E₃ → ℝ} {r : ℝ}
    (hf : IntegrableOn f (ball 0 r) volume) (hχ : Continuous χ)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (houter : ∀ x, r ≤ ‖x‖ → χ x = 1) :
    Integrable (fun x => (1 - χ x) * f x) volume := by
  have hi := integrable_cutoff_mul hf
    (continuous_const.sub hχ).aestronglyMeasurable
    (fun x => sub_nonneg.mpr (hχ₁ x)) (fun x => sub_le_self _ (hχ₀ x))
  exact IntegrableOn.integrable_of_forall_notMem_eq_zero hi fun x hx => by
    simp only [mem_ball, dist_zero_right, not_lt] at hx
    simp only [houter x hx, sub_self, zero_mul]

/-- The smoothly weighted vorticity increment is genuinely integrable on the
whole space for every positive Hölder exponent. -/
theorem integrable_directional_near_increment
    {ω : E₃ → E₃} {H α : ℝ≥0} (hα : 0 < α) (hω : HolderWith H α ω)
    {χ : E₃ → ℝ} (hχ : Continuous χ) (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    {r : ℝ} (houter : ∀ x, r ≤ ‖x‖ → χ x = 1) (e : E₃) (he : ‖e‖ = 1) :
    Integrable (fun x : E₃ =>
      let w := ω x - ω 0
      (1 - χ x) * (⟪e, x⟫_ℝ *
        ⟪e, (!₂[x 1 * w 2 - x 2 * w 1, x 2 * w 0 - x 0 * w 2,
          x 0 * w 1 - x 1 * w 0] : E₃)⟫_ℝ / ‖x‖ ^ 5)) volume := by
  exact integrable_near_cutoff_mul
    (integrableOn_directional_strain_increment_ball hα hω e he r) hχ hχ₀ hχ₁ houter

/-- A continuous numerator with a positive regularizing length is integrable
against the complementary cutoff. This applies to the constant-vorticity term. -/
theorem integrable_near_regularized_numerator {f χ : E₃ → ℝ}
    (hf : Continuous f) (hχ : Continuous χ)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    {r : ℝ} (houter : ∀ x, r ≤ ‖x‖ → χ x = 1) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : E₃ => (1 - χ x) *
      (f x * (ε ^ 2 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2))) volume := by
  have hc : Continuous (fun x : E₃ =>
      f x * (ε ^ 2 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)) := by
    exact hf.mul ((continuous_const.add (continuous_norm.pow 2)).rpow_const
      (fun x => Or.inl (ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos hε) (sq_nonneg ‖x‖)))))
  exact integrable_near_cutoff_mul
    ((hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : E₃) r)).mono_set
      ball_subset_closedBall) hχ hχ₀ hχ₁ houter

end ClockBarrier.Analysis
