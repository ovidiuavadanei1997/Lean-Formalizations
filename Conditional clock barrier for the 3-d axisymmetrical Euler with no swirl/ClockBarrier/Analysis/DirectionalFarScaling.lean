/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.DirectionalFarField
public import ClockBarrier.Analysis.EnergyScaling
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Scaling the complete directional far field -/

public section
namespace ClockBarrier.Analysis
open MeasureTheory Geometry
open scoped Topology ContDiff NNReal InnerProductSpace
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The full directional kernel, including its smooth cutoff, has degree `-3`. -/
theorem directional_far_kernel_smul (χ : E₃ → ℝ) (w : E₃ → E₃) (e : E₃)
    {L : ℝ} (hL : 0 < L) (x : E₃) :
    χ (L⁻¹ • (L • x)) * (⟪e, L • x⟫_ℝ *
      ⟪e, (!₂[(L • x) 1 * w (L • x) 2 - (L • x) 2 * w (L • x) 1,
        (L • x) 2 * w (L • x) 0 - (L • x) 0 * w (L • x) 2,
        (L • x) 0 * w (L • x) 1 - (L • x) 1 * w (L • x) 0] : E₃)⟫_ℝ /
      ‖L • x‖ ^ 5) =
      (L ^ 3)⁻¹ * (χ x * (⟪e, x⟫_ℝ *
        ⟪e, (!₂[x 1 * w (L • x) 2 - x 2 * w (L • x) 1,
          x 2 * w (L • x) 0 - x 0 * w (L • x) 2,
          x 0 * w (L • x) 1 - x 1 * w (L • x) 0] : E₃)⟫_ℝ / ‖x‖ ^ 5)) := by
  simp only [inv_smul_smul₀ hL.ne', PiLp.smul_apply, smul_eq_mul,
    norm_smul, Real.norm_of_nonneg hL.le, mul_pow, div_eq_mul_inv, mul_inv_rev]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  field_simp

/-- Whole-space scaling preserves the directional far-field integral. -/
theorem integral_directional_far_kernel_scaling (χ : E₃ → ℝ) (w : E₃ → E₃) (e : E₃)
    {L : ℝ} (hL : 0 < L) :
    (∫ x : E₃, χ x * (⟪e, x⟫_ℝ *
      ⟪e, (!₂[x 1 * w (L • x) 2 - x 2 * w (L • x) 1,
        x 2 * w (L • x) 0 - x 0 * w (L • x) 2,
        x 0 * w (L • x) 1 - x 1 * w (L • x) 0] : E₃)⟫_ℝ / ‖x‖ ^ 5)) =
      ∫ x : E₃, χ (L⁻¹ • x) * (⟪e, x⟫_ℝ *
        ⟪e, (!₂[x 1 * w x 2 - x 2 * w x 1, x 2 * w x 0 - x 0 * w x 2,
          x 0 * w x 1 - x 1 * w x 0] : E₃)⟫_ℝ / ‖x‖ ^ 5) := by
  have hs := Measure.integral_comp_smul_of_nonneg (volume : Measure E₃)
    (fun x => χ (L⁻¹ • x) * (⟪e, x⟫_ℝ *
      ⟪e, (!₂[x 1 * w x 2 - x 2 * w x 1, x 2 * w x 0 - x 0 * w x 2,
        x 0 * w x 1 - x 1 * w x 0] : E₃)⟫_ℝ / ‖x‖ ^ 5)) L (hR := hL.le)
  simp only [directional_far_kernel_smul χ w e hL, integral_const_mul,
    finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at hs
  exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 hL.ne')) hs

/-- The full directional far-field estimate has the `L^(-5/2)`
energy scaling and is uniform in all unit directions. -/
theorem exists_scaled_directional_far_energy_constant
    {χ : E₃ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : χ =ᶠ[𝓝 (0 : E₃)] 0)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : E₃ → E₃} {H α : ℝ≥0},
      Differentiable ℝ u → 0 < α → HolderWith H α (fderiv ℝ u) →
      Integrable (fun x => ‖u x‖ ^ 2) volume → ∀ {L : ℝ}, 0 < L →
      ∀ e : E₃, ‖e‖ = 1 →
      let f := fun x : E₃ =>
        let w := curlLinearMap (fderiv ℝ u x)
        χ (L⁻¹ • x) * (⟪e, x⟫_ℝ *
          ⟪e, (!₂[x 1 * w 2 - x 2 * w 1, x 2 * w 0 - x 0 * w 2,
            x 0 * w 1 - x 1 * w 0] : E₃)⟫_ℝ / ‖x‖ ^ 5)
      Integrable f volume ∧ |∫ x, f x| ≤
        C * L ^ (-(5 : ℝ) / 2) * Real.sqrt (∫ x : E₃, ‖u x‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_directional_far_energy_constant hχ hzero hχ₀ hχ₁ houter
  refine ⟨C, hC, ?_⟩
  intro u H α hu hα hD henergy L hL e he f
  have hv : Differentiable ℝ (fun x => L⁻¹ • u (L • x)) :=
    (hu.comp (differentiable_id.const_smul L)).const_smul L⁻¹
  obtain ⟨HL, hHL⟩ := exists_holderWith_fderiv_rescaled_velocity hu hD hL.ne'
  obtain ⟨hi, hb⟩ := hbound hv hα hHL (integrable_sq_norm_rescaled_velocity henergy hL.ne') e he
  simp only [fderiv_rescaled_velocity hu hL.ne'] at hi hb
  refine ⟨?_, by
    simpa only [integral_directional_far_kernel_scaling χ
      (fun x => curlLinearMap (fderiv ℝ u x)) e hL,
      sqrt_energy_rescaled_velocity u hL, mul_assoc] using hb⟩
  apply (integrable_comp_smul_iff volume _ hL.ne').mp
  change Integrable (fun x => f (L • x)) volume
  simpa only [f, directional_far_kernel_smul χ
    (fun x => curlLinearMap (fderiv ℝ u x)) e hL] using hi.const_mul ((L ^ 3)⁻¹)

end ClockBarrier.Analysis
