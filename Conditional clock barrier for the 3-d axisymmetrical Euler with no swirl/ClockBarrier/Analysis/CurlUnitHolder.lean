/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.CurlNearHolder
public import ClockBarrier.Analysis.CurlFarDifference
import ClockBarrier.Analysis.DirectionalBiotSavartTranslation
import ClockBarrier.Analysis.RadialFarCutoff
import ClockBarrier.Geometry.CurlOperatorNorm
/-! # Unit-scale Calderón–Zygmund comparison for the actual derivative -/

public section
namespace ClockBarrier.Analysis
open Set Metric MeasureTheory Geometry
open scoped Topology InnerProductSpace NNReal
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- A unit-distance comparison for the actual derivative, with a constant
independent of the field, its energy, and its preliminary derivative bound. -/
theorem exists_unit_curl_holder_constant {α : ℝ≥0} (hα : 0 < α) (hα₁ : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : E₃ → E₃} {K H : ℝ≥0},
      Differentiable ℝ u → HolderWith K α (fderiv ℝ u) →
      Integrable (fun x => ‖u x‖ ^ 2) volume →
      (∃ B : ℝ, ∀ x, ‖u x‖ ≤ B) → (∃ B : ℝ, ∀ x, ‖fderiv ℝ u x‖ ≤ B) →
      (∀ x, ∑ i : Fin 3, fderiv ℝ u x (EuclideanSpace.single i 1) i = 0) →
      HolderWith H α (fun x => curlLinearMap (fderiv ℝ u x)) →
      ∀ b : E₃, ‖b‖ ≤ 1 → ‖fderiv ℝ u b - fderiv ℝ u 0‖ ≤ C * H := by
  obtain ⟨χ, hχ, hzero, hχ₀, hχ₁, _, houter, hradial⟩ := exists_radial_far_cutoff
  obtain ⟨F, hF, hfar⟩ := exists_directional_far_difference_constant hχ hzero houter hradial hα₁
  let A : ℝ := 3 * volume.real (ball (0 : E₃) 1) / (α : ℝ)
  let c : ℝ := (3 / (4 * Real.pi)) * (2 * A + F)
  have hc : 0 ≤ c := by dsimp [c, A]; positivity
  refine ⟨3 * c + 1, by positivity, ?_⟩
  rintro u K H hu hD henergy ⟨B, hB⟩ ⟨BD, hBD⟩ hdiv hw b hb
  have hq : ∀ e : E₃, ‖e‖ = 1 →
      |⟪e, (fderiv ℝ u b - fderiv ℝ u 0) e⟫_ℝ| ≤ c * H := by
    intro e he
    have hrep (a : E₃) := directional_strain_eq_smooth_near_add_far_sub hu hα hD henergy
      hB hBD hdiv hχ hzero hχ₀ hχ₁ houter hradial zero_lt_one a e he
    simp only [inv_one, one_smul] at hrep
    have hn (a : E₃) := (directional_smooth_near_holder_bound_sub hα hw
      hχ.continuous.measurable hχ₀ hχ₁ houter a e he).2
    have hf := (hfar (fderiv ℝ u) (hD.continuous hα) H hw b e hb he).2
    rw [integral_sub (hrep b).2.1 (hrep 0).2.1] at hf
    rw [sub_apply, inner_sub_right, (hrep b).2.2, (hrep 0).2.2, ← mul_sub,
      abs_mul, abs_of_nonneg (by positivity : 0 ≤ (3 : ℝ) / (4 * Real.pi))]
    rw [add_sub_add_comm]
    exact (mul_le_mul_of_nonneg_left
      ((abs_add_le _ _).trans (add_le_add
        ((abs_sub _ _).trans (add_le_add (hn b) (hn 0))) hf))
      (by positivity : 0 ≤ (3 : ℝ) / (4 * Real.pi))).trans_eq (by dsimp [c, A]; ring)
  have hwbound : ‖curlLinearMap (fderiv ℝ u b - fderiv ℝ u 0)‖ ≤ H := by
    have hd : ‖curlLinearMap (fderiv ℝ u b) - curlLinearMap (fderiv ℝ u 0)‖ ≤
        H * ‖b‖ ^ (α : ℝ) := by
      simpa only [dist_eq_norm, sub_zero] using hw.dist_le b 0
    simpa only [map_sub] using hd.trans
      (mul_le_of_le_one_right H.coe_nonneg (Real.rpow_le_one (norm_nonneg b) hb α.coe_nonneg))
  exact (norm_le_of_quadratic_curl_bound _ (mul_nonneg hc H.coe_nonneg) hq).trans
    ((add_le_add le_rfl hwbound).trans_eq (by ring))
end ClockBarrier.Analysis
