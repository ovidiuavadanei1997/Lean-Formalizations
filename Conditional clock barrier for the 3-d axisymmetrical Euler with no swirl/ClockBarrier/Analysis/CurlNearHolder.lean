/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.CurlLocalIntegralEstimates
import Mathlib.MeasureTheory.Group.Integral
/-! # Pure Hölder control of the smooth near field -/

public section
namespace ClockBarrier.Analysis
open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The unit smooth near field is bounded solely by the curl Hölder constant. -/
theorem directional_smooth_near_holder_bound
    {w : E₃ → E₃} {H α : ℝ≥0} (hα : 0 < α) (hw : HolderWith H α w)
    {χ : E₃ → ℝ} (hχ : Measurable χ)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1) (e : E₃) (he : ‖e‖ = 1) :
    let f := fun x : E₃ =>
      let v := w x - w 0
      (1 - χ x) * (⟪e, x⟫_ℝ *
        ⟪e, (!₂[x 1 * v 2 - x 2 * v 1, x 2 * v 0 - x 0 * v 2,
          x 0 * v 1 - x 1 * v 0] : E₃)⟫_ℝ / ‖x‖ ^ 5)
    Integrable f volume ∧ |∫ x, f x| ≤
      (3 * volume.real (ball (0 : E₃) 1) / (α : ℝ)) * H := by
  have hc := hw.continuous hα
  have hcutoff (x : E₃) (v : ℝ) : |(1 - χ x) * v| ≤ |v| := by
    simpa only [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hχ₁ x))] using
      (mul_le_of_le_one_left (abs_nonneg v) (sub_le_self 1 (hχ₀ x)))
  simpa only [Real.one_rpow, mul_one, div_mul_eq_mul_div, mul_comm (H : ℝ)] using
    integrable_abs_integral_le_holder_radial (NNReal.coe_pos.mpr hα) zero_lt_one
      (by apply Measurable.aestronglyMeasurable; fun_prop)
      (fun x hx => by simp only [houter x hx, sub_self, zero_mul])
      (fun x => (hcutoff x _).trans (abs_directional_strain_increment_le_rpow hw e he x))

/-- Translation makes the near Hölder estimate uniform in its center. -/
theorem directional_smooth_near_holder_bound_sub
    {w : E₃ → E₃} {H α : ℝ≥0} (hα : 0 < α) (hw : HolderWith H α w)
    {χ : E₃ → ℝ} (hχ : Measurable χ)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1) (a e : E₃) (he : ‖e‖ = 1) :
    let f := fun x : E₃ =>
      let y := x - a
      let v := w x - w a
      (1 - χ y) * (⟪e, y⟫_ℝ *
        ⟪e, (!₂[y 1 * v 2 - y 2 * v 1, y 2 * v 0 - y 0 * v 2,
          y 0 * v 1 - y 1 * v 0] : E₃)⟫_ℝ / ‖y‖ ^ 5)
    Integrable f volume ∧ |∫ x, f x| ≤
      (3 * volume.real (ball (0 : E₃) 1) / (α : ℝ)) * H := by
  have hwa : HolderWith H α (fun x => w (x + a)) := fun x y => by
    simpa only [edist_add_right] using hw (x + a) (y + a)
  obtain ⟨hi, hb⟩ := directional_smooth_near_holder_bound hα hwa hχ hχ₀ hχ₁ houter e he
  intro f
  refine ⟨by simpa only [f, zero_add, ← sub_eq_add_neg, sub_add_cancel] using
    hi.comp_add_right (-a), ?_⟩
  rw [← integral_add_right_eq_self f a]
  simpa only [f, add_sub_cancel_right, zero_add] using hb
end ClockBarrier.Analysis
