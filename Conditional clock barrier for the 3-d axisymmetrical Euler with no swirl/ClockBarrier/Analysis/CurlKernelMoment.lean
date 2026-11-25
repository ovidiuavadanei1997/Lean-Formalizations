/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.CurlKernelDifference
public import ClockBarrier.Analysis.CurlRadialIntegrals
import Mathlib.Analysis.Calculus.MeanValue

/-! # Weighted integrability of kernel translation differences

Inverse-fourth derivative decay gives a uniformly integrable translation
moment for exponents in `[0, 1)`. The zero exponent also proves absolute
integrability before applying the midpoint cancellation identity.
-/

public section
namespace ClockBarrier.Analysis
open Set Metric MeasureTheory
open scoped Topology ContDiff
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The regularized derivative bound gives global translation control. -/
theorem norm_kernel_sub_le_global_of_fderiv_decay
    {f : E₃ → ℝ} {C : ℝ} (hC : 0 ≤ C) (hf : Differentiable ℝ f)
    (hdecay : ∀ z, ‖fderiv ℝ f z‖ ≤ C / (1 + ‖z‖) ^ 4) (a b : E₃) :
    ‖f (a - b) - f a‖ ≤ C * ‖b‖ := by
  have hd (z : E₃) : ‖fderiv ℝ f z‖ ≤ C :=
    (hdecay z).trans (div_le_self hC (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg z))))
  simpa only [sub_sub_cancel_left, norm_neg] using
    (convex_univ : Convex ℝ (univ : Set E₃)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hf z) (fun z _ => hd z) (mem_univ a) (mem_univ (a - b))

/-- For bounded translations, the difference has inverse-fourth decay. -/
theorem norm_kernel_sub_le_inverse_fourth
    {f : E₃ → ℝ} {C : ℝ} (hC : 0 ≤ C) (hf : Differentiable ℝ f)
    (hdecay : ∀ z, ‖fderiv ℝ f z‖ ≤ C / (1 + ‖z‖) ^ 4)
    {a b : E₃} (hb : ‖b‖ ≤ 1) (ha : 2 ≤ ‖a‖) :
    ‖f (a - b) - f a‖ ≤ 16 * C / ‖a‖ ^ 4 := by
  calc
    _ ≤ (16 * C / (1 + ‖a‖) ^ 4) * ‖b‖ :=
      norm_kernel_sub_le_of_fderiv_decay hC hf hdecay (by linarith)
    _ ≤ 16 * C / (1 + ‖a‖) ^ 4 := mul_le_of_le_one_right (by positivity) hb
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (pow_pos (by linarith : 0 < ‖a‖) 4)
      (pow_le_pow_left₀ (norm_nonneg a) (le_add_of_nonneg_left zero_le_one) 4)

/-- The Hölder-weighted translation difference is uniformly integrable for
translations of norm at most one, including the unweighted exponent zero. -/
theorem exists_kernel_translation_holder_moment_bound
    {f : E₃ → ℝ} {C α : ℝ} (hC : 0 ≤ C) (hf : Differentiable ℝ f)
    (hdecay : ∀ z, ‖fderiv ℝ f z‖ ≤ C / (1 + ‖z‖) ^ 4)
    (hα₀ : 0 ≤ α) (hα₁ : α < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ b : E₃, ‖b‖ ≤ 1 →
      Integrable (fun x => |f (x - b) - f x| * ‖x‖ ^ α) volume ∧
        (∫ x, |f (x - b) - f x| * ‖x‖ ^ α) ≤ B := by
  let A : Set E₃ := closedBall 0 2
  let g := fun x : E₃ => A.indicator (fun y : E₃ => ‖y‖ ^ α) x +
    Aᶜ.indicator (fun y : E₃ => 16 * ‖y‖ ^ (α - 4)) x
  have hA : MeasurableSet A := measurableSet_closedBall
  have hn : Integrable (A.indicator (fun y : E₃ => ‖y‖ ^ α)) volume :=
    (integrable_indicator_iff hA).mpr
      ((continuous_norm.rpow_const (fun _ => Or.inr hα₀)).continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : E₃) 2))
  have hAc : Aᶜ = (fun x : E₃ => ‖x‖) ⁻¹' Ioi 2 := by ext x; simp [A]
  have ht : Integrable (Aᶜ.indicator (fun y : E₃ => 16 * ‖y‖ ^ (α - 4))) volume :=
    (integrable_indicator_iff hA.compl).mpr (by
      simpa only [hAc, IntegrableOn] using (integrableOn_holder_radial_tail hα₁ (by norm_num : (0 : ℝ) < 2)).const_mul 16)
  have hg : Integrable g volume := hn.add ht
  refine ⟨C * |∫ x, g x|, mul_nonneg hC (abs_nonneg _), fun b hb => ?_⟩
  have hm (x : E₃) : |f (x - b) - f x| * ‖x‖ ^ α ≤ C * g x := by
    by_cases hx : x ∈ A
    · simpa [g, hx, Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_right
          ((norm_kernel_sub_le_global_of_fderiv_decay hC hf hdecay x b).trans
            (mul_le_of_le_one_right hC hb)) (Real.rpow_nonneg (norm_nonneg x) α)
    · have hxr : 2 < ‖x‖ := by simpa only [A, mem_closedBall, dist_zero_right, not_le] using hx
      simp only [g, indicator_of_notMem hx, indicator_of_mem (show x ∈ Aᶜ from hx), zero_add]
      refine (mul_le_mul_of_nonneg_right (norm_kernel_sub_le_inverse_fourth hC hf hdecay hb hxr.le)
        (Real.rpow_nonneg (norm_nonneg x) α)).trans_eq ?_
      rw [Real.rpow_sub (by linarith : 0 < ‖x‖), Real.rpow_ofNat]
      ring
  have hfc : Continuous f := hf.continuous
  have hi : Integrable (fun x => |f (x - b) - f x| * ‖x‖ ^ α) volume :=
    (hg.const_mul C).mono'
      ((by fun_prop : Measurable (fun x : E₃ => |f (x - b) - f x| * ‖x‖ ^ α)).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs, abs_mul, abs_abs,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) α)] using hm x))
  refine ⟨hi, (integral_mono hi (hg.const_mul C) hm).trans ?_⟩
  simpa only [integral_const_mul] using mul_le_mul_of_nonneg_left (le_abs_self (∫ x, g x)) hC

/-- The moment estimate applies to the actual smooth far-field coefficients. -/
theorem exists_axis_far_translation_holder_moment_bound
    {χ : E₃ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : χ =ᶠ[𝓝 (0 : E₃)] 0)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    (i j : Fin 3) :
    let k := fun x : E₃ => χ x * (x i * x j / ‖x‖ ^ 5)
    ∃ B : ℝ, 0 ≤ B ∧ ∀ b : E₃, ‖b‖ ≤ 1 →
      Integrable (fun x => |k (x - b) - k x| * ‖x‖ ^ α) volume ∧
        (∫ x, |k (x - b) - k x| * ‖x‖ ^ α) ≤ B := by
  obtain ⟨C, hC, hdecay⟩ := exists_axis_far_fderiv_decay_constant hχ hzero houter i j
  exact exists_kernel_translation_holder_moment_bound hC
    ((contDiff_axis_far_coefficient hχ hzero i j).differentiable (by simp)) hdecay hα₀ hα₁

/-- For a radial cutoff the actual coefficient difference is absolutely
integrable and its integral vanishes by midpoint reflection. -/
theorem integrable_axis_far_translate_sub_and_integral_eq_zero
    {χ : E₃ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : χ =ᶠ[𝓝 (0 : E₃)] 0)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1)
    (hradial : ∀ x y, ‖x‖ = ‖y‖ → χ x = χ y)
    (i j : Fin 3) (b : E₃) (hb : ‖b‖ ≤ 1) :
    let k := fun x : E₃ => χ x * (x i * x j / ‖x‖ ^ 5)
    Integrable (fun x => k (x - b) - k x) volume ∧
      (∫ x, k (x - b) - k x) = 0 := by
  intro k
  obtain ⟨_, _, hm⟩ := exists_axis_far_translation_holder_moment_bound
    hχ hzero houter (α := 0) le_rfl zero_lt_one i j
  have hkc : Continuous k := (contDiff_axis_far_coefficient hχ hzero i j).continuous
  refine ⟨(integrable_norm_iff (by fun_prop)).mp ?_, ?_⟩
  · simpa only [k, Real.norm_eq_abs, Real.rpow_zero, mul_one] using (hm b hb).1
  · have heven (x : E₃) : k (-x) = k x := by
      simp only [k, hradial (-x) x (norm_neg x), PiLp.neg_apply, neg_mul_neg, norm_neg]
    simpa only [sub_zero] using integral_even_kernel_sub_translates_eq_zero heven b 0

end ClockBarrier.Analysis
