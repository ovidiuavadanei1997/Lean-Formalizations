/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.AxisFarCutoff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.Abel

/-! # Translation differences of smooth strain kernels

The derivative bound includes the cutoff transition annulus. The cancellation
identity concerns the difference of translates as a single function; it does
not split two possibly nonintegrable kernel integrals.
-/

public section
open Set Metric MeasureTheory
open scoped Topology ContDiff

namespace ClockBarrier.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] in
/-- An inverse-fourth weight changes by at most a factor of sixteen on a
half-radius ball. -/
theorem inverse_fourth_decay_on_half_ball {C : ℝ} (hC : 0 ≤ C)
    {a z : E} (hz : z ∈ closedBall a (‖a‖ / 2)) :
    C / (1 + ‖z‖) ^ 4 ≤ 16 * C / (1 + ‖a‖) ^ 4 := by
  have ha : 1 + ‖a‖ ≤ 2 * (1 + ‖z‖) := by
    nlinarith [norm_sub_norm_le a z, show ‖a - z‖ ≤ ‖a‖ / 2 by simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hz]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simpa only [mul_pow, show (2 : ℝ) ^ 4 = 16 by norm_num, mul_left_comm C, mul_assoc] using
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ha 4) hC

/-- Mean-value control of a kernel translation difference away from its center. -/
theorem norm_kernel_sub_le_of_fderiv_decay {f : E → F} {C : ℝ}
    (hC : 0 ≤ C) (hf : Differentiable ℝ f)
    (hdecay : ∀ z, ‖fderiv ℝ f z‖ ≤ C / (1 + ‖z‖) ^ 4)
    {a b : E} (hb : ‖b‖ ≤ ‖a‖ / 2) :
    ‖f (a - b) - f a‖ ≤ (16 * C / (1 + ‖a‖) ^ 4) * ‖b‖ := by
  have h := (convex_closedBall a (‖a‖ / 2)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hf z)
    (fun z hz => (hdecay z).trans (inverse_fourth_decay_on_half_ball hC hz))
    (show a ∈ closedBall a (‖a‖ / 2) from mem_closedBall_self (by positivity))
    (show a - b ∈ closedBall a (‖a‖ / 2) from by
      simpa only [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg] using hb)
  simpa only [sub_sub_cancel_left, norm_neg] using h

/-- The difference of two translates of an even kernel has zero integral by
midpoint reflection. Integrability remains a separate obligation when using
this identity to subtract a constant from an absolutely convergent integral. -/
theorem integral_even_kernel_sub_translates_eq_zero
    {k : EuclideanSpace ℝ (Fin 3) → ℝ} (hk : ∀ x, k (-x) = k x)
    (a b : EuclideanSpace ℝ (Fin 3)) :
    (∫ x, k (x - a) - k (x - b)) = 0 := by
  let f := fun x => k (x - a) - k (x - b)
  have hodd (x) : f (a + b - x) = -f x := by
    change k (a + b - x - a) - k (a + b - x - b) = -(k (x - a) - k (x - b))
    rw [show a + b - x - a = -(x - b) by abel,
      show a + b - x - b = -(x - a) by abel, hk, hk, neg_sub]
  have hreflect : (∫ x, f (a + b - x)) = ∫ x, f x := by
    simpa only [sub_eq_add_neg, add_comm] using
      (integral_neg_eq_self (fun x => f (a + b + x)) volume).trans
        (integral_add_left_eq_self f (a + b))
  have hz : -(∫ x, f x) = ∫ x, f x := by simpa only [hodd, integral_neg] using hreflect
  linarith

/-- The full smooth coefficient has inverse-fourth derivative decay, including
the transition annulus. The constant is independent of the evaluation point. -/
theorem exists_axis_far_fderiv_decay_constant
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hzero : χ =ᶠ[𝓝 (0 : EuclideanSpace ℝ (Fin 3))] 0)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1) (i j : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      ‖fderiv ℝ (fun y => χ y * (y i * y j / ‖y‖ ^ 5)) x‖ ≤
        C / (1 + ‖x‖) ^ 4 := by
  let k := fun y => χ y * (y i * y j / ‖y‖ ^ 5)
  have hc : Continuous (fun x => ‖fderiv ℝ k x‖ * (1 + ‖x‖) ^ 4) :=
    ((contDiff_axis_far_coefficient hχ hzero i j).fderiv_right
      (m := 0) (by simp)).continuous.norm.mul ((continuous_const.add continuous_norm).pow 4)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2).bddAbove_image hc.continuousOn
  refine ⟨max M 112, (by positivity), fun x => ?_⟩
  by_cases hx : ‖x‖ ≤ 2
  · exact (le_div_iff₀ (by positivity)).mpr
      ((hM (mem_image_of_mem _ (by simpa only [mem_closedBall, dist_zero_right] using hx))).trans
        (le_max_left _ _))
  · rw [fderiv_axis_far_coefficient_eq houter i j (by linarith : 1 < ‖x‖)]
    have hd : ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => y i * y j / ‖y‖ ^ 5) x‖ ≤
        7 / ‖x‖ ^ 4 := by
      exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v =>
        by simpa only [Real.norm_eq_abs, div_mul_eq_mul_div, mul_comm (‖v‖)] using
          abs_fderiv_axis_strain_coefficient_le i j
            (norm_ne_zero_iff.mp (by linarith : ‖x‖ ≠ 0)) v)
    have hp : (1 + ‖x‖) ^ 4 ≤ 16 * ‖x‖ ^ 4 := by
      simpa only [mul_pow, show (2 : ℝ) ^ 4 = 16 by norm_num] using
        pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖x‖) (by linarith : 1 + ‖x‖ ≤ 2 * ‖x‖) 4
    exact hd.trans (((div_le_div_iff₀ (pow_pos (by linarith : 0 < ‖x‖) 4)
      (by positivity : 0 < (1 + ‖x‖) ^ 4)).mpr (by nlinarith)).trans
        (div_le_div_of_nonneg_right (le_max_right M 112) (by positivity)))

end ClockBarrier.Analysis
