/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.HomogeneousStrain
public import ClockBarrier.Analysis.InverseCubeIntegrability
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Smooth far-field coefficients and their square integrability

The cutoff removes the pole and equals one outside a fixed ball. Both the
coefficients and their first derivatives are square integrable, including
the full transition annulus.
-/

public section

namespace ClockBarrier.Analysis

open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- A smooth cutoff vanishing near zero removes the strain coefficient's pole. -/
theorem contDiff_axis_far_coefficient {χ : E₃ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hzero : χ =ᶠ[𝓝 (0 : E₃)] 0) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun x : E₃ => χ x * (x i * x j / ‖x‖ ^ 5)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    exact hzero.mono fun y hy => by simp [show χ y = 0 from hy]
  · exact hχ.contDiffAt.mul (contDiffAt_axis_strain_coefficient i j hx)

/-- A unit-scale smooth far coefficient belongs to `L²`. -/
theorem memLp_axis_far_coefficient {χ : E₃ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hzero : χ =ᶠ[𝓝 (0 : E₃)] 0)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1) (i j : Fin 3) :
    MemLp (fun x : E₃ => χ x * (x i * x j / ‖x‖ ^ 5)) 2 volume := by
  apply memLp_two_of_continuous_inverse_cube_decay
    (contDiff_axis_far_coefficient hχ hzero i j).continuous (R := 1) (C := 1) le_rfl
  exact fun x hx => by simpa only [houter x hx, one_mul] using
    abs_axis_strain_coefficient_le i j x

/-- The differentiated coefficient has inverse-fourth-power decay outside the cutoff. -/
theorem fderiv_axis_far_coefficient_eq {χ : E₃ → ℝ}
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1) (i j : Fin 3) {x : E₃}
    (hx : 1 < ‖x‖) :
    fderiv ℝ (fun y : E₃ => χ y * (y i * y j / ‖y‖ ^ 5)) x =
      fderiv ℝ (fun y : E₃ => y i * y j / ‖y‖ ^ 5) x := by
  apply Filter.EventuallyEq.fderiv_eq
  have hnear : ∀ᶠ y in 𝓝 x, 1 < ‖y‖ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hx
  exact hnear.mono fun y hy => by simp only [houter y (le_of_lt hy), one_mul]

/-- The derivative is square integrable on the whole space, including the
transition annulus where the derivative of the cutoff contributes. -/
theorem memLp_fderiv_axis_far_coefficient {χ : E₃ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hzero : χ =ᶠ[𝓝 (0 : E₃)] 0)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1) (i j : Fin 3) (v : E₃) :
    MemLp (fun x : E₃ => fderiv ℝ
      (fun y : E₃ => χ y * (y i * y j / ‖y‖ ^ 5)) x v) 2 volume := by
  have hc := (contDiff_axis_far_coefficient hχ hzero i j).fderiv_right
    (m := 0) (by simp)
  apply memLp_two_of_continuous_inverse_cube_decay
    (hc.continuous.clm_apply continuous_const) (R := 2) (C := 7 * ‖v‖) (by norm_num)
  intro x hx
  rw [fderiv_axis_far_coefficient_eq houter i j (by linarith : 1 < ‖x‖)]
  refine (abs_fderiv_axis_strain_coefficient_le i j
    (norm_ne_zero_iff.mp (by linarith : ‖x‖ ≠ 0)) v).trans ?_
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_right₀ (by linarith : 1 ≤ ‖x‖) (by norm_num : 3 ≤ 4))

/-- A fixed smooth cutoff can be used for the far field. Its transition occurs
between radii `1 / 2` and `1`. -/
theorem exists_axis_far_cutoff :
    ∃ χ : E₃ → ℝ, ContDiff ℝ ∞ χ ∧ (χ =ᶠ[𝓝 (0 : E₃)] 0) ∧
      (∀ x, 0 ≤ χ x) ∧ (∀ x, χ x ≤ 1) ∧
      (∀ x, ‖x‖ ≤ 1 / 2 → χ x = 0) ∧ (∀ x, 1 ≤ ‖x‖ → χ x = 1) := by
  let b : ContDiffBump (0 : E₃) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  refine ⟨fun x => 1 - b x, contDiff_const.sub b.contDiff, ?_, ?_, ?_, ?_, ?_⟩
  · exact b.eventuallyEq_one.mono fun x hx => by simp [show b x = 1 from hx]
  · exact fun x => sub_nonneg.mpr b.le_one
  · exact fun x => sub_le_self _ b.nonneg
  · exact fun x hx => sub_eq_zero.mpr (b.one_of_mem_closedBall
      (by simpa only [mem_closedBall, dist_zero_right] using hx)).symm
  · exact fun x hx => by simp only [b.zero_of_le_dist
      (by simpa only [dist_zero_right] using hx), sub_zero]

end ClockBarrier.Analysis
