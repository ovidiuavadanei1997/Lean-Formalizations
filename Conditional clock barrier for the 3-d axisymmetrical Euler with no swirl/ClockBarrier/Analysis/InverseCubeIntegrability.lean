/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.NewtonianIntegrability
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # Square integrability of continuous coefficients with inverse-cube tails -/

public section

namespace ClockBarrier.Analysis

open Set Metric MeasureTheory

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- An inverse sixth power is bounded by an integrable regularized weight
outside the unit ball. -/
theorem inverse_sixth_le_regularized {r : ℝ} (hr : 1 ≤ r) :
    1 / r ^ 6 ≤ 8 / (1 + r ^ 2) ^ 3 := by
  have hr₀ : 0 < r := zero_lt_one.trans_le hr
  have hh : 1 + r ^ 2 ≤ 2 * r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
  have ht : (1 + r ^ 2) ^ 3 ≤ 8 * r ^ 6 := by
    simpa only [mul_pow, ← pow_mul, show (2 : ℝ) ^ 3 = 8 by norm_num] using
      pow_le_pow_left₀ (by positivity : 0 ≤ 1 + r ^ 2) hh 3
  exact (div_le_div_iff₀ (pow_pos hr₀ 6) (by positivity)).mpr (by simpa only [one_mul] using ht)

/-- The regularized inverse-sixth-power weight is integrable in three dimensions. -/
theorem integrable_regularized_inverse_sixth :
    Integrable (fun x : E₃ => 1 / (1 + ‖x‖ ^ 2) ^ 3) volume := by
  have hi := integrable_rpow_neg_one_add_norm_sq (μ := volume) (E := E₃)
    (r := 6) (by norm_num)
  simpa only [show -(6 : ℝ) / 2 = -(3 : ℝ) by norm_num,
    Real.rpow_neg_ofNat, zpow_neg, zpow_ofNat, one_div] using hi

/-- Inverse-cube decay at infinity suffices for square integrability of a
continuous scalar coefficient in three dimensions. -/
theorem memLp_two_of_continuous_inverse_cube_decay {f : E₃ → ℝ}
    (hf : Continuous f) {C R : ℝ} (hR : 1 ≤ R)
    (hdecay : ∀ x : E₃, R ≤ ‖x‖ → |f x| ≤ C / ‖x‖ ^ 3) :
    MemLp f 2 volume := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
  have hn : IntegrableOn (fun x => f x ^ 2) (closedBall 0 R) volume :=
    (hf.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have ht : IntegrableOn (fun x => f x ^ 2) (ball 0 R)ᶜ volume := by
    refine (integrable_regularized_inverse_sixth.const_mul (8 * C ^ 2)).integrableOn.mono'
      (hf.pow 2).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with x hx
    have hxR : R ≤ ‖x‖ := by simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] using hx
    have hs : (f x) ^ 2 ≤ C ^ 2 / ‖x‖ ^ 6 := by
      simpa only [sq_abs, div_pow, ← pow_mul] using
        pow_le_pow_left₀ (abs_nonneg (f x)) (hdecay x hxR) 2
    have hh : C ^ 2 / ‖x‖ ^ 6 ≤ 8 * C ^ 2 * (1 / (1 + ‖x‖ ^ 2) ^ 3) := by
      simpa only [div_eq_mul_inv, one_mul, mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_left (inverse_sixth_le_regularized (hR.trans hxR)) (sq_nonneg C)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f x))] using hs.trans hh
  simpa only [union_compl_self, integrableOn_univ] using
    (hn.mono_set ball_subset_closedBall).union ht

end ClockBarrier.Analysis
