/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! # Finite differences for a Hölder continuous spatial derivative -/

public section

namespace ClockBarrier.Analysis

open Set Metric
open scoped NNReal

/-- A global Hölder bound on the actual derivative gives a first-order remainder
bound, with no second derivative assumption. -/
theorem norm_sub_sub_fderiv_le_of_holderWith
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {H α : ℝ≥0} (hf : Differentiable ℝ f)
    (hD : HolderWith H α (fderiv ℝ f)) (x y : E) :
    ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ H * ‖y - x‖ ^ (α : ℝ) * ‖y - x‖ := by
  apply (convex_closedBall x ‖y - x‖).norm_image_sub_le_of_norm_fderiv_le'
    (fun z _ => hf z)
  · exact fun z hz => by simpa only [dist_eq_norm] using hD.dist_le_of_le hz
  · exact mem_closedBall_self (norm_nonneg _)
  · exact mem_closedBall.mpr (by rw [dist_eq_norm])

/-- Coordinate derivatives can be estimated by finite differences and a Hölder
remainder. This permits spatial tail estimates using the velocity's finite energy. -/
theorem norm_fderiv_apply_le_finite_difference
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {H α : ℝ≥0} (hf : Differentiable ℝ f)
    (hD : HolderWith H α (fderiv ℝ f)) (x v : E) (hv : ‖v‖ = 1)
    {h : ℝ} (hh : 0 < h) :
    ‖fderiv ℝ f x v‖ ≤ (‖f (x + h • v)‖ + ‖f x‖) / h + H * h ^ (α : ℝ) := by
  have hr := norm_sub_sub_fderiv_le_of_holderWith hf hD x (x + h • v)
  simp only [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hh.le, hv, mul_one,
    map_smul] at hr
  have hn := (norm_le_norm_add_norm_sub (f (x + h • v) - f x)
    (h • fderiv ℝ f x v)).trans (add_le_add (norm_sub_le _ _) hr)
  simpa only [norm_smul, Real.norm_of_nonneg hh.le, add_div, mul_div_cancel_right₀ _ hh.ne',
    mul_div_cancel_left₀ _ hh.ne'] using (div_le_div_of_nonneg_right hn hh.le)

/-- A quadratic version of the finite-difference bound is adapted to finite
energy and avoids a global integrability assumption on the derivative. -/
theorem norm_fderiv_apply_le_sq_finite_difference
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {H α : ℝ≥0} (hf : Differentiable ℝ f)
    (hD : HolderWith H α (fderiv ℝ f)) (x v : E) (hv : ‖v‖ = 1)
    {h : ℝ} (hh : 0 < h) :
    ‖fderiv ℝ f x v‖ ≤
      (‖f (x + h • v)‖ ^ 2 + ‖f x‖ ^ 2) / h ^ 3 + h / 2 + H * h ^ (α : ℝ) := by
  have hq (a : ℝ) : a / h ≤ a ^ 2 / h ^ 3 + h / 4 := by
    field_simp
    nlinarith [sq_nonneg (2 * a - h ^ 2)]
  have hb := norm_fderiv_apply_le_finite_difference hf hD x v hv hh
  simp only [add_div] at hb ⊢
  linarith [hq ‖f (x + h • v)‖, hq ‖f x‖]

end ClockBarrier.Analysis
