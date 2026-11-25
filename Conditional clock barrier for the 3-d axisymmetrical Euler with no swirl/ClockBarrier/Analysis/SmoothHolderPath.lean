/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.SmoothBoundedCauchy
public import ClockBarrier.Analysis.CurlHolder
import Mathlib.Analysis.Calculus.MeanValue

/-! # Uniform Hölder estimates on compact paths of actual smooth fields -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Sobolev
open MeasureTheory ContinuousLinearMap SmoothL2Field
open scoped NNReal BoundedContinuousFunction
local notation "Space" => EuclideanSpace ℝ (Fin 3)
variable {V K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace K] [CompactSpace K]

theorem compact_holder (A : K → SmoothL2Field V)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
    (α : ℝ≥0) (hα : α ≤ 1) : ∃ H : ℝ≥0, ∀ t, HolderWith H α (A t).field := by
  let P := boundedFieldPath A hA
  let Q := boundedFieldPath (fun t => (A t).derivative) (continuous_jetLp_derivative A hA)
  let H : ℝ≥0 := 2*‖P‖₊+‖Q‖₊
  have hPn : 2*‖P‖ ≤ (H : ℝ) := by
    change 2*‖P‖ ≤ 2*‖P‖+‖Q‖
    exact le_add_of_nonneg_right (norm_nonneg Q)
  have hQn : ‖Q‖ ≤ (H : ℝ) := by
    change ‖Q‖ ≤ 2*‖P‖+‖Q‖
    exact le_add_of_nonneg_left (mul_nonneg (by norm_num) (norm_nonneg P))
  refine ⟨H, fun t => ?_⟩
  have hp (x : Space) : ‖(A t).field x‖ ≤ ‖P‖ := by
    simpa only [finiteField_apply] using ((finiteField (A t)).norm_coe_le_norm x).trans (P.norm_coe_le_norm t)
  have hq (x : Space) : ‖fderiv ℝ (A t).field x‖ ≤ ‖Q‖ := by
    convert! (by simpa only [finiteField_apply] using ((finiteField (A t).derivative).norm_coe_le_norm x).trans (Q.norm_coe_le_norm t)) using 1
  have hLip : LipschitzWith H (A t).field :=
    lipschitzWith_of_nnnorm_fderiv_le ((A t).smooth.differentiable (by simp))
      (fun x => by exact_mod_cast (hq x).trans hQn)
  have hzero : HolderWith H 0 (A t).field := by
    apply holderWith_of_dist_le_mul_rpow
    intro x y
    simp only [NNReal.coe_zero, Real.rpow_zero, mul_one]
    exact (dist_le_norm_add_norm _ _).trans ((add_le_add (hp x) (hp y)).trans (by linarith))
  simpa only [one_mul, zero_mul, add_zero] using
    hLip.holderWith.interpolate_const (t₁ := α) (t₂ := 1-α) hzero (add_tsub_cancel_of_le hα)

end ClockBarrier.Analysis.Sobolev
