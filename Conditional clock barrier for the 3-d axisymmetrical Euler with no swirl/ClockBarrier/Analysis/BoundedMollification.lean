/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.HolderMollification
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Differentiating bounded C¹ data under spatial mollification -/

public section
namespace ClockBarrier.Analysis
open MeasureTheory ContinuousLinearMap Set Filter
open scoped Convolution BoundedContinuousFunction Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {μ : Measure E} [μ.IsAddHaarMeasure] (φ : ContDiffBump (0 : E))

omit [CompleteSpace F] in
/-- The derivative can fall on bounded C¹ data, even without compact support. -/
theorem hasFDerivAt_normed_convolution (f : E →ᵇ F) (D : E →ᵇ (E →L[ℝ] F))
    (hD : ∀ x, HasFDerivAt (f : E → F) (D x) x) (x : E) :
    HasFDerivAt (φ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → F))
      ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] (D : E → E →L[ℝ] F)) x) x := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ)
    (F' := fun x y => φ.normed μ y • D (x - y))
    (bound := fun y => φ.normed μ y * ‖D‖) (univ_mem)
  case hF_meas =>
    exact Eventually.of_forall (fun y =>
      ((φ.continuous_normed (μ := μ)).smul
        (f.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
  case hF_int =>
    exact φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
      (lsmul ℝ ℝ) φ.integrable_normed.locallyIntegrable f.continuous x
  case hF'_meas =>
    exact ((φ.continuous_normed (μ := μ)).smul
      (D.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  case h_bound =>
    exact Eventually.of_forall (fun y x _ => by
      simpa only [norm_smul, Real.norm_of_nonneg (φ.nonneg_normed y)] using
        mul_le_mul_of_nonneg_left (D.norm_coe_le_norm (x - y)) (φ.nonneg_normed y))
  case bound_integrable => exact φ.integrable_normed.mul_const ‖D‖
  case h_diff =>
    exact Eventually.of_forall (fun y x _ => by
      simpa [Function.comp_def, Pi.sub_apply, Pi.smul_def] using ((hD (x - y)).comp x
        ((hasFDerivAt_id x).sub (hasFDerivAt_const y x))).const_smul (φ.normed μ y))

end ClockBarrier.Analysis
