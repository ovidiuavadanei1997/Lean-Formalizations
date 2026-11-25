/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! # Bounds for spatial mollification

Normalized nonnegative bumps preserve supremum and Hölder bounds. The error
bound is uniform in space and applies in particular to velocity derivatives.
-/

public section
namespace ClockBarrier.Analysis
open MeasureTheory ContinuousLinearMap Metric
open scoped Convolution NNReal BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {μ : Measure E} [μ.IsAddHaarMeasure] (φ : ContDiffBump (0 : E))

/-- Spatial averaging by a normalized bump does not increase the supremum bound. -/
theorem norm_normed_convolution_le (f : E →ᵇ F) (x : E) :
    ‖(φ.normed μ ⋆[lsmul ℝ ℝ, μ] (f : E → F)) x‖ ≤ ‖f‖ := by
  simpa only [dist_zero_right] using
    (dist_convolution_le (norm_nonneg f) φ.support_normed_eq.subset
      φ.nonneg_normed φ.integral_normed f.continuous.aestronglyMeasurable
      (fun y _ => (show dist (f y) (0 : F) ≤ ‖f‖ from by
        simpa only [dist_zero_right] using f.norm_coe_le_norm y)))

/-- A Hölder modulus gives a spatially uniform mollification error. -/
theorem dist_normed_convolution_le_holder {f : E → F} (hf : Continuous f)
    {H α : ℝ≥0} (hH : HolderWith H α f) (x : E) :
    dist ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x) (f x) ≤
      (H : ℝ) * φ.rOut ^ (α : ℝ) := by
  exact φ.dist_normed_convolution_le hf.aestronglyMeasurable
    (fun _ hy => hH.dist_le_of_le (mem_ball.mp hy).le)

omit [CompleteSpace F] in
/-- Averaging controls differences by any bound on the translated differences. -/
theorem dist_normed_convolution_le_of_translate_bound {f : E → F}
    (hf : Continuous f) (x y : E) {K : ℝ}
    (hK : ∀ z, dist (f (x - z)) (f (y - z)) ≤ K) :
    dist ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x)
      ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) y) ≤ K := by
  have hi (z : E) := (φ.hasCompactSupport_normed (μ := μ)).convolutionExists_left_of_continuous_right
    (lsmul ℝ ℝ) (φ.integrable_normed (μ := μ)).locallyIntegrable hf z
  rw [dist_eq_norm, convolution_def, convolution_def, ← integral_sub (hi x) (hi y)]
  have hbound : ∀ᵐ z ∂μ,
      ‖(lsmul ℝ ℝ) (φ.normed μ z) (f (x - z)) -
        (lsmul ℝ ℝ) (φ.normed μ z) (f (y - z))‖ ≤ φ.normed μ z * K := by
    exact Filter.Eventually.of_forall (fun z => by
      simpa only [lsmul_apply, ← smul_sub, norm_smul,
        Real.norm_of_nonneg (φ.nonneg_normed z), ← dist_eq_norm] using
        mul_le_mul_of_nonneg_left (hK z) (φ.nonneg_normed z))
  simpa only [integral_mul_const, φ.integral_normed, one_mul] using
    norm_integral_le_of_norm_le ((φ.integrable_normed (μ := μ)).mul_const K) hbound

omit [CompleteSpace F] in
/-- Spatial mollification preserves the original Hölder exponent and constant. -/
theorem holderWith_normed_convolution {f : E → F} (hf : Continuous f)
    {H α : ℝ≥0} (hH : HolderWith H α f) :
    HolderWith H α (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) := by
  have hd (x y : E) :
      dist ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x)
        ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) y) ≤
        (H : ℝ) * dist x y ^ (α : ℝ) :=
    dist_normed_convolution_le_of_translate_bound φ hf x y
      (fun z => by simpa only [dist_sub_right] using hH.dist_le (x - z) (y - z))
  intro x y
  rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ α.coe_nonneg,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  simpa only [NNReal.coe_mul, NNReal.coe_rpow, coe_nndist] using hd x y

end ClockBarrier.Analysis
