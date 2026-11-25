/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.L2PointwiseLimit
import ClockBarrier.Analysis.CurlHolder
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! # Closedness of the bounded C¹ and spatial Hölder conditions -/
public section
namespace ClockBarrier.Analysis
open MeasureTheory Filter
open scoped Topology NNReal BoundedContinuousFunction
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem hasFDerivAt_bounded_limit (u : ℕ → E →ᵇ V)
    (D : ℕ → E →ᵇ (E →L[ℝ] V)) (v : E →ᵇ V) (F : E →ᵇ (E →L[ℝ] V))
    (hu : Tendsto u atTop (𝓝 v)) (hD : Tendsto D atTop (𝓝 F))
    (hd : ∀ n x, HasFDerivAt (u n : E → V) (D n x) x) (x : E) :
    HasFDerivAt (v : E → V) (F x) x := by
  exact hasFDerivAt_of_tendstoUniformly
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hD) hd
    (fun y => (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hu).tendsto_at y) x

omit [NormedSpace ℝ E] [NormedSpace ℝ V] in
theorem holderWith_bounded_limit (u : ℕ → E →ᵇ V) (v : E →ᵇ V)
    (hu : Tendsto u atTop (𝓝 v)) (H α : ℝ≥0)
    (hH : ∀ n, HolderWith H α (u n : E → V)) :
    HolderWith H α (v : E → V) := by
  have hp := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hu).tendsto_at
  apply holderWith_of_dist_le_mul_rpow
  intro x y
  exact le_of_tendsto ((hp x).dist (hp y)) (Eventually.of_forall (fun n => (hH n).dist_le x y))

end ClockBarrier.Analysis
