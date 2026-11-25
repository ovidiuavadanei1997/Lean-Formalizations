/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! # Continuous application of operator-valued paths -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis
open Filter
open scoped Topology
variable {K E F : Type*} [TopologicalSpace K] [LocallyCompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def clmApplyPath (D : C(K, E →L[ℝ] F)) (u : C(K, E)) : C(K, F) :=
  ⟨fun t => D t (u t), D.continuous.clm_apply u.continuous⟩

theorem continuous_clmApplyPath :
    Continuous (fun p : C(K, E →L[ℝ] F) × C(K, E) => clmApplyPath p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hd : Continuous (fun p : (C(K, E →L[ℝ] F) × C(K, E)) × K => p.1.1 p.2) :=
    ContinuousEval.continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd)
  have hu : Continuous (fun p : (C(K, E →L[ℝ] F) × C(K, E)) × K => p.1.2 p.2) :=
    ContinuousEval.continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd)
  exact hd.clm_apply hu

end ClockBarrier.Analysis
