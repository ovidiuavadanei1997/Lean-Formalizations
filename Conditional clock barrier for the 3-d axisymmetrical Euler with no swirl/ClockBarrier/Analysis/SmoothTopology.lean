/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.SmoothPaths
public import Mathlib.Topology.CompactOpen

/-! # The topology of convergence of every actual spatial L² jet -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Sobolev
open MeasureTheory SmoothL2Field Filter Topology
local notation "Space" => EuclideanSpace ℝ (Fin 3)
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

instance smoothFieldTopology : TopologicalSpace (SmoothL2Field V) :=
  TopologicalSpace.induced (fun A : SmoothL2Field V => A.jetLp) inferInstance

theorem continuous_smooth_iff {K : Type*} [TopologicalSpace K] {A : K → SmoothL2Field V} :
    Continuous A ↔ ∀ n, Continuous (fun t => (A t).jetLp n) := by
  rw [continuous_induced_rng, continuous_pi_iff]
  rfl

theorem continuous_smooth_jet (n : ℕ) : Continuous (fun A : SmoothL2Field V => A.jetLp n) :=
  continuous_smooth_iff.mp continuous_id n

def smoothPath {K : Type*} [TopologicalSpace K] (A : K → SmoothL2Field V)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) : C(K, SmoothL2Field V) :=
  ⟨A, continuous_smooth_iff.mpr hA⟩

variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K]

theorem tendsto_smoothPath {ι : Type*} {l : Filter ι}
    (A : ι → K → SmoothL2Field V) (hA : ∀ k n, Continuous (fun t => (A k t).jetLp n))
    (F : K → SmoothL2Field V) (hF : ∀ n, Continuous (fun t => (F t).jetLp n))
    (h : ∀ n, Tendsto (fun k => jetPath (A k) (hA k) n) l (𝓝 (jetPath F hF n))) :
    Tendsto (fun k => smoothPath (A k) (hA k)) l (𝓝 (smoothPath F hF)) := by
  let J : C(SmoothL2Field V, ∀ n, Lp (Space [×n]→L[ℝ] V) 2 (volume : Measure Space)) :=
    ⟨fun A => A.jetLp, continuous_induced_dom⟩
  have hJ : IsInducing J := ⟨rfl⟩
  rw [(ContinuousMap.isInducing_postcomp J hJ).tendsto_nhds_iff]
  have hp := tendsto_pi_nhds.mpr h
  let combine := ContinuousMap.piEquiv K (fun n => Lp (Space [×n]→L[ℝ] V) 2 (volume : Measure Space))
  have hc : Continuous combine := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply continuous_pi
    intro n
    exact continuous_eval.comp ((continuous_apply n |>.comp continuous_fst).prodMk continuous_snd)
  exact (hc.tendsto _).comp hp

end ClockBarrier.Analysis.Sobolev
