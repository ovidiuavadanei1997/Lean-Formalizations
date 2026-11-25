/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.SmoothTopology
public import ClockBarrier.Analysis.SmoothProductContinuity
public import ClockBarrier.Analysis.SmoothHelmholtz

/-! # Uniform convergence of smooth field operations on compact time intervals -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Sobolev
open MeasureTheory ContinuousLinearMap SmoothL2Field Filter Topology
local notation "Space" => EuclideanSpace ℝ (Fin 3)
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K]

theorem tendsto_jetPath_operation {ι : Type*} {l : Filter ι}
    (A : ι → K → SmoothL2Field V) (hA : ∀ k n, Continuous (fun t => (A k t).jetLp n))
    (F : K → SmoothL2Field V) (hF : ∀ n, Continuous (fun t => (F t).jetLp n))
    (h : ∀ n, Tendsto (fun k => jetPath (A k) (hA k) n) l (𝓝 (jetPath F hF n)))
    (op : SmoothL2Field V → SmoothL2Field W) (hop : Continuous op) (n : ℕ) :
    Tendsto (fun k => jetPath (fun t => op (A k t))
      (continuous_smooth_iff.mp (hop.comp (continuous_smooth_iff.mpr (hA k)))) n) l
      (𝓝 (jetPath (fun t => op (F t))
        (continuous_smooth_iff.mp (hop.comp (continuous_smooth_iff.mpr hF))) n)) := by
  let J : C(SmoothL2Field V, Lp (Space [×n]→L[ℝ] W) 2 (volume : Measure Space)) :=
    ⟨fun a => (op a).jetLp n, (continuous_smooth_jet n).comp hop⟩
  exact ((ContinuousMap.continuous_postcomp (X := K) J).tendsto _).comp
    (tendsto_smoothPath A hA F hF h)

theorem continuous_self_advection :
    Continuous (fun A : SmoothL2Field Space => advectionField A A) :=
  continuous_smooth_iff.mpr (continuous_advectionField_jet id id
    continuous_smooth_jet continuous_smooth_jet)

theorem continuous_solenoidalField : Continuous solenoidalField :=
  continuous_smooth_iff.mpr (solenoidalField_continuous id continuous_smooth_jet)

theorem continuous_scaleField (c : ℝ) : Continuous (scaleField (V := V) c) :=
  continuous_smooth_iff.mpr (scaleField_continuous c id continuous_smooth_jet)

end ClockBarrier.Analysis.Sobolev
