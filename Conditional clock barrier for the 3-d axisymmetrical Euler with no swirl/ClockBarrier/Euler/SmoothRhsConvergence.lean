/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.SmoothRegularizerConvergence
public import ClockBarrier.Euler.RegularizedEnergyProduction
public import ClockBarrier.Euler.SmoothProjectedEquation

/-! # Convergence of the actual regularized Euler right hand sides -/
@[expose] public noncomputable section
namespace ClockBarrier.Euler.Regularized
open MeasureTheory ContinuousLinearMap ClockBarrier.Analysis
  Sobolev Solenoidal SmoothL2Field Filter Topology
local notation "Space" => EuclideanSpace ℝ (Fin 3)
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K] [LocallyCompactSpace K]

theorem smoothRhs_continuous (k : ℕ) : Continuous (smoothRhs k) := by
  apply continuous_smooth_iff.mpr
  intro m
  simp only [smoothRhs_jetLp]
  apply Continuous.neg
  apply (regularizedJetMap k m).continuous.comp
  have hc := continuous_toLp (fun a : SmoothL2Field Space => a) (continuous_smooth_jet 0)
  exact ((advection k).continuous.comp hc).clm_apply hc

theorem smoothRhs_tendsto (A : ℕ → K → SmoothL2Field Space)
    (hA : ∀ k n, Continuous (fun t => (A k t).jetLp n))
    (F : K → SmoothL2Field Space) (hF : ∀ n, Continuous (fun t => (F t).jetLp n))
    (h : ∀ n, Tendsto (fun k => jetPath (A k) (hA k) n) atTop (𝓝 (jetPath F hF n)))
    (hs : ∀ t, (F t).toLp ∈ solenoidalSpace) (n : ℕ) :
    Tendsto (fun k => jetPath (fun t => smoothRhs k (A k t))
      (continuous_smooth_iff.mp ((smoothRhs_continuous k).comp (continuous_smooth_iff.mpr (hA k)))) n)
      atTop (𝓝 (jetPath (fun t => Smooth.rhs (F t))
        (continuous_smooth_iff.mp (Smooth.continuous_rhs.comp (continuous_smooth_iff.mpr hF))) n)) := by
  let U (k : ℕ) (t : K) := regularizedSmoothField k (A k t).toLp
  have hU (k m : ℕ) : Continuous (fun t => (U k t).jetLp m) :=
    continuous_regularizedSmoothField_jets k m (continuous_toLp (A k) (hA k 0))
  have he (t : K) : solenoidalField (F t) = F t := by
    apply SmoothL2Field.toLp_injective
    rw [solenoidalField_toLp]
    exact solenoidalSpace.starProjection_eq_self_iff.mpr (hs t)
  have hu (m : ℕ) : Tendsto (fun k => jetPath (U k) (hU k) m) atTop (𝓝 (jetPath F hF m)) := by
    have hh := regularized_path_tendsto A hA F hF h m
    simpa only [he] using hh
  let B (k : ℕ) (t : K) := advectionField (U k t) (U k t)
  let G (t : K) := advectionField (F t) (F t)
  have hB k := continuous_smooth_iff.mp (continuous_self_advection.comp (continuous_smooth_iff.mpr (hU k)))
  have hG := continuous_smooth_iff.mp (continuous_self_advection.comp (continuous_smooth_iff.mpr hF))
  have hb m := tendsto_jetPath_operation U hU F hF hu _ continuous_self_advection m
  have hr m := regularized_path_tendsto B hB G hG hb m
  have hh := tendsto_jetPath_operation
    (fun k t => regularizedSmoothField k (B k t).toLp)
    (fun k m => continuous_regularizedSmoothField_jets k m (continuous_toLp (B k) (hB k 0)))
    (fun t => solenoidalField (G t)) (solenoidalField_continuous G hG) hr
    (scaleField (-1)) (continuous_scaleField (-1)) n
  have eqrhs (k : ℕ) (t : K) :
      scaleField (-1) (regularizedSmoothField k (B k t).toLp) = smoothRhs k (A k t) := by
    dsimp only [B, U, smoothRhs]
    rw [advection_toLp]
  simpa only [eqrhs, Smooth.rhs, G] using hh

end ClockBarrier.Euler.Regularized
