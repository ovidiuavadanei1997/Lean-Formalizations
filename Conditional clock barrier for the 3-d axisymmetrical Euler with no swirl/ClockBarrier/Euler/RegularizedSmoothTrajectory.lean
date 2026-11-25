/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.RegularizedJets
public import ClockBarrier.Euler.RegularizedFamily
import ClockBarrier.Dynamics.FlowDifferentiability
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # All spatial L² jets of the actual regularized trajectories

The solution is lifted by its integral equation. Thus smoothness and time
regularity of the state are conclusions, rather than additional ODE hypotheses.
-/
@[expose] public noncomputable section
namespace ClockBarrier.Euler.Regularized
open Set MeasureTheory ContinuousLinearMap ClockBarrier.Analysis
  Solenoidal SmoothL2Field Sobolev
open scoped ContDiff
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

def smoothRhs (n : ℕ) (A : SmoothL2Field E₃) : SmoothL2Field E₃ :=
  scaleField (-1) (regularizedSmoothField n (advection n A.toLp A.toLp))

theorem smoothRhs_toLp (n : ℕ) (A : SmoothL2Field E₃) :
    (smoothRhs n A).toLp = quadratic n A.toLp A.toLp := by
  simp only [smoothRhs, scaleField_toLp, regularizedSmoothField_toLp, neg_smul,
    one_smul, quadratic_apply]

theorem smoothRhs_jetLp (n m : ℕ) (A : SmoothL2Field E₃) :
    (smoothRhs n A).jetLp m = -regularizedJetMap n m (advection n A.toLp A.toLp) := by
  simp only [smoothRhs, scaleField_jetLp, neg_smul, one_smul, regularizedJetMap_apply]

/-- The integral equation lifts a regularized L² solution to an actual smooth
field, with all spatial L² jets continuously differentiable in time. -/
theorem smooth_lift {n : ℕ} {T : ℝ} (hT : 0 ≤ T) (A : SmoothL2Field E₃)
    {u : ℝ → L2} (hinit : u 0 = A.toLp)
    (hcont : ContinuousOn u (Icc 0 T))
    (hode : ∀ t ∈ Ico 0 T,
      HasDerivWithinAt u (quadratic n (u t) (u t)) (Ici t) t) :
    ∃ V : ℝ → SmoothL2Field E₃,
      V 0 = A ∧ (∀ t ∈ Icc 0 T, (V t).toLp = u t) ∧
      (∀ m, Continuous (fun t => (V t).jetLp m)) ∧
      ∀ m, ∀ t ∈ Icc 0 T,
        HasDerivAt (fun s => (V s).jetLp m) ((smoothRhs n (V t)).jetLp m) t := by
  let v : ℝ → L2 := fun t => u (projIcc 0 T hT t)
  have hv : Continuous v := hcont.restrict.comp continuous_projIcc
  have he (t : ℝ) (ht : t ∈ Icc 0 T) : v t = u t := by
    simp only [v, projIcc_of_mem hT ht]
  let f : ℝ → L2 := fun t => -advection n (v t) (v t)
  have hf : Continuous f := ((advection n).continuous.comp hv |>.clm_apply hv).neg
  let z : ℝ → L2 := fun t => ∫ s in 0..t, f s
  have hz (t : ℝ) : HasDerivAt z (f t) t :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hi (t : ℝ) (ht : t ∈ Icc 0 T) : u t = A.toLp + regularizerMap n (z t) := by
    have hq := ClockBarrier.Dynamics.eq_add_integral_of_trajectory
      (u := fun _ a => quadratic n a a)
      (((quadratic n).continuous.comp continuous_snd |>.clm_apply continuous_snd).continuousOn)
      hcont hode ht
    rw [hinit] at hq
    rw [← (regularizerMap n).intervalIntegral_comp_comm (hf.intervalIntegrable 0 t)]
    apply hq.trans
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc 0 T := (uIcc_subset_Icc ⟨le_rfl, hT⟩ ht) hs
    simp only [f, map_neg, he s hs', quadratic_apply]
  let V : ℝ → SmoothL2Field E₃ := fun t => addField A (regularizedSmoothField n (z t))
  have hV (t : ℝ) (ht : t ∈ Icc 0 T) : (V t).toLp = u t := by
    rw [show V t = addField A (regularizedSmoothField n (z t)) from rfl,
      toLp_addField, regularizedSmoothField_toLp]
    exact (hi t ht).symm
  refine ⟨V, ?_, hV, ?_, ?_⟩
  · apply SmoothL2Field.toLp_injective
    rw [hV 0 ⟨le_rfl, hT⟩, hinit]
  · intro m
    exact continuous_jetLp_addField (fun _ => A) (fun t => regularizedSmoothField n (z t))
      (fun _ => continuous_const)
      (fun k => continuous_regularizedSmoothField_jets n k (continuous_iff_continuousAt.mpr (fun t => (hz t).continuousAt))) m
  · intro m t ht
    simp only [V, jetLp_addField]
    have hd := ((regularizedJetMap n m).hasFDerivAt.comp_hasDerivAt t (hz t)).const_add (A.jetLp m)
    convert! hd using 1
    rw [smoothRhs_jetLp, hV t ht]
    simp only [f, he t ht, map_neg]

/-- For a smooth solenoidal datum the existing global L² ODE supplies smooth
regularized trajectories with genuine time derivatives of every spatial jet. -/
theorem exists_smooth_solution_Icc (n : ℕ) (A : SmoothL2Field E₃)
    (hA : A.toLp ∈ solenoidalSpace) {T : ℝ} (hT : 0 ≤ T) :
    ∃ V : ℝ → SmoothL2Field E₃,
      V 0 = A ∧ (∀ m, Continuous (fun t => (V t).jetLp m)) ∧
      (∀ m, ∀ t ∈ Icc 0 T,
        HasDerivAt (fun s => (V s).jetLp m) ((smoothRhs n (V t)).jetLp m) t) ∧
      ∀ t ∈ Icc 0 T, (V t).toLp ∈ solenoidalSpace ∧ ‖(V t).toLp‖ = ‖A.toLp‖ := by
  obtain ⟨u, hi, hc, hd, hn⟩ := exists_solution_Icc n A.toLp hT
  obtain ⟨V, hV0, hV, hVc, hVd⟩ := smooth_lift hT A hi hc hd
  refine ⟨V, hV0, hVc, hVd, fun t ht => ?_⟩
  rw [hV t ht]
  exact ⟨solution_solenoidal hc hd (hi.symm ▸ hA) t ht, hn t ht⟩

end ClockBarrier.Euler.Regularized
