/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.SmoothLocalSolver
public import ClockBarrier.Analysis.ClosedIntervalJoin

/-! # Restarting actual smooth Euler trajectories at a matching endpoint -/
@[expose] public noncomputable section
namespace ClockBarrier.Euler.Smooth
open Set MeasureTheory ContinuousLinearMap ClockBarrier.Analysis
  Sobolev Solenoidal SmoothL2Field Filter Topology
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem join_continuous (S : ℝ) (U V : ℝ → SmoothL2Field Space) (he : U S = V 0)
    (hU : ∀ n, Continuous (fun t => (U t).jetLp n))
    (hV : ∀ n, Continuous (fun t => (V t).jetLp n)) (n : ℕ) :
    Continuous (fun t => (joinTime S U V t).jetLp n) := by
  simp_rw [joinTime_comp (fun A : SmoothL2Field Space => A.jetLp n)]
  exact continuous_joinTime S _ _ (hU n) (hV n) (congrArg (fun A => A.jetLp n) he)

theorem join_equation (S D : ℝ) (U V : ℝ → SmoothL2Field Space) (he : U S = V 0)
    (hU : ∀ n, ∀ t ∈ Icc 0 S, HasDerivWithinAt (fun r => (U r).jetLp n)
      ((rhs (U t)).jetLp n) (Icc 0 S) t)
    (hV : ∀ n, ∀ t ∈ Icc 0 D, HasDerivWithinAt (fun r => (V r).jetLp n)
      ((rhs (V t)).jetLp n) (Icc 0 D) t) (n : ℕ) (t : ℝ) :
    HasDerivWithinAt (fun r => (joinTime S U V r).jetLp n)
      ((rhs (joinTime S U V t)).jetLp n) (Icc 0 (S+D)) t := by
  have hh := hasDerivWithinAt_joinTime S D
    (fun r => (U r).jetLp n) (fun r => (V r).jetLp n)
    (fun r => (rhs (U r)).jetLp n) (fun r => (rhs (V r)).jetLp n)
    (congrArg (fun A => A.jetLp n) he) (congrArg (fun A => (rhs A).jetLp n) he)
    (hU n) (hV n) t
  have he₁ := funext (joinTime_comp (fun A : SmoothL2Field Space => A.jetLp n) S U V)
  have he₂ := joinTime_comp (fun A : SmoothL2Field Space => (rhs A).jetLp n) S U V t
  rw [he₁, he₂]
  exact hh

theorem join_solenoidal (S D : ℝ) (U V : ℝ → SmoothL2Field Space)
    (hU : ∀ t ∈ Icc 0 S, (U t).toLp ∈ solenoidalSpace)
    (hV : ∀ t ∈ Icc 0 D, (V t).toLp ∈ solenoidalSpace)
    (t : ℝ) (ht : t ∈ Icc 0 (S+D)) : (joinTime S U V t).toLp ∈ solenoidalSpace := by
  unfold joinTime
  split_ifs with h
  · exact hU t ⟨ht.1, h⟩
  · apply hV
    constructor <;> linarith [ht.2]

/-- The genuine local construction restarts any supplied smooth trajectory.
Its extra time is the explicit H³-controlled local lifespan at the endpoint. -/
theorem exists_restart (S : ℝ) (hS : 0 ≤ S) (U : ℝ → SmoothL2Field Space)
    (hc : ∀ n, Continuous (fun t => (U t).jetLp n))
    (hd : ∀ n, ∀ t ∈ Icc 0 S, HasDerivWithinAt (fun r => (U r).jetLp n)
      ((rhs (U t)).jetLp n) (Icc 0 S) t)
    (hs : ∀ t ∈ Icc 0 S, (U t).toLp ∈ solenoidalSpace) :
    ∃ W : ℝ → SmoothL2Field Space,
      (∀ t ≤ S, W t = U t) ∧
      (∀ n, Continuous (fun t => (W t).jetLp n)) ∧
      (∀ n, ∀ t ∈ Icc 0 (S+Regularized.regularizedTime (U S)),
        HasDerivWithinAt (fun r => (W r).jetLp n) ((rhs (W t)).jetLp n)
          (Icc 0 (S+Regularized.regularizedTime (U S))) t) ∧
      ∀ t ∈ Icc 0 (S+Regularized.regularizedTime (U S)), (W t).toLp ∈ solenoidalSpace := by
  obtain ⟨V, hi, hV, hdV, hsV⟩ := exists_smooth_local (U S) (hs S ⟨hS, le_rfl⟩)
  refine ⟨joinTime S U V, fun t ht => joinTime_left S U V ht,
    join_continuous S U V hi.symm hc hV,
    fun n t _ => join_equation S _ U V hi.symm hd hdV n t,
    join_solenoidal S _ U V hs (fun t ht => (hsV t ht).1)⟩

end ClockBarrier.Euler.Smooth
