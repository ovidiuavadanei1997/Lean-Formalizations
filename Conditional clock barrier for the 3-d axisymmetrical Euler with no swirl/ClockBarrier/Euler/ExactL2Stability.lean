/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.PerturbedEulerEnergy
public import ClockBarrier.Euler.SmoothProjectedEquation
public import ClockBarrier.Analysis.SmoothPaths

/-! # Strong L² stability of exact smooth Euler trajectories

The estimate uses only the uniform first derivative bound. In particular, its
constant is independent of the higher Sobolev norms of the mollified data.
-/
@[expose] public noncomputable section
namespace ClockBarrier.Euler.Smooth
open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap ClockBarrier.Analysis
  Solenoidal SmoothL2Field Sobolev
open scoped Topology
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem exact_l2_stability {T : ℝ} {U V : ℝ → SmoothL2Field Space}
    (hUc : Continuous (fun t => (U t).toLp))
    (hVc : Continuous (fun t => (V t).toLp))
    (hUd : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => (U s).toLp)
      (rhs (U t)).toLp (Icc 0 T) t)
    (hVd : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => (V s).toLp)
      (rhs (V t)).toLp (Icc 0 T) t)
    (hUs : ∀ t ∈ Icc 0 T, (U t).toLp ∈ solenoidalSpace)
    (hVs : ∀ t ∈ Icc 0 T, (V t).toLp ∈ solenoidalSpace)
    (R : ℝ) (hR : 0 ≤ R)
    (hgrad : ∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (U t).field x‖ ≤ R)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖(V t).toLp - (U t).toLp‖ ≤
      ‖(V 0).toLp - (U 0).toLp‖ * Real.exp (R * T) := by
  let X (r : ℝ) := ‖(V r).toLp - (U r).toLp‖ ^ 2
  let X' (r : ℝ) := 2 * ⟪(V r).toLp - (U r).toLp,
    (rhs (V r)).toLp - (rhs (U r)).toLp⟫_ℝ
  have hd (r : ℝ) (hr : r ∈ Ico 0 T) :
      HasDerivWithinAt X (X' r) (Icc 0 T) r := by
    simpa only [X, X', Pi.sub_apply] using
      ((hVd r ⟨hr.1, hr.2.le⟩).sub (hUd r ⟨hr.1, hr.2.le⟩)).norm_sq
  have hb (r : ℝ) (hr : r ∈ Ico 0 T) : X' r ≤ (2 * R) * X r := by
    simpa only [X, X', rhs_toLp, Regularized.projectedRhsL2] using
      Regularized.projected_difference_energy (U r) (V r)
        (hUs r ⟨hr.1, hr.2.le⟩) (hVs r ⟨hr.1, hr.2.le⟩) R
        (hgrad r ⟨hr.1, hr.2.le⟩)
  have he := linear_stability_within X X' (2 * R) T
    ((hVc.sub hUc).norm.pow 2).continuousOn hd hb t ht
  have hexp : Real.exp (2 * R * t) ≤ (Real.exp (R * T)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    nlinarith [mul_le_mul_of_nonneg_left ht.2 hR]
  have he' : X t ≤ X 0 * (Real.exp (R * T)) ^ 2 :=
    he.trans (mul_le_mul_of_nonneg_left hexp (sq_nonneg _))
  dsimp only [X] at he'
  nlinarith [norm_nonneg ((V t).toLp - (U t).toLp),
    mul_nonneg (norm_nonneg ((V 0).toLp - (U 0).toLp)) (Real.exp_pos (R * T)).le]

theorem exact_l2_cauchy {T : ℝ} {U : ℕ → ℝ → SmoothL2Field Space}
    (hUc : ∀ k m, Continuous (fun t => (U k t).jetLp m))
    (hUd : ∀ k, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => (U k s).toLp)
      (rhs (U k t)).toLp (Icc 0 T) t)
    (hUs : ∀ k, ∀ t ∈ Icc 0 T, (U k t).toLp ∈ solenoidalSpace)
    (R : ℝ) (hR : 0 ≤ R)
    (hgrad : ∀ k, ∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (U k t).field x‖ ≤ R)
    (hinit : CauchySeq (fun k => (U k 0).toLp)) :
    CauchySeq (fun k => fieldPath (fun t : Icc (0 : ℝ) T => U k t)
      (fun m => (hUc k m).comp continuous_subtype_val)) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hinit
    (ε / Real.exp (R * T)) (div_pos hε (Real.exp_pos _))
  refine ⟨N, fun j hj k hk => ?_⟩
  rw [dist_eq_norm]
  have hb : ‖fieldPath (fun t : Icc (0 : ℝ) T => U j t)
      (fun m => (hUc j m).comp continuous_subtype_val) -
      fieldPath (fun t : Icc (0 : ℝ) T => U k t)
      (fun m => (hUc k m).comp continuous_subtype_val)‖ ≤
        ‖(U j 0).toLp - (U k 0).toLp‖ * Real.exp (R * T) := by
    apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)).mpr
    intro t
    exact exact_l2_stability (continuous_toLp _ (hUc k 0))
      (continuous_toLp _ (hUc j 0)) (hUd k) (hUd j) (hUs k) (hUs j)
      R hR (hgrad k) t t.property
  apply hb.trans_lt
  exact (lt_div_iff₀ (Real.exp_pos _)).mp (by simpa only [dist_eq_norm] using hN j hj k hk)

end ClockBarrier.Euler.Smooth
