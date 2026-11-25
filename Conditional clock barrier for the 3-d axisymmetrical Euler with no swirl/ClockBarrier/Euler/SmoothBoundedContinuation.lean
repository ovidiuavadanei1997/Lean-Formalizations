/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.SmoothJoin
public import ClockBarrier.Euler.SmoothEnergyTime

/-! # Repeated genuine restarts under a uniform gradient bound

The a priori hypothesis bounds every already constructed short trajectory.
It supplies neither a solution nor a continuation. The local solver and the
H³ evolution estimate give a fixed positive restart increment, after which a
finite induction constructs the trajectory to the prescribed time.
-/
@[expose] public noncomputable section
namespace ClockBarrier.Euler.Smooth
open Set MeasureTheory ContinuousLinearMap ClockBarrier.Analysis
  Sobolev Solenoidal SmoothL2Field Regularized Filter Topology
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem exists_smooth_on_of_gradient_bound (A : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) (T K : ℝ) (hT : 0 < T) (hK : 0 ≤ K)
    (hbound : ∀ (S : ℝ), 0 < S → S ≤ T → ∀ U : ℝ → SmoothL2Field Space,
      U 0 = A → (∀ n, Continuous (fun t => (U t).jetLp n)) →
      (∀ n, ∀ t ∈ Icc 0 S, HasDerivWithinAt (fun r => (U r).jetLp n)
        ((rhs (U t)).jetLp n) (Icc 0 S) t) →
      (∀ t ∈ Icc 0 S, (U t).toLp ∈ solenoidalSpace) →
      ∀ t ∈ Ico 0 S, ∀ x, ‖fderiv ℝ (U t).field x‖ ≤ K) :
    ∃ U : ℝ → SmoothL2Field Space,
      U 0 = A ∧ (∀ n, Continuous (fun t => (U t).jetLp n)) ∧
      (∀ n, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun r => (U r).jetLp n)
        ((rhs (U t)).jetLp n) (Icc 0 T) t) ∧
      ∀ t ∈ Icc 0 T, (U t).toLp ∈ solenoidalSpace := by
  let P (S : ℝ) := ∃ U : ℝ → SmoothL2Field Space,
    U 0 = A ∧ (∀ n, Continuous (fun t => (U t).jetLp n)) ∧
    (∀ n, ∀ t ∈ Icc 0 S, HasDerivWithinAt (fun r => (U r).jetLp n)
      ((rhs (U t)).jetLp n) (Icc 0 S) t) ∧
    ∀ t ∈ Icc 0 S, (U t).toLp ∈ solenoidalSpace
  let E := wordEnergy 3 A * Real.exp (gradientEnergyConstant*K*T)
  let δ := (2*(1+tameEnergyConstant 3)*(1+E))⁻¹
  have hE : 0 ≤ E := mul_nonneg (wordEnergy_nonneg 3 A) (Real.exp_pos _).le
  have hC : 0 < 2*(1+tameEnergyConstant 3) := by linarith [tameEnergyConstant_nonneg 3]
  have hδ : 0 < δ := inv_pos.mpr (mul_pos hC (by linarith))
  have hzero : P 0 := by
    refine ⟨fun _ => A, rfl, fun _ => continuous_const, ?_, fun _ _ => hA⟩
    intro n t _
    apply HasFDerivWithinAt.of_subsingleton
    rw [Icc_self]
    exact subsingleton_singleton
  have hstep (S : ℝ) (hS : 0 ≤ S) (hST : S ≤ T) (hP : P S) : P (min (S+δ) T) := by
    obtain ⟨U, hi, hc, hd, hs⟩ := hP
    have hEU : wordEnergy 3 (U S) ≤ E := by
      have hh := h3_gradient_bound S K U hc hd hs
        (fun t ht => hbound S (ht.1.trans_lt ht.2) hST U hi hc hd hs t ht)
        S ⟨hS, le_rfl⟩
      rw [hi] at hh
      apply hh.trans
      apply mul_le_mul_of_nonneg_left _ (wordEnergy_nonneg 3 A)
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left hST
      exact mul_nonneg (by norm_num [gradientEnergyConstant]) hK
    have hδU : δ ≤ regularizedTime (U S) := by
      apply inv_anti₀
      · exact mul_pos hC (by linarith [wordEnergy_nonneg 3 (U S)])
      · exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hEU) hC.le
    obtain ⟨W, hW, hWc, hWd, hWs⟩ := exists_restart S hS U hc hd hs
    have hsmall : Icc (0 : ℝ) (min (S+δ) T) ⊆ Icc 0 (S+regularizedTime (U S)) :=
      Icc_subset_Icc le_rfl ((min_le_left _ _).trans (add_le_add le_rfl hδU))
    refine ⟨W, (hW 0 hS).trans hi, hWc,
      fun n t ht => (hWd n t (hsmall ht)).mono hsmall,
      fun t ht => hWs t (hsmall ht)⟩
  have hsteps (n : ℕ) : P (min ((n : ℝ)*δ) T) := by
    induction n with
    | zero => simpa only [Nat.cast_zero, zero_mul, min_eq_left hT.le] using hzero
    | succ n ih =>
      by_cases hNT : T ≤ (n : ℝ)*δ
      · have hnext : T ≤ ((n+1 : ℕ) : ℝ)*δ := by
          simp only [Nat.cast_add, Nat.cast_one]
          nlinarith
        simpa only [min_eq_right hNT, min_eq_right hnext] using ih
      · have hn : (n : ℝ)*δ ≤ T := (not_le.mp hNT).le
        have hh := hstep ((n : ℝ)*δ) (mul_nonneg (Nat.cast_nonneg _) hδ.le) hn
          (by simpa only [min_eq_left hn] using ih)
        simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hh
  obtain ⟨N, hN⟩ := exists_nat_gt (T/δ)
  have hNT : T ≤ (N : ℝ)*δ := ((div_lt_iff₀ hδ).mp hN).le
  simpa only [min_eq_right hNT] using hsteps N

end ClockBarrier.Euler.Smooth
