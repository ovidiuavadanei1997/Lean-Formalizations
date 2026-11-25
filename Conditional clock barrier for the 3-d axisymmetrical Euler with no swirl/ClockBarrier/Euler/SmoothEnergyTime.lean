/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.SmoothProjectedEquation
public import ClockBarrier.Analysis.SmoothGradientEnergy
public import ClockBarrier.Analysis.SmoothEnergyControl

/-! # Gradient-controlled H³ evolution of actual smooth Euler trajectories -/
@[expose] public noncomputable section
namespace ClockBarrier.Euler.Smooth
open Set MeasureTheory ContinuousLinearMap ClockBarrier.Analysis
  Sobolev Solenoidal SmoothL2Field Filter Topology
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem word_hasDerivWithinAt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A : ℝ → SmoothL2Field V} {B : SmoothL2Field V} {t : ℝ} {s : Set ℝ}
    {n : ℕ} (w : Fin n → Fin 3)
    (hA : HasDerivWithinAt (fun r => (A r).jetLp n) (B.jetLp n) s t) :
    HasDerivWithinAt (fun r => (wordField (A r) w).toLp) (wordField B w).toLp s t := by
  simpa only [Function.comp_def, wordJetMap_apply] using
    (wordJetMap w).hasFDerivAt.comp_hasDerivWithinAt t hA

theorem wordEnergy_hasDerivWithinAt {A : ℝ → SmoothL2Field Space} {B : SmoothL2Field Space}
    {t : ℝ} {s : Set ℝ}
    (hA : ∀ n, HasDerivWithinAt (fun r => (A r).jetLp n) (B.jetLp n) s t) (m : ℕ) :
    HasDerivWithinAt (fun r => wordEnergy m (A r)) (integerEnergyProduction m (A t) B) s t := by
  have hw (n : ℕ) (w : Fin n → Fin 3) := (word_hasDerivWithinAt w (hA n)).norm_sq
  have hs := HasDerivWithinAt.fun_sum (u := Finset.range (m+1))
    (fun n _ => HasDerivWithinAt.fun_sum (u := Finset.univ) (fun w _ => hw n w))
  simpa only [wordEnergy, integerEnergyProduction, ← Finset.mul_sum] using hs

theorem rhs_eq_eulerRhs (A : SmoothL2Field Space) : rhs A = eulerRhs A (pressureForce A) := by
  apply field_ext
  funext x
  simp only [rhs, pressureForce, eulerRhs_field, fieldSub_field, scaleField_field,
    neg_smul, one_smul, advectionField_field]
  abel

theorem h3_gradient_bound (T K : ℝ) (A : ℝ → SmoothL2Field Space)
    (hc : ∀ n, Continuous (fun t => (A t).jetLp n))
    (hd : ∀ n, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun r => (A r).jetLp n)
      ((rhs (A t)).jetLp n) (Icc 0 T) t)
    (hs : ∀ t ∈ Icc 0 T, (A t).toLp ∈ solenoidalSpace)
    (hg : ∀ t ∈ Ico 0 T, ∀ x, ‖fderiv ℝ (A t).field x‖ ≤ K)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    wordEnergy 3 (A t) ≤ wordEnergy 3 (A 0)*Real.exp (gradientEnergyConstant*K*t) := by
  apply linear_stability_within (fun r => wordEnergy 3 (A r))
    (fun r => integerEnergyProduction 3 (A r) (rhs (A r)))
    (gradientEnergyConstant*K) T (wordEnergy_continuous A hc 3).continuousOn _ _ t ht
  · intro r hr
    exact wordEnergy_hasDerivWithinAt (fun n => hd n r (Ico_subset_Icc_self hr)) 3
  · intro r hr
    rw [rhs_eq_eulerRhs]
    exact h3_energy_gradient (A r) (pressureForce (A r)) K (hg r hr)
      (solenoidal_divergence (A r) (hs r (Ico_subset_Icc_self hr)))
      (hs r (Ico_subset_Icc_self hr)) (pressureForce_gradient (A r))

end ClockBarrier.Euler.Smooth
