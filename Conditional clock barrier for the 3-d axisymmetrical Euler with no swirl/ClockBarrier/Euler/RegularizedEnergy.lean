/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd.
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: actual constructed trajectories and their direct L² jet derivatives.
-/
module
public import ClockBarrier.Euler.RegularizedEnergyProduction
public import ClockBarrier.Analysis.SmoothWordTime
public import ClockBarrier.Analysis.SmoothEnergyControl

/-! # Energy bounds for actual regularized Euler trajectories

The short interval depends on the smooth datum, and is independent of the
regularization index. It is the inner approximation interval, before the
separate gradient-controlled continuation step.
-/
@[expose] public noncomputable section
namespace ClockBarrier.Euler.Regularized
open Set MeasureTheory ClockBarrier.Analysis Solenoidal SmoothL2Field Sobolev
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {k : ℕ} {T : ℝ} {U : ℝ → SmoothL2Field E₃}
  (hUc : ∀ m, Continuous (fun t => (U t).jetLp m))
  (hUd : ∀ m, ∀ t ∈ Icc 0 T,
    HasDerivAt (fun s => (U s).jetLp m) ((smoothRhs k (U t)).jetLp m) t)

include hUc hUd in
theorem short_energy (hT : 0 ≤ T)
    (hsmall : tameEnergyConstant 3*T ≤ (1+wordEnergy 3 (U 0))⁻¹/2)
    (t : ℝ) (ht : t ∈ Icc 0 T) : wordEnergy 3 (U t) ≤ 2*wordEnergy 3 (U 0)+1 := by
  apply quadratic_energy_bound T (tameEnergyConstant 3) hT
    (fun s => wordEnergy 3 (U s))
    (fun s => integerEnergyProduction 3 (U s) (smoothRhs k (U s)))
    (wordEnergy_continuous U hUc 3).continuousOn
    (fun s _ => wordEnergy_nonneg 3 (U s))
    (fun s hs => (wordEnergy_hasDerivAt (fun m => hUd m s hs) 3).hasDerivWithinAt)
    _ (tameEnergyConstant_nonneg 3) hsmall t ht
  intro s _hs
  have h := smoothRhs_energy k (U s) 3 (le_refl 3) _ (wordBound_sqrt_energy 3 (U s))
  apply h.trans
  have hx := wordEnergy_nonneg 3 (U s)
  have hr := Real.sqrt_nonneg (wordEnergy 3 (U s))
  have hs := Real.sq_sqrt hx
  have hsq : Real.sqrt (wordEnergy 3 (U s))*wordEnergy 3 (U s) ≤
      (1+wordEnergy 3 (U s))^2 := by
    have hl : Real.sqrt (wordEnergy 3 (U s)) ≤ 1+wordEnergy 3 (U s) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hl hx]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsq (tameEnergyConstant_nonneg 3)

include hUc hUd in
theorem energy_uniform (hT : 0 ≤ T) (m : ℕ) (hm : 3 ≤ m) (M : ℝ)
    (hM : ∀ t ∈ Icc 0 T, WordBound 3 M (U t)) (t : ℝ) (ht : t ∈ Icc 0 T) :
    wordEnergy m (U t) ≤ wordEnergy m (U 0)*Real.exp (tameEnergyConstant m*M*T) := by
  have hi := linear_stability_within (fun s => wordEnergy m (U s))
    (fun s => integerEnergyProduction m (U s) (smoothRhs k (U s)))
    (tameEnergyConstant m*M) T (wordEnergy_continuous U hUc m).continuousOn
    (fun s hs => (wordEnergy_hasDerivAt (fun j => hUd j s (Ico_subset_Icc_self hs)) m).hasDerivWithinAt)
    (fun s hs => smoothRhs_energy k (U s) m hm M (hM s (Ico_subset_Icc_self hs))) t ht
  apply hi.trans
  apply mul_le_mul_of_nonneg_left _ (wordEnergy_nonneg m _)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left ht.2
    (mul_nonneg (tameEnergyConstant_nonneg m) (wordBound_nonneg (hM 0 ⟨le_rfl, hT⟩)))

def regularizedTime (A : SmoothL2Field E₃) : ℝ :=
  (2*(1+tameEnergyConstant 3)*(1+wordEnergy 3 A))⁻¹

theorem regularizedTime_pos (A : SmoothL2Field E₃) : 0 < regularizedTime A := by
  have := tameEnergyConstant_nonneg 3
  have := wordEnergy_nonneg 3 A
  unfold regularizedTime
  positivity

def regularizedH3 (A : SmoothL2Field E₃) : ℝ := Real.sqrt (2*wordEnergy 3 A+1)

theorem regularized_h3 (A : SmoothL2Field E₃) {k : ℕ} {U : ℝ → SmoothL2Field E₃}
    (hUc : ∀ m, Continuous (fun t => (U t).jetLp m))
    (hUd : ∀ m, ∀ t ∈ Icc 0 (regularizedTime A),
      HasDerivAt (fun s => (U s).jetLp m) ((smoothRhs k (U t)).jetLp m) t)
    (hinit : U 0 = A) (t : ℝ) (ht : t ∈ Icc 0 (regularizedTime A)) :
    WordBound 3 (regularizedH3 A) (U t) := by
  have hc : 0 < 1+tameEnergyConstant 3 := by linarith [tameEnergyConstant_nonneg 3]
  have ha : 0 < 1+wordEnergy 3 A := by linarith [wordEnergy_nonneg 3 A]
  have hs : tameEnergyConstant 3*regularizedTime A ≤ (1+wordEnergy 3 A)⁻¹/2 := by
    calc
      _ ≤ (1+tameEnergyConstant 3)*regularizedTime A := by
        nlinarith [regularizedTime_pos A]
      _ = _ := by unfold regularizedTime; field_simp [hc.ne',ha.ne']
  have hu := short_energy hUc hUd (regularizedTime_pos A).le
    (by simpa only [hinit] using hs) t ht
  rw [hinit] at hu
  intro n hn w
  exact (wordBound_sqrt_energy 3 (U t) n hn w).trans (Real.sqrt_le_sqrt hu)

/-- An explicit bound for each derivative order, uniform in the inner smoothing index. -/
def regularizedWordBound (A : SmoothL2Field E₃) (m : ℕ) : ℝ :=
  Real.sqrt (wordEnergy (max 3 m) A *
    Real.exp (tameEnergyConstant (max 3 m)*regularizedH3 A*regularizedTime A))

/-- Concrete smooth regularized solutions, all starting at the given smooth datum,
with estimates for every spatial derivative on one common positive interval. -/
theorem exists_smooth_family_uniform (A : SmoothL2Field E₃) (hA : A.toLp ∈ solenoidalSpace) :
    ∃ U : ℕ → ℝ → SmoothL2Field E₃, ∀ k,
      U k 0 = A ∧ (∀ m, Continuous (fun t => (U k t).jetLp m)) ∧
      (∀ m, ∀ t ∈ Icc 0 (regularizedTime A),
        HasDerivAt (fun s => (U k s).jetLp m) ((smoothRhs k (U k t)).jetLp m) t) ∧
      (∀ t ∈ Icc 0 (regularizedTime A),
        (U k t).toLp ∈ solenoidalSpace ∧ ‖(U k t).toLp‖ = ‖A.toLp‖) ∧
      ∀ m, ∀ t ∈ Icc 0 (regularizedTime A), WordBound m (regularizedWordBound A m) (U k t) := by
  choose U hi hc hd he using fun k =>
    exists_smooth_solution_Icc k A hA (regularizedTime_pos A).le
  refine ⟨U, fun k => ⟨hi k, hc k, hd k, he k, ?_⟩⟩
  intro m t ht
  have hb := energy_uniform (hc k) (hd k) (regularizedTime_pos A).le (max 3 m)
    (le_max_left 3 m) (regularizedH3 A) (regularized_h3 A (hc k) (hd k) (hi k)) t ht
  rw [hi k] at hb
  intro j hj w
  exact (wordBound_sqrt_energy (max 3 m) (U k t) j (hj.trans (le_max_right 3 m)) w).trans
    (Real.sqrt_le_sqrt hb)

end ClockBarrier.Euler.Regularized
