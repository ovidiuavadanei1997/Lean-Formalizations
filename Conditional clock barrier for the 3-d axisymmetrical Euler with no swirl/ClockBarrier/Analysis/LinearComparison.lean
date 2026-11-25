/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.ACComparison
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # Linear equality solutions and right-derivative comparison for L¹ coefficients -/

public section
namespace ClockBarrier.Analysis
open Set MeasureTheory Filter
open scoped Topology

/-- A continuous right-differentiable subsolution is bounded by the absolutely
continuous equality solution, even with merely integrable time coefficients. -/
theorem le_linear_solution_of_right_deriv
    {H H' G k : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hH : ContinuousOn H (Icc a b))
    (hdH : ∀ t ∈ Ioo a b, HasDerivWithinAt H (H' t) (Ioi t) t)
    (hk : IntegrableOn k (Icc a b)) (hk₀ : ∀ t ∈ Icc a b, 0 ≤ k t)
    (hbound : ∀ t ∈ Ioo a b, H' t ≤ k t * H t + c)
    (hG : AbsolutelyContinuousOnInterval G a b) (ha : G a = H a)
    (hdG : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt G (k t * G t + c) t) :
    H b ≤ G b := by
  let A := fun t => H a + ∫ s in a..t, k s * H s + c
  have hi : IntegrableOn (fun t => k t * H t + c) (Icc a b) :=
    (hk.mul_continuousOn hH isCompact_Icc).add
      (integrableOn_const isCompact_Icc.measure_lt_top.ne)
  have hinterval := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hi
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => H a) a b :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => H a)).contDiffOn.absolutelyContinuousOnInterval
  have hA : AbsolutelyContinuousOnInterval A a b :=
    hconst.fun_add (hinterval.absolutelyContinuousOnInterval_intervalIntegral (by simp))
  have hHA (t : ℝ) (ht : t ∈ Icc a b) : H t ≤ A t := by
    have hh := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le ht.1
      (hH.mono (Icc_subset_Icc le_rfl ht.2))
      (fun s hs => hdH s ⟨hs.1, hs.2.trans_le ht.2⟩)
      (hi.mono_set (Icc_subset_Icc le_rfl ht.2))
      (fun s hs => hbound s ⟨hs.1, hs.2.trans_le ht.2⟩)
    dsimp only [A]
    linarith only [hh]
  have hdA : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt A (k t * H t + c) t := by
    filter_upwards [hinterval.ae_hasDerivAt_integral] with t ht hm
    exact (ht hm a (by simp)).const_add (H a)
  have hdW : ∀ᵐ t, t ∈ uIcc a b →
      HasDerivAt (fun t => A t - G t) (k t * (H t - G t)) t := by
    filter_upwards [hdA, hdG] with t ht hg hm
    apply ((ht hm).sub (hg hm)).congr_deriv
    ring
  have hbW : ∀ᵐ t, t ∈ uIcc a b → k t * (H t - G t) ≤ k t * (A t - G t) := by
    filter_upwards with t ht
    have hm : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right (hHA t hm) _) (hk₀ t hm)
  have hW := le_mul_exp_integral_of_ac_deriv_le hab (hA.fun_sub hG)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hk) hdW hbW
  have hba : A b ≤ G b := by
    simpa only [A, intervalIntegral.integral_same, add_zero, ha, sub_self, zero_mul,
      sub_nonpos] using hW
  exact (hHA b (right_mem_Icc.mpr hab)).trans hba

/-- Construct the positive solution of the inhomogeneous linear comparison ODE
by its integrating factor. All time derivatives are asserted almost everywhere. -/
theorem exists_ac_linear_comparison {k : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hc : 0 ≤ c) (hk : IntegrableOn k (Icc a b))
    (hk₀ : ∀ t ∈ Icc a b, 0 ≤ k t) :
    ∃ G : ℝ → ℝ, AbsolutelyContinuousOnInterval G a b ∧ G a = 1 ∧
      (∀ t ∈ Icc a b, 1 ≤ G t) ∧
      (∀ᵐ t, t ∈ uIcc a b → HasDerivAt G (k t * G t + c) t) ∧
      G b ≤ Real.exp (∫ t in a..b, k t + c) := by
  let P := fun t => ∫ s in a..t, k s
  let E := fun t => Real.exp (P t)
  let Q := fun t => ∫ s in a..t, Real.exp (-P s)
  let G := fun t => E t * (1 + c * Q t)
  have hki := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hk
  have hP : AbsolutelyContinuousOnInterval P a b :=
    hki.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hE : AbsolutelyContinuousOnInterval E a b := ac_exp hP
  have hEi : IntervalIntegrable (fun s => Real.exp (-P s)) volume a b :=
    (ac_exp hP.fun_neg).continuousOn.intervalIntegrable
  have hQ : AbsolutelyContinuousOnInterval Q a b :=
    hEi.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ))).contDiffOn.absolutelyContinuousOnInterval
  have hG : AbsolutelyContinuousOnInterval G a b := hE.fun_mul (hconst.fun_add (hQ.const_mul c))
  have hGa : G a = 1 := by simp [G, E, P, Q]
  have hG₁ (t : ℝ) (ht : t ∈ Icc a b) : 1 ≤ G t := by
    have hP₀ : 0 ≤ P t := intervalIntegral.integral_nonneg ht.1
      (fun s hs => hk₀ s ⟨hs.1, hs.2.trans ht.2⟩)
    have hE₁ : 1 ≤ E t := Real.one_le_exp_iff.mpr hP₀
    have hQ₀ : 0 ≤ Q t := intervalIntegral.integral_nonneg ht.1 (fun s _ => (Real.exp_pos _).le)
    dsimp only [G]
    nlinarith only [hE₁, mul_nonneg (Real.exp_pos (P t)).le (mul_nonneg hc hQ₀)]
  have hdG : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt G (k t * G t + c) t := by
    filter_upwards [hki.ae_hasDerivAt_integral, hEi.ae_hasDerivAt_integral] with t hp hq ht
    have hdE : HasDerivAt E (E t * k t) t := (hp ht a (by simp)).exp
    have hdQ : HasDerivAt Q (Real.exp (-P t)) t := hq ht a (by simp)
    apply (hdE.mul ((hdQ.const_mul c).const_add 1)).congr_deriv
    have hexp : E t * Real.exp (-P t) = 1 := by
      dsimp only [E]
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    dsimp only [G]
    nlinarith only [congrArg (c * ·) hexp]
  have hgrowth : ∀ᵐ t, t ∈ uIcc a b → k t * G t + c ≤ (k t + c) * G t := by
    filter_upwards with t ht
    have hmem : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
    nlinarith only [mul_nonneg hc (sub_nonneg.mpr (hG₁ t hmem))]
  have hfinal := le_mul_exp_integral_of_ac_deriv_le hab hG (hki.add intervalIntegrable_const) hdG hgrowth
  exact ⟨G, hG, hGa, hG₁, hdG, by simpa only [hGa, one_mul, Pi.add_apply] using hfinal⟩
end ClockBarrier.Analysis
