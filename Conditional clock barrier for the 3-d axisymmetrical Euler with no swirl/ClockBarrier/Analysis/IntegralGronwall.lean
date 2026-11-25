/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
/-! # Variable-coefficient differential and integral Grönwall

The integral estimate needs no time continuity of the unknown function, and
includes zero initial data without a positivity hypothesis.
-/

public section
namespace ClockBarrier.Analysis
open Set MeasureTheory Filter
open scoped Topology
/-- Interior derivative of a primitive whose integrand is continuous on a closed interval. -/
theorem hasDerivAt_primitive_of_continuousOn {k : ℝ → ℝ} {a b t : ℝ}
    (hk : ContinuousOn k (Icc a b)) (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => ∫ r in a..s, k r) (k t) t := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact (hk.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1.le
  · exact ⟨Icc a b, Icc_mem_nhds ht.1 ht.2, hk.aestronglyMeasurable measurableSet_Icc⟩
  · exact hk.continuousAt (Icc_mem_nhds ht.1 ht.2)
/-- Variable-coefficient differential Grönwall, including zero initial data. -/
theorem le_mul_exp_integral_of_deriv_le
    {f f' k : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hk : ContinuousOn k (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hb : ∀ t ∈ Ioo a b, f' t ≤ k t * f t) :
    f b ≤ f a * Real.exp (∫ t in a..b, k t) := by
  let g (t : ℝ) := f t * Real.exp (-(∫ s in a..t, k s))
  have hg (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt g ((f' t - k t * f t) * Real.exp (-(∫ s in a..t, k s))) t := by
    apply ((hd t ht).mul (hasDerivAt_primitive_of_continuousOn hk ht).neg.exp).congr_deriv
    simp only [Pi.neg_apply]
    ring
  have hprim : ContinuousOn (fun t => ∫ s in a..t, k s) (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := a) (b := b) (f := k) (by
        simpa only [uIcc_of_le hab] using hk.integrableOn_Icc (μ := volume))
  have hm : AntitoneOn g (Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) (hf.mul (Real.continuous_exp.comp_continuousOn hprim.neg))
      (fun t ht => (hg t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt)
    intro t ht
    exact mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (hb t (by simpa only [interior_Icc] using ht))) (Real.exp_pos _).le
  have hfinal := hm (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  simpa only [g, intervalIntegral.integral_same, neg_zero, Real.exp_zero, mul_one,
    Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _), div_one] using hfinal
/-- Integral Grönwall for an integrable majorant, with no continuity assumption on `f`. -/
theorem le_mul_exp_integral_of_integral_le
    {f k : ℝ → ℝ} {a b H : ℝ} (hab : a ≤ b)
    (hk : ContinuousOn k (Icc a b)) (hk0 : ∀ t ∈ Icc a b, 0 ≤ k t)
    (hi : IntegrableOn (fun t => k t * f t) (Icc a b))
    (hf : ∀ t ∈ Icc a b, f t ≤ H + ∫ s in a..t, k s * f s) :
    f b ≤ H * Real.exp (∫ t in a..b, k t) := by
  let B (t : ℝ) := ∫ s in a..t, k s * f s
  have hB : ContinuousOn B (Icc a b) := by
    simpa only [uIcc_of_le hab] using intervalIntegral.continuousOn_primitive_interval
      (a := a) (b := b) (μ := volume) (f := fun t => k t * f t)
      (by simpa only [uIcc_of_le hab] using hi)
  let z (t : ℝ) := H + ∫ s in a..t, k s * (H + B s)
  have hzint : ContinuousOn (fun s => k s * (H + B s)) (Icc a b) :=
    hk.mul (continuousOn_const.add hB)
  have hz : ContinuousOn z (Icc a b) := continuousOn_const.add (by
    simpa only [uIcc_of_le hab] using intervalIntegral.continuousOn_primitive_interval
      (a := a) (b := b) (μ := volume) (f := fun s => k s * (H + B s))
      (by simpa only [uIcc_of_le hab] using hzint.integrableOn_Icc (μ := volume)))
  have hBz (t : ℝ) (ht : t ∈ Icc a b) : H + B t ≤ z t := by
    apply add_le_add le_rfl
    apply intervalIntegral.integral_mono_on ht.1
      ((intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr
        (hi.mono_set (Icc_subset_Icc le_rfl ht.2)))
      ((hzint.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1)
    intro s hs
    exact mul_le_mul_of_nonneg_left (hf s ⟨hs.1, hs.2.trans ht.2⟩)
      (hk0 s ⟨hs.1, hs.2.trans ht.2⟩)
  have hzg := le_mul_exp_integral_of_deriv_le hab hz hk
    (fun t ht => (hasDerivAt_primitive_of_continuousOn hzint ht).const_add H)
    (fun t ht => mul_le_mul_of_nonneg_left (hBz t (Ioo_subset_Icc_self ht))
      (hk0 t (Ioo_subset_Icc_self ht)))
  exact ((hf b (right_mem_Icc.mpr hab)).trans (hBz b (right_mem_Icc.mpr hab))).trans
    (by simpa only [z, intervalIntegral.integral_same, add_zero] using hzg)
/-- Vector-valued Grönwall with a continuous variable coefficient. -/
theorem norm_le_mul_exp_integral_of_norm_deriv_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} {k : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hk : ContinuousOn k (Icc a b))
    (hk0 : ∀ t ∈ Icc a b, 0 ≤ k t)
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Ioo a b, ‖f' t‖ ≤ k t * ‖f t‖) :
    ‖f b‖ ≤ ‖f a‖ * Real.exp (∫ t in a..b, k t) := by
  apply le_mul_exp_integral_of_integral_le hab hk hk0 (hk.mul hf.norm).integrableOn_Icc
  intro t ht
  have hh := norm_sub_le_integral_of_norm_deriv_le_of_le ht.1
    (hf.mono (Icc_subset_Icc le_rfl ht.2))
    (fun s hs => (hd s ⟨hs.1, hs.2.trans_le ht.2⟩).differentiableAt.differentiableWithinAt)
    (Eventually.of_forall (fun s hs => by
      rw [(hd s ⟨hs.1, hs.2.trans_le ht.2⟩).deriv]
      exact hbound s ⟨hs.1, hs.2.trans_le ht.2⟩))
    (((hk.mul hf.norm).mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1)
  simp only [Pi.mul_apply] at hh
  linarith [norm_sub_norm_le (f t) (f a)]
end ClockBarrier.Analysis
