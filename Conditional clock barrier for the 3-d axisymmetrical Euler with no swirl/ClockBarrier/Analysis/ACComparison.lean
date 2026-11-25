/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # Absolutely continuous comparison calculus for integrable time coefficients -/

public section
namespace ClockBarrier.Analysis
open Set MeasureTheory Filter
open scoped Topology

theorem ac_comp_of_dist_le {f g : ℝ → ℝ} {a b K : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hK : 0 ≤ K)
    (hg : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b,
      dist (g (f x)) (g (f y)) ≤ K * dist (f x) (f y)) :
    AbsolutelyContinuousOnInterval (fun x => g (f x)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hf (ε / (K + 1)) (by positivity)
  refine ⟨δ, hδ, fun E hE hsmall => ?_⟩
  calc
    _ ≤ ∑ i ∈ Finset.range E.1, K * dist (f (E.2 i).1) (f (E.2 i).2) :=
      Finset.sum_le_sum (fun i hi => hg _ (hE.1 i hi).1 _ (hE.1 i hi).2)
    _ = K * ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) := (Finset.mul_sum _ _ _).symm
    _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left (hbound E hE hsmall).le hK
    _ < ε := by
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < K + 1)]
      nlinarith only [hε]

theorem ac_exp {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => Real.exp (f x)) a b := by
  obtain ⟨M, hM⟩ := hf.exists_bound
  apply ac_comp_of_dist_le hf (Real.exp_pos M).le
  intro x hx y hy
  have hfx : f x ≤ M := (le_abs_self _).trans (hM x hx)
  have hfy : f y ≤ M := (le_abs_self _).trans (hM y hy)
  have hb (z : ℝ) (hz : z ∈ Iic M) : ‖Real.exp z‖ ≤ Real.exp M := by
    rw [Real.norm_of_nonneg (Real.exp_pos z).le]
    exact Real.exp_le_exp.mpr hz
  simpa only [Real.dist_eq, Real.norm_eq_abs] using
    (convex_Iic M).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z _ => (Real.hasDerivAt_exp z).hasDerivWithinAt) hb hfy hfx

theorem ac_le_of_ae_deriv_nonpos {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt f (f' t) t)
    (hbound : ∀ᵐ t, t ∈ uIcc a b → f' t ≤ 0) : f b ≤ f a := by
  have hb : (∫ t in a..b, deriv f t) ≤ 0 := by
    rw [intervalIntegral.integral_of_le hab]
    apply integral_nonpos_of_ae
    change ∀ᵐ t ∂volume.restrict (Ioc a b), deriv f t ≤ 0
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hd, hbound] with t ht hb htmem
    have hm : t ∈ uIcc a b := by simpa only [uIcc_of_le hab] using Ioc_subset_Icc_self htmem
    rw [(ht hm).deriv]
    exact hb hm
  rw [hf.integral_deriv_eq_sub] at hb
  exact sub_nonpos.mp hb

/-- Integrating-factor Grönwall with an integrable time coefficient and an
absolutely continuous unknown. -/
theorem le_mul_exp_integral_of_ac_deriv_le {f f' k : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hk : IntervalIntegrable k volume a b)
    (hd : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt f (f' t) t)
    (hbound : ∀ᵐ t, t ∈ uIcc a b → f' t ≤ k t * f t) :
    f b ≤ f a * Real.exp (∫ t in a..b, k t) := by
  let P := fun t => ∫ s in a..t, k s
  let E := fun t => Real.exp (-P t)
  have hP : AbsolutelyContinuousOnInterval P a b :=
    hk.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hE : AbsolutelyContinuousOnInterval E a b := ac_exp hP.fun_neg
  have hdE : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt E (-k t * E t) t := by
    filter_upwards [hk.ae_hasDerivAt_integral] with t ht hmem
    simpa only [E, P, Pi.neg_apply, mul_comm] using (ht hmem a (by simp)).neg.exp
  have hprod : ∀ᵐ t, t ∈ uIcc a b →
      HasDerivAt (fun t => f t * E t) ((f' t - k t * f t) * E t) t := by
    filter_upwards [hd, hdE] with t ht he hmem
    apply ((ht hmem).mul (he hmem)).congr_deriv
    ring
  have hnonpos : ∀ᵐ t, t ∈ uIcc a b → (f' t - k t * f t) * E t ≤ 0 := by
    filter_upwards [hbound] with t ht hmem
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (ht hmem)) (Real.exp_pos _).le
  have hb := ac_le_of_ae_deriv_nonpos hab (hf.fun_mul hE) hprod hnonpos
  simpa only [E, P, intervalIntegral.integral_same, neg_zero, Real.exp_zero, mul_one,
    Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _), div_one] using hb

/-- Nonpositive powers preserve absolute continuity when the argument is at least one. -/
theorem ac_rpow_of_one_le {f : ℝ → ℝ} {a b q : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hq : q ≤ 0)
    (hf₁ : ∀ t ∈ uIcc a b, 1 ≤ f t) :
    AbsolutelyContinuousOnInterval (fun t => f t ^ q) a b := by
  apply ac_comp_of_dist_le (g := fun x : ℝ => x ^ q) hf (abs_nonneg q)
  intro x hx y hy
  have hd (z : ℝ) (hz : z ∈ Ici (1 : ℝ)) :
      HasDerivWithinAt (fun z : ℝ => z ^ q) (q * z ^ (q - 1)) (Ici 1) z :=
    (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (zero_lt_one.trans_le hz)))).hasDerivWithinAt
  have hb (z : ℝ) (hz : z ∈ Ici (1 : ℝ)) : ‖q * z ^ (q - 1)‖ ≤ |q| := by
    rw [norm_mul, Real.norm_eq_abs q, Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hz) _)]
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos hz (by linarith only [hq])) (abs_nonneg q)).trans_eq (mul_one _)
  simpa only [Real.dist_eq, Real.norm_eq_abs] using
    (convex_Ici (1 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (hf₁ y hy) (hf₁ x hx)
end ClockBarrier.Analysis
