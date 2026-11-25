/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.LinearComparison
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # The auxiliary nonlinear clock ODE and its negative-power linearization -/

public section
namespace ClockBarrier.Analysis
open Set MeasureTheory Filter
open scoped Topology
theorem negative_power_derivative_bound
    {x v B C p : ℝ} (hx : 0 < x) (hp : 1 < p)
    (hv : -B * x - C * x ^ p ≤ v) :
    v * (1 - p) * x ^ ((1 - p) - 1) ≤
      (p - 1) * (B * x ^ (1 - p) + C) := by
  have hmul := mul_le_mul_of_nonpos_right hv
    (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hp.le)
      (Real.rpow_pos_of_pos hx ((1 - p) - 1)).le)
  have hpow : x ^ p * x ^ ((1 - p) - 1) = 1 := by
    rw [← Real.rpow_add hx, show p + ((1 - p) - 1) = 0 by ring, Real.rpow_zero]
  have hxpow : x * x ^ ((1 - p) - 1) = x ^ (1 - p) := by
    simpa only [Real.rpow_one, show 1 + ((1 - p) - 1) = 1 - p by ring] using
      (Real.rpow_add hx 1 ((1 - p) - 1)).symm
  calc
    _ = v * ((1 - p) * x ^ ((1 - p) - 1)) := by ring
    _ ≤ (-B * x - C * x ^ p) * ((1 - p) * x ^ ((1 - p) - 1)) := hmul
    _ = (p - 1) * (B * (x * x ^ ((1 - p) - 1)) +
        C * (x ^ p * x ^ ((1 - p) - 1))) := by ring
    _ = _ := by rw [hxpow, hpow, mul_one]


/-- Inverting the linear equality solution gives precisely the nonlinear ODE. -/
theorem inverse_power_linear_derivative {x B C p : ℝ} (hx : 0 < x) (hp : 1 < p) :
    ((p - 1) * B * x + (p - 1) * C) * (1 / (1 - p)) * x ^ (1 / (1 - p) - 1) =
      -B * x ^ (1 / (1 - p)) - C * (x ^ (1 / (1 - p))) ^ p := by
  have hpne : 1 - p ≠ 0 := (sub_neg.mpr hp).ne
  have hcoeff : ((p - 1) * B * x + (p - 1) * C) * (1 / (1 - p)) = -(B * x + C) := by
    field_simp
    ring
  have hpow : (x ^ (1 / (1 - p))) ^ p = x ^ (1 / (1 - p) - 1) := by
    rw [← Real.rpow_mul hx.le]
    congr 1
    field_simp
    ring
  have hxpow : x * x ^ (1 / (1 - p) - 1) = x ^ (1 / (1 - p)) := by
    simpa only [Real.rpow_one, show 1 + (1 / (1 - p) - 1) = 1 / (1 - p) by ring] using
      (Real.rpow_add hx 1 (1 / (1 - p) - 1)).symm
  rw [hcoeff, hpow]
  nlinarith only [congrArg (B * ·) hxpow]

/-- The paper's positive auxiliary equality solution, built through its linear
negative-power transform. Its ODE holds a.e., as required for an L¹ coefficient. -/
theorem exists_positive_power_comparison
    {J J' B : ℝ → ℝ} {a b C p : ℝ} (hab : a ≤ b) (hC : 0 ≤ C) (hp : 1 < p)
    (hcont : ContinuousOn J (Icc a b)) (ha : J a = 1)
    (hpos : ∀ t ∈ Icc a b, 0 < J t)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivWithinAt J (J' t) (Ioi t) t)
    (hB : IntegrableOn B (Icc a b)) (hB₀ : ∀ t ∈ Icc a b, 0 ≤ B t)
    (hbound : ∀ t ∈ Ioo a b, -B t * J t - C * J t ^ p ≤ J' t) :
    ∃ f : ℝ → ℝ, AbsolutelyContinuousOnInterval f a b ∧ f a = 1 ∧
      (∀ t ∈ Icc a b, 0 < f t ∧ f t ≤ 1) ∧
      (∀ᵐ t, t ∈ uIcc a b → HasDerivAt f (-B t * f t - C * f t ^ p) t) ∧
      Real.exp (-(∫ t in a..b, B t + C)) ≤ f b ∧ f b ≤ J b := by
  let k := fun t => (p - 1) * B t
  let c := (p - 1) * C
  let H := fun t => J t ^ (1 - p)
  have hk : IntegrableOn k (Icc a b) := hB.const_mul (p - 1)
  have hk₀ : ∀ t ∈ Icc a b, 0 ≤ k t := fun t ht => mul_nonneg (sub_pos.mpr hp).le (hB₀ t ht)
  obtain ⟨G, hG, hGa, hG₁, hdG, hGbound⟩ := exists_ac_linear_comparison hab
    (mul_nonneg (sub_pos.mpr hp).le hC) hk hk₀
  let q := 1 / (1 - p)
  let f := fun t => G t ^ q
  have hq : q < 0 := one_div_neg.mpr (sub_neg.mpr hp)
  have hGpos (t : ℝ) (ht : t ∈ Icc a b) : 0 < G t := zero_lt_one.trans_le (hG₁ t ht)
  have hf : AbsolutelyContinuousOnInterval f a b := ac_rpow_of_one_le hG hq.le
    (fun t ht => hG₁ t (by simpa only [uIcc_of_le hab] using ht))
  have hfpos (t : ℝ) (ht : t ∈ Icc a b) : 0 < f t ∧ f t ≤ 1 :=
    ⟨Real.rpow_pos_of_pos (hGpos t ht) _, Real.rpow_le_one_of_one_le_of_nonpos (hG₁ t ht) hq.le⟩
  have hdf : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt f (-B t * f t - C * f t ^ p) t := by
    filter_upwards [hdG] with t ht hm
    have hmem : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using hm
    apply ((ht hm).rpow_const (p := q) (Or.inl (hGpos t hmem).ne')).congr_deriv
    exact inverse_power_linear_derivative (hGpos t hmem) hp
  have hHcont : ContinuousOn H (Icc a b) := hcont.rpow_const (fun t ht => Or.inl (hpos t ht).ne')
  have hHderiv : ∀ t ∈ Ioo a b, HasDerivWithinAt H
      (J' t * (1 - p) * J t ^ ((1 - p) - 1)) (Ioi t) t :=
    fun t ht => (hderiv t ht).rpow_const (Or.inl (hpos t (Ioo_subset_Icc_self ht)).ne')
  have hHbound (t : ℝ) (ht : t ∈ Ioo a b) :
      J' t * (1 - p) * J t ^ ((1 - p) - 1) ≤ k t * H t + c := by
    have hh := negative_power_derivative_bound (hpos t (Ioo_subset_Icc_self ht)) hp (hbound t ht)
    dsimp only [k, H, c]
    nlinarith only [hh]
  have hHG := le_linear_solution_of_right_deriv hab hHcont hHderiv hk hk₀ hHbound hG
    (by simpa only [H, ha, Real.one_rpow] using hGa) hdG
  have hfb : f b ≤ J b := by
    have hb := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos (hpos b (right_mem_Icc.mpr hab)) _)
      hHG hq.le
    have hHpow : H b ^ q = J b := by
      dsimp only [H]
      rw [← Real.rpow_mul (hpos b (right_mem_Icc.mpr hab)).le]
      have hpq : (1 - p) * q = 1 := mul_one_div_cancel (sub_neg.mpr hp).ne
      rw [hpq, Real.rpow_one]
    exact hb.trans_eq hHpow
  have hint : (∫ t in a..b, k t + c) = (p - 1) * ∫ t in a..b, B t + C := by
    simp only [k, c, ← mul_add, intervalIntegral.integral_const_mul]
  have hlower : Real.exp (-(∫ t in a..b, B t + C)) ≤ f b := by
    have hb := Real.rpow_le_rpow_of_nonpos (hGpos b (right_mem_Icc.mpr hab)) hGbound hq.le
    rw [← Real.exp_mul, hint] at hb
    have hscale : (p - 1) * (∫ t in a..b, B t + C) * q = -(∫ t in a..b, B t + C) := by
      have hpne : 1 - p ≠ 0 := (sub_neg.mpr hp).ne
      have hpq : (p - 1) * q = -1 := by
        dsimp only [q]
        field_simp
        ring
      calc
        _ = ((p - 1) * q) * (∫ t in a..b, B t + C) := by ring
        _ = _ := by rw [hpq, neg_one_mul]
    rwa [hscale] at hb
  exact ⟨f, hf, by simp only [f, hGa, Real.one_rpow], hfpos, hdf, hlower, hfb⟩
end ClockBarrier.Analysis
