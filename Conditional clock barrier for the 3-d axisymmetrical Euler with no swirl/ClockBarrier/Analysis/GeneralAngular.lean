/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.DyadicDriver
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! # Weighted angular summation for the general clock blocks -/

public section
namespace ClockBarrier.Analysis

/-- On an ordered angular pair, the smaller coordinate retains its geometric weight. -/
theorem general_angular_weight_le_small {a b α : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) (hα : 0 ≤ α) :
    (Real.sqrt (a ^ 2 + b ^ 2)) ^ α * a * b /
      (Real.sqrt (1 + a ^ 2 + b ^ 2)) ^ 3 ≤ (2 : ℝ) ^ α * b ^ (α + 1) * a := by
  have hr : Real.sqrt (a ^ 2 + b ^ 2) ≤ 2 * b := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith only [sq_nonneg b, (sq_le_sq₀ ha.le hb.le).mpr hab]
  have hq : 1 ≤ Real.sqrt (1 + a ^ 2 + b ^ 2) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith only [sq_nonneg a, sq_nonneg b]
  calc
    _ ≤ (Real.sqrt (a ^ 2 + b ^ 2)) ^ α * a * b :=
      div_le_self (by positivity) (one_le_pow₀ hq)
    _ ≤ (2 * b) ^ α * a * b :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (Real.sqrt_nonneg _) hr hα) ha.le) hb.le
    _ = _ := by
      rw [Real.mul_rpow (by norm_num) hb.le, Real.rpow_add hb, Real.rpow_one]
      ring

/-- The large-angle denominator gives three powers of the larger coordinate. -/
theorem general_angular_weight_le_large {a b α : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) (hα : 0 ≤ α) :
    (Real.sqrt (a ^ 2 + b ^ 2)) ^ α * a * b /
      (Real.sqrt (1 + a ^ 2 + b ^ 2)) ^ 3 ≤ (2 : ℝ) ^ α * b ^ (α - 2) * a := by
  have hr : Real.sqrt (a ^ 2 + b ^ 2) ≤ 2 * b := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith only [sq_nonneg b, (sq_le_sq₀ ha.le hb.le).mpr hab]
  have hq : b ≤ Real.sqrt (1 + a ^ 2 + b ^ 2) := by
    apply (Real.le_sqrt hb.le (by positivity)).mpr
    nlinarith only [sq_nonneg a]
  calc
    _ ≤ (Real.sqrt (a ^ 2 + b ^ 2)) ^ α * a * b / b ^ 3 :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hb 3) (pow_le_pow_left₀ hb.le hq 3)
    _ ≤ (2 * b) ^ α * a * b / b ^ 3 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (Real.sqrt_nonneg _) hr hα) ha.le) hb.le) (pow_nonneg hb.le 3)
    _ = _ := by
      have hp : b ^ α = b ^ (α - 2) * b ^ 2 := by
        conv_lhs => rw [show α = (α - 2) + (2 : ℕ) by ring]
        rw [Real.rpow_add hb, Real.rpow_natCast]
      rw [Real.mul_rpow (by norm_num) hb.le, hp]
      field_simp

/-- The radial maximum scale has summable tails on both sides of the unit scale. -/
theorem summable_general_radial_weight {α : ℝ} (hα₀ : -2 < α) (hα₁ : α < 1) :
    Summable (fun k : ℤ => min (((2 : ℝ) ^ k) ^ (α + 2)) (((2 : ℝ) ^ k) ^ (α - 1))) := by
  apply Summable.of_nat_of_neg_add_one
  · have hg := summable_geometric_of_lt_one
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (α - 1))
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) (sub_neg.mpr hα₁))
    refine hg.of_nonneg_of_le (fun n => le_min (by positivity) (by positivity)) ?_
    intro n
    simpa only [zpow_natCast, Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)] using
      min_le_right (((2 : ℝ) ^ n) ^ (α + 2)) (((2 : ℝ) ^ n) ^ (α - 1))
  · have hg := summable_geometric_of_lt_one
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) (α + 2))
      (Real.rpow_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1) (by linarith : 0 < α + 2))
    have hs : Summable (fun n : ℕ => min (((2 : ℝ)⁻¹ ^ n) ^ (α + 2))
        (((2 : ℝ)⁻¹ ^ n) ^ (α - 1))) := hg.of_nonneg_of_le
      (fun n => le_min (by positivity) (by positivity)) (fun n => by
        simpa only [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2⁻¹)] using
          min_le_left (((2 : ℝ)⁻¹ ^ n) ^ (α + 2)) (((2 : ℝ)⁻¹ ^ n) ^ (α - 1)))
    simpa only [Function.comp_def, Nat.succ_eq_add_one, ← Int.natCast_one,
      ← Int.natCast_add, zpow_neg, zpow_natCast, inv_pow] using
      hs.comp_injective Nat.succ_injective

end ClockBarrier.Analysis
