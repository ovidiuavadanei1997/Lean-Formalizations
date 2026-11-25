/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dyadic angular summation for the axis driver

These ordinary analytic lemmas control the angular weight in Section 6.
They do not assume or assert a Biot–Savart representation of an Euler solution.
-/

public section

namespace ClockBarrier.Analysis

/-- The angular kernel weight is nonnegative. -/
theorem axis_kernel_weight_nonneg {l α : ℝ} (hl : 0 ≤ l) :
    0 ≤ l ^ (α + 3) / (1 + l ^ 2) ^ 2 := by
  exact div_nonneg (Real.rpow_nonneg hl _) (sq_nonneg _)

/-- Dropping the angular denominator bounds the small-scale tail. -/
theorem axis_kernel_weight_le_rpow_add_three {l α : ℝ} (hl : 0 ≤ l) :
    l ^ (α + 3) / (1 + l ^ 2) ^ 2 ≤ l ^ (α + 3) := by
  exact div_le_self (Real.rpow_nonneg hl _) (by nlinarith [sq_nonneg l, sq_nonneg (l ^ 2)])

/-- The denominator supplies four powers for the large-scale tail. -/
theorem axis_kernel_weight_le_rpow_sub_one {l α : ℝ} (hl : 0 < l) :
    l ^ (α + 3) / (1 + l ^ 2) ^ 2 ≤ l ^ (α - 1) := by
  rw [div_le_iff₀ (by positivity : 0 < (1 + l ^ 2) ^ 2)]
  rw [show α + 3 = α - 1 + (4 : ℕ) by ring, Real.rpow_add hl, Real.rpow_natCast]
  exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg l]) (Real.rpow_nonneg hl.le _)

/-- The large dyadic angular scales are summable exactly below the upper exponent threshold. -/
theorem summable_axis_kernel_weight_nat {α : ℝ} (hα : α < 1) :
    Summable (fun n : ℕ => ((2 : ℝ) ^ n) ^ (α + 3) / (1 + ((2 : ℝ) ^ n) ^ 2) ^ 2) := by
  have hg := summable_geometric_of_lt_one
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (α - 1))
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) (sub_neg.mpr hα))
  exact hg.of_nonneg_of_le (fun n => axis_kernel_weight_nonneg (by positivity))
    (fun n => by simpa only [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)] using
      axis_kernel_weight_le_rpow_sub_one (α := α) (by positivity : (0 : ℝ) < 2 ^ n))

/-- Small dyadic angular scales are summable when the numerator exponent is positive. -/
theorem summable_axis_kernel_weight_inv_pow {α : ℝ} (hα : -3 < α) :
    Summable (fun n : ℕ => ((2 : ℝ)⁻¹ ^ n) ^ (α + 3) /
      (1 + ((2 : ℝ)⁻¹ ^ n) ^ 2) ^ 2) := by
  have hg := summable_geometric_of_lt_one
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) (α + 3))
    (Real.rpow_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1) (by linarith : 0 < α + 3))
  exact hg.of_nonneg_of_le (fun n => axis_kernel_weight_nonneg (by positivity))
    (fun n => by simpa only [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2⁻¹)] using
      axis_kernel_weight_le_rpow_add_three (α := α) (by positivity : (0 : ℝ) ≤ 2⁻¹ ^ n))

/-- The full angular dyadic series converges for the entire range used by the axis argument. -/
theorem summable_axis_kernel_weight {α : ℝ} (hα₀ : -3 < α) (hα₁ : α < 1) :
    Summable (fun k : ℤ => ((2 : ℝ) ^ k) ^ (α + 3) /
      (1 + ((2 : ℝ) ^ k) ^ 2) ^ 2) := by
  apply Summable.of_nat_of_neg_add_one
  · simpa only [zpow_natCast] using summable_axis_kernel_weight_nat hα₁
  · simpa only [Function.comp_def, Nat.succ_eq_add_one, ← Int.natCast_one,
      ← Int.natCast_add, zpow_neg, zpow_natCast, inv_pow] using
      (summable_axis_kernel_weight_inv_pow hα₀).comp_injective Nat.succ_injective

/-- An angular dyadic majorant and a summable axial tail give absolute summability. -/
theorem summable_norm_of_axis_kernel_bound {α A : ℝ} {b : ℤ → ℝ} {F : ℤ × ℤ → ℝ}
    (hα₀ : -3 < α) (hα₁ : α < 1) (hb : Summable b) (hb₀ : ∀ n, 0 ≤ b n)
    (hF : ∀ p : ℤ × ℤ, ‖F p‖ ≤ A *
      ((((2 : ℝ) ^ p.1) ^ (α + 3) / (1 + ((2 : ℝ) ^ p.1) ^ 2) ^ 2) * b p.2)) :
    Summable (fun p => ‖F p‖) := by
  exact ((summable_axis_kernel_weight hα₀ hα₁).mul_of_nonneg hb
    (fun k => axis_kernel_weight_nonneg (le_of_lt (zpow_pos (by norm_num) k))) hb₀).mul_left A
    |>.of_nonneg_of_le (fun p => norm_nonneg (F p)) hF

/-- Sum the block contributions without losing the separation of angular and axial scales. -/
theorem norm_tsum_le_of_axis_kernel_bound {α A : ℝ} {b : ℤ → ℝ} {F : ℤ × ℤ → ℝ}
    (hα₀ : -3 < α) (hα₁ : α < 1) (hb : Summable b) (hb₀ : ∀ n, 0 ≤ b n)
    (hF : ∀ p : ℤ × ℤ, ‖F p‖ ≤ A *
      ((((2 : ℝ) ^ p.1) ^ (α + 3) / (1 + ((2 : ℝ) ^ p.1) ^ 2) ^ 2) * b p.2)) :
    ‖∑' p, F p‖ ≤ A *
      (∑' k : ℤ, ((2 : ℝ) ^ k) ^ (α + 3) / (1 + ((2 : ℝ) ^ k) ^ 2) ^ 2) * ∑' n, b n := by
  have hw := summable_axis_kernel_weight hα₀ hα₁
  have hp := hw.mul_of_nonneg hb
    (fun k => axis_kernel_weight_nonneg (le_of_lt (zpow_pos (by norm_num) k))) hb₀
  calc
    ‖∑' p, F p‖ ≤ ∑' p, ‖F p‖ :=
      norm_tsum_le_tsum_norm (summable_norm_of_axis_kernel_bound hα₀ hα₁ hb hb₀ hF)
    _ ≤ ∑' p : ℤ × ℤ, A *
        ((((2 : ℝ) ^ p.1) ^ (α + 3) / (1 + ((2 : ℝ) ^ p.1) ^ 2) ^ 2) * b p.2) :=
      (summable_norm_of_axis_kernel_bound hα₀ hα₁ hb hb₀ hF).tsum_le_tsum hF (hp.mul_left A)
    _ = _ := by rw [hp.tsum_mul_left, ← hw.tsum_mul_tsum hb hp, mul_assoc]

/-- A nonnegative tail envelope with bounded finite subsums is genuinely summable. -/
theorem summable_axial_tail_of_finset_sum_le {α B : ℝ} {b : ℤ → ℝ}
    (hb : ∀ n, 0 ≤ b n)
    (hB : ∀ s : Finset ℤ, ∑ n ∈ s, ((2 : ℝ) ^ n) ^ α * b n ≤ B) :
    Summable (fun n : ℤ => ((2 : ℝ) ^ n) ^ α * b n) ∧
      (∑' n : ℤ, ((2 : ℝ) ^ n) ^ α * b n) ≤ B := by
  have hn (n : ℤ) : 0 ≤ ((2 : ℝ) ^ n) ^ α * b n :=
    mul_nonneg (Real.rpow_nonneg (le_of_lt (zpow_pos (by norm_num) n)) α) (hb n)
  exact ⟨summable_of_sum_le hn hB, Real.tsum_le_of_sum_le hn hB⟩

/-- A tail assumption only below the clock radius controls the envelope truncated
to those scales; no condition on the untruncated large-scale tail is needed. -/
theorem axial_tail_indicator_finset_sum_le {α ℓ B : ℝ} {b : ℤ → ℝ}
    (hB : ∀ q : Finset ℤ, (∀ n ∈ q, (2 : ℝ) ^ n ≤ ℓ) →
      ∑ n ∈ q, ((2 : ℝ) ^ n) ^ α * b n ≤ B) (q : Finset ℤ) :
    ∑ n ∈ q, ((2 : ℝ) ^ n) ^ α * (if (2 : ℝ) ^ n ≤ ℓ then b n else 0) ≤ B := by
  classical
  have h := hB (q.filter (fun n => (2 : ℝ) ^ n ≤ ℓ))
    (fun n hn => (Finset.mem_filter.mp hn).2)
  simpa only [Finset.sum_filter, mul_ite, mul_zero] using h

end ClockBarrier.Analysis
