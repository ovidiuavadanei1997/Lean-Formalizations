/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.DyadicDriver
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # The truncated dyadic Hölder tail at unit clock scale -/

public section
namespace ClockBarrier.Analysis
open scoped ENNReal

/-- The unit-scale truncated Hölder tail is summable for every positive exponent. -/
theorem summable_truncated_dyadic_holder {α : ℝ} (hα : 0 < α) :
    Summable (fun n : ℤ => if (2 : ℝ) ^ n ≤ 1 then ((2 : ℝ) ^ n) ^ α else 0) := by
  apply Summable.of_nat_of_neg_add_one
  · simp_rw [zpow_le_one_iff_right₀ (by norm_num : (1 : ℝ) < 2)]
    simpa +contextual using (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).summable
  · have hg := summable_geometric_of_lt_one
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) α)
      (Real.rpow_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1) hα)
    convert! hg.comp_injective Nat.succ_injective using 1
    ext n
    rw [if_pos ((zpow_le_one_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr
      (neg_nonpos.mpr (by positivity)))]
    simp only [Function.comp_apply, Nat.succ_eq_add_one, ← Int.natCast_one,
      ← Int.natCast_add, zpow_neg, zpow_natCast, ← inv_pow,
      Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2⁻¹)]

/-- The exact ENNReal clock tail is bounded by a positive real constant. -/
theorem exists_truncated_dyadic_holder_budget {α : ℝ} (hα : 0 < α) :
    ∃ B : ℝ, 0 < B ∧
      (∑' n : ℤ, if (2 : ℝ) ^ n ≤ 1 then ENNReal.ofReal (((2 : ℝ) ^ n) ^ α)
        else 0) ≤ ENNReal.ofReal B := by
  let f := fun n : ℤ => if (2 : ℝ) ^ n ≤ 1 then ((2 : ℝ) ^ n) ^ α else 0
  have hf : ∀ n, 0 ≤ f n := fun n => by dsimp [f]; split_ifs <;> positivity
  refine ⟨‖∑' n, f n‖ + 1, add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one, ?_⟩
  calc
    _ = ∑' n, ENNReal.ofReal (f n) := tsum_congr (fun n => by
      dsimp [f]
      split_ifs <;> simp only [ENNReal.ofReal_zero])
    _ = ENNReal.ofReal (∑' n, f n) :=
      (ENNReal.ofReal_tsum_of_nonneg hf (summable_truncated_dyadic_holder hα)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_one))

end ClockBarrier.Analysis
