/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.CoherenceIntegral
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Summable real envelopes from finite coherence series -/

public section
namespace ClockBarrier.Analysis
open scoped ENNReal

/-- A nonnegative real series inherits finiteness and its bound from the extended series. -/
theorem summable_and_tsum_le_of_ofReal_budget {I : Type*} {f : I → ℝ} {B : ℝ}
    (hf : ∀ i, 0 ≤ f i) (hB : 0 ≤ B)
    (hbudget : (∑' i, ENNReal.ofReal (f i)) ≤ ENNReal.ofReal B) :
    Summable f ∧ (∑' i, f i) ≤ B := by
  have hs : Summable f := by
    simpa only [ENNReal.toReal_ofReal (hf _)] using
      ENNReal.summable_toReal (hbudget.trans_lt ENNReal.ofReal_lt_top).ne
  refine ⟨hs, ?_⟩
  rw [← ENNReal.ofReal_tsum_of_nonneg hf hs] at hbudget
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hbudget

/-- Only the axial scales allowed by the tail cutoff enter the real envelope. -/
theorem summable_truncated_axial_tail_of_budget {α ℓ B : ℝ} {b : ℤ → ℝ}
    (hb : ∀ n, 0 ≤ b n) (hB : 0 ≤ B)
    (hbudget : (∑' n : ℤ, if (2 : ℝ) ^ n ≤ ℓ then
      ENNReal.ofReal (b n * ((2 : ℝ) ^ n) ^ α) else 0) ≤ ENNReal.ofReal B) :
    Summable (fun n : ℤ => if (2 : ℝ) ^ n ≤ ℓ then b n * ((2 : ℝ) ^ n) ^ α else 0) ∧
      (∑' n : ℤ, if (2 : ℝ) ^ n ≤ ℓ then b n * ((2 : ℝ) ^ n) ^ α else 0) ≤ B := by
  refine summable_and_tsum_le_of_ofReal_budget ?_ hB ?_
  · intro n
    split_ifs
    · exact mul_nonneg (hb n) (Real.rpow_nonneg (zpow_nonneg (by norm_num) n) _)
    · exact le_rfl
  · simpa only [apply_ite, ENNReal.ofReal_zero] using hbudget

end ClockBarrier.Analysis
