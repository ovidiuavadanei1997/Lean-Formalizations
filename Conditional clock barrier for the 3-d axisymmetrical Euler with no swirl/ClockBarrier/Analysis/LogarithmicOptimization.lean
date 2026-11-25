/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-! # Scalar optimization of a Hölder small-scale remainder -/

public section
namespace ClockBarrier.Analysis

/-- A positive Hölder exponent gives a cutoff with a bounded small-scale
remainder and an exactly logarithmic annular cost. -/
theorem exists_holder_logarithmic_cutoff {α H : ℝ} (hα : 0 < α) (hH : 0 ≤ H) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      -Real.log ε = α⁻¹ * Real.log (Real.exp 1 + H) ∧ H * ε ^ α ≤ 1 := by
  refine ⟨Real.exp (-(α⁻¹ * Real.log (Real.exp 1 + H))), Real.exp_pos _, ?_, ?_, ?_⟩
  · exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos
      (mul_pos (inv_pos.mpr hα) (Real.log_pos
        ((Real.one_lt_exp_iff.mpr zero_lt_one).trans_le (le_add_of_nonneg_right hH)))))
  · simp only [Real.log_exp, neg_neg]
  · rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    rw [neg_mul, mul_assoc, mul_comm (Real.log (Real.exp 1 + H)) α,
      ← mul_assoc, inv_mul_cancel₀ hα.ne', one_mul]
    rw [Real.exp_neg, Real.exp_log (add_pos_of_pos_of_nonneg (Real.exp_pos _) hH),
      ← div_eq_mul_inv]
    exact (div_le_one (add_pos_of_pos_of_nonneg (Real.exp_pos _) hH)).mpr
      (le_add_of_nonneg_left (Real.exp_pos 1).le)

/-- Optimize the actual small-scale and annular costs for any positive Hölder
exponent. The near-field coefficient may be zero. -/
theorem le_logarithmic_bound_of_holder_split {X c L W H α : ℝ}
    (hc : 0 ≤ c) (hW : 0 ≤ W) (hH : 0 ≤ H) (hα : 0 < α)
    (hbound : ∀ ε : ℝ, 0 < ε → ε < 1 →
      X ≤ c * (L + W * (1 - Real.log ε) + H * ε ^ α)) :
    X ≤ c * (1 + L + (1 + α⁻¹) * W * Real.log (Real.exp 1 + H)) := by
  obtain ⟨ε, hε₀, hε₁, hlog, hsmall⟩ := exists_holder_logarithmic_cutoff hα hH
  have h := hbound ε hε₀ hε₁
  rw [sub_eq_add_neg, hlog] at h
  have hl : 1 ≤ Real.log (Real.exp 1 + H) := by
    simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right hH)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hc)
  nlinarith only [hsmall, mul_nonneg hW (sub_nonneg.mpr hl)]

end ClockBarrier.Analysis
