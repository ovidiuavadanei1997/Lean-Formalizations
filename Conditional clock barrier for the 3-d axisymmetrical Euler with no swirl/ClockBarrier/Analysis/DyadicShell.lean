/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Positive half-open dyadic shells -/

public section
namespace ClockBarrier.Analysis
open Set

/-- Positive half-open dyadic shells have unique integer indices. -/
theorem dyadic_shell_index_eq {c x : ℝ} (hc : 0 < c) {m n : ℤ}
    (hm : (2 : ℝ) ^ m * c ≤ x ∧ x < 2 * ((2 : ℝ) ^ m * c))
    (hn : (2 : ℝ) ^ n * c ≤ x ∧ x < 2 * ((2 : ℝ) ^ n * c)) : m = n := by
  have hle {j k : ℤ}
      (hj : (2 : ℝ) ^ j * c ≤ x ∧ x < 2 * ((2 : ℝ) ^ j * c))
      (hk : (2 : ℝ) ^ k * c ≤ x ∧ x < 2 * ((2 : ℝ) ^ k * c)) : j ≤ k := by
    by_contra h
    have hg : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ j :=
      zpow_le_zpow_right₀ (by norm_num) (Int.add_one_le_iff.mpr (lt_of_not_ge h))
    have hx : 2 * ((2 : ℝ) ^ k * c) ≤ x := by
      calc
        2 * ((2 : ℝ) ^ k * c) = (2 : ℝ) ^ (k + 1) * c := by
          rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
          ring
        _ ≤ (2 : ℝ) ^ j * c := mul_le_mul_of_nonneg_right hg hc.le
        _ ≤ x := hj.1
    exact (not_lt_of_ge hx) hk.2
  exact le_antisymm (hle hm hn) (hle hn hm)

/-- Every positive real lies in exactly one positive scaled dyadic shell. -/
theorem existsUnique_dyadic_shell {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    ∃! n : ℤ, (2 : ℝ) ^ n * c ≤ x ∧ x < 2 * ((2 : ℝ) ^ n * c) := by
  obtain ⟨n, hn⟩ := exists_mem_Ico_zpow (div_pos hx hc) (by norm_num : (1 : ℝ) < 2)
  have hl : (2 : ℝ) ^ n * c ≤ x := (le_div_iff₀ hc).mp hn.1
  have hu : x < 2 * ((2 : ℝ) ^ n * c) := by
    have h := (div_lt_iff₀ hc).mp hn.2
    rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)] at h
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  exact ⟨n, ⟨hl, hu⟩, fun m hm => dyadic_shell_index_eq hc hm ⟨hl, hu⟩⟩

end ClockBarrier.Analysis
