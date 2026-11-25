/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.SingularFrame
public import ClockBarrier.Analysis.DyadicShell
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity

/-! # Coverage and uniqueness of the general half-open dyadic shells -/

public section
namespace ClockBarrier.Geometry
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Every label off the three singular coordinate planes has a unique shell. -/
theorem existsUnique_singular_shell {σ : Fin 3 → ℝ} (hσ : ∀ i, 0 < σ i)
    {η : E₃} (hη : ∀ i, η i ≠ 0) :
    ∃! k : Fin 3 → ℤ,
      (2 : ℝ) ^ (k 2) ≤ |η 2| ∧ |η 2| < 2 * (2 : ℝ) ^ (k 2) ∧
      (2 : ℝ) ^ (k 0) * σ 2 * (2 : ℝ) ^ (k 2) / σ 0 ≤ |η 0| ∧
      |η 0| < 2 * ((2 : ℝ) ^ (k 0) * σ 2 * (2 : ℝ) ^ (k 2) / σ 0) ∧
      (2 : ℝ) ^ (k 1) * σ 2 * (2 : ℝ) ^ (k 2) / σ 1 ≤ |η 1| ∧
      |η 1| < 2 * ((2 : ℝ) ^ (k 1) * σ 2 * (2 : ℝ) ^ (k 2) / σ 1) := by
  obtain ⟨n, hn, hnu⟩ := Analysis.existsUnique_dyadic_shell (by norm_num : (0 : ℝ) < 1)
    (abs_pos.mpr (hη 2))
  obtain ⟨i, hi, hiu⟩ := Analysis.existsUnique_dyadic_shell
    (div_pos (mul_pos (hσ 2) (zpow_pos (by norm_num : (0 : ℝ) < 2) n)) (hσ 0))
    (abs_pos.mpr (hη 0))
  obtain ⟨j, hj, hju⟩ := Analysis.existsUnique_dyadic_shell
    (div_pos (mul_pos (hσ 2) (zpow_pos (by norm_num : (0 : ℝ) < 2) n)) (hσ 1))
    (abs_pos.mpr (hη 1))
  refine ⟨![i, j, n], ?_, ?_⟩
  · simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      mul_one, mul_div_assoc, mul_assoc] using
      And.intro hn.1 (And.intro hn.2 (And.intro hi.1 (And.intro hi.2 hj)))
  · intro k hk
    have hk₂ : k 2 = n := hnu (k 2) (by simpa only [mul_one] using And.intro hk.1 hk.2.1)
    rw [hk₂] at hk
    have hk₀ : k 0 = i := hiu (k 0) (by
      simpa only [mul_div_assoc, mul_assoc] using And.intro hk.2.2.1 hk.2.2.2.1)
    have hk₁ : k 1 = j := hju (k 1) (by
      simpa only [mul_div_assoc, mul_assoc] using hk.2.2.2.2)
    funext q
    fin_cases q
    · exact hk₀
    · exact hk₁
    · exact hk₂

end ClockBarrier.Geometry
