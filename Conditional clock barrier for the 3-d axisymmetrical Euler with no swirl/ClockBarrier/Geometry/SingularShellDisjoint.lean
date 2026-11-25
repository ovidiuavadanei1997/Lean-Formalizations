/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.SingularShells
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity

/-! # Disjointness and measurability of the general half-open shells -/

public section
namespace ClockBarrier.Geometry
open Set Function
open scoped ENNReal
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Any subsets of the same half-open singular shells are pairwise disjoint. -/
theorem pairwise_disjoint_of_singular_shells {σ : Fin 3 → ℝ} (hσ : ∀ i, 0 < σ i)
    (aStar : E₃) (V : E₃ ≃ₗᵢ[ℝ] E₃) (S : (Fin 3 → ℤ) → Set E₃)
    (hS : ∀ k a, a ∈ S k →
      let η := V.symm (a - aStar)
      (2 : ℝ) ^ (k 2) ≤ |η 2| ∧ |η 2| < 2 * (2 : ℝ) ^ (k 2) ∧
      (2 : ℝ) ^ (k 0) * σ 2 * (2 : ℝ) ^ (k 2) / σ 0 ≤ |η 0| ∧
      |η 0| < 2 * ((2 : ℝ) ^ (k 0) * σ 2 * (2 : ℝ) ^ (k 2) / σ 0) ∧
      (2 : ℝ) ^ (k 1) * σ 2 * (2 : ℝ) ^ (k 2) / σ 1 ≤ |η 1| ∧
      |η 1| < 2 * ((2 : ℝ) ^ (k 1) * σ 2 * (2 : ℝ) ^ (k 2) / σ 1)) :
    Pairwise (Disjoint on S) := by
  intro k l hkl
  refine disjoint_left.mpr (fun a hak hal => ?_)
  have hk := hS k a hak
  have hn : ∀ i : Fin 3, V.symm (a - aStar) i ≠ 0 := by
    intro i
    fin_cases i
    · exact abs_pos.mp ((by have := hσ 0; have := hσ 2; positivity : 0 < (2 : ℝ) ^ (k 0) * σ 2 * (2 : ℝ) ^ (k 2) / σ 0).trans_le hk.2.2.1)
    · exact abs_pos.mp ((by have := hσ 1; have := hσ 2; positivity : 0 < (2 : ℝ) ^ (k 1) * σ 2 * (2 : ℝ) ^ (k 2) / σ 1).trans_le hk.2.2.2.2.1)
    · exact abs_pos.mp ((zpow_pos (by norm_num : (0 : ℝ) < 2) _).trans_le hk.1)
  obtain ⟨m, _, hm⟩ := existsUnique_singular_shell hσ hn
  exact hkl ((hm k hk).trans (hm l (hS l a hal)).symm)

/-- The literal half-open singular shell is Borel measurable, without clock cutoffs. -/
theorem measurableSet_singular_shell (aStar : E₃) (V : E₃ ≃ₗᵢ[ℝ] E₃)
    (σ : Fin 3 → ℝ) (k : Fin 3 → ℤ) :
    MeasurableSet {a : E₃ | let η := V.symm (a - aStar)
      (2 : ℝ) ^ (k 2) ≤ |η 2| ∧ |η 2| < 2 * (2 : ℝ) ^ (k 2) ∧
      (2 : ℝ) ^ (k 0) * σ 2 * (2 : ℝ) ^ (k 2) / σ 0 ≤ |η 0| ∧
      |η 0| < 2 * ((2 : ℝ) ^ (k 0) * σ 2 * (2 : ℝ) ^ (k 2) / σ 0) ∧
      (2 : ℝ) ^ (k 1) * σ 2 * (2 : ℝ) ^ (k 2) / σ 1 ≤ |η 1| ∧
      |η 1| < 2 * ((2 : ℝ) ^ (k 1) * σ 2 * (2 : ℝ) ^ (k 2) / σ 1)} := by
  have hη (i : Fin 3) : Continuous (fun a : E₃ => |V.symm (a - aStar) i|) := by fun_prop
  exact (isClosed_le continuous_const (hη 2)).measurableSet.inter
    ((isOpen_lt (hη 2) continuous_const).measurableSet.inter
      ((isClosed_le continuous_const (hη 0)).measurableSet.inter
        ((isOpen_lt (hη 0) continuous_const).measurableSet.inter
          ((isClosed_le continuous_const (hη 1)).measurableSet.inter
            (isOpen_lt (hη 1) continuous_const).measurableSet))))

end ClockBarrier.Geometry
