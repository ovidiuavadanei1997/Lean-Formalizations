/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.GeneralAngularTail
import Mathlib.Tactic.FinCases

/-! # Angular and axial summation on the literal three-index clock carrier -/

public section
namespace ClockBarrier.Analysis

/-- The exact `Fin 3 → ℤ` block indices inherit the shared bound and its separate
cone/off-cone restrictions, without changing the axial tail index. -/
theorem summable_general_clock_subseries {α A B : ℝ}
    (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hA : 0 ≤ A)
    {b : ℤ → ℝ} (hb : Summable b) (hb₀ : ∀ n, 0 ≤ b n) (hbB : (∑' n, b n) ≤ B)
    {f : (Fin 3 → ℤ) → ℝ} (hf₀ : ∀ k, 0 ≤ f k) :
    let w := fun k : ℤ × ℤ =>
      (Real.sqrt (((2 : ℝ) ^ k.1) ^ 2 + ((2 : ℝ) ^ k.2) ^ 2)) ^ α *
        (2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2 /
      (Real.sqrt (1 + ((2 : ℝ) ^ k.1) ^ 2 + ((2 : ℝ) ^ k.2) ^ 2)) ^ 3
    (∀ k, f k ≤ A * (w (k 0, k 1) * b (k 2))) →
    Summable f ∧ (∑' k, f k) ≤ A * (∑' k, w k) * B ∧ ∀ S : Set (ℤ × ℤ),
      Summable (fun k : {k : Fin 3 → ℤ // (k 0, k 1) ∈ S} => f k.val) ∧
      (∑' k : {k : Fin 3 → ℤ // (k 0, k 1) ∈ S}, f k.val) ≤ A * (∑' k, w k) * B := by
  intro w hbound
  let e : ((ℤ × ℤ) × ℤ) ≃ (Fin 3 → ℤ) :=
    { toFun := fun p => ![p.1.1, p.1.2, p.2]
      invFun := fun k => ((k 0, k 1), k 2)
      left_inv := fun p => rfl
      right_inv := fun k => by funext i; fin_cases i <;> rfl }
  obtain ⟨hs, ht, _⟩ := summable_general_angular_tail_subseries hα₀ hα₁ hA hb hb₀ hbB
    (fun p => hf₀ (e p)) (fun p => hbound (e p))
  have hf : Summable f := e.summable_iff.mp hs
  have htotal : (∑' k, f k) ≤ A * (∑' k, w k) * B := by
    simpa only [e.tsum_eq] using ht
  refine ⟨hf, htotal, fun S => ⟨hf.subtype (fun k => (k 0, k 1) ∈ S), ?_⟩⟩
  exact (tsum_comp_le_tsum_of_inj hf hf₀ Subtype.coe_injective).trans htotal

end ClockBarrier.Analysis
