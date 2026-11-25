/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Real integral bounds from the finite extended-integral coherence budgets -/

public section
namespace ClockBarrier.Analysis
open Set MeasureTheory
open scoped ENNReal

/-- A finite extended-integral budget gives genuine integrability and a real bound. -/
theorem integrable_and_integral_le_of_lintegral_bound
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ} {B : ℝ}
    (hf : AEStronglyMeasurable f μ) (hf₀ : 0 ≤ᵐ[μ] f) (hB : 0 ≤ B)
    (hbudget : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal B) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ B := by
  have hi : Integrable f μ := ⟨hf,
    (hasFiniteIntegral_iff_ofReal hf₀).mpr (hbudget.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi hf₀] at hbudget
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hbudget

/-- A summed coherence budget controls the full region covered by the blocks almost everywhere. -/
theorem integrableOn_and_integral_le_of_cover_budget
    {X I : Type*} [MeasurableSpace X] [Countable I] {μ : Measure X}
    {E : I → Set X} {s : Set X} {f : X → ℝ} {B : ℝ}
    (hcover : (⋃ i, E i) =ᵐ[μ] s) (hf : AEStronglyMeasurable f (μ.restrict s))
    (hf₀ : 0 ≤ᵐ[μ.restrict s] f) (hB : 0 ≤ B)
    (hbudget : (∑' i, ∫⁻ x in E i, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal B) :
    IntegrableOn f s μ ∧ (∫ x in s, f x ∂μ) ≤ B := by
  apply integrable_and_integral_le_of_lintegral_bound hf hf₀ hB
  calc
    (∫⁻ x in s, ENNReal.ofReal (f x) ∂μ) =
        ∫⁻ x in ⋃ i, E i, ENNReal.ofReal (f x) ∂μ := by
      rw [Measure.restrict_congr_set hcover]
    _ ≤ ∑' i, ∫⁻ x in E i, ENNReal.ofReal (f x) ∂μ := lintegral_iUnion_le E _
    _ ≤ ENNReal.ofReal B := hbudget

end ClockBarrier.Analysis
