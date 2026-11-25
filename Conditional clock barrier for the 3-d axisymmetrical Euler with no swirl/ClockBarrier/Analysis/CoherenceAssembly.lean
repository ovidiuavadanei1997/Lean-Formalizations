/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.CoherenceIntegral
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Combining nonnegative coherence budgets on countable covers -/

public section
namespace ClockBarrier.Analysis
open Set MeasureTheory
open scoped ENNReal

/-- Block-dependent majorants can be summed before integrating the signed kernel.
Overlaps are harmless because only an upper bound is asserted. -/
theorem lintegral_le_of_cover_add
    {X I : Type*} [MeasurableSpace X] [Countable I] {μ : Measure X}
    {E : I → Set X} {s : Set X} {f : X → ℝ≥0∞} {g h : I → X → ℝ≥0∞}
    (hcover : (⋃ i, E i) =ᵐ[μ] s) (hE : ∀ i, MeasurableSet (E i))
    (hg : ∀ i, Measurable (g i))
    (hpoint : ∀ i, ∀ x ∈ E i, f x ≤ g i x + h i x) :
    (∫⁻ x in s, f x ∂μ) ≤
      (∑' i, ∫⁻ x in E i, g i x ∂μ) + ∑' i, ∫⁻ x in E i, h i x ∂μ := by
  calc
    (∫⁻ x in s, f x ∂μ) = ∫⁻ x in ⋃ i, E i, f x ∂μ := by
      rw [Measure.restrict_congr_set hcover]
    _ ≤ ∑' i, ∫⁻ x in E i, f x ∂μ := lintegral_iUnion_le E f
    _ ≤ ∑' i, ((∫⁻ x in E i, g i x ∂μ) + ∫⁻ x in E i, h i x ∂μ) := by
      apply ENNReal.tsum_le_tsum
      intro i
      exact (setLIntegral_mono' (hE i) (hpoint i)).trans_eq
        (lintegral_add_left (hg i) (h i))
    _ = _ := ENNReal.tsum_add

end ClockBarrier.Analysis
