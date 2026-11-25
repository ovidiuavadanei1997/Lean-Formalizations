/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.WeightedDecomposition

/-! # Weighted near integrals controlled by a partitioned majorant -/

public section

namespace ClockBarrier.Analysis

open Set MeasureTheory

/-- A cutoff between zero and one preserves the sum of two bounds on a
nonnegative majorant, with no loss in the constants. -/
theorem abs_integral_cutoff_mul_le_add_of_majorant
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {s a : Set X}
    {f g χ : X → ℝ} {C B : ℝ}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ) (ha : MeasurableSet a)
    (hχ : AEStronglyMeasurable χ (μ.restrict s))
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (hfg : ∀ x, |f x| ≤ g x)
    (hc : (∫ x in s ∩ a, g x ∂μ) ≤ C) (hb : (∫ x in s \ a, g x ∂μ) ≤ B) :
    |∫ x in s, χ x * f x ∂μ| ≤ C + B := by
  refine (abs_integral_cutoff_mul_le_integral_abs hf hχ hχ₀ hχ₁).trans ?_
  refine (integral_mono hf.abs hg hfg).trans ?_
  rw [← integral_inter_add_sdiff ha hg]
  exact add_le_add hc hb

end ClockBarrier.Analysis
