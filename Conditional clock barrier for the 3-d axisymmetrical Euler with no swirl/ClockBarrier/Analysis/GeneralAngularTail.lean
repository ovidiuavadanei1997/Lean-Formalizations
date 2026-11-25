/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.GeneralAngularSummation
public import ClockBarrier.Analysis.CoherenceSeries

/-! # Separate angular subseries with a shared axial tail bound -/

public section
namespace ClockBarrier.Analysis

/-- The angular and axial envelopes control every angular subregion separately.
Taking a cone and its complement preserves the two branches of the source proof. -/
theorem summable_general_angular_tail_subseries {α A B : ℝ}
    (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hA : 0 ≤ A)
    {b : ℤ → ℝ} (hb : Summable b) (hb₀ : ∀ n, 0 ≤ b n) (hbB : (∑' n, b n) ≤ B)
    {f : (ℤ × ℤ) × ℤ → ℝ} (hf₀ : ∀ p, 0 ≤ f p) :
    let w := fun k : ℤ × ℤ =>
      (Real.sqrt (((2 : ℝ) ^ k.1) ^ 2 + ((2 : ℝ) ^ k.2) ^ 2)) ^ α *
        (2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2 /
      (Real.sqrt (1 + ((2 : ℝ) ^ k.1) ^ 2 + ((2 : ℝ) ^ k.2) ^ 2)) ^ 3
    (∀ p, f p ≤ A * (w p.1 * b p.2)) →
    Summable f ∧ (∑' p, f p) ≤ A * (∑' k, w k) * B ∧ ∀ S : Set (ℤ × ℤ),
      Summable (fun p : {p : (ℤ × ℤ) × ℤ // p.1 ∈ S} => f p.val) ∧
      (∑' p : {p : (ℤ × ℤ) × ℤ // p.1 ∈ S}, f p.val) ≤ A * (∑' k, w k) * B := by
  intro w hbound
  have hw : Summable w := summable_general_angular_weight hα₀ hα₁
  have hw₀ (k : ℤ × ℤ) : 0 ≤ w k := by dsimp only [w]; positivity
  have hp := hw.mul_of_nonneg hb hw₀ hb₀
  have hm := hp.mul_left A
  have hf : Summable f := hm.of_nonneg_of_le hf₀ hbound
  have htotal : (∑' p, f p) ≤ A * (∑' k, w k) * B := by
    refine (hf.tsum_le_tsum hbound hm).trans ?_
    rw [hp.tsum_mul_left, ← hw.tsum_mul_tsum hb hp, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hbB (mul_nonneg hA (tsum_nonneg hw₀))
  refine ⟨hf, htotal, fun S => ⟨hf.subtype (fun p => p.1 ∈ S), ?_⟩⟩
  exact (tsum_comp_le_tsum_of_inj hf hf₀ Subtype.coe_injective).trans htotal

end ClockBarrier.Analysis
