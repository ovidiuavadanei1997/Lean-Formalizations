/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.GeneralCuspScaling
public import ClockBarrier.Analysis.CoherenceIntegral
public import ClockBarrier.Analysis.AxisBlockIntegral

/-! # Integrating a transverse general clock block -/

public section
namespace ClockBarrier.Analysis
open Set MeasureTheory
open scoped ENNReal

/-- The geometric kernel bound and literal cusp mass give an integrable block
with the exact clock power and angular weight. -/
theorem integrableOn_general_cusp_block
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {s : Set X} {f g d : X → ℝ}
    {τ₁ τ₂ ν Λ c q l l₁ l₂ α M b : ℝ}
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) (hν : 0 < ν) (hΛ : 0 < Λ)
    (hc : 0 < c) (hq : 0 < q) (hl : 0 ≤ l) (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂)
    (hM : 0 ≤ M) (hb : 0 ≤ b) (hdet : τ₁ * τ₂ * ν = 1)
    (hs : MeasurableSet s) (hf : AEStronglyMeasurable f (μ.restrict s))
    (hg : AEStronglyMeasurable g (μ.restrict s)) (hg₀ : ∀ x, 0 ≤ g x)
    (hpoint : ∀ x ∈ s, |f x| ≤ τ₁ * g x / (d x) ^ 3)
    (hgeom : ∀ x ∈ s, c * ν * Λ * q ≤ d x)
    (hmass : (∫⁻ x in s, ENNReal.ofReal (g x) ∂μ) ≤ ENNReal.ofReal
      ((M * b) * (l * ν * Λ / τ₂) ^ α * (l₁ * l₂ * ν ^ 2 * Λ ^ 3 / (τ₁ * τ₂)))) :
    IntegrableOn f s μ ∧ (∫ x in s, |f x| ∂μ) ≤
      (M * b / c ^ 3) * Λ ^ α * ν ^ ((3 * α - 1) / 2) *
        (τ₁ / τ₂) ^ ((α + 1) / 2) * (l ^ α * l₁ * l₂ / q ^ 3) := by
  obtain ⟨hgi, hgb⟩ := integrable_and_integral_le_of_lintegral_bound hg
    (Filter.Eventually.of_forall hg₀) (by positivity) hmass
  have hp (x : X) (hx : x ∈ s) : |f x| ≤ (τ₁ / (c * ν * Λ * q) ^ 3) * g x := by
    refine (hpoint x hx).trans ?_
    calc
      τ₁ * g x / (d x) ^ 3 ≤ τ₁ * g x / (c * ν * Λ * q) ^ 3 :=
        div_le_div_of_nonneg_left (mul_nonneg hτ₁.le (hg₀ x)) (by positivity)
          (pow_le_pow_left₀ (by positivity) (hgeom x hx) 3)
      _ = _ := by ring
  obtain ⟨hi, hiB⟩ := integrableOn_and_integral_abs_le_of_mass_bound hs
    (by positivity) hf hgi hp hgb
  exact ⟨hi, hiB.trans_eq (general_kernel_cusp_scaling hτ₁ hτ₂ hν hΛ hc hq hl hdet)⟩

end ClockBarrier.Analysis
