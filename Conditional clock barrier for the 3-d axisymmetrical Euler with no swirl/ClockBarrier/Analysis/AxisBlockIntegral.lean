/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.AxisKernel
public import ClockBarrier.Analysis.DyadicDriver
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Integrating and summing clock-local axis-driver blocks

The estimates derive integrability from the block majorants. Their hypotheses
remain ordinary analytic inputs; no Euler transport or kernel representation is assumed proved.
-/

public section

namespace ClockBarrier.Analysis

open Set MeasureTheory

/-- A measurable function dominated by an integrable mass has a controlled absolute integral. -/
theorem integrableOn_and_integral_abs_le_of_mass_bound
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {s : Set X}
    {f g : X → ℝ} {C M : ℝ} (hs : MeasurableSet s) (hC : 0 ≤ C)
    (hf : AEStronglyMeasurable f (μ.restrict s)) (hg : IntegrableOn g s μ)
    (hbound : ∀ x ∈ s, |f x| ≤ C * g x) (hmass : ∫ x in s, g x ∂μ ≤ M) :
    IntegrableOn f s μ ∧ (∫ x in s, |f x| ∂μ) ≤ C * M := by
  have hmajor : IntegrableOn (fun x => C * g x) s μ := hg.const_mul C
  have hfi : IntegrableOn f s μ := hmajor.mono' hf
    (ae_restrict_of_forall_mem hs (fun x hx => by simpa only [Real.norm_eq_abs] using hbound x hx))
  refine ⟨hfi, (integral_mono_ae hfi.abs hmajor (ae_restrict_of_forall_mem hs hbound)).trans ?_⟩
  simpa only [integral_const_mul] using mul_le_mul_of_nonneg_left hmass hC

/-- Integrate a kernel and transported-vorticity bound against the cusp mass of one block.
The resulting clock exponent is derived, and block integrability is a conclusion. -/
theorem integrableOn_axis_block_and_integral_abs_le
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {s : Set X} {k v : X → ℝ} {ω₀ : X → E}
    {l J Λ α CK CV M b : ℝ} (hs : MeasurableSet s)
    (hl : 0 < l) (hJ : 0 < J) (hΛ : 0 < Λ) (hCK : 0 ≤ CK) (hCV : 0 ≤ CV)
    (hf : AEStronglyMeasurable (fun a => k a * v a) (μ.restrict s))
    (hω : IntegrableOn ω₀ s μ)
    (hk : ∀ a ∈ s, |k a| ≤ CK * (l / (J ^ 6 * Λ ^ 3 * (1 + l ^ 2) ^ 2)))
    (hv : ∀ a ∈ s, |v a| ≤ CV * J⁻¹ * ‖ω₀ a‖)
    (hmass : (∫ a in s, ‖ω₀ a‖ ∂μ) ≤
      (M * b) * (l ^ (α + 2) * J ^ (3 * α + 6) * Λ ^ (α + 3))) :
    IntegrableOn (fun a => k a * v a) s μ ∧
      (∫ a in s, |k a * v a| ∂μ) ≤
        (CK * CV * M) * J ^ (3 * α - 1) *
          (l ^ (α + 3) / (1 + l ^ 2) ^ 2) * (Λ ^ α * b) := by
  have hpoint : ∀ a ∈ s, |k a * v a| ≤
      (CK * (l / (J ^ 6 * Λ ^ 3 * (1 + l ^ 2) ^ 2))) * (CV * J⁻¹) * ‖ω₀ a‖ := by
    intro a ha
    simpa only [abs_mul, mul_assoc] using
      mul_le_mul (hk a ha) (hv a ha) (abs_nonneg (v a)) (by positivity)
  obtain ⟨hi, hb⟩ := integrableOn_and_integral_abs_le_of_mass_bound hs
    (by positivity) hf hω.norm hpoint hmass
  refine ⟨hi, hb.trans_eq ?_⟩
  calc
    _ = (CK * CV * M) * ((l / (J ^ 6 * Λ ^ 3 * (1 + l ^ 2) ^ 2)) *
        (J⁻¹ * (l ^ (α + 2) * J ^ (3 * α + 6) * Λ ^ (α + 3)))) * b := by ring
    _ = _ := by rw [axis_kernel_cusp_scaling hl hJ hΛ]; ring

/-- Block majorants prove absolute integrability and bound the integral over their disjoint union. -/
theorem integrableOn_iUnion_and_integral_abs_le_of_axis_kernel_bound
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {s : ℤ × ℤ → Set X} {f : X → ℝ}
    {α A : ℝ} {b : ℤ → ℝ} (hα₀ : -3 < α) (hα₁ : α < 1)
    (hs : ∀ p, MeasurableSet (s p)) (hd : Pairwise (fun p q => Disjoint (s p) (s q)))
    (hi : ∀ p, IntegrableOn f (s p) μ) (hb : Summable b) (hb₀ : ∀ n, 0 ≤ b n)
    (hbound : ∀ p : ℤ × ℤ, (∫ a in s p, |f a| ∂μ) ≤ A *
      ((((2 : ℝ) ^ p.1) ^ (α + 3) / (1 + ((2 : ℝ) ^ p.1) ^ 2) ^ 2) * b p.2)) :
    IntegrableOn f (⋃ p, s p) μ ∧ (∫ a in ⋃ p, s p, |f a| ∂μ) ≤ A *
      (∑' k : ℤ, ((2 : ℝ) ^ k) ^ (α + 3) / (1 + ((2 : ℝ) ^ k) ^ 2) ^ 2) * ∑' n, b n := by
  have hpos (p : ℤ × ℤ) : 0 ≤ ∫ a in s p, |f a| ∂μ := integral_nonneg (fun a => abs_nonneg (f a))
  have hn : ∀ p : ℤ × ℤ, ‖∫ a in s p, |f a| ∂μ‖ ≤ A *
      ((((2 : ℝ) ^ p.1) ^ (α + 3) / (1 + ((2 : ℝ) ^ p.1) ^ 2) ^ 2) * b p.2) :=
    fun p => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hpos p)] using hbound p
  have hsum : Summable (fun p => ∫ a in s p, ‖f a‖ ∂μ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hpos _)] using
      summable_norm_of_axis_kernel_bound hα₀ hα₁ hb hb₀ hn
  have hfi := integrableOn_iUnion_of_summable_integral_norm hi hsum
  refine ⟨hfi, ?_⟩
  rw [integral_iUnion hs hd hfi.abs]
  simpa only [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg hpos)] using
    norm_tsum_le_of_axis_kernel_bound hα₀ hα₁ hb hb₀ hn

/-- Clock-local geometry, a transported-vorticity bound and the integrated cusp/tail
hypothesis imply the absolute near-clock driver estimate. All summability is derived. -/
theorem integrableOn_axis_driver_of_cusp
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {s : ℤ × ℤ → Set X} {r z d v : X → ℝ} {ω₀ : X → E}
    {J α cR cd CV M B : ℝ} {b : ℤ → ℝ}
    (hJ : 0 < J) (hα₀ : -3 < α) (hα₁ : α < 1)
    (hcR : 0 ≤ cR) (hcd : 0 < cd) (hCV : 0 ≤ CV) (hM : 0 ≤ M)
    (hs : ∀ p, MeasurableSet (s p)) (hd : Pairwise (fun p q => Disjoint (s p) (s q)))
    (hf : ∀ p, AEStronglyMeasurable (fun a => (r a * z a / d a ^ 5) * v a) (μ.restrict (s p)))
    (hω : ∀ p, IntegrableOn ω₀ (s p) μ)
    (hr : ∀ p, ∀ a ∈ s p, 0 ≤ r a)
    (hz : ∀ p, ∀ a ∈ s p, |z a| ≤ d a)
    (hrR : ∀ p : ℤ × ℤ, ∀ a ∈ s p, r a ≤ cR * (2 : ℝ) ^ p.1 * J ^ 2 * (2 : ℝ) ^ p.2)
    (hDd : ∀ p : ℤ × ℤ, ∀ a ∈ s p,
      cd * J ^ 2 * (2 : ℝ) ^ p.2 * Real.sqrt (1 + ((2 : ℝ) ^ p.1) ^ 2) ≤ d a)
    (hv : ∀ p, ∀ a ∈ s p, |v a| ≤ CV * J⁻¹ * ‖ω₀ a‖)
    (hmass : ∀ p : ℤ × ℤ, (∫ a in s p, ‖ω₀ a‖ ∂μ) ≤ (M * b p.2) *
      (((2 : ℝ) ^ p.1) ^ (α + 2) * J ^ (3 * α + 6) * ((2 : ℝ) ^ p.2) ^ (α + 3)))
    (hb : ∀ n, 0 ≤ b n)
    (hB : ∀ q : Finset ℤ, ∑ n ∈ q, ((2 : ℝ) ^ n) ^ α * b n ≤ B) :
    IntegrableOn (fun a => (r a * z a / d a ^ 5) * v a) (⋃ p, s p) μ ∧
      (∫ a in ⋃ p, s p, |(r a * z a / d a ^ 5) * v a| ∂μ) ≤
        ((cR / cd ^ 4) * CV * M) *
          (∑' k : ℤ, ((2 : ℝ) ^ k) ^ (α + 3) / (1 + ((2 : ℝ) ^ k) ^ 2) ^ 2) *
          B * J ^ (3 * α - 1) := by
  have hblock (p : ℤ × ℤ) := integrableOn_axis_block_and_integral_abs_le
    (hs p) (zpow_pos (by norm_num : (0 : ℝ) < 2) p.1) hJ
    (zpow_pos (by norm_num : (0 : ℝ) < 2) p.2) (by positivity : 0 ≤ cR / cd ^ 4) hCV
    (hf p) (hω p)
    (fun a ha => abs_axis_kernel_le_clock_scale (hr p a ha) (zpow_pos (by norm_num) p.1)
      hJ (zpow_pos (by norm_num) p.2) hcd (hrR p a ha) (hDd p a ha) (hz p a ha))
    (hv p) (hmass p)
  have htail := summable_axial_tail_of_finset_sum_le hb hB
  obtain ⟨hi, hsum⟩ := integrableOn_iUnion_and_integral_abs_le_of_axis_kernel_bound
    (A := (cR / cd ^ 4 * CV * M) * J ^ (3 * α - 1))
    hα₀ hα₁ hs hd (fun p => (hblock p).1) htail.1
    (fun n => mul_nonneg (Real.rpow_nonneg (le_of_lt (zpow_pos (by norm_num) n)) α) (hb n))
    (fun p => by simpa only [mul_assoc] using (hblock p).2)
  have hw₀ : 0 ≤ ∑' k : ℤ, ((2 : ℝ) ^ k) ^ (α + 3) / (1 + ((2 : ℝ) ^ k) ^ 2) ^ 2 :=
    tsum_nonneg (fun k => axis_kernel_weight_nonneg (le_of_lt (zpow_pos (by norm_num) k)))
  refine ⟨hi, hsum.trans ?_⟩
  calc
    _ ≤ (cR / cd ^ 4 * CV * M * J ^ (3 * α - 1) *
        (∑' k : ℤ, ((2 : ℝ) ^ k) ^ (α + 3) / (1 + ((2 : ℝ) ^ k) ^ 2) ^ 2)) * B :=
      mul_le_mul_of_nonneg_left htail.2 (by positivity)
    _ = _ := by ring

end ClockBarrier.Analysis
