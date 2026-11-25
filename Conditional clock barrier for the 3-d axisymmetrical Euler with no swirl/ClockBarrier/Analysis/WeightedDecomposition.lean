/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Smooth near/far decompositions with their transition region

A cutoff between zero and one preserves absolute integral bounds. The smooth
far contribution contains its transition annulus; the complementary near
weight removes exactly that annular contribution.
-/

public section

namespace ClockBarrier.Analysis

open Set MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {f χ : X → ℝ}

/-- Multiplication by a measurable cutoff between zero and one preserves
integrability, including for signed kernels. -/
theorem integrable_cutoff_mul (hf : Integrable f μ) (hχ : AEStronglyMeasurable χ μ)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1) :
    Integrable (fun x => χ x * f x) μ := by
  have hb : ∀ x, ‖χ x‖ ≤ 1 := fun x => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hχ₀ x)] using hχ₁ x
  simpa only [mul_comm] using hf.mul_bdd hχ (Filter.Eventually.of_forall hb)

/-- A cutoff in the unit interval loses no constant in an absolute integral
estimate. This applies also to a restricted measure on a clock region. -/
theorem abs_integral_cutoff_mul_le_integral_abs (hf : Integrable f μ)
    (hχ : AEStronglyMeasurable χ μ) (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1) :
    |∫ x, χ x * f x ∂μ| ≤ ∫ x, |f x| ∂μ := by
  refine abs_integral_le_integral_abs.trans
    (integral_mono (integrable_cutoff_mul hf hχ hχ₀ hχ₁).abs hf.abs ?_)
  intro x
  simpa only [abs_mul, abs_of_nonneg (hχ₀ x), one_mul] using
    mul_le_mul_of_nonneg_right (hχ₁ x) (abs_nonneg (f x))

/-- The exact smooth decomposition retains the whole far integral, including
its transition annulus, and uses the complementary near weight. -/
theorem integral_eq_weighted_near_add_far (hf : Integrable f μ)
    (hχ : AEStronglyMeasurable χ μ) (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    {s : Set X} (houtside : ∀ x ∉ s, χ x = 1) :
    (∫ x, f x ∂μ) = (∫ x in s, (1 - χ x) * f x ∂μ) + ∫ x, χ x * f x ∂μ := by
  have hi := integrable_cutoff_mul hf hχ hχ₀ hχ₁
  have hj : Integrable (fun x => (1 - χ x) * f x) μ :=
    integrable_cutoff_mul hf (aestronglyMeasurable_const.sub hχ)
      (fun x => sub_nonneg.mpr (hχ₁ x)) (fun x => sub_le_self _ (hχ₀ x))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by simp only [houtside x hx, sub_self, zero_mul]), ← integral_add hj hi]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))

/-- The smooth far integral equals the sharp far integral plus its transition
annulus. Dropping this second term would change the decomposition. -/
theorem integral_cutoff_eq_far_add_annulus (hf : Integrable f μ)
    (hχ : AEStronglyMeasurable χ μ) (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    {d : X → ℝ} (hd : Measurable d) (a b : ℝ)
    (hinner : ∀ x, d x ≤ a → χ x = 0) (houter : ∀ x, b < d x → χ x = 1) :
    (∫ x, χ x * f x ∂μ) = (∫ x in {x | b < d x}, f x ∂μ) +
      ∫ x in {x | a < d x ∧ d x ≤ b}, χ x * f x ∂μ := by
  have hi := integrable_cutoff_mul hf hχ hχ₀ hχ₁
  have he := integral_add_compl (s := {x | d x ≤ b})
    (measurableSet_le hd measurable_const) hi
  rw [← integral_inter_add_sdiff (measurableSet_le hd (measurable_const (a := a)))
    (hi.integrableOn (s := {x | d x ≤ b}))] at he
  have hz : (∫ x in {x | d x ≤ b} ∩ {x | d x ≤ a}, χ x * f x ∂μ) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero
      (fun x hx => by simp only [hinner x hx.2, zero_mul])
  have hfar : (∫ x in {x | d x ≤ b}ᶜ, χ x * f x ∂μ) =
      ∫ x in {x | b < d x}, f x ∂μ := by
    simpa only [compl_setOf, not_le] using
      setIntegral_congr_fun (measurableSet_lt measurable_const hd)
        (fun x hx => by simp only [houter x hx, one_mul])
  rw [hz, zero_add, hfar] at he
  simpa only [Set.sdiff_eq, compl_setOf, not_le, setOf_and, inter_comm, add_comm] using he.symm

end ClockBarrier.Analysis
