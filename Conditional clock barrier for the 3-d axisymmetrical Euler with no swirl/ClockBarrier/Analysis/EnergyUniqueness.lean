/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.EnergyIncrement
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Module

/-! # Uniqueness from integrated momentum and a quadratic energy estimate -/

public section

namespace ClockBarrier.Analysis

open Set MeasureTheory Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Integrated orthogonality gives the energy derivative without requiring
strong time differentiability of the Hilbert-valued velocity. -/
theorem hasDerivAt_norm_sq_of_integrated_orthogonality [CompleteSpace H]
    {U N : ℝ → H} (hU : Continuous U) (hN : Continuous N) {a b : ℝ}
    (ho : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      inner ℝ (U t - U a + ∫ r in a..t, N r) (U s) = 0)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => ‖U s‖ ^ 2) (-2 * inner ℝ (N t) (U t)) t := by
  let I (t : ℝ) := ∫ r in a..t, N r
  have hI (t : ℝ) : HasDerivAt I (N t) t :=
    intervalIntegral.integral_hasDerivAt_right (hN.intervalIntegrable _ _)
      hN.aestronglyMeasurable.stronglyMeasurableAtFilter hN.continuousAt
  have hi {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
      ‖U t‖ ^ 2 - ‖U s‖ ^ 2 = -inner ℝ (I t - I s) (U t + U s) :=
    norm_sq_sub_eq_of_integrated_orthogonality (ho s hs s hs) (ho t ht t ht)
      (ho s hs t ht) (ho t ht s hs)
  have hd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt (fun s => ‖U s‖ ^ 2) (-2 * inner ℝ (N t) (U t)) t := by
    have hb := hasFDerivAt_bilinear_of_zero (innerSL ℝ (E := H)) (g := fun s => U s + U t)
      ((hI t).sub_const (I t)).hasFDerivAt (sub_self (I t))
      (hU.continuousAt.add continuousAt_const)
    have hb' : HasDerivAt (fun s => inner ℝ (I s - I t) (U s + U t)) (2 * inner ℝ (N t) (U t)) t := by
      apply hb.hasDerivAt.congr_deriv
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.toSpanSingleton_apply, one_smul]
      change inner ℝ (N t) (U t + U t) = 2 * inner ℝ (N t) (U t)
      rw [inner_add_right, two_mul]
    apply ((hb'.neg.congr_deriv (by ring)).add_const (‖U t‖ ^ 2)).congr_of_eventuallyEq
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact eq_add_of_sub_eq (hi ⟨ht.1.le, ht.2.le⟩ hs)
  exact hd t ht

/-- A quadratic lower bound on the nonlinear pairing gives uniqueness for
zero initial data, using only integrated pressure orthogonality. -/
theorem eq_zero_of_integrated_orthogonality [CompleteSpace H]
    {U N : ℝ → H} (hU : Continuous U) (hN : Continuous N) {a b K : ℝ}
    (hab : a ≤ b) (h0 : U a = 0)
    (ho : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      inner ℝ (U t - U a + ∫ r in a..t, N r) (U s) = 0)
    (hbound : ∀ t ∈ Icc a b, -K * ‖U t‖ ^ 2 ≤ inner ℝ (N t) (U t)) :
    U b = 0 := by
  let f (t : ℝ) := Real.exp (-2 * K * t) * ‖U t‖ ^ 2
  have hd (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt f (Real.exp (-2 * K * t) *
        (-2 * inner ℝ (N t) (U t) - 2 * K * ‖U t‖ ^ 2)) t := by
    apply (((hasDerivAt_id t).const_mul (-2 * K)).exp.mul
      (hasDerivAt_norm_sq_of_integrated_orthogonality hU hN ho ht)).congr_deriv
    dsimp only [id_eq]
    ring
  have hm : AntitoneOn f (Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
      (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul (hU.norm.pow 2)).continuousOn)
    · intro t ht
      exact (hd t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
    · intro t ht
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      have hh := hbound t (Ioo_subset_Icc_self (by simpa only [interior_Icc] using ht))
      linarith
  have hf := hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have hz : ‖U b‖ ^ 2 ≤ 0 := by
    have hh : Real.exp (-2 * K * b) * ‖U b‖ ^ 2 ≤ 0 := by simpa [f, h0] using hf
    nlinarith [Real.exp_pos (-2 * K * b)]
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (U b)])

end ClockBarrier.Analysis
