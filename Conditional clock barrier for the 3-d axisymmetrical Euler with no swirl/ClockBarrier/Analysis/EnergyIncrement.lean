/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.BilinearZero
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Module

/-! # Energy conservation from integrated momentum and orthogonality -/

public section

namespace ClockBarrier.Analysis

open Set MeasureTheory Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Orthogonality of integrated momentum gives the exact energy increment
without differentiating the velocity in the Hilbert norm. -/
theorem norm_sq_sub_eq_of_integrated_orthogonality {U I : ℝ → H} {a s t : ℝ}
    (hss : inner ℝ (U s - U a + I s) (U s) = 0)
    (htt : inner ℝ (U t - U a + I t) (U t) = 0)
    (hst : inner ℝ (U t - U a + I t) (U s) = 0)
    (hts : inner ℝ (U s - U a + I s) (U t) = 0) :
    ‖U t‖ ^ 2 - ‖U s‖ ^ 2 = -inner ℝ (I t - I s) (U t + U s) := by
  simp only [inner_add_left, inner_sub_left] at hss htt hst hts
  simp only [inner_sub_left, inner_add_right]
  rw [real_inner_self_eq_norm_sq] at hss htt
  rw [real_inner_comm] at hst
  linarith

/-- Integrated momentum orthogonality and convective cancellation imply energy
conservation, assuming only Hilbert-norm continuity of the velocity. -/
theorem norm_sq_eq_of_integrated_orthogonality [CompleteSpace H]
    {U N : ℝ → H} (hU : Continuous U) (hN : Continuous N) {a b : ℝ} (hab : a ≤ b)
    (hc : ∀ t ∈ Icc a b, inner ℝ (U t) (N t) = 0)
    (ho : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      inner ℝ (U t - U a + ∫ r in a..t, N r) (U s) = 0) :
    ‖U b‖ ^ 2 = ‖U a‖ ^ 2 := by
  let I (t : ℝ) := ∫ r in a..t, N r
  have hI (t : ℝ) : HasDerivAt I (N t) t :=
    intervalIntegral.integral_hasDerivAt_right (hN.intervalIntegrable _ _)
      hN.aestronglyMeasurable.stronglyMeasurableAtFilter hN.continuousAt
  have hi {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
      ‖U t‖ ^ 2 - ‖U s‖ ^ 2 = -inner ℝ (I t - I s) (U t + U s) :=
    norm_sq_sub_eq_of_integrated_orthogonality (ho s hs s hs) (ho t ht t ht)
      (ho s hs t ht) (ho t ht s hs)
  have hd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt (fun s => ‖U s‖ ^ 2) 0 t := by
    have hb := hasFDerivAt_bilinear_of_zero (innerSL ℝ (E := H)) (g := fun s => U s + U t)
      ((hI t).sub_const (I t)).hasFDerivAt (sub_self (I t))
      (hU.continuousAt.add continuousAt_const)
    have hb' : HasDerivAt (fun s => inner ℝ (I s - I t) (U s + U t)) 0 t := by
      apply hb.hasDerivAt.congr_deriv
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.toSpanSingleton_apply, one_smul]
      change inner ℝ (N t) (U t + U t) = 0
      rw [inner_add_right, real_inner_comm (U t), hc t ⟨ht.1.le, ht.2.le⟩, add_zero]
    apply ((hb'.neg.congr_deriv (neg_zero : -(0 : ℝ) = 0)).add_const (‖U t‖ ^ 2)).congr_of_eventuallyEq
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact eq_add_of_sub_eq (hi ⟨ht.1.le, ht.2.le⟩ hs)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (hU.norm.pow 2).continuousOn hd (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume a b)
  apply sub_eq_zero.mp
  simpa only [intervalIntegral.integral_zero, Pi.pow_apply] using he.symm

end ClockBarrier.Analysis
