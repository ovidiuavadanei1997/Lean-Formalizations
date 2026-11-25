/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisFlow
public import ClockBarrier.Analysis.ExactIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Module

/-! # Exactness of time-integrated Euler momentum -/

public section

namespace ClockBarrier.Euler

open Set MeasureTheory Filter
open scoped Topology NNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Integrated Euler momentum is a genuine exact gradient. The construction
normalizes pressure in space and requires no temporal regularity of its gauge. -/
theorem classical_euler_on.exists_potential_integrated_momentum
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {b : ℝ} (hb : b ∈ Ico 0 T)
    {N : ℝ → E₃ →ᵇ E₃} (hN : Continuous N)
    (hNe : ∀ t ∈ Icc 0 b, ∀ x, N t x = fderiv ℝ (u t) x (u t x)) :
    ∃ q : E₃ → ℝ, ∀ x, HasFDerivAt q
      (innerSL ℝ (u b x - u 0 x + ((∫ t in 0..b, N t) : E₃ →ᵇ E₃) x)) x := by
  have hsub : Icc 0 b ⊆ Ico 0 T := fun _ ht => ⟨ht.1, ht.2.trans_lt hb.2⟩
  obtain ⟨_, _, _, hu, _, _, _, hp, hgp, hut, _⟩ := h
  let I (t : ℝ) : E₃ →ᵇ E₃ := ∫ s in 0..t, N s
  have hI (t : ℝ) (x : E₃) : HasDerivAt (fun s => I s x) (N t x) t :=
    (BoundedContinuousFunction.evalCLM (β := E₃) ℝ x).hasFDerivAt.comp_hasDerivAt t
      (intervalIntegral.integral_hasDerivAt_right (a := 0) (b := t) (hN.intervalIntegrable _ _)
        hN.aestronglyMeasurable.stronglyMeasurableAtFilter hN.continuousAt)
  let A (t : ℝ) (x : E₃) := innerSL ℝ (u t x + I t x)
  have hA (x : E₃) : ContinuousOn (fun t => A t x) (Icc 0 b) :=
    (innerSL ℝ).continuous.comp_continuousOn
      ((((BoundedContinuousFunction.evalCLM (β := E₃) ℝ x).continuous.comp_continuousOn hu).mono hsub).add
        ((continuous_iff_continuousAt.mpr (fun t => (hI t x).continuousAt)).continuousOn))
  have hAt (x : E₃) (t : ℝ) (ht : t ∈ Ioo 0 b) :
      HasDerivAt (fun s => A s x) (-(innerSL ℝ (gradient (p t) x))) t := by
    have htc : t ∈ Icc 0 b := ⟨ht.1.le, ht.2.le⟩
    have hs := ((hut t (hsub htc) x).hasDerivAt
      (Ico_mem_nhds ht.1 (ht.2.trans hb.2))).add (hI t x)
    have heq : -(fderiv ℝ (u t) x) (u t x) - gradient (p t) x + N t x =
        -gradient (p t) x := by rw [hNe t htc x]; module
    simpa only [Function.comp_def, map_neg, Pi.add_apply, A] using
      (innerSL ℝ (E := E₃)).hasFDerivAt.comp_hasDerivAt t (hs.congr_deriv heq)
  obtain ⟨q, hq⟩ := Analysis.exists_potential_endpoint_sub (f := fun t x => -p t x)
    (D := fun tx => -(innerSL ℝ (gradient (p tx.1) tx.2))) (A := A) hb.1
    (((innerSL ℝ).continuous.comp_continuousOn (hgp.mono (prod_mono_left hsub))).neg)
    (fun t ht x => ((hp t (hsub ht) x).hasGradientAt.hasFDerivAt).neg) hA hAt
  refine ⟨q, fun x => (hq x).congr_fderiv ?_⟩
  simp only [A, I, intervalIntegral.integral_same, BoundedContinuousFunction.coe_zero, Pi.zero_apply,
    add_zero, map_add, map_sub, map_zero]
  module

/-- The exact integrated momentum is the negative time integral of the actual
pressure gradient. All time integrals here have continuous integrands. -/
theorem classical_euler_on.integrated_momentum_eq_neg_pressure
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {b : ℝ} (hb : b ∈ Ico 0 T)
    {N : ℝ → E₃ →ᵇ E₃} (hN : Continuous N)
    (hNe : ∀ t ∈ Icc 0 b, ∀ x, N t x = fderiv ℝ (u t) x (u t x)) (x : E₃) :
    u b x - u 0 x + ((∫ t in 0..b, N t) : E₃ →ᵇ E₃) x =
      -(∫ t in 0..b, gradient (p t) x) := by
  have hsub : Icc 0 b ⊆ Ico 0 T := fun _ ht => ⟨ht.1, ht.2.trans_lt hb.2⟩
  obtain ⟨_, _, _, hu, _, _, _, _, hgp, hut, _⟩ := h
  let I (t : ℝ) : E₃ →ᵇ E₃ := ∫ s in 0..t, N s
  have hI (t : ℝ) (x : E₃) : HasDerivAt (fun s => I s x) (N t x) t :=
    (BoundedContinuousFunction.evalCLM (β := E₃) ℝ x).hasFDerivAt.comp_hasDerivAt t
      (intervalIntegral.integral_hasDerivAt_right (a := 0) (b := t) (hN.intervalIntegrable _ _)
        hN.aestronglyMeasurable.stronglyMeasurableAtFilter hN.continuousAt)
  have hV : ContinuousOn (fun t => u t x + I t x) (Icc 0 b) :=
    (((BoundedContinuousFunction.evalCLM (β := E₃) ℝ x).continuous.comp_continuousOn hu).mono hsub).add
      ((continuous_iff_continuousAt.mpr (fun t => (hI t x).continuousAt)).continuousOn)
  have hVd (t : ℝ) (ht : t ∈ Ioo 0 b) :
      HasDerivAt (fun s => u s x + I s x) (-gradient (p t) x) t := by
    have htc : t ∈ Icc 0 b := ⟨ht.1.le, ht.2.le⟩
    apply (((hut t (hsub htc) x).hasDerivAt
      (Ico_mem_nhds ht.1 (ht.2.trans hb.2))).add (hI t x)).congr_deriv
    rw [hNe t htc x]
    module
  have hpg : ContinuousOn (fun t => gradient (p t) x) (Icc 0 b) :=
    hgp.comp (continuousOn_id.prodMk continuousOn_const)
      (fun t ht => ⟨hsub ht, mem_univ x⟩)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb.1 hV hVd
    (hpg.neg.intervalIntegrable_of_Icc hb.1)
  simp only [intervalIntegral.integral_neg, I, intervalIntegral.integral_same,
    BoundedContinuousFunction.coe_zero, Pi.zero_apply, add_zero] at he
  rw [he]
  module

end ClockBarrier.Euler
