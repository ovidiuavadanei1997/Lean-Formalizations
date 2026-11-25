/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.BoundedLp
public import Mathlib.MeasureTheory.Function.Holder

/-! # Continuous bounded-operator application on finite-energy fields -/

public section

namespace ClockBarrier.Analysis

open MeasureTheory
open scoped ENNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Applying a continuously varying bounded operator field to an `L²`-continuous
vector field produces an `L²`-continuous family with the expected representative. -/
theorem exists_continuous_lp_apply {S : Type*} [TopologicalSpace S]
    (D : S → E₃ →ᵇ (E₃ →L[ℝ] E₃)) (U : S → Lp E₃ 2 volume)
    (hD : Continuous D) (hU : Continuous U) {u : S → E₃ → E₃}
    (he : ∀ t, U t =ᵐ[volume] u t) :
    ∃ N : S → Lp E₃ 2 volume, Continuous N ∧
      ∀ t, N t =ᵐ[volume] fun x => D t x (u t x) := by
  let d (t : S) := ((D t).memLp_top (μ := volume)).toLp (D t)
  let B := (ContinuousLinearMap.id ℝ (E₃ →L[ℝ] E₃)).holderL (volume : Measure E₃) ∞ 2 2
  have hd : Continuous d := continuous_bounded_toLp_top.comp hD
  refine ⟨fun t => B (d t) (U t), (B.continuous.comp hd).clm_apply hU, ?_⟩
  intro t
  filter_upwards [(ContinuousLinearMap.id ℝ (E₃ →L[ℝ] E₃)).coeFn_holder (r := 2) (d t) (U t),
    ((D t).memLp_top (μ := volume)).coeFn_toLp, he t] with x hx hd' hu'
  simp only [B, ContinuousLinearMap.holderL_apply_apply, hx, ContinuousLinearMap.id_apply,
    d, hd', hu']

end ClockBarrier.Analysis
