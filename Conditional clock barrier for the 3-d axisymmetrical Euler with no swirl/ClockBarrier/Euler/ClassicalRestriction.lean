/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.Classical

/-! # Restriction of the classical Euler interface in time -/

public section
namespace ClockBarrier.Euler
open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Restricting a classical solution preserves the exact temporal and spatial conventions. -/
theorem classical_euler_on.restrict_time
    {α : ℝ≥0} {S T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (hS : 0 < S) (hST : S ≤ T) :
    classical_euler_on α S u p := by
  have hsub : Ico (0 : ℝ) S ⊆ Ico 0 T := Ico_subset_Ico_right hST
  rcases h with ⟨_, hα₀, hα₁, hu, ⟨D, hD, hDu, hDH⟩,
    hL₂, htime, hp, hgrad, hPDE, hdiv⟩
  exact ⟨hS, hα₀, hα₁, hu.mono hsub,
    ⟨D, hD.mono hsub, fun t ht x => hDu t (hsub ht) x,
      fun b hb => hDH b (hsub hb)⟩,
    fun t ht => hL₂ t (hsub ht),
    fun t ht => (htime t (hsub ht)).mono_left (nhdsWithin_mono _ hsub),
    fun t ht => hp t (hsub ht), hgrad.mono (prod_mono hsub subset_rfl),
    fun t ht x => (hPDE t (hsub ht) x).mono hsub,
    fun t ht x => hdiv t (hsub ht) x⟩

end ClockBarrier.Euler
