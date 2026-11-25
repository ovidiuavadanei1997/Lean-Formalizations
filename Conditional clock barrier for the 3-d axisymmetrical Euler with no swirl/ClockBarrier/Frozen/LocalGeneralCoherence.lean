/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.GeneralCoherent
import ClockBarrier.Euler.LocalGeneralCoherence

/-! # Proposition 3.1: local membership in the general coherence class

The initial symmetry is a premise; its propagation remains a proof obligation.
-/

public section
open scoped NNReal BoundedContinuousFunction


theorem ClockBarrier.Euler.local_general_coherence {α : ℝ≥0} {T : ℝ} {u : ℝ → EuclideanSpace ℝ (Fin 3) →ᵇ EuclideanSpace ℝ (Fin 3)} {p : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ} (h : ClockBarrier.Euler.classical_euler_on α T u p) (haxis : ClockBarrier.Euler.axisymmetric_no_swirl (u 0)) : ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ < T ∧ ClockBarrier.Euler.general_coherent_on α T₀ u :=

by exact ClockBarrier.Euler.classical_euler_on.exists_local_general_coherence h haxis



end


