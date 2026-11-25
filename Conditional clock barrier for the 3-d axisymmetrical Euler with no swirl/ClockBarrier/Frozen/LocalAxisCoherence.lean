/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisCoherent
public import ClockBarrier.Euler.Reflection
import ClockBarrier.Euler.LocalAxisCoherence

/-! # Proposition 3.2: local membership in the axis coherence class

-/

public section
open scoped NNReal BoundedContinuousFunction


theorem ClockBarrier.Euler.local_axis_coherence
    {α : ℝ≥0} {T : ℝ}
    {u : ℝ → EuclideanSpace ℝ (Fin 3) →ᵇ EuclideanSpace ℝ (Fin 3)}
    {p : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ClockBarrier.Euler.classical_euler_on α T u p)
    (haxis : ClockBarrier.Euler.axisymmetric_no_swirl (u 0))
    (hreflection : ClockBarrier.Euler.z_reflection_symmetric (u 0)) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ < T ∧
      ClockBarrier.Euler.axis_coherent_on α T₀ u :=

by exact ClockBarrier.Euler.classical_euler_on.exists_local_axis_coherence h haxis hreflection



end


