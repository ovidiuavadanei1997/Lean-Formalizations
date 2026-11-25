/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.GeneralCoherent
import ClockBarrier.Euler.LocalCoherenceAssembly
import ClockBarrier.Euler.SymmetryPreservation

/-! # Provider for Proposition 3.1

Initial symmetry propagates by finite-energy uniqueness and orthogonal
covariance. The existing local assembly supplies every coherence estimate,
actual flow and measurable singular frame on a common positive interval.
-/

public section
namespace ClockBarrier.Euler
open scoped NNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Every classical Euler solution with initially axisymmetric,
no-swirl data belongs locally to the exact general coherence class. -/
theorem classical_euler_on.exists_local_general_coherence
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (haxis : axisymmetric_no_swirl (u 0)) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ < T ∧ general_coherent_on α T₀ u :=
  h.exists_local_general_coherence_of_lifespan_axisymmetry
    (fun _ ht => h.axisymmetric_no_swirl haxis ht)

end ClockBarrier.Euler
