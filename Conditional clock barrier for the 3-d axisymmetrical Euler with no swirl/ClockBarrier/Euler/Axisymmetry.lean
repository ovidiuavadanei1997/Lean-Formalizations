/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Axisymmetric velocity fields without swirl

See docs/ERRATA-AND-DEVIATIONS.md for the conventions.
-/

@[expose] public section

namespace ClockBarrier.Euler

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The usual cylindrical formula, with no azimuthal velocity component. -/
def axisymmetric_no_swirl (f : E₃ → E₃) : Prop :=
  ∃ v w : ℝ → ℝ → ℝ, ∀ r : ℝ, 0 ≤ r → ∀ θ z : ℝ,
    f !₂[r * Real.cos θ, r * Real.sin θ, z] =
      !₂[v r z * Real.cos θ, v r z * Real.sin θ, w r z]

end ClockBarrier.Euler

