/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # The Cartesian z-reflection symmetry

See docs/ERRATA-AND-DEVIATIONS.md for the conventions.
-/

@[expose] public section

namespace ClockBarrier.Euler

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Horizontal components are even and the axial component is odd in z. -/
def z_reflection_symmetric (f : E₃ → E₃) : Prop :=
  ∀ x : E₃, f !₂[x 0, x 1, -x 2] = !₂[f x 0, f x 1, -f x 2]

end ClockBarrier.Euler

