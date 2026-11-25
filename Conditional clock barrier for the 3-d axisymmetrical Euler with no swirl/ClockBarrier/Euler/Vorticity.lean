/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Cartesian vorticity

The right-handed Cartesian curl on fields with Cartesian partial derivatives.
Continuity of the partial derivatives and total differentiability are not required.
-/

@[expose] public section

namespace ClockBarrier.Euler

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Vorticity is the Cartesian curl of a field with all Cartesian partial derivatives. -/
noncomputable def vorticity (u : E₃ → E₃)
    (_hpartial : ∀ x : E₃, ∀ i j : Fin 3,
      DifferentiableAt ℝ (fun s : ℝ => u (x + s • EuclideanSpace.single i 1) j) 0)
    (x : E₃) : E₃ :=
  let D := fun i j : Fin 3 =>
    deriv (fun s : ℝ => u (x + s • EuclideanSpace.single i 1) j) 0
  !₂[D 1 2 - D 2 1, D 2 0 - D 0 2, D 0 1 - D 1 0]

end ClockBarrier.Euler
