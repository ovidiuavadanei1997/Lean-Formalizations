/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Sqrt

/-! # Exact dyadic blocks for the axis clock

See docs/ERRATA-AND-DEVIATIONS.md for the conventions.
-/

@[expose] public section

namespace ClockBarrier.Euler

open Set

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Half-open dyadic blocks for a positive axis clock; k is angular and n is axial. -/
def axisDyadicBlock (J : {j : ℝ // 0 < j}) (z : ℝ) (k n : ℤ) : Set E₃ :=
  {a | (2 : ℝ) ^ n ≤ |a 2 - z| ∧ |a 2 - z| < 2 * (2 : ℝ) ^ n ∧
    (2 : ℝ) ^ k * J.val ^ 3 * (2 : ℝ) ^ n ≤ Real.sqrt ((a 0)^2 + (a 1)^2) ∧
    Real.sqrt ((a 0)^2 + (a 1)^2) < 2 * ((2 : ℝ) ^ k * J.val ^ 3 * (2 : ℝ) ^ n)}

end ClockBarrier.Euler
