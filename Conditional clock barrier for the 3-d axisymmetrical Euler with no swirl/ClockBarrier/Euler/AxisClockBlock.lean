/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisDyadicBlock

/-! # Exact clock-local dyadic blocks

See docs/ERRATA-AND-DEVIATIONS.md for the conventions.
-/

@[expose] public section

namespace ClockBarrier.Euler

open Set

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The source's closed clock-local portion of an axis dyadic block. -/
def axisClockBlock (Φ : E₃ → E₃) (J : {j : ℝ // 0 < j})
    (z : ℝ) (L ℓ : {r : ℝ // 0 < r}) (k n : ℤ) : Set E₃ :=
  axisDyadicBlock J z k n ∩ {a | ‖a - !₂[0, 0, z]‖ ≤ ℓ.val} ∩
    {a | ‖Φ a - Φ !₂[0, 0, z]‖ ≤ L.val}

end ClockBarrier.Euler
