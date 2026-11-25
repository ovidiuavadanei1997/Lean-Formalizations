/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.Holder

/-! # Hölder decay away from a zero axis -/

public section

namespace ClockBarrier.Analysis

open scoped NNReal

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The distance to the point on the axis with the same height is the radius. -/
theorem dist_axis_same_height (x : E₃) :
    dist x !₂[0, 0, x 2] = Real.sqrt ((x 0)^2 + (x 1)^2) := by
  simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three, Real.norm_eq_abs]

/-- A globally Hölder field vanishing on the axis decays with the same exponent
in the cylindrical radius. The constant is uniform over the axis height. -/
theorem norm_le_radius_rpow_of_holderWith_axis_zero
    {E : Type*} [NormedAddCommGroup E] {ω : E₃ → E} {H α : ℝ≥0}
    (hω : HolderWith H α ω) (hzero : ∀ z : ℝ, ω !₂[0, 0, z] = 0) (x : E₃) :
    ‖ω x‖ ≤ H * (Real.sqrt ((x 0)^2 + (x 1)^2)) ^ (α : ℝ) := by
  simpa only [hzero, dist_zero_right, dist_axis_same_height] using
    hω.dist_le x !₂[0, 0, x 2]

end ClockBarrier.Analysis
