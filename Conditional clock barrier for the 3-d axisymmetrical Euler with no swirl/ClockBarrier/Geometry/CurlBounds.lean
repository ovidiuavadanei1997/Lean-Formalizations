/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.CurlLinear
public import ClockBarrier.Analysis.AxisStrainKernel

/-! # Transverse curl bounds from actual coordinate derivatives -/

public section

namespace ClockBarrier.Geometry

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Only first coordinate derivatives enter the two transverse curl components. -/
theorem abs_curlLinearMap_transverse_le (A : E₃ →L[ℝ] E₃) :
    |curlLinearMap A 0| + |curlLinearMap A 1| ≤
      (‖A !₂[0, 1, 0]‖ + ‖A !₂[0, 0, 1]‖) +
        (‖A !₂[0, 0, 1]‖ + ‖A !₂[1, 0, 0]‖) := by
  simp only [curlLinearMap_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact add_le_add
    ((abs_sub _ _).trans (add_le_add (Analysis.abs_euclidean_coordinate_le_norm _ _)
      (Analysis.abs_euclidean_coordinate_le_norm _ _)))
    ((abs_sub _ _).trans (add_le_add (Analysis.abs_euclidean_coordinate_le_norm _ _)
      (Analysis.abs_euclidean_coordinate_le_norm _ _)))

end ClockBarrier.Geometry
