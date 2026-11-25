/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.CurlLinear
public import ClockBarrier.Geometry.AxisEvaluation
public import ClockBarrier.Geometry.CylindricalSymmetry

/-! # Curl vanishes on the axis of a differentiable no-swirl field

Only differentiability at the selected axis point and the cylindrical velocity
formula are used. No second derivative, incompressibility, or time equation is needed.
-/

public section

namespace ClockBarrier.Geometry

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Curl of an operator agrees with the antisymmetric entries of its actual matrix. -/
theorem curlLinearMap_euclideanMatrix (A : E₃ →L[ℝ] E₃) :
    curlLinearMap A =
      !₂[euclideanMatrix A 2 1 - euclideanMatrix A 1 2,
         euclideanMatrix A 0 2 - euclideanMatrix A 2 0,
         euclideanMatrix A 1 0 - euclideanMatrix A 0 1] := by
  have h := curlLinearMap_toEuclideanLin (euclideanMatrix A)
  rwa [toEuclideanLin_euclideanMatrix] at h

/-- The cylindrical no-swirl formula forces zero curl at every differentiability
point on the axis. The cylindrical coefficient functions need no extra regularity. -/
theorem curlLinearMap_fderiv_axis_eq_zero
    {u : E₃ → E₃} {v w : ℝ → ℝ → ℝ} {z : ℝ}
    (hu : DifferentiableAt ℝ u !₂[0, 0, z])
    (haxis : ∀ r : ℝ, 0 ≤ r → ∀ θ z : ℝ,
      u !₂[r * Real.cos θ, r * Real.sin θ, z] =
        !₂[v r z * Real.cos θ, v r z * Real.sin θ, w r z]) :
    curlLinearMap (fderiv ℝ u !₂[0, 0, z]) = 0 := by
  obtain ⟨hx, hy, hq⟩ := transverse_symmetries_of_cylindrical_representation haxis
  have hdiag := eq_diagonal_of_hasFDerivAt_axis
    (hasFDerivAt_euclideanMatrix_fderiv hu) hx hy hq
  rw [curlLinearMap_euclideanMatrix, hdiag]
  ext i
  fin_cases i <;> simp

end ClockBarrier.Geometry
