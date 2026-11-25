/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.AxisDerivative
public import Mathlib.LinearAlgebra.Trace

/-! # The matrix of an actual Euclidean continuous linear map -/

@[expose] public section

namespace ClockBarrier.Geometry

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Matrix representation in the standard Euclidean basis, as a bounded linear map. -/
noncomputable def euclideanMatrix :
    (EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) →L[ℝ] Matrix n n ℝ :=
  (((LinearMap.toMatrix (PiLp.basisFun 2 ℝ n) (PiLp.basisFun 2 ℝ n)).toLinearMap).comp
    (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap

/-- The matrix represents exactly the original operator. -/
theorem toEuclideanLin_euclideanMatrix (A : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) :
    Matrix.toEuclideanLin (euclideanMatrix A) = A.toLinearMap := by
  change Matrix.toLpLin 2 2 (euclideanMatrix A) = A.toLinearMap
  rw [Matrix.toLpLin_eq_toLin]
  exact Matrix.toLin_toMatrix _ _ A.toLinearMap

/-- Composition of operators is matrix multiplication in the standard basis. -/
@[simp] theorem euclideanMatrix_comp
    (A B : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) :
    euclideanMatrix (A.comp B) = euclideanMatrix A * euclideanMatrix B := by
  exact LinearMap.toMatrix_comp _ _ _ A.toLinearMap B.toLinearMap

/-- The identity operator has identity matrix. -/
@[simp] theorem euclideanMatrix_id :
    euclideanMatrix (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ n)) = 1 := by
  exact LinearMap.toMatrix_id _

/-- Matrix and basis-independent operator determinants agree. -/
@[simp] theorem det_euclideanMatrix (A : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) :
    (euclideanMatrix A).det = A.toLinearMap.det := by
  exact LinearMap.det_toMatrix _ A.toLinearMap

/-- Matrix trace equals the basis-independent trace of the operator. -/
theorem trace_euclideanMatrix (A : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) :
    (euclideanMatrix A).trace = LinearMap.trace ℝ (EuclideanSpace ℝ n) A.toLinearMap := by
  exact (LinearMap.trace_eq_matrix_trace ℝ _ A.toLinearMap).symm

end ClockBarrier.Geometry
