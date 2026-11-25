/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.CurlLinear
public import ClockBarrier.Geometry.EuclideanMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

/-! # Three-dimensional algebra for Cauchy's vorticity identity -/

public section

namespace ClockBarrier.Geometry

open scoped InnerProductSpace

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The alternating part of a pulled-back covector transforms with the determinant.
This polynomial identity requires no invertibility assumption. -/
theorem matrix_mul_skew_eq_det_smul_curl (M N : Matrix (Fin 3) (Fin 3) ℝ) :
    let A := Matrix.toEuclideanLin M
    let B := Matrix.toEuclideanLin N
    A !₂[⟪B (A !₂[0, 1, 0]), A !₂[0, 0, 1]⟫_ℝ -
            ⟪B (A !₂[0, 0, 1]), A !₂[0, 1, 0]⟫_ℝ,
          ⟪B (A !₂[0, 0, 1]), A !₂[1, 0, 0]⟫_ℝ -
            ⟪B (A !₂[1, 0, 0]), A !₂[0, 0, 1]⟫_ℝ,
          ⟪B (A !₂[1, 0, 0]), A !₂[0, 1, 0]⟫_ℝ -
            ⟪B (A !₂[0, 1, 0]), A !₂[1, 0, 0]⟫_ℝ] =
      M.det • !₂[N 2 1 - N 1 2, N 0 2 - N 2 0, N 1 0 - N 0 1] := by
  ext i
  fin_cases i <;>
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three,
      Matrix.det_fin_three, Matrix.mul_apply] <;> ring

/-- Preservation of the curl two-form by a determinant-one linear map gives
the usual vector-valued Cauchy transport identity. -/
theorem curl_eq_map_of_skew_eq
    (A B C : E₃ →L[ℝ] E₃) (hdet : A.toLinearMap.det = 1)
    (hskew : ∀ v w : E₃,
      ⟪B (A v), A w⟫_ℝ - ⟪B (A w), A v⟫_ℝ = ⟪C v, w⟫_ℝ - ⟪C w, v⟫_ℝ) :
    curlLinearMap B = A (curlLinearMap C) := by
  have hp := matrix_mul_skew_eq_det_smul_curl (euclideanMatrix A) (euclideanMatrix B)
  have hc := curlLinearMap_toEuclideanLin (euclideanMatrix B)
  rw [toEuclideanLin_euclideanMatrix] at hc
  have hB : B.toLinearMap.toContinuousLinearMap = B := by ext x; rfl
  rw [hB] at hc
  rw [toEuclideanLin_euclideanMatrix, toEuclideanLin_euclideanMatrix,
    ← hc, det_euclideanMatrix, hdet, one_smul] at hp
  rw [← hp]
  apply congrArg A
  ext i
  fin_cases i
  · simpa [curlLinearMap_apply, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_three] using hskew !₂[0, 1, 0] !₂[0, 0, 1]
  · simpa [curlLinearMap_apply, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_three] using hskew !₂[0, 0, 1] !₂[1, 0, 0]
  · simpa [curlLinearMap_apply, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_three] using hskew !₂[1, 0, 0] !₂[0, 1, 0]

end ClockBarrier.Geometry
