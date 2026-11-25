/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.CylindricalSymmetry
public import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

/-! # Orthogonal rotations and reflections in cylindrical coordinates -/

public section
namespace ClockBarrier.Geometry
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Every axial rotation is an orthogonal linear equivalence, with its full
Cartesian formula. -/
theorem exists_cylindrical_rotation (θ : ℝ) :
    ∃ R : E₃ ≃ₗᵢ[ℝ] E₃, ∀ x : E₃,
      R x = !₂[Real.cos θ * x 0 - Real.sin θ * x 1,
        Real.sin θ * x 0 + Real.cos θ * x 1, x 2] := by
  let A : E₃ →ₗ[ℝ] E₃ := Matrix.toEuclideanLin
    !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1]
  have hA (x : E₃) : A x = !₂[Real.cos θ * x 0 - Real.sin θ * x 1,
      Real.sin θ * x 0 + Real.cos θ * x 1, x 2] := by
    ext i
    fin_cases i <;> simp [A, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      dotProduct, Fin.sum_univ_succ, sub_eq_add_neg]
  have hi (x y : E₃) : inner ℝ (A x) (A y) = inner ℝ x y := by
    rw [hA, hA]
    simp [PiLp.inner_apply, Fin.sum_univ_succ]
    linear_combination (x 0 * y 0 + x 1 * y 1) * Real.cos_sq_add_sin_sq θ
  exact ⟨(A.isometryOfInner hi).toLinearIsometryEquiv rfl, hA⟩

/-- Reflection in a plane containing the axis is an orthogonal equivalence. -/
theorem exists_meridional_reflection :
    ∃ R : E₃ ≃ₗᵢ[ℝ] E₃, ∀ x : E₃, R x = !₂[x 0, -x 1, x 2] := by
  let A : E₃ →ₗ[ℝ] E₃ := Matrix.toEuclideanLin (Matrix.diagonal ![1, -1, 1])
  have hA (x : E₃) : A x = !₂[x 0, -x 1, x 2] := by
    ext i
    fin_cases i <;> simp [A, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have hi (x y : E₃) : inner ℝ (A x) (A y) = inner ℝ x y := by
    rw [hA, hA]
    simp [PiLp.inner_apply, Fin.sum_univ_succ]
  exact ⟨(A.isometryOfInner hi).toLinearIsometryEquiv rfl, hA⟩

end ClockBarrier.Geometry
