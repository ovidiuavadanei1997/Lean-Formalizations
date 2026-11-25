/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.AxisDerivative
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Transverse symmetries from the cylindrical no-swirl formula -/

public section

namespace ClockBarrier.Geometry

/-- Every Cartesian point has cylindrical coordinates, including points on the axis. -/
theorem exists_cylindrical_coordinates (x : EuclideanSpace ℝ (Fin 3)) :
    ∃ r θ z : ℝ, 0 ≤ r ∧ x = !₂[r * Real.cos θ, r * Real.sin θ, z] := by
  refine ⟨‖(⟨x 0, x 1⟩ : ℂ)‖, Complex.arg ⟨x 0, x 1⟩, x 2, norm_nonneg _, ?_⟩
  simp only [Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg]
  ext i
  fin_cases i <;> rfl

/-- An angular action preserving the cylindrical formula is a symmetry of the field. -/
theorem semiconj_of_cylindrical_representation
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {v w : ℝ → ℝ → ℝ} {R : Matrix (Fin 3) (Fin 3) ℝ} {τ : ℝ → ℝ}
    (hf : ∀ r : ℝ, 0 ≤ r → ∀ θ z : ℝ,
      f !₂[r * Real.cos θ, r * Real.sin θ, z] =
        !₂[v r z * Real.cos θ, v r z * Real.sin θ, w r z])
    (hR : ∀ r θ z : ℝ,
      Matrix.toEuclideanLin R !₂[r * Real.cos θ, r * Real.sin θ, z] =
        !₂[r * Real.cos (τ θ), r * Real.sin (τ θ), z]) :
    Function.Semiconj f (Matrix.toEuclideanLin R) (Matrix.toEuclideanLin R) := by
  intro x
  obtain ⟨r, θ, z, hr, rfl⟩ := exists_cylindrical_coordinates x
  rw [hR, hf r hr, hf r hr, hR]

/-- Axisymmetry without swirl gives both transverse reflections and a quarter-turn. -/
theorem transverse_symmetries_of_cylindrical_representation
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {v w : ℝ → ℝ → ℝ}
    (hf : ∀ r : ℝ, 0 ≤ r → ∀ θ z : ℝ,
      f !₂[r * Real.cos θ, r * Real.sin θ, z] =
        !₂[v r z * Real.cos θ, v r z * Real.sin θ, w r z]) :
    Function.Semiconj f
      (Matrix.toEuclideanLin (Matrix.diagonal ![-1, 1, 1]))
      (Matrix.toEuclideanLin (Matrix.diagonal ![-1, 1, 1])) ∧
    Function.Semiconj f
      (Matrix.toEuclideanLin (Matrix.diagonal ![1, -1, 1]))
      (Matrix.toEuclideanLin (Matrix.diagonal ![1, -1, 1])) ∧
    Function.Semiconj f
      (Matrix.toEuclideanLin !![0, -1, 0; 1, 0, 0; 0, 0, 1])
      (Matrix.toEuclideanLin !![0, -1, 0; 1, 0, 0; 0, 0, 1]) := by
  refine ⟨semiconj_of_cylindrical_representation (τ := fun θ => Real.pi - θ) hf ?_,
    semiconj_of_cylindrical_representation (τ := fun θ => -θ) hf ?_,
    semiconj_of_cylindrical_representation (τ := fun θ => θ + Real.pi / 2) hf ?_⟩
  all_goals intro r θ z
  all_goals ext i
  all_goals fin_cases i <;> simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Real.cos_add, Real.sin_add]

end ClockBarrier.Geometry
