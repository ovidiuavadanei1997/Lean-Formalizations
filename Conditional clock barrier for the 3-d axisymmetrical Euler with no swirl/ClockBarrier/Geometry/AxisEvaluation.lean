/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.EuclideanMatrix
public import ClockBarrier.Geometry.CylindricalRadius
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Actual derivatives and values along the Cartesian axis -/

public section

namespace ClockBarrier.Geometry

/-- The standard matrix of an actual derivative represents that same derivative. -/
theorem hasFDerivAt_euclideanMatrix_fderiv
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {x : EuclideanSpace ℝ (Fin 3)} (hf : DifferentiableAt ℝ f x) :
    HasFDerivAt f (Matrix.toEuclideanLin (euclideanMatrix (fderiv ℝ f x))).toContinuousLinearMap x := by
  convert! hf.hasFDerivAt using 1
  exact (LinearMap.toContinuousLinearMap_eq_iff_eq_toLinearMap _ _).mpr
    (toEuclideanLin_euclideanMatrix _)

/-- The two transverse reflection symmetries preserve the Cartesian axis. -/
theorem map_axis_of_transverse_reflections
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {z : ℝ}
    (hx : Function.Semiconj f
      (Matrix.toEuclideanLin (Matrix.diagonal ![-1, 1, 1]))
      (Matrix.toEuclideanLin (Matrix.diagonal ![-1, 1, 1])))
    (hy : Function.Semiconj f
      (Matrix.toEuclideanLin (Matrix.diagonal ![1, -1, 1]))
      (Matrix.toEuclideanLin (Matrix.diagonal ![1, -1, 1]))) :
    f !₂[0, 0, z] = !₂[0, 0, f !₂[0, 0, z] 2] := by
  ext i
  fin_cases i <;> simp [radial_coordinate_eq_zero_of_reflection hx,
    second_coordinate_eq_zero_of_reflection hy]

/-- The axial scalar derivative is the axial entry of the actual Cartesian derivative. -/
theorem hasDerivAt_axial_coordinate
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {A : Matrix (Fin 3) (Fin 3) ℝ} {z : ℝ}
    (hf : HasFDerivAt f (Matrix.toEuclideanLin A).toContinuousLinearMap !₂[0, 0, z]) :
    HasDerivAt (fun r : ℝ => f !₂[0, 0, r] 2) (A 2 2) z := by
  have hline : HasDerivAt (fun r : ℝ => (!₂[0, 0, r] : EuclideanSpace ℝ (Fin 3)))
      !₂[0, 0, 1] z := by
    convert! (hasDerivAt_id z).smul_const (!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)) using 1
    all_goals simp [funext_iff, WithLp.ext_iff]
  convert! ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).hasFDerivAt.comp
    !₂[0, 0, z] hf).comp_hasDerivAt z hline using 1
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]

end ClockBarrier.Geometry
