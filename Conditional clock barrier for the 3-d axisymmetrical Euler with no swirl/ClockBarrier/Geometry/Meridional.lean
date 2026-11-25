/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.AxisDerivative
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# The derivative and Jacobian of a meridional restriction

The map here is the signed Cartesian restriction `(R,Z) ↦ (f(R,0,Z)₀,f(R,0,Z)₂)`.
Its derivative and determinant are computed from the actual Fréchet derivative of `f`.
Identifying an Euler flow with this restriction and its positive-radius interpretation
requires separate flow arguments.
-/

public section

namespace ClockBarrier.Geometry

/-- Restrict a differentiable Cartesian map to the meridional plane and project its output
onto that plane. Its derivative is the corresponding two by two submatrix. -/
theorem hasFDerivAt_meridional_restriction
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {A : Matrix (Fin 3) (Fin 3) ℝ} {r z : ℝ}
    (hf : HasFDerivAt f (Matrix.toEuclideanLin A).toContinuousLinearMap !₂[r, 0, z]) :
    HasFDerivAt
      (fun p : EuclideanSpace ℝ (Fin 2) =>
        (!₂[f !₂[p 0, 0, p 1] 0, f !₂[p 0, 0, p 1] 2] : EuclideanSpace ℝ (Fin 2)))
      (Matrix.toEuclideanLin !![A 0 0, A 0 2; A 2 0, A 2 2]).toContinuousLinearMap
      !₂[r, z] := by
  let E := (Matrix.toEuclideanLin
    (!![1, 0; 0, 0; 0, 1] : Matrix (Fin 3) (Fin 2) ℝ)).toContinuousLinearMap
  let P := (Matrix.toEuclideanLin
    (!![1, 0, 0; 0, 0, 1] : Matrix (Fin 2) (Fin 3) ℝ)).toContinuousLinearMap
  have hE (p : EuclideanSpace ℝ (Fin 2)) : E p = !₂[p 0, 0, p 1] := by
    ext i
    fin_cases i <;> simp [E, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      dotProduct, Fin.sum_univ_succ]
  have hP (p : EuclideanSpace ℝ (Fin 3)) : P p = !₂[p 0, p 2] := by
    ext i
    fin_cases i <;> simp [P, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      dotProduct, Fin.sum_univ_succ]
  have hfE : HasFDerivAt f (Matrix.toEuclideanLin A).toContinuousLinearMap (E !₂[r, z]) := by
    simpa [hE] using hf
  convert! (P.hasFDerivAt.comp !₂[r, z] (hfE.comp !₂[r, z] E.hasFDerivAt)) using 1
  · simp only [Function.comp_def, hE, hP]
  · ext p i
    fin_cases i <;> simp [ContinuousLinearMap.comp_apply, hE, hP,
      Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The actual Jacobian of the signed meridional restriction is the meridional minor of
the Cartesian derivative. Differentiability prevents a default `fderiv` value from being used. -/
theorem det_fderiv_meridional_restriction
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {A : Matrix (Fin 3) (Fin 3) ℝ} {r z : ℝ}
    (hf : HasFDerivAt f (Matrix.toEuclideanLin A).toContinuousLinearMap !₂[r, 0, z]) :
    (fderiv ℝ
      (fun p : EuclideanSpace ℝ (Fin 2) =>
        (!₂[f !₂[p 0, 0, p 1] 0, f !₂[p 0, 0, p 1] 2] : EuclideanSpace ℝ (Fin 2)))
      !₂[r, z]).toLinearMap.det = A 0 0 * A 2 2 - A 0 2 * A 2 0 := by
  rw [(hasFDerivAt_meridional_restriction hf).fderiv]
  simp [Matrix.toEuclideanLin, Matrix.det_fin_two]

/-- For an axis-shaped derivative with determinant one, the actual signed meridional
Jacobian equals the reciprocal transverse stretch. -/
theorem det_fderiv_meridional_eq_inv
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {A : Matrix (Fin 3) (Fin 3) ℝ} {a c z : ℝ}
    (hf : HasFDerivAt f (Matrix.toEuclideanLin A).toContinuousLinearMap !₂[0, 0, z])
    (hdiag : A = Matrix.diagonal ![a, a, c]) (hdet : A.det = 1) :
    (fderiv ℝ
      (fun p : EuclideanSpace ℝ (Fin 2) =>
        (!₂[f !₂[p 0, 0, p 1] 0, f !₂[p 0, 0, p 1] 2] : EuclideanSpace ℝ (Fin 2)))
      !₂[0, z]).toLinearMap.det = a⁻¹ := by
  simpa [det_fderiv_meridional_restriction hf, hdiag] using
    (axis_entries_of_det_eq_one hdiag hdet).2.2

end ClockBarrier.Geometry
