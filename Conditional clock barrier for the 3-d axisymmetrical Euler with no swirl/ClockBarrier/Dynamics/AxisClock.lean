/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.Meridional
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Axis Jacobian evolution from a matrix variational equation

These are finite-dimensional differentiation results. The equation `A' = M * A`,
trace zero, and equal transverse velocity-gradient entries are explicit inputs.
Deriving these inputs from an Euler solution is not part of this module.
The meridional Jacobian is always an actual derivative determinant, not a new
scalar definition stipulated to satisfy the desired clock equation.
-/

public section

namespace ClockBarrier.Dynamics

open ClockBarrier.Geometry
open scoped Topology

/-- Differentiate the meridional minor along `A' = M A` at an axis-shaped matrix.
Trace zero and equal transverse entries of `M` give the factor one half. -/
theorem hasDerivAt_meridional_minor_of_matrix_ode
    {A : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {M : Matrix (Fin 3) (Fin 3) ℝ} {t a c : ℝ}
    (hA : HasDerivAt A (M * A t) t)
    (hdiag : A t = Matrix.diagonal ![a, a, c])
    (htransverse : M 0 0 = M 1 1) (htrace : M.trace = 0) :
    HasDerivAt (fun s => A s 0 0 * A s 2 2 - A s 0 2 * A s 2 0)
      ((1 / 2 : ℝ) * (a * c) * M 2 2) t := by
  have he (i j : Fin 3) : HasDerivAt (fun s => A s i j) ((M * A t) i j) t :=
    hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i) j
  have htr : M 0 0 + (M 0 0 + M 2 2) = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_succ, ← htransverse] using htrace
  have hM : M 0 0 = -(M 2 2) / 2 := by linarith only [htr]
  convert! ((he 0 0).mul (he 2 2)).sub ((he 0 2).mul (he 2 0)) using 1
  simp [hdiag, Matrix.mul_apply, Fin.sum_univ_succ, hM]
  ring

/-- The actual signed meridional Jacobian obeys the axis clock equation whenever the
Cartesian spatial derivative obeys the matrix variational equation. Spatial differentiability
is required only for times in a neighborhood of the time under consideration. -/
theorem hasDerivAt_det_fderiv_meridional_of_matrix_ode
    {f : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {A : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {M : Matrix (Fin 3) (Fin 3) ℝ}
    {t a c z : ℝ}
    (hspace : ∀ᶠ s in 𝓝 t,
      HasFDerivAt (f s) (Matrix.toEuclideanLin (A s)).toContinuousLinearMap !₂[0, 0, z])
    (htime : HasDerivAt A (M * A t) t)
    (hdiag : A t = Matrix.diagonal ![a, a, c])
    (htransverse : M 0 0 = M 1 1) (htrace : M.trace = 0) :
    let J : ℝ → ℝ := fun s =>
      (fderiv ℝ
        (fun p : EuclideanSpace ℝ (Fin 2) =>
          (!₂[f s !₂[p 0, 0, p 1] 0, f s !₂[p 0, 0, p 1] 2] : EuclideanSpace ℝ (Fin 2)))
        !₂[0, z]).toLinearMap.det
    HasDerivAt J ((1 / 2 : ℝ) * J t * M 2 2) t := by
  convert! (hasDerivAt_meridional_minor_of_matrix_ode htime hdiag htransverse htrace).congr_of_eventuallyEq
    (hspace.mono fun s hs => det_fderiv_meridional_restriction hs) using 1
  simp [det_fderiv_meridional_restriction hspace.self_of_nhds, hdiag]

end ClockBarrier.Dynamics
