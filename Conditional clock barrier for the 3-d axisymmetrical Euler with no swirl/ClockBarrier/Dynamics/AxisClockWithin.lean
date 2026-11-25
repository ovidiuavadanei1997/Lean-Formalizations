/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Dynamics.AxisClock
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Axis clock differentiation within a lifespan -/

public section

namespace ClockBarrier.Dynamics

open ClockBarrier.Geometry Filter Set
open scoped Topology

/-- The meridional minor derivative also holds for derivatives within a time set. -/
theorem hasDerivWithinAt_meridional_minor_of_matrix_ode
    {A : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {M : Matrix (Fin 3) (Fin 3) ℝ}
    {s : Set ℝ} {t a c : ℝ}
    (hA : HasDerivWithinAt A (M * A t) s t)
    (hdiag : A t = Matrix.diagonal ![a, a, c])
    (htransverse : M 0 0 = M 1 1) (htrace : M.trace = 0) :
    HasDerivWithinAt (fun r => A r 0 0 * A r 2 2 - A r 0 2 * A r 2 0)
      ((1 / 2 : ℝ) * (a * c) * M 2 2) s t := by
  have he (i j : Fin 3) : HasDerivWithinAt (fun r => A r i j) ((M * A t) i j) s t :=
    hasDerivWithinAt_pi.mp (hasDerivWithinAt_pi.mp hA i) j
  have htr : M 0 0 + (M 0 0 + M 2 2) = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_succ, ← htransverse] using htrace
  have hM : M 0 0 = -(M 2 2) / 2 := by linarith only [htr]
  convert! ((he 0 0).mul (he 2 2)).sub ((he 0 2).mul (he 2 0)) using 1
  simp [hdiag, Matrix.mul_apply, Fin.sum_univ_succ, hM]
  ring

/-- The actual signed meridional Jacobian satisfies the clock equation within its time domain. -/
theorem hasDerivWithinAt_det_fderiv_meridional_of_matrix_ode
    {f : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {A : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {M : Matrix (Fin 3) (Fin 3) ℝ}
    {s : Set ℝ} {t a c z : ℝ} (ht : t ∈ s)
    (hspace : ∀ r ∈ s,
      HasFDerivAt (f r) (Matrix.toEuclideanLin (A r)).toContinuousLinearMap !₂[0, 0, z])
    (htime : HasDerivWithinAt A (M * A t) s t)
    (hdiag : A t = Matrix.diagonal ![a, a, c])
    (htransverse : M 0 0 = M 1 1) (htrace : M.trace = 0) :
    let J : ℝ → ℝ := fun r =>
      (fderiv ℝ
        (fun p : EuclideanSpace ℝ (Fin 2) =>
          (!₂[f r !₂[p 0, 0, p 1] 0, f r !₂[p 0, 0, p 1] 2] : EuclideanSpace ℝ (Fin 2)))
        !₂[0, z]).toLinearMap.det
    HasDerivWithinAt J ((1 / 2 : ℝ) * J t * M 2 2) s t := by
  convert! (hasDerivWithinAt_meridional_minor_of_matrix_ode htime hdiag htransverse htrace).congr_of_mem
    (fun r hr => det_fderiv_meridional_restriction (hspace r hr)) ht using 1
  simp [det_fderiv_meridional_restriction (hspace t ht), hdiag]

end ClockBarrier.Dynamics
