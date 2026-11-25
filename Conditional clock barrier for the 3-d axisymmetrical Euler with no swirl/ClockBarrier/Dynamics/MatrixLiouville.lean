/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.AxisDerivative
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.Ring

/-!
# Liouville's determinant identity in three dimensions

The derivative of the determinant follows by polynomial differentiation,
without assuming invertibility of the evolving matrix.
-/

public section

namespace ClockBarrier.Dynamics

open Set

/-- A three-dimensional matrix solution of `A' = M A` satisfies Liouville's identity. -/
theorem hasDerivWithinAt_det_of_matrix_ode
    {A : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {M : Matrix (Fin 3) (Fin 3) ℝ}
    {s : Set ℝ} {t : ℝ} (hA : HasDerivWithinAt A (M * A t) s t) :
    HasDerivWithinAt (fun r => (A r).det) (M.trace * (A t).det) s t := by
  have he (i j : Fin 3) : HasDerivWithinAt (fun r => A r i j) ((M * A t) i j) s t :=
    hasDerivWithinAt_pi.mp (hasDerivWithinAt_pi.mp hA i) j
  simp only [Matrix.det_fin_three]
  convert! ((((((he 0 0).mul (he 1 1)).mul (he 2 2)).sub
    (((he 0 0).mul (he 1 2)).mul (he 2 1))).sub
    (((he 0 1).mul (he 1 0)).mul (he 2 2))).add
    (((he 0 1).mul (he 1 2)).mul (he 2 0))).add
    (((he 0 2).mul (he 1 0)).mul (he 2 1)) |>.sub
    (((he 0 2).mul (he 1 1)).mul (he 2 0)) using 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ,
    Fin.sum_univ_zero, add_zero, Pi.mul_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  ring

/-- Trace-free matrix evolution preserves the determinant on a closed time interval. -/
theorem det_eq_of_matrix_ode_trace_zero
    {A M : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {a b : ℝ}
    (hcont : ContinuousOn A (Icc a b))
    (hode : ∀ t ∈ Ico a b, HasDerivWithinAt A (M t * A t) (Ici t) t)
    (htrace : ∀ t ∈ Ico a b, (M t).trace = 0) :
    ∀ t ∈ Icc a b, (A t).det = (A a).det := by
  apply constant_of_has_deriv_right_zero (continuous_id.matrix_det.comp_continuousOn hcont)
  intro t ht
  convert! hasDerivWithinAt_det_of_matrix_ode (hode t ht) using 1
  simp only [htrace t ht, zero_mul]

end ClockBarrier.Dynamics
