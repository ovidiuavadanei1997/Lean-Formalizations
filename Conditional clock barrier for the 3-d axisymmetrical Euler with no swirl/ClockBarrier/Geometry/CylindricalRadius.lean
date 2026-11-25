/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.Meridional
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Positive-radius interpretation of the Cartesian restriction

For a differentiable map with transverse reflection covariance and positive transverse
derivative, the signed first coordinate agrees with the physical cylindrical radius along
a sufficiently short positive radial ray. This is a local statement at each fixed axis label;
it does not assert global angle preservation or construct an Euler flow.
-/

public section

namespace ClockBarrier.Geometry

open Filter Set
open scoped Topology

/-- Reflection covariance preserves the meridional plane `y = 0`. -/
theorem second_coordinate_eq_zero_of_reflection
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {r z : ℝ}
    (hy : Function.Semiconj f
      (Matrix.toEuclideanLin (Matrix.diagonal ![1, -1, 1]))
      (Matrix.toEuclideanLin (Matrix.diagonal ![1, -1, 1]))) :
    f !₂[r, 0, z] 1 = 0 := by
  have hfix : Matrix.toEuclideanLin (Matrix.diagonal ![1, -1, 1]) !₂[r, 0, z] =
      (!₂[r, 0, z] : EuclideanSpace ℝ (Fin 3)) := by
    ext i
    fin_cases i <;> norm_num [Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      Matrix.mulVec_diagonal, Matrix.cons_val_two]
  have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) (hy !₂[r, 0, z])
  norm_num [hfix, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_diagonal] at hcoord
  linarith only [hcoord]

/-- Along a short positive radial ray, the physical cylindrical radius equals the signed
first coordinate. Positivity is derived from the positive transverse derivative. -/
theorem eventually_cylindrical_radius_eq_coordinate
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {A : Matrix (Fin 3) (Fin 3) ℝ} {z : ℝ}
    (hf : HasFDerivAt f (Matrix.toEuclideanLin A).toContinuousLinearMap !₂[0, 0, z])
    (hx : Function.Semiconj f
      (Matrix.toEuclideanLin (Matrix.diagonal ![-1, 1, 1]))
      (Matrix.toEuclideanLin (Matrix.diagonal ![-1, 1, 1])))
    (hy : Function.Semiconj f
      (Matrix.toEuclideanLin (Matrix.diagonal ![1, -1, 1]))
      (Matrix.toEuclideanLin (Matrix.diagonal ![1, -1, 1])))
    (ha : 0 < A 0 0) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      Real.sqrt ((f !₂[r, 0, z] 0) ^ 2 + (f !₂[r, 0, z] 1) ^ 2) = f !₂[r, 0, z] 0 := by
  have hlim := (tendsto_radial_ratios_of_hasFDerivAt hf
    (radial_coordinate_eq_zero_of_reflection hx) ha.ne').1
  have hratio : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < f !₂[r, 0, z] 0 / r :=
    hlim.eventually (Ioi_mem_nhds ha)
  refine (hratio.and self_mem_nhdsWithin).mono fun r hr => ?_
  have hpos : 0 < f !₂[r, 0, z] 0 := (div_pos_iff_of_pos_right hr.2).mp hr.1
  simpa only [second_coordinate_eq_zero_of_reflection hy, zero_pow (by decide : 2 ≠ 0),
    add_zero] using Real.sqrt_sq hpos.le

/-- The physical radius has the same first-order and reciprocal limits as the signed
coordinate when the transverse derivative is positive. -/
theorem tendsto_cylindrical_radius_ratios
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {A : Matrix (Fin 3) (Fin 3) ℝ} {z : ℝ}
    (hf : HasFDerivAt f (Matrix.toEuclideanLin A).toContinuousLinearMap !₂[0, 0, z])
    (hx : Function.Semiconj f
      (Matrix.toEuclideanLin (Matrix.diagonal ![-1, 1, 1]))
      (Matrix.toEuclideanLin (Matrix.diagonal ![-1, 1, 1])))
    (hy : Function.Semiconj f
      (Matrix.toEuclideanLin (Matrix.diagonal ![1, -1, 1]))
      (Matrix.toEuclideanLin (Matrix.diagonal ![1, -1, 1])))
    (ha : 0 < A 0 0) :
    let ρ : ℝ → ℝ := fun r =>
      Real.sqrt ((f !₂[r, 0, z] 0) ^ 2 + (f !₂[r, 0, z] 1) ^ 2)
    Tendsto (fun r => ρ r / r) (𝓝[>] 0) (𝓝 (A 0 0)) ∧
      Tendsto (fun r => r / ρ r) (𝓝[>] 0) (𝓝 (A 0 0)⁻¹) := by
  have heq := eventually_cylindrical_radius_eq_coordinate hf hx hy ha
  have hlim := tendsto_radial_ratios_of_hasFDerivAt hf
    (radial_coordinate_eq_zero_of_reflection hx) ha.ne'
  exact ⟨hlim.1.congr' (heq.mono fun r hr => congrArg (fun x : ℝ => x / r) hr.symm),
    hlim.2.congr' (heq.mono fun r hr => congrArg (fun x : ℝ => r / x) hr.symm)⟩

/-- The reciprocal physical-radius limit equals the actual signed meridional Jacobian at
the axis, for a covariant differentiable map with unit determinant and positive stretch. -/
theorem tendsto_div_cylindrical_radius_det_fderiv
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {A : Matrix (Fin 3) (Fin 3) ℝ} {z : ℝ}
    (hf : HasFDerivAt f (Matrix.toEuclideanLin A).toContinuousLinearMap !₂[0, 0, z])
    (hx : Function.Semiconj f
      (Matrix.toEuclideanLin (Matrix.diagonal ![-1, 1, 1]))
      (Matrix.toEuclideanLin (Matrix.diagonal ![-1, 1, 1])))
    (hy : Function.Semiconj f
      (Matrix.toEuclideanLin (Matrix.diagonal ![1, -1, 1]))
      (Matrix.toEuclideanLin (Matrix.diagonal ![1, -1, 1])))
    (hq : Function.Semiconj f
      (Matrix.toEuclideanLin !![0, -1, 0; 1, 0, 0; 0, 0, 1])
      (Matrix.toEuclideanLin !![0, -1, 0; 1, 0, 0; 0, 0, 1]))
    (hdet : A.det = 1) (ha : 0 < A 0 0) :
    Tendsto (fun r : ℝ =>
      r / Real.sqrt ((f !₂[r, 0, z] 0) ^ 2 + (f !₂[r, 0, z] 1) ^ 2)) (𝓝[>] 0)
      (𝓝 ((fderiv ℝ
        (fun p : EuclideanSpace ℝ (Fin 2) =>
          (!₂[f !₂[p 0, 0, p 1] 0, f !₂[p 0, 0, p 1] 2] : EuclideanSpace ℝ (Fin 2)))
        !₂[0, z]).toLinearMap.det)) := by
  rw [det_fderiv_meridional_eq_inv hf (eq_diagonal_of_hasFDerivAt_axis hf hx hy hq) hdet]
  exact (tendsto_cylindrical_radius_ratios hf hx hy ha).2

end ClockBarrier.Geometry
