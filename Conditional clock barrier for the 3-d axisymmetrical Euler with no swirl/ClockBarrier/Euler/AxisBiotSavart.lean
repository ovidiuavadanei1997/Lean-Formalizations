/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisStrainConvergence
public import ClockBarrier.Analysis.AxisBiotSavart
public import ClockBarrier.Geometry.AxisEvaluation
import ClockBarrier.Euler.AxisFlow
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! # The normalized signed on-axis Biot–Savart representation for Euler solutions -/

public section

namespace ClockBarrier.Euler

open Set MeasureTheory Geometry
open scoped NNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The actual axial derivative has the signed Cartesian Biot–Savart representation.
The integral is absolutely convergent by `integrable_axis_strain_vorticity`. -/
theorem classical_euler_on.fderiv_axis_eq_biot_savart
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (t : ℝ) (ht : t ∈ Ico 0 T)
    (haxis : axisymmetric_no_swirl (u t)) (z : ℝ) :
    fderiv ℝ (u t) !₂[0, 0, z] (EuclideanSpace.single 2 1) 2 =
      -(3 / (4 * Real.pi)) * ∫ y : E₃, (z - y 2) *
        (y 0 * vorticity (u t) (h.cartesian_partials t ht) y 1 -
          y 1 * vorticity (u t) (h.cartesian_partials t ht) y 0) /
            ‖y - !₂[0, 0, z]‖ ^ 5 := by
  obtain ⟨D, _, hd, hHolder⟩ := h.2.2.2.2.1
  obtain ⟨H, hH⟩ := hHolder t ht
  have hD : HolderWith H α (fderiv ℝ (u t)) := by
    have heq : fderiv ℝ (u t) = D t := funext (fun x => (hd t ht x).fderiv)
    rw [heq]
    exact hH t ⟨ht.1, le_rfl⟩
  have hL2 := h.2.2.2.2.2.1 t ht
  have hdiv (x : E₃) : ∑ i : Fin 3,
      fderiv ℝ (u t) x (EuclideanSpace.single i 1) i = 0 := by
    have htr := h.velocity_regular.2.2.2.2 t ht x
    simpa [LinearMap.trace_eq_matrix_trace ℝ (PiLp.basisFun 2 ℝ (Fin 3)),
      Matrix.trace, LinearMap.toMatrix_apply] using htr
  have hid := Analysis.axis_strain_eq_biot_savart_sub
    (fun x => (hd t ht x).differentiableAt) h.2.1 hD
    ((memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).mp hL2)
    (fun x => (u t).norm_coe_le_norm x)
    (fun x => by rw [(hd t ht x).fderiv]; exact (D t).norm_coe_le_norm x)
    hdiv !₂[0, 0, z] (h.curl_axis_eq_zero ht haxis z)
  rw [hid]
  rw [neg_mul, ← mul_neg, ← integral_neg]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  simp only [PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, sub_zero, h.vorticity_eq_curlLinearMap t ht]
  ring

/-- The paper's scalar on-axis driver has coefficient `-3 / (4π)` for the
right-handed Cartesian curl and the numerator `z - y₂`. -/
theorem classical_euler_on.deriv_axis_eq_biot_savart
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (t : ℝ) (ht : t ∈ Ico 0 T)
    (haxis : axisymmetric_no_swirl (u t)) (z : ℝ) :
    deriv (fun s : ℝ => u t !₂[0, 0, s] 2) z =
      -(3 / (4 * Real.pi)) * ∫ y : E₃, (z - y 2) *
        (y 0 * vorticity (u t) (h.cartesian_partials t ht) y 1 -
          y 1 * vorticity (u t) (h.cartesian_partials t ht) y 0) /
            ‖y - !₂[0, 0, z]‖ ^ 5 := by
  have hd := hasDerivAt_axial_coordinate
    (hasFDerivAt_euclideanMatrix_fderiv (h.velocity_regular.2.1 t ht !₂[0, 0, z]))
  rw [hd.deriv]
  exact h.fderiv_axis_eq_biot_savart t ht haxis z

end ClockBarrier.Euler
