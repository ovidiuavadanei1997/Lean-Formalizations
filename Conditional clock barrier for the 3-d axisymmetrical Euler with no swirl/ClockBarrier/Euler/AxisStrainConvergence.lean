/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.VorticityRegularity
public import ClockBarrier.Analysis.CurlStrainIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Ring

/-! # Absolute convergence of the actual on-axis Euler strain integral -/

public section

namespace ClockBarrier.Euler

open Set MeasureTheory Geometry
open scoped NNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The signed Cartesian integral in the on-axis Biot–Savart formula is absolutely
convergent under the Euler regularity and no-swirl symmetry alone. -/
theorem classical_euler_on.integrable_axis_strain_vorticity
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (t : ℝ) (ht : t ∈ Ico 0 T)
    (haxis : axisymmetric_no_swirl (u t)) (z : ℝ) :
    Integrable (fun y => (z - y 2) *
      (y 0 * vorticity (u t) (h.cartesian_partials t ht) y 1 -
        y 1 * vorticity (u t) (h.cartesian_partials t ht) y 0) /
          ‖y - !₂[0, 0, z]‖ ^ 5) volume := by
  obtain ⟨D, _, hd, hHolder⟩ := h.2.2.2.2.1
  obtain ⟨H, hH⟩ := hHolder t ht
  have hD : HolderWith H α (fderiv ℝ (u t)) := by
    have heq : fderiv ℝ (u t) = D t := funext (fun x => (hd t ht x).fderiv)
    rw [heq]
    exact hH t ⟨ht.1, le_rfl⟩
  have hL2 := h.2.2.2.2.2.1 t ht
  have hi := Analysis.integrable_axis_strain_curl_fderiv_sub
    (fun x => (hd t ht x).differentiableAt) h.2.1 hD
    ((memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).mp hL2)
    !₂[0, 0, z] (h.curl_axis_eq_zero ht haxis z)
  apply hi.neg.congr
  filter_upwards with x
  simp only [Pi.neg_apply, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, sub_zero,
    h.vorticity_eq_curlLinearMap t ht]
  ring

end ClockBarrier.Euler
