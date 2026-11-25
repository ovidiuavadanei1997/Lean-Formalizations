/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisBiotSavart
public import ClockBarrier.Analysis.CylindricalIntegral
import ClockBarrier.Geometry.CylindricalCurl
import ClockBarrier.Euler.AxisFlow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The absolutely convergent cylindrical on-axis Biot–Savart formula

The azimuthal vorticity at `(r, z)` is the second Cartesian curl component at
`(r, 0, z)`. Angular integration converts `-3 / (4 * π)` to `-3 / 2`.
The positive-radius meridional integral retains its Jacobian factor `r`.
-/

public section

namespace ClockBarrier.Euler

open Set MeasureTheory Geometry
open scoped NNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
  (h : classical_euler_on α T u p) (t : ℝ) (ht : t ∈ Ico 0 T)
  (haxis : axisymmetric_no_swirl (u t))

include haxis

/-- The signed Cartesian kernel is independent of the cylindrical angle. -/
theorem classical_euler_on.axis_strain_kernel_cylindrical (r θ ζ z : ℝ) :
    (z - ζ) *
      ((r * Real.cos θ) *
          vorticity (u t) (h.cartesian_partials t ht) !₂[r * Real.cos θ, r * Real.sin θ, ζ] 1 -
        (r * Real.sin θ) *
          vorticity (u t) (h.cartesian_partials t ht) !₂[r * Real.cos θ, r * Real.sin θ, ζ] 0) /
        ‖(!₂[r * Real.cos θ, r * Real.sin θ, ζ] : E₃) - !₂[0, 0, z]‖ ^ 5 =
      (z - ζ) * (r * vorticity (u t) (h.cartesian_partials t ht) !₂[r, 0, ζ] 1) /
        ‖(!₂[r, 0, ζ] : E₃) - !₂[0, 0, z]‖ ^ 5 := by
  obtain ⟨v, w, hrep⟩ := haxis
  simp only [h.vorticity_eq_curlLinearMap t ht, norm_cylindrical_sub_axis,
    axis_curl_numerator_cylindrical (h.velocity_regular.2.1 t ht) hrep]

/-- The cylindrical kernel, including its radial Jacobian, is jointly absolutely
integrable on all heights and positive radii. -/
theorem classical_euler_on.integrableOn_axis_strain_cylindrical (z : ℝ) :
    IntegrableOn (fun q : ℝ × ℝ => q.2 *
      ((z - q.1) * (q.2 * vorticity (u t) (h.cartesian_partials t ht) !₂[q.2, 0, q.1] 1) /
        ‖(!₂[q.2, 0, q.1] : E₃) - !₂[0, 0, z]‖ ^ 5))
      (univ ×ˢ Ioi (0 : ℝ)) := by
  have hrot (r : ℝ) (_hr : 0 < r) (θ ζ : ℝ) :=
    h.axis_strain_kernel_cylindrical t ht haxis r θ ζ z
  have hω := h.continuous_vorticity t ht
  have hi := Analysis.integrableOn_cylindrical_of_integrable
    (f := fun y : E₃ => (z - y 2) *
      (y 0 * vorticity (u t) (h.cartesian_partials t ht) y 1 -
        y 1 * vorticity (u t) (h.cartesian_partials t ht) y 0) / ‖y - !₂[0, 0, z]‖ ^ 5)
    (by fun_prop) (h.integrable_axis_strain_vorticity t ht haxis z)
    (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, zero_mul, sub_zero] using hrot)
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, zero_mul, sub_zero] using hi

/-- The signed cylindrical on-axis formula has coefficient `-3 / 2`, positive
radius, and radial measure `r dr`. Absolute convergence is proved separately above. -/
theorem classical_euler_on.deriv_axis_eq_cylindrical_biot_savart (z : ℝ) :
    deriv (fun s : ℝ => u t !₂[0, 0, s] 2) z =
      -(3 / 2 : ℝ) * ∫ ζ : ℝ, ∫ r in Ioi (0 : ℝ), r *
        ((z - ζ) * (r * vorticity (u t) (h.cartesian_partials t ht) !₂[r, 0, ζ] 1) /
          ‖(!₂[r, 0, ζ] : E₃) - !₂[0, 0, z]‖ ^ 5) := by
  rw [h.deriv_axis_eq_biot_savart t ht haxis z]
  have he := Analysis.integral_eq_two_pi_mul_cylindrical
    (h.integrable_axis_strain_vorticity t ht haxis z)
    (fun r _hr θ ζ => by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, zero_mul, sub_zero]
      using h.axis_strain_kernel_cylindrical t ht haxis r θ ζ z)
  rw [he, ← mul_assoc]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, zero_mul, sub_zero]
  congr 1
  field_simp
  norm_num

end ClockBarrier.Euler
