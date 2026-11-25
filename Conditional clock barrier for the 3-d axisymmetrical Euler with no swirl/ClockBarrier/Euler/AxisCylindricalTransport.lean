/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisCylindricalBiotSavart
public import ClockBarrier.Euler.AxisLagrangianBiotSavart
public import ClockBarrier.Euler.FlowCylindrical
import Mathlib.Tactic.FieldSimp

/-! # Cylindrical label-space Biot–Savart and Cauchy transport

The label radius is positive and the measure is `R dR dZ`. The flow's first
coordinate on this ray is its positive physical radius. Cauchy's vector identity
is projected onto Cartesian component one, the azimuthal component on this ray.
-/

public section

namespace ClockBarrier.Euler

open Set MeasureTheory Geometry
open scoped NNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
  (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
  (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
  (hode : ∀ x, ∀ t ∈ Ico 0 T,
    HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
  (hinit : ∀ x, Φ 0 x = x)
  (haxis : ∀ t ∈ Ico 0 T, axisymmetric_no_swirl (u t))

include h hcont hode hinit haxis

/-- The pulled-back signed kernel is independent of the label angle. -/
theorem classical_euler_on.axis_strain_kernel_flow_rotation
    (t : ℝ) (ht : t ∈ Ico 0 T) (z : ℝ) :
    let K : E₃ → ℝ := fun y => (Φ t !₂[0, 0, z] 2 - y 2) *
      (y 0 * vorticity (u t) (h.cartesian_partials t ht) y 1 -
        y 1 * vorticity (u t) (h.cartesian_partials t ht) y 0) / ‖y - Φ t !₂[0, 0, z]‖ ^ 5
    ∀ R θ Z : ℝ, K (Φ t !₂[R * Real.cos θ, R * Real.sin θ, Z]) = K (Φ t !₂[R, 0, Z]) := by
  intro K
  have hK (r θ Z : ℝ) : K !₂[r * Real.cos θ, r * Real.sin θ, Z] = K !₂[r, 0, Z] := by
    simpa only [K, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, zero_mul, sub_zero,
      ← h.flow_axis_eq hcont hode hinit haxis t ht z] using
      h.axis_strain_kernel_cylindrical t ht (haxis t ht) r θ Z (Φ t !₂[0, 0, z] 2)
  exact cylindrical_invariant_comp_of_semiconj hK
    (h.rotation_semiconj_flow hcont hode hinit haxis t ht)

/-- Absolute convergence in cylindrical label coordinates, with physical radius
in the kernel and label radius in the measure. -/
theorem classical_euler_on.integrableOn_axis_strain_cylindrical_flow
    (t : ℝ) (ht : t ∈ Ico 0 T) (z : ℝ) :
    IntegrableOn (fun q : ℝ × ℝ => q.2 *
      ((Φ t !₂[0, 0, z] 2 - Φ t !₂[q.2, 0, q.1] 2) *
        (Real.sqrt ((Φ t !₂[q.2, 0, q.1] 0)^2 + (Φ t !₂[q.2, 0, q.1] 1)^2) *
          vorticity (u t) (h.cartesian_partials t ht) (Φ t !₂[q.2, 0, q.1]) 1) /
            ‖Φ t !₂[q.2, 0, q.1] - Φ t !₂[0, 0, z]‖ ^ 5))
      (univ ×ˢ Ioi (0 : ℝ)) := by
  have hΦ := (h.contDiff_bijective_measurePreserving_flow hcont hode hinit ht).1.continuous
  have hω := h.continuous_vorticity t ht
  have hi := Analysis.integrableOn_cylindrical_of_integrable
    (f := fun a : E₃ => (Φ t !₂[0, 0, z] 2 - Φ t a 2) *
      (Φ t a 0 * vorticity (u t) (h.cartesian_partials t ht) (Φ t a) 1 -
        Φ t a 1 * vorticity (u t) (h.cartesian_partials t ht) (Φ t a) 0) /
          ‖Φ t a - Φ t !₂[0, 0, z]‖ ^ 5)
    (by fun_prop) (h.integrable_axis_strain_vorticity_flow hcont hode hinit haxis t ht z)
    (fun R _hr θ Z => h.axis_strain_kernel_flow_rotation hcont hode hinit haxis t ht z R θ Z)
  refine hi.congr_fun (fun q hq => ?_) (MeasurableSet.univ.prod measurableSet_Ioi)
  rw [h.flow_meridional_radius_eq hcont hode hinit haxis t ht hq.2 q.1]
  simp only [h.flow_meridional_second_eq_zero hcont hode hinit haxis t ht q.2 q.1,
    zero_mul, sub_zero]

/-- The signed cylindrical formula over labels uses physical radius in the kernel
and the initial radius `R` as its Jacobian weight. -/
theorem classical_euler_on.deriv_axis_eq_cylindrical_biot_savart_flow
    (t : ℝ) (ht : t ∈ Ico 0 T) (z : ℝ) :
    deriv (fun s : ℝ => u t !₂[0, 0, s] 2) (Φ t !₂[0, 0, z] 2) =
      -(3 / 2 : ℝ) * ∫ Z : ℝ, ∫ R in Ioi (0 : ℝ), R *
        ((Φ t !₂[0, 0, z] 2 - Φ t !₂[R, 0, Z] 2) *
          (Real.sqrt ((Φ t !₂[R, 0, Z] 0)^2 + (Φ t !₂[R, 0, Z] 1)^2) *
            vorticity (u t) (h.cartesian_partials t ht) (Φ t !₂[R, 0, Z]) 1) /
              ‖Φ t !₂[R, 0, Z] - Φ t !₂[0, 0, z]‖ ^ 5) := by
  have he := Analysis.integral_eq_two_pi_mul_cylindrical
    (h.integrable_axis_strain_vorticity_flow hcont hode hinit haxis t ht z)
    (fun R _hr θ Z => h.axis_strain_kernel_flow_rotation hcont hode hinit haxis t ht z R θ Z)
  rw [h.deriv_axis_eq_biot_savart_flow hcont hode hinit haxis t ht z, he, ← mul_assoc]
  congr 1
  · field_simp
    norm_num
  · refine integral_congr_ae (Filter.Eventually.of_forall (fun Z => ?_))
    refine setIntegral_congr_fun measurableSet_Ioi (fun R hR => ?_)
    rw [h.flow_meridional_radius_eq hcont hode hinit haxis t ht hR Z]
    simp only [h.flow_meridional_second_eq_zero hcont hode hinit haxis t ht R Z,
      zero_mul, sub_zero]

/-- The cylindrical label formula with the actual Cauchy transport substituted.
The vector `DΦ · ω₀` is explicitly projected onto its azimuthal component. -/
theorem classical_euler_on.axis_strain_cylindrical_cauchy
    (t : ℝ) (ht : t ∈ Ico 0 T) (z : ℝ) :
    IntegrableOn (fun q : ℝ × ℝ => q.2 *
      ((Φ t !₂[0, 0, z] 2 - Φ t !₂[q.2, 0, q.1] 2) *
        (Real.sqrt ((Φ t !₂[q.2, 0, q.1] 0)^2 + (Φ t !₂[q.2, 0, q.1] 1)^2) *
          (fderiv ℝ (Φ t) !₂[q.2, 0, q.1]
            (vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩) !₂[q.2, 0, q.1])) 1) /
            ‖Φ t !₂[q.2, 0, q.1] - Φ t !₂[0, 0, z]‖ ^ 5))
      (univ ×ˢ Ioi (0 : ℝ)) ∧
    deriv (fun s : ℝ => u t !₂[0, 0, s] 2) (Φ t !₂[0, 0, z] 2) =
      -(3 / 2 : ℝ) * ∫ Z : ℝ, ∫ R in Ioi (0 : ℝ), R *
        ((Φ t !₂[0, 0, z] 2 - Φ t !₂[R, 0, Z] 2) *
          (Real.sqrt ((Φ t !₂[R, 0, Z] 0)^2 + (Φ t !₂[R, 0, Z] 1)^2) *
            (fderiv ℝ (Φ t) !₂[R, 0, Z]
            (vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩) !₂[R, 0, Z])) 1) /
              ‖Φ t !₂[R, 0, Z] - Φ t !₂[0, 0, z]‖ ^ 5) := by
  simpa only [h.vorticity_flow_eq_fderiv_apply hcont hode hinit t ht] using
    And.intro (h.integrableOn_axis_strain_cylindrical_flow hcont hode hinit haxis t ht z)
      (h.deriv_axis_eq_cylindrical_biot_savart_flow hcont hode hinit haxis t ht z)

end ClockBarrier.Euler
