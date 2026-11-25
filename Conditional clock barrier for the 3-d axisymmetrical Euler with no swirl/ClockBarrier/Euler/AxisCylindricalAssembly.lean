/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisCylindricalTransport
public import ClockBarrier.Euler.AxisSmoothDecomposition
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
/-! # Axis-driver assembly through the signed cylindrical Cauchy formula -/

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

/-- Return from the projected cylindrical Cauchy formula to the volume integral
used to estimate its near and far pieces. The normalization passes through −3/2. -/
theorem classical_euler_on.deriv_axis_eq_biot_savart_of_cylindrical_cauchy
    (t : ℝ) (ht : t ∈ Ico 0 T) (z : ℝ) :
    let zt := Φ t !₂[0, 0, z] 2
    deriv (fun s : ℝ => u t !₂[0, 0, s] 2) zt =
      -(3 / (4 * Real.pi)) * ∫ y : E₃, (zt - y 2) *
        (y 0 * vorticity (u t) (h.cartesian_partials t ht) y 1 -
          y 1 * vorticity (u t) (h.cartesian_partials t ht) y 0) /
            ‖y - !₂[0, 0, zt]‖ ^ 5 := by
  intro zt
  have hcauchy := (h.axis_strain_cylindrical_cauchy hcont hode hinit haxis t ht z).2
  simp only [← h.vorticity_flow_eq_fderiv_apply hcont hode hinit t ht] at hcauchy
  have he := Analysis.integral_eq_two_pi_mul_cylindrical
    (h.integrable_axis_strain_vorticity_flow hcont hode hinit haxis t ht z)
    (fun R _hr θ Z => h.axis_strain_kernel_flow_rotation hcont hode hinit haxis t ht z R θ Z)
  rw [← h.integral_comp_flow hcont hode hinit ht]
  rw [show (!₂[0, 0, zt] : E₃) = Φ t !₂[0, 0, z] from
    (h.flow_axis_eq hcont hode hinit haxis t ht z).symm]
  rw [he, ← mul_assoc]
  have hnorm : -(3 / (4 * Real.pi)) * (2 * Real.pi) = -(3 / 2 : ℝ) := by
    field_simp
    norm_num
  rw [hnorm, hcauchy]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun Z => ?_))
  refine setIntegral_congr_fun measurableSet_Ioi (fun R hR => ?_)
  rw [h.flow_meridional_radius_eq hcont hode hinit haxis t ht hR Z]
  simp only [h.flow_meridional_second_eq_zero hcont hode hinit haxis t ht R Z,
    zero_mul, sub_zero]
/-- The manuscript's cylindrical Cauchy formula supplies the smooth split,
including the full transition annulus. -/
theorem classical_euler_on.deriv_axis_eq_smooth_near_add_far_of_cylindrical
    (t : ℝ) (ht : t ∈ Ico 0 T) (z : ℝ)
    {χ : E₃ → ℝ} (hχ : Continuous χ) (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1) {L : ℝ} (hL : 0 < L) :
    let zt := Φ t !₂[0, 0, z] 2
    let K := fun y : E₃ => (zt - y 2) *
      (y 0 * vorticity (u t) (h.cartesian_partials t ht) y 1 -
        y 1 * vorticity (u t) (h.cartesian_partials t ht) y 0) / ‖y - !₂[0, 0, zt]‖ ^ 5
    let η := fun y : E₃ => χ (L⁻¹ • (y - !₂[0, 0, zt]))
    deriv (fun s : ℝ => u t !₂[0, 0, s] 2) zt =
      -(3 / (4 * Real.pi)) * (∫ y in {y : E₃ | ‖y - !₂[0, 0, zt]‖ ≤ L}, (1 - η y) * K y) +
      -(3 / (4 * Real.pi)) * ∫ y : E₃, η y * K y := by
  intro zt
  dsimp only
  have hc : Continuous (fun y : E₃ => χ (L⁻¹ • (y - !₂[0, 0, zt]))) :=
    hχ.comp (by fun_prop)
  have hout : ∀ y : E₃, y ∉ {y : E₃ | ‖y - !₂[0, 0, zt]‖ ≤ L} →
      χ (L⁻¹ • (y - !₂[0, 0, zt])) = 1 := fun y hy => houter _ (by
    simpa only [norm_smul, norm_inv, Real.norm_of_nonneg hL.le, div_eq_mul_inv, mul_comm]
      using (one_le_div hL).mpr (le_of_lt (lt_of_not_ge hy)))
  have heq := Analysis.integral_eq_weighted_near_add_far
    (h.integrable_axis_strain_vorticity t ht (haxis t ht) zt) hc.aestronglyMeasurable
    (fun y => hχ₀ _) (fun y => hχ₁ _) hout
  rw [h.deriv_axis_eq_biot_savart_of_cylindrical_cauchy hcont hode hinit haxis t ht z, heq, mul_add]

end ClockBarrier.Euler
