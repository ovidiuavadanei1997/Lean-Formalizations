/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.SmoothProjectedEquation
public import ClockBarrier.Analysis.SmoothAdvectionDivergence
public import ClockBarrier.Analysis.SmoothPressureInterpolation

/-! # The bounded divergence of smooth Euler pressure gradients -/
public section
namespace ClockBarrier.Euler.Smooth
open MeasureTheory ClockBarrier.Analysis SmoothL2Field Solenoidal Sobolev
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem pressureForce_divergence (A : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) (x : Space) :
    (∑ i : Fin 3, fderiv ℝ (pressureForce A).field x (EuclideanSpace.single i 1) i) =
      -(∑ i : Fin 3, fderiv ℝ A.field x
        (fderiv ℝ A.field x (EuclideanSpace.single i 1)) i) := by
  have he : (pressureForce A).field = fun y =>
      (solenoidalField (advectionField A A)).field y - (advectionField A A).field y := by
    funext y
    rw [pressureForce, fieldSub_field]
  rw [he, fderiv_fun_sub
    ((solenoidalField (advectionField A A)).smooth.differentiable (by simp) x)
    ((advectionField A A).smooth.differentiable (by simp) x)]
  simp only [sub_apply, PiLp.sub_apply, Finset.sum_sub_distrib]
  have hp := solenoidal_divergence (solenoidalField (advectionField A A))
    (by rw [solenoidalField_toLp]; exact solenoidalProjection_mem _) x
  rw [hp, zero_sub]
  congr 1
  have ha : (advectionField A A).field = fun y => fderiv ℝ A.field y (A.field y) :=
    funext (advectionField_field A A)
  rw [ha]
  exact divergence_advection_eq_quadratic A.smooth (solenoidal_divergence A hA) x

theorem abs_pressureForce_divergence_le (A : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) {R : ℝ} (hR : ‖finiteField A.derivative‖ ≤ R)
    (x : Space) :
    |∑ i : Fin 3, fderiv ℝ (pressureForce A).field x (EuclideanSpace.single i 1) i| ≤
      3 * R ^ 2 := by
  rw [pressureForce_divergence A hA x, abs_neg]
  have hDx : ‖fderiv ℝ A.field x‖ ≤ R := by
    convert! ((finiteField A.derivative).norm_coe_le_norm x).trans hR using 1
    rw [finiteField_apply]
    rfl
  exact (abs_sum_diagonal_square_le (fderiv ℝ A.field x)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hDx 2) (by norm_num))

theorem abs_pressureForce_difference_divergence_le (A D : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) (hD : D.toLp ∈ solenoidalSpace)
    {R : ℝ} (hRA : ‖finiteField A.derivative‖ ≤ R) (hRD : ‖finiteField D.derivative‖ ≤ R)
    (x : Space) :
    |∑ i : Fin 3, fderiv ℝ (fieldSub (pressureForce A) (pressureForce D)).field x
      (EuclideanSpace.single i 1) i| ≤ 6 * R ^ 2 := by
  have he : (fieldSub (pressureForce A) (pressureForce D)).field =
      fun y => (pressureForce A).field y - (pressureForce D).field y :=
    funext (fieldSub_field _ _)
  rw [he, fderiv_fun_sub ((pressureForce A).smooth.differentiable (by simp) x)
    ((pressureForce D).smooth.differentiable (by simp) x)]
  simp only [sub_apply, PiLp.sub_apply, Finset.sum_sub_distrib]
  calc
    _ ≤ |∑ i : Fin 3, fderiv ℝ (pressureForce A).field x (EuclideanSpace.single i 1) i| +
        |∑ i : Fin 3, fderiv ℝ (pressureForce D).field x (EuclideanSpace.single i 1) i| :=
      abs_sub _ _
    _ ≤ 3 * R ^ 2 + 3 * R ^ 2 := add_le_add
      (abs_pressureForce_divergence_le A hA hRA x) (abs_pressureForce_divergence_le D hD hRD x)
    _ = _ := by ring

theorem exists_pressureForce_difference_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ A D : SmoothL2Field Space,
      A.toLp ∈ solenoidalSpace → D.toLp ∈ solenoidalSpace →
      ∀ R : ℝ, ‖finiteField A.derivative‖ ≤ R → ‖finiteField D.derivative‖ ≤ R →
      ∀ r : ℝ, 0 < r →
        ‖finiteField (pressureForce A) - finiteField (pressureForce D)‖ ≤
          C * (r * (6 * R ^ 2) + r ^ (-(3 : ℝ) / 2) *
            ‖(pressureForce A).toLp - (pressureForce D).toLp‖) := by
  obtain ⟨C, hC, hb⟩ := exists_smooth_gradient_interpolation_constant
  refine ⟨C, hC, ?_⟩
  intro A D hA hD R hRA hRD r hr
  have hgrad : (fieldSub (pressureForce A) (pressureForce D)).toLp ∈ gradientSpace := by
    rw [toLp_fieldSub]
    exact gradientSpace.sub_mem (pressureForce_gradient A) (pressureForce_gradient D)
  have he : finiteField (fieldSub (pressureForce A) (pressureForce D)) =
      finiteField (pressureForce A) - finiteField (pressureForce D) := by
    ext x
    simp only [finiteField_apply, fieldSub_field, BoundedContinuousFunction.sub_apply]
  simpa only [he, toLp_fieldSub] using hb (fieldSub (pressureForce A) (pressureForce D))
    hgrad (6 * R ^ 2) (abs_pressureForce_difference_divergence_le A D hA hD hRA hRD) r hr

end ClockBarrier.Euler.Smooth
