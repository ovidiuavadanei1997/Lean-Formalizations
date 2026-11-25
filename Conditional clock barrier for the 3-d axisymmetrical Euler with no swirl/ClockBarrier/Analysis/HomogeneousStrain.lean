/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.AxisStrainKernel
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-! # The homogeneous coefficients of the axis-strain kernel

The scalar coefficients have degree minus three; their derivatives have degree
minus four. A smooth cutoff will remove their singularity at the origin.
-/

public section

namespace ClockBarrier.Analysis

open scoped RealInnerProductSpace ContDiff

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The derivative of the homogeneous denominator, also at zero. -/
theorem hasFDerivAt_norm_fifth (x : E₃) :
    HasFDerivAt (fun y : E₃ => ‖y‖ ^ 5) ((5 * ‖x‖ ^ 3) • innerSL ℝ x) x := by
  simpa only [show (5 : ℝ) - 2 = 3 by norm_num, Real.rpow_ofNat] using
    hasFDerivAt_norm_rpow x (p := 5) (by norm_num)

/-- Each scalar strain coefficient is smooth away from its pole. -/
theorem contDiffAt_axis_strain_coefficient (i j : Fin 3) {x : E₃} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y : E₃ => y i * y j / ‖y‖ ^ 5) x := by
  exact ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt.mul
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffAt).div
      ((contDiffAt_norm ℝ hx).pow 5) (pow_ne_zero 5 (norm_ne_zero_iff.mpr hx))

/-- Differentiating a degree-minus-three coefficient gives the exact
degree-minus-four kernel used after integration by parts. -/
theorem fderiv_axis_strain_coefficient_apply (i j : Fin 3) {x : E₃}
    (hx : x ≠ 0) (v : E₃) :
    fderiv ℝ (fun y : E₃ => y i * y j / ‖y‖ ^ 5) x v =
      (v i * x j + x i * v j) / ‖x‖ ^ 5 -
        5 * x i * x j * ⟪x, v⟫ / ‖x‖ ^ 7 := by
  have hd := ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.mul
    (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt).mul
      ((hasDerivAt_inv (pow_ne_zero 5 (norm_ne_zero_iff.mpr hx))).comp_hasFDerivAt x
        (hasFDerivAt_norm_fifth x))
  simp only [div_eq_mul_inv] at ⊢
  change HasFDerivAt (fun y : E₃ => y i * y j * (‖y‖ ^ 5)⁻¹) _ x at hd
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, Pi.mul_apply, Function.comp_apply, innerSL_apply_apply]
  field_simp
  change -(x i * x j * 5 * ⟪x, v⟫) + ‖x‖ ^ 2 * (x i * v j + x j * v i) = _
  ring

/-- The derivative of a scalar strain coefficient has inverse-fourth-power
decay, uniformly in its coordinate indices. -/
theorem abs_fderiv_axis_strain_coefficient_le (i j : Fin 3) {x : E₃}
    (hx : x ≠ 0) (v : E₃) :
    |fderiv ℝ (fun y : E₃ => y i * y j / ‖y‖ ^ 5) x v| ≤ 7 * ‖v‖ / ‖x‖ ^ 4 := by
  rw [fderiv_axis_strain_coefficient_apply i j hx v]
  calc
    _ ≤ |(v i * x j + x i * v j) / ‖x‖ ^ 5| +
        |5 * x i * x j * ⟪x, v⟫ / ‖x‖ ^ 7| := abs_sub _ _
    _ ≤ (‖v‖ * ‖x‖ + ‖x‖ * ‖v‖) / ‖x‖ ^ 5 +
        5 * ‖x‖ * ‖x‖ * (‖x‖ * ‖v‖) / ‖x‖ ^ 7 := by
      simp only [abs_div, abs_mul, abs_pow, abs_norm, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5)]
      gcongr
      · refine (abs_add_le _ _).trans ?_
        simpa only [abs_mul] using add_le_add
          (mul_le_mul (abs_euclidean_coordinate_le_norm v i) (abs_euclidean_coordinate_le_norm x j)
            (abs_nonneg _) (norm_nonneg _))
          (mul_le_mul (abs_euclidean_coordinate_le_norm x i) (abs_euclidean_coordinate_le_norm v j)
            (abs_nonneg _) (norm_nonneg _))
      · exact abs_euclidean_coordinate_le_norm x i
      · exact abs_euclidean_coordinate_le_norm x j
      · exact abs_real_inner_le_norm x v
    _ = _ := by
      field_simp
      norm_num

/-- The coefficients themselves have inverse-cube decay. -/
theorem abs_axis_strain_coefficient_le (i j : Fin 3) (x : E₃) :
    |x i * x j / ‖x‖ ^ 5| ≤ 1 / ‖x‖ ^ 3 := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [abs_div, abs_mul, abs_pow, abs_norm]
    refine (div_le_div_of_nonneg_right
      (mul_le_mul (abs_euclidean_coordinate_le_norm x i) (abs_euclidean_coordinate_le_norm x j)
        (abs_nonneg _) (norm_nonneg _)) (pow_nonneg (norm_nonneg x) 5)).trans_eq ?_
    field_simp

end ClockBarrier.Analysis
