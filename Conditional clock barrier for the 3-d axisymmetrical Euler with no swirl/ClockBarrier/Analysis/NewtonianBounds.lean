/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.NewtonianDerivatives
public import ClockBarrier.Analysis.AxisStrainKernel
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Decay bounds for the regularized Newtonian derivatives -/

public section

namespace ClockBarrier.Analysis

open scoped RealInnerProductSpace

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Polynomial factors are absorbed into half-powers of the regularizing denominator. -/
theorem norm_pow_mul_newtonian_power_le (x : E₃) (n : ℕ) (p : ℝ) :
    ‖x‖ ^ n * (1 + ‖x‖ ^ 2) ^ p ≤ (1 + ‖x‖ ^ 2) ^ ((n : ℝ) / 2 + p) := by
  have hb : ‖x‖ ≤ Real.sqrt (1 + ‖x‖ ^ 2) :=
    Real.le_sqrt_of_sq_le (by linarith)
  calc
    _ ≤ (Real.sqrt (1 + ‖x‖ ^ 2)) ^ n * (1 + ‖x‖ ^ 2) ^ p := by gcongr
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_div_two_eq_sqrt (n : ℝ) (by positivity),
        ← Real.rpow_add (by positivity)]

/-- Each regularized Hessian entry has inverse-cube decay. -/
theorem abs_fderiv_newtonian_gradient_le (i : Fin 3) (x v : E₃) :
    |fderiv ℝ (fun y : E₃ => -(y i * (1 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2))) x v| ≤
      4 * (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) * ‖v‖ := by
  rw [fderiv_newtonian_gradient_apply]
  calc
    _ ≤ |3 * x i * (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) * ⟪x, v⟫| +
        |v i * (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2)| := abs_sub _ _
    _ ≤ 3 * ‖x‖ * (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) * (‖x‖ * ‖v‖) +
        ‖v‖ * (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) := by
      simp only [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3),
        abs_of_nonneg (by positivity : 0 ≤ (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)),
        abs_of_nonneg (by positivity : 0 ≤ (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2))]
      gcongr
      · exact abs_euclidean_coordinate_le_norm x i
      · exact abs_real_inner_le_norm x v
      · exact abs_euclidean_coordinate_le_norm v i
    _ ≤ _ := by
      have hb := norm_pow_mul_newtonian_power_le x 2 (-(5 : ℝ) / 2)
      norm_num at hb
      have hs := mul_le_mul_of_nonneg_right hb (norm_nonneg v)
      nlinarith

/-- Derivatives of regularized Hessian entries have integrable inverse-fourth-power decay. -/
theorem abs_fderiv_newtonian_hessian_le (i : Fin 3) (x v w : E₃) :
    |fderiv ℝ (fun y : E₃ => fderiv ℝ
      (fun a : E₃ => -(a i * (1 + ‖a‖ ^ 2) ^ (-(3 : ℝ) / 2))) y v) x w| ≤
      24 * (1 + ‖x‖ ^ 2) ^ (-2 : ℝ) * ‖v‖ * ‖w‖ := by
  rw [fderiv_newtonian_hessian_apply]
  have hs : |w i * ⟪x, v⟫ + x i * ⟪w, v⟫ + v i * ⟪x, w⟫| ≤
      |w i| * |⟪x, v⟫| + |x i| * |⟪w, v⟫| + |v i| * |⟪x, w⟫| := by
    have h := (abs_add_le (w i * ⟪x, v⟫ + x i * ⟪w, v⟫)
      (v i * ⟪x, w⟫)).trans
        (add_le_add (abs_add_le (w i * ⟪x, v⟫) (x i * ⟪w, v⟫)) le_rfl)
    simpa only [abs_mul] using h
  calc
    _ ≤ 3 * (|w i| * |⟪x, v⟫| + |x i| * |⟪w, v⟫| + |v i| * |⟪x, w⟫|) *
        (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) +
      15 * |x i| * |⟪x, v⟫| * |⟪x, w⟫| * (1 + ‖x‖ ^ 2) ^ (-(7 : ℝ) / 2) := by
      refine (abs_sub _ _).trans ?_
      simp only [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 15),
        abs_of_nonneg (by positivity : 0 ≤ (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)),
        abs_of_nonneg (by positivity : 0 ≤ (1 + ‖x‖ ^ 2) ^ (-(7 : ℝ) / 2))]
      gcongr
    _ ≤ 3 * (‖w‖ * (‖x‖ * ‖v‖) + ‖x‖ * (‖w‖ * ‖v‖) + ‖v‖ * (‖x‖ * ‖w‖)) *
        (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) +
      15 * ‖x‖ * (‖x‖ * ‖v‖) * (‖x‖ * ‖w‖) * (1 + ‖x‖ ^ 2) ^ (-(7 : ℝ) / 2) := by
      gcongr
      all_goals first | exact abs_euclidean_coordinate_le_norm _ _ |
        exact abs_real_inner_le_norm _ _
    _ ≤ _ := by
      have h₁ := norm_pow_mul_newtonian_power_le x 1 (-(5 : ℝ) / 2)
      have h₃ := norm_pow_mul_newtonian_power_le x 3 (-(7 : ℝ) / 2)
      norm_num at h₁ h₃
      have hs₁ := mul_le_mul_of_nonneg_right h₁ (mul_nonneg (norm_nonneg v) (norm_nonneg w))
      have hs₃ := mul_le_mul_of_nonneg_right h₃ (mul_nonneg (norm_nonneg v) (norm_nonneg w))
      norm_num
      nlinarith

/-- Away from zero, the regularized inverse-cube weight is bounded by the singular one. -/
theorem newtonian_hessian_weight_le_inv_cube {x : E₃} (hx : x ≠ 0) :
    (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) ≤ 1 / ‖x‖ ^ 3 := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  calc
    _ ≤ (‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
    _ = _ := by
      rw [← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_mul hr.le]
      norm_num [Real.rpow_neg hr.le]

end ClockBarrier.Analysis
