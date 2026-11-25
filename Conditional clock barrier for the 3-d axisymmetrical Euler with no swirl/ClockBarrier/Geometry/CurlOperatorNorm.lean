/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.DirectionalStrainKernel
public import ClockBarrier.Geometry.CurlLinear
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic.FinCases

/-! # Controlling an operator by quadratic forms and curl

Polarization bounds its symmetric part. The Cartesian curl gives the exact
antisymmetric bilinear form. The resulting estimate also applies to differences
of two derivative operators.
-/

public section
open scoped InnerProductSpace
namespace ClockBarrier.Geometry
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The antisymmetric bilinear form is the curl paired with a cross product. -/
theorem inner_apply_sub_inner_apply_eq_curl (A : E₃ →L[ℝ] E₃) (x y : E₃) :
    ⟪y, A x⟫_ℝ - ⟪x, A y⟫_ℝ =
      ⟪curlLinearMap A, (!₂[x 1 * y 2 - x 2 * y 1, x 2 * y 0 - x 0 * y 2,
        x 0 * y 1 - x 1 * y 0] : E₃)⟫_ℝ := by
  have ha (z : E₃) : A z = z 0 • A !₂[1, 0, 0] + z 1 • A !₂[0, 1, 0] +
      z 2 • A !₂[0, 0, 1] := by
    simpa only [map_add, map_smul] using congrArg A
      (show z = z 0 • (!₂[1, 0, 0] : E₃) + z 1 • !₂[0, 1, 0] + z 2 • !₂[0, 0, 1] by
        ext i; fin_cases i <;> simp)
  rw [ha x, ha y, curlLinearMap_apply]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  ring

/-- A unit-sphere quadratic bound scales with the square of the vector norm. -/
theorem abs_quadratic_le_norm_sq (A : E₃ →L[ℝ] E₃) {B : ℝ}
    (hB : ∀ e : E₃, ‖e‖ = 1 → |⟪e, A e⟫_ℝ| ≤ B) (x : E₃) :
    |⟪x, A x⟫_ℝ| ≤ B * ‖x‖ ^ 2 := by
  by_cases hx : x = 0
  · simp [hx]
  · have hh := hB (‖x‖⁻¹ • x) (by simp [norm_smul, norm_ne_zero_iff.mpr hx])
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right, abs_mul, abs_inv, abs_norm] at hh
    have hh' : |⟪x, A x⟫_ℝ| / ‖x‖ ^ 2 ≤ B := by
      simpa only [← mul_assoc, ← inv_pow, ← sq, div_eq_mul_inv, mul_comm] using hh
    exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))).mp hh'

/-- Uniform quadratic-form bounds and curl control the full operator norm. -/
theorem norm_le_of_quadratic_curl_bound (A : E₃ →L[ℝ] E₃) {B : ℝ} (hB₀ : 0 ≤ B)
    (hB : ∀ e : E₃, ‖e‖ = 1 → |⟪e, A e⟫_ℝ| ≤ B) :
    ‖A‖ ≤ 3 * B + ‖curlLinearMap A‖ := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity)
  intro x y hx hy
  have hn : ‖x + y‖ ≤ 2 := by simpa only [hx, hy, one_add_one_eq_two] using norm_add_le x y
  have hsum : |⟪x + y, A (x + y)⟫_ℝ| ≤ 4 * B :=
    (abs_quadratic_le_norm_sq A hB (x + y)).trans
      ((mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg (x + y)] : ‖x + y‖ ^ 2 ≤ 4) hB₀).trans_eq (mul_comm B 4))
  have hw : |⟪y, A x⟫_ℝ - ⟪x, A y⟫_ℝ| ≤ ‖curlLinearMap A‖ := by
    rw [inner_apply_sub_inner_apply_eq_curl]
    simpa only [hx, hy, one_mul, mul_one] using
      (abs_real_inner_le_norm (curlLinearMap A) _).trans
        (mul_le_mul_of_nonneg_left (Analysis.norm_cartesian_cross_le x y) (norm_nonneg _))
  simp only [map_add, inner_add_left, inner_add_right] at hsum
  change ⟪A x, y⟫_ℝ ≤ _
  rw [real_inner_comm y (A x)]
  linarith only [(abs_le.mp (hB x hx)).1, (abs_le.mp (hB y hy)).1,
    (abs_le.mp hsum).2, (abs_le.mp hw).2, norm_nonneg (curlLinearMap A)]

end ClockBarrier.Geometry
