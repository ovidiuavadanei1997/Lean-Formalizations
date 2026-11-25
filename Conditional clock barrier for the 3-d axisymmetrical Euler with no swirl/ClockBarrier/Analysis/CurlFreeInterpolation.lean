/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.CurlFreeNewtonianMean
public import ClockBarrier.Analysis.L2Pairing
public import ClockBarrier.Analysis.AffineScalarField
import Mathlib.Tactic.Linarith

/-! # Interpolation for curl-free vector fields with bounded divergence -/
public section
namespace ClockBarrier.Analysis
open MeasureTheory Filter Set
open scoped Topology ContDiff
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem memLp_newtonian_mean_weight :
    MemLp (fun x : Space => (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)) 2 volume := by
  refine memLp_newtonian_hessian_weight.mono'
    (contDiff_newtonian_power _).continuous.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2))] using
    Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (sq_nonneg ‖x‖))
      (show -(5 : ℝ) / 2 ≤ -(3 : ℝ) / 2 by norm_num)

theorem curl_free_origin_component_bound (F : Fin 3 → Space → ℝ)
    (hF : ∀ i, Differentiable ℝ (F i)) (hF0 : ∀ i, MemLp (F i) 2 volume)
    (hF1 : ∀ i j, MemLp (fun x => fderiv ℝ (F i) x (EuclideanSpace.single j 1)) 2 volume)
    (hFs : ∀ x i j, fderiv ℝ (F i) x (EuclideanSpace.single j 1) =
      fderiv ℝ (F j) x (EuclideanSpace.single i 1))
    {B A : ℝ} (hB : ∀ x, |∑ i : Fin 3,
      fderiv ℝ (F i) x (EuclideanSpace.single i 1)| ≤ B)
    (j : Fin 3) (hA : ∀ x, |F j x| ≤ A) :
    4 * Real.pi * |F j 0| ≤
      (∫ x : Space, ‖x‖ * ((‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) -
        (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2))) * B +
      3 * Real.sqrt (∫ x : Space, ‖(1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)‖ ^ 2) *
        Real.sqrt (∫ x : Space, ‖F j x‖ ^ 2) := by
  have he := curl_free_newtonian_mean_error F hF hF0 hF1 hFs hB j hA
  have hc : |∫ x : Space, (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) * F j x| ≤
      Real.sqrt (∫ x : Space, ‖(1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)‖ ^ 2) *
        Real.sqrt (∫ x : Space, ‖F j x‖ ^ 2) := by
    refine abs_integral_le_integral_abs.trans ?_
    simpa only [Real.norm_eq_abs, abs_mul] using
      integral_mul_norm_le_sqrt_energy memLp_newtonian_mean_weight (hF0 j)
  have ht := abs_sub_le (4 * Real.pi * F j 0)
    (3 * ∫ x : Space, (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) * F j x) 0
  norm_num only [sub_zero, abs_mul, abs_of_pos Real.pi_pos] at ht
  nlinarith

theorem curl_free_component_interpolation (F : Fin 3 → Space → ℝ)
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) (hF0 : ∀ i, MemLp (F i) 2 volume)
    (hF1 : ∀ i j, MemLp (fun x => fderiv ℝ (F i) x (EuclideanSpace.single j 1)) 2 volume)
    (hFs : ∀ x i j, fderiv ℝ (F i) x (EuclideanSpace.single j 1) =
      fderiv ℝ (F j) x (EuclideanSpace.single i 1))
    {B A : ℝ} (hB : ∀ x, |∑ i : Fin 3,
      fderiv ℝ (F i) x (EuclideanSpace.single i 1)| ≤ B)
    (j : Fin 3) (hA : ∀ x, |F j x| ≤ A) {r : ℝ} (hr : 0 < r) (a : Space) :
    4 * Real.pi * |F j a| ≤
      (∫ x : Space, ‖x‖ * ((‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) -
        (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2))) * (r * B) +
      3 * Real.sqrt (∫ x : Space, ‖(1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)‖ ^ 2) *
        (r ^ (-(3 : ℝ) / 2) * Real.sqrt (∫ x : Space, ‖F j x‖ ^ 2)) := by
  let G (i : Fin 3) (x : Space) := F i (r • x + a)
  have hFd (i : Fin 3) := (hF i).differentiable (by simp)
  have hG (i : Fin 3) : Differentiable ℝ (G i) := by
    convert! (hFd i).comp ((differentiable_id.const_smul r).add_const a) using 1
  have hG0 (i : Fin 3) : MemLp (G i) 2 volume :=
    memLp_two_affine (hF i).continuous (hF0 i) hr.ne' a
  have hG1 (i k : Fin 3) :
      MemLp (fun x => fderiv ℝ (G i) x (EuclideanSpace.single k 1)) 2 volume := by
    simp only [G, fderiv_scalar_affine_apply (hFd i)]
    have hc : Continuous (fun x => fderiv ℝ (F i) x (EuclideanSpace.single k 1)) :=
      ((hF i).fderiv_right (m := 0) (by simp)).continuous.clm_apply continuous_const
    exact (memLp_two_affine hc (hF1 i k) hr.ne' a).const_mul r
  have hGs (x : Space) (i k : Fin 3) :
      fderiv ℝ (G i) x (EuclideanSpace.single k 1) =
        fderiv ℝ (G k) x (EuclideanSpace.single i 1) := by
    simp only [G, fderiv_scalar_affine_apply (hFd i), fderiv_scalar_affine_apply (hFd k),
      hFs _ i k]
  have hGB (x : Space) :
      |∑ i : Fin 3, fderiv ℝ (G i) x (EuclideanSpace.single i 1)| ≤ r * B := by
    simp only [G, fderiv_scalar_affine_apply (hFd _), ← Finset.mul_sum, abs_mul,
      abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (hB _) hr.le
  have hb := curl_free_origin_component_bound G hG hG0 hG1 hGs hGB j
    (fun x => hA (r • x + a))
  simpa only [G, smul_zero, zero_add, sqrt_energy_affine (F j) hr a] using hb

theorem exists_curl_free_component_interpolation_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Fin 3 → Space → ℝ),
      (∀ i, ContDiff ℝ ∞ (F i)) → (∀ i, MemLp (F i) 2 volume) →
      (∀ i j, MemLp (fun x => fderiv ℝ (F i) x (EuclideanSpace.single j 1)) 2 volume) →
      (∀ x i j, fderiv ℝ (F i) x (EuclideanSpace.single j 1) =
        fderiv ℝ (F j) x (EuclideanSpace.single i 1)) →
      ∀ B : ℝ, (∀ x, |∑ i : Fin 3,
        fderiv ℝ (F i) x (EuclideanSpace.single i 1)| ≤ B) →
      ∀ (j : Fin 3) (A : ℝ), (∀ x, |F j x| ≤ A) → ∀ r : ℝ, 0 < r → ∀ a : Space,
        |F j a| ≤ C * (r * B + r ^ (-(3 : ℝ) / 2) *
          Real.sqrt (∫ x : Space, ‖F j x‖ ^ 2)) := by
  let K := ∫ x : Space, ‖x‖ * ((‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) -
    (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2))
  let L := 3 * Real.sqrt (∫ x : Space, ‖(1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)‖ ^ 2)
  have hK : 0 ≤ K := integral_nonneg newtonian_difference_weight_nonneg
  have hL : 0 ≤ L := by positivity
  have hπ : 0 < 4 * Real.pi := by positivity
  refine ⟨(K + L + 1) / (4 * Real.pi), div_pos (by positivity) hπ, ?_⟩
  intro F hF hF0 hF1 hFs B hB j A hA r hr a
  have hb := curl_free_component_interpolation F hF hF0 hF1 hFs hB j hA hr a
  change 4 * Real.pi * |F j a| ≤ K * (r * B) +
    L * (r ^ (-(3 : ℝ) / 2) * Real.sqrt (∫ x : Space, ‖F j x‖ ^ 2)) at hb
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hX : 0 ≤ r * B := mul_nonneg hr.le hB0
  have hY : 0 ≤ r ^ (-(3 : ℝ) / 2) * Real.sqrt (∫ x : Space, ‖F j x‖ ^ 2) := by positivity
  apply (mul_le_mul_iff_right₀ hπ).mp
  calc
    _ ≤ (K + L + 1) * (r * B + r ^ (-(3 : ℝ) / 2) *
        Real.sqrt (∫ x : Space, ‖F j x‖ ^ 2)) := by
      nlinarith [mul_nonneg hK hY, mul_nonneg hL hX]
    _ = _ := by field_simp

end ClockBarrier.Analysis
