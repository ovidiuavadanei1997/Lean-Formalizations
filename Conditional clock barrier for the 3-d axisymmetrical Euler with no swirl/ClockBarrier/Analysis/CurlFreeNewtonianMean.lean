/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.CurlFreeKernelIdentity
public import ClockBarrier.Analysis.NewtonianGradientScaling
public import ClockBarrier.Analysis.NewtonianLimit
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # Newtonian means of curl-free fields -/
public section
namespace ClockBarrier.Analysis
open MeasureTheory Filter Set
open scoped Topology
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem integral_scaled_newtonian_divergence_mul (f : Space → ℝ)
    {r : ℝ} (hr : 0 < r) :
    (∫ x : Space, (r ^ 3)⁻¹ * (-3 * (1 + ‖r⁻¹ • x‖ ^ 2) ^ (-(5 : ℝ) / 2)) * f x) =
      -3 * ∫ x : Space, (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) * f (r • x) := by
  let g (x : Space) := (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) * f (r • x)
  have he (x : Space) :
      (r ^ 3)⁻¹ * (-3 * (1 + ‖r⁻¹ • x‖ ^ 2) ^ (-(5 : ℝ) / 2)) * f x =
        (-3 * (r ^ 3)⁻¹) * g (r⁻¹ • x) := by
    simp only [g, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    ring
  simp_rw [he]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume g hr.le]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  field_simp
  simp only [g, neg_div]

theorem curl_free_newtonian_mean (F : Fin 3 → Space → ℝ)
    (hF : ∀ i, Differentiable ℝ (F i)) (hF0 : ∀ i, MemLp (F i) 2 volume)
    (hF1 : ∀ i j, MemLp (fun x => fderiv ℝ (F i) x (EuclideanSpace.single j 1)) 2 volume)
    (hFs : ∀ x i j, fderiv ℝ (F i) x (EuclideanSpace.single j 1) =
      fderiv ℝ (F j) x (EuclideanSpace.single i 1))
    {r : ℝ} (hr : 0 < r) (j : Fin 3) :
    3 * (∫ x : Space, (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) * F j (r • x)) =
      ∫ x : Space, -(x j * (r ^ 2 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2)) *
        ∑ i : Fin 3, fderiv ℝ (F i) x (EuclideanSpace.single i 1) := by
  have hi := integral_curl_free_kernel_divergence
    (fun i x => -(x i * (r ^ 2 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2))) F
    (fun i => (contDiff_scaled_newtonian_gradient hr i).differentiable (by simp)) hF
    (memLp_scaled_newtonian_gradient hr) hF0
    (fun i k => memLp_fderiv_scaled_newtonian_gradient hr i (EuclideanSpace.single k 1)) hF1
    (fderiv_scaled_newtonian_gradient_symm hr) hFs j
  simp only [sum_fderiv_scaled_newtonian_gradient hr] at hi
  rw [integral_scaled_newtonian_divergence_mul (F j) hr] at hi
  linarith

theorem abs_integral_newtonian_difference_mul_le {d : Space → ℝ}
    (hd : MemLp d 2 volume) {B : ℝ} (hB : ∀ x, |d x| ≤ B)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (j : Fin 3) :
    |(∫ x : Space, -(x j * (r ^ 2 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2)) * d x) -
      (∫ x : Space, -(x j * (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2)) * d x)| ≤
      (∫ x : Space, ‖x‖ * ((‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) -
        (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2))) * B := by
  have hIr : Integrable (fun x : Space =>
      -(x j * (r ^ 2 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2)) * d x) volume := by
    convert! (memLp_scaled_newtonian_gradient hr j).integrable_mul hd using 1
  have hI1 : Integrable (fun x : Space =>
      -(x j * (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2)) * d x) volume := by
    convert! (memLp_newtonian_gradient j).integrable_mul hd using 1
  rw [← integral_sub hIr hI1, ← integral_mul_const]
  refine abs_integral_le_integral_abs.trans
    (integral_mono (hIr.sub hI1).abs
      (integrable_newtonian_difference_weight.mul_const B) (fun x => ?_))
  rw [← sub_mul, abs_mul]
  exact mul_le_mul (abs_newtonian_gradient_difference_le hr hr1 j x) (hB x)
    (abs_nonneg _) (newtonian_difference_weight_nonneg x)

theorem tendsto_unnormalized_newtonian_mean {f : Space → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    Tendsto (fun r : ℝ => 3 * ∫ x : Space,
      (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) * f (r • x))
      (𝓝 0) (𝓝 (4 * Real.pi * f 0)) := by
  have ht := (tendsto_integral_newtonian_density_smul hf hB).const_mul (4 * Real.pi)
  have he (r : ℝ) : (∫ x : Space, (3 / (4 * Real.pi)) *
      (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) * f (r • x)) =
      (3 / (4 * Real.pi)) * ∫ x : Space,
        (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) * f (r • x) := by
    simp only [mul_assoc, integral_const_mul]
  simp only [he, ← mul_assoc, mul_div_cancel₀ _ (show 4 * Real.pi ≠ 0 by positivity)] at ht
  exact ht

theorem curl_free_newtonian_mean_error (F : Fin 3 → Space → ℝ)
    (hF : ∀ i, Differentiable ℝ (F i)) (hF0 : ∀ i, MemLp (F i) 2 volume)
    (hF1 : ∀ i j, MemLp (fun x => fderiv ℝ (F i) x (EuclideanSpace.single j 1)) 2 volume)
    (hFs : ∀ x i j, fderiv ℝ (F i) x (EuclideanSpace.single j 1) =
      fderiv ℝ (F j) x (EuclideanSpace.single i 1))
    {B A : ℝ} (hB : ∀ x, |∑ i : Fin 3,
      fderiv ℝ (F i) x (EuclideanSpace.single i 1)| ≤ B)
    (j : Fin 3) (hA : ∀ x, |F j x| ≤ A) :
    |4 * Real.pi * F j 0 - 3 * ∫ x : Space,
      (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) * F j x| ≤
      (∫ x : Space, ‖x‖ * ((‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) -
        (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2))) * B := by
  have hd : MemLp (fun x => ∑ i : Fin 3,
      fderiv ℝ (F i) x (EuclideanSpace.single i 1)) 2 volume :=
    memLp_finsetSum Finset.univ (fun i _ => hF1 i i)
  have h1 := curl_free_newtonian_mean F hF hF0 hF1 hFs (r := 1) zero_lt_one j
  simp only [one_pow, one_smul] at h1
  have he (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
      |3 * (∫ x : Space, (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) * F j (r • x)) -
        3 * (∫ x : Space, (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) * F j x)| ≤
        (∫ x : Space, ‖x‖ * ((‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) -
          (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2))) * B := by
    rw [curl_free_newtonian_mean F hF hF0 hF1 hFs hr j, h1]
    exact abs_integral_newtonian_difference_mul_le hd hB hr hr1 j
  have hlim : Tendsto (fun r : ℝ => 3 * ∫ x : Space,
      (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) * F j (r • x))
      (𝓝[>] 0) (𝓝 (4 * Real.pi * F j 0)) :=
    (tendsto_unnormalized_newtonian_mean (hF j).continuous hA).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto (hlim.sub_const _).abs
  filter_upwards [self_mem_nhdsWithin,
    (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
    with r hr hr1
  exact he r hr hr1

end ClockBarrier.Analysis
