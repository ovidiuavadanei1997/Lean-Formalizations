/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.RegularizedStrain
public import ClockBarrier.Analysis.NewtonianScaling
public import ClockBarrier.Analysis.VelocityScaling
public import ClockBarrier.Analysis.CurlStrainIntegral
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! # The signed on-axis Biot–Savart formula at a zero of the curl -/

public section

namespace ClockBarrier.Analysis

open Set Filter MeasureTheory Geometry
open scoped Topology NNReal

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The on-axis strain representation, with its explicit Cartesian coefficient.
The curl-zero hypothesis removes the local singularity; finite energy supplies the tail. -/
theorem axis_strain_eq_biot_savart
    {u : E₃ → E₃} {H α : ℝ≥0} (hu : Differentiable ℝ u)
    (hα : 0 < α) (hD : HolderWith H α (fderiv ℝ u))
    (henergy : Integrable (fun x => ‖u x‖ ^ 2) volume)
    {B C : ℝ} (hbound : ∀ x, ‖u x‖ ≤ B) (hDbound : ∀ x, ‖fderiv ℝ u x‖ ≤ C)
    (hdiv : ∀ x, ∑ i : Fin 3, fderiv ℝ u x (EuclideanSpace.single i 1) i = 0)
    (hzero : curlLinearMap (fderiv ℝ u 0) = 0) :
    fderiv ℝ u 0 (EuclideanSpace.single 2 1) 2 = (3 / (4 * Real.pi)) *
      ∫ x : E₃, x 2 *
        (x 0 * curlLinearMap (fderiv ℝ u x) 1 - x 1 * curlLinearMap (fderiv ℝ u x) 0) /
          ‖x‖ ^ 5 := by
  have hid (ε : ℝ) (hε : 0 < ε) :
      (1 / (4 * Real.pi)) * (∫ x : E₃, 3 * x 2 *
        (x 0 * curlLinearMap (fderiv ℝ u x) 1 - x 1 * curlLinearMap (fderiv ℝ u x) 0) *
          (ε ^ 2 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)) =
      ∫ x : E₃, (3 / (4 * Real.pi)) * (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) *
        fderiv ℝ u (ε • x) (EuclideanSpace.single 2 1) 2 := by
    have hv : Differentiable ℝ (fun x => ε⁻¹ • u (ε • x)) :=
      (hu.comp (differentiable_id.const_smul ε)).const_smul ε⁻¹
    obtain ⟨Hε, hHε⟩ := exists_holderWith_fderiv_rescaled_velocity hu hD hε.ne'
    have hvb (x : E₃) : ‖ε⁻¹ • u (ε • x)‖ ≤ ‖ε⁻¹‖ * B := by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)
    have hvdiv (x : E₃) : ∑ i : Fin 3,
        fderiv ℝ (fun y => ε⁻¹ • u (ε • y)) x (EuclideanSpace.single i 1) i = 0 := by
      rw [fderiv_rescaled_velocity hu hε.ne']
      exact hdiv _
    have heq := integral_regularized_axis_strain hv hα hHε
      (integrable_sq_norm_rescaled_velocity henergy hε.ne') hvb hvdiv
    simp only [fderiv_rescaled_velocity hu hε.ne'] at heq
    rw [integral_regularized_axis_kernel_scaling (fun x => curlLinearMap (fderiv ℝ u x)) hε] at heq
    rw [heq, ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  have hc := hD.continuous hα
  have hg : Continuous (fun x => fderiv ℝ u x (EuclideanSpace.single 2 1) 2) := by fun_prop
  have hgb (x : E₃) : |fderiv ℝ u x (EuclideanSpace.single 2 1) 2| ≤ C := by
    calc
      _ ≤ ‖fderiv ℝ u x (EuclideanSpace.single 2 1)‖ := abs_euclidean_coordinate_le_norm _ _
      _ ≤ ‖fderiv ℝ u x‖ * ‖(EuclideanSpace.single 2 1 : E₃)‖ :=
        (fderiv ℝ u x).le_opNorm _
      _ ≤ C := by simpa using hDbound x
  have hright := (tendsto_integral_newtonian_density_smul hg hgb).mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hleft := ((tendsto_integral_regularized_axis_kernel
    ((holderWith_curlLinearMap hD).continuous hα)
    (integrable_axis_strain_curl_fderiv hu hα hD henergy hzero)).const_mul
      (1 / (4 * Real.pi))).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hevent := Eventually.mono (self_mem_nhdsWithin : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioi 0)
    (fun ε hε => hid ε hε)
  have hvalue := tendsto_nhds_unique hleft (hright.congr' (hevent.mono fun _ h => h.symm))
  rw [← hvalue]
  ring

/-- Translation of the signed strain formula to any zero of the curl. -/
theorem axis_strain_eq_biot_savart_sub
    {u : E₃ → E₃} {H α : ℝ≥0} (hu : Differentiable ℝ u)
    (hα : 0 < α) (hD : HolderWith H α (fderiv ℝ u))
    (henergy : Integrable (fun x => ‖u x‖ ^ 2) volume)
    {B C : ℝ} (hbound : ∀ x, ‖u x‖ ≤ B) (hDbound : ∀ x, ‖fderiv ℝ u x‖ ≤ C)
    (hdiv : ∀ x, ∑ i : Fin 3, fderiv ℝ u x (EuclideanSpace.single i 1) i = 0)
    (a : E₃) (hzero : curlLinearMap (fderiv ℝ u a) = 0) :
    fderiv ℝ u a (EuclideanSpace.single 2 1) 2 = (3 / (4 * Real.pi)) *
      ∫ x : E₃, (x - a) 2 *
        ((x - a) 0 * curlLinearMap (fderiv ℝ u x) 1 -
          (x - a) 1 * curlLinearMap (fderiv ℝ u x) 0) / ‖x - a‖ ^ 5 := by
  have hdiff : Differentiable ℝ (fun x => u (x + a)) :=
    fun x => (differentiableAt_comp_add_right a).mpr (hu (x + a))
  have hDa : HolderWith H α (fderiv ℝ (fun x => u (x + a))) := by
    intro x y
    simpa only [fderiv_comp_add_right, edist_add_right] using hD (x + a) (y + a)
  have hid := axis_strain_eq_biot_savart hdiff hα hDa (henergy.comp_add_right a)
    (fun x => hbound (x + a))
    (fun x => by simpa only [fderiv_comp_add_right] using hDbound (x + a))
    (fun x => by simpa only [fderiv_comp_add_right] using hdiv (x + a))
    (by simpa only [fderiv_comp_add_right, zero_add] using hzero)
  simp only [fderiv_comp_add_right, zero_add] at hid
  have hi := integral_add_right_eq_self (μ := volume) (fun x : E₃ => (x - a) 2 *
    ((x - a) 0 * curlLinearMap (fderiv ℝ u x) 1 -
      (x - a) 1 * curlLinearMap (fderiv ℝ u x) 0) / ‖x - a‖ ^ 5) a
  simp only [add_sub_cancel_right] at hi
  exact hid.trans (congrArg (fun b => (3 / (4 * Real.pi)) * b) hi)

end ClockBarrier.Analysis
