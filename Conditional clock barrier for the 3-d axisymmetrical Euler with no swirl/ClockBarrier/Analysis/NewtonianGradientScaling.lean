/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.NewtonianIntegrability
public import ClockBarrier.Analysis.NewtonianDifferenceBound
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Tactic.FieldSimp

/-! # Dilations of the Newtonian gradient -/
public section
namespace ClockBarrier.Analysis
open MeasureTheory
open scoped ContDiff
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem memLp_two_comp_smul {V : Type*} [NormedAddCommGroup V]
    {f : Space → V} (hc : Continuous f) (hf : MemLp f 2 volume)
    {r : ℝ} (hr : r ≠ 0) : MemLp (fun x => f (r • x)) 2 volume := by
  have hc' : Continuous (fun x : Space => f (r • x)) := by fun_prop
  have hi : Integrable (fun x => ‖f x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mp hf
  exact (memLp_two_iff_integrable_sq_norm hc'.aestronglyMeasurable).mpr (hi.comp_smul hr)

theorem memLp_newtonian_gradient (i : Fin 3) :
    MemLp (fun x : Space => -(x i * (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2))) 2 volume := by
  have hw : MemLp (fun x : Space => (1 + ‖x‖ ^ 2) ^ (-1 : ℝ)) 2 volume := by
    apply (memLp_two_iff_integrable_sq
      (contDiff_newtonian_power _).continuous.aestronglyMeasurable).mpr
    have hi := integrable_rpow_neg_one_add_norm_sq (μ := volume) (E := Space)
      (r := 4) (by norm_num)
    refine hi.congr (ae_of_all _ fun x => ?_)
    change (1 + ‖x‖ ^ 2) ^ (-(4 : ℝ) / 2) = ((1 + ‖x‖ ^ 2) ^ (-1 : ℝ)) ^ 2
    rw [← Real.rpow_natCast ((1 + ‖x‖ ^ 2) ^ (-1 : ℝ)) 2,
      ← Real.rpow_mul (by positivity)]
    norm_num
  refine hw.mono' (contDiff_newtonian_gradient i).continuous.aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_nonneg (by positivity :
    0 ≤ (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2))]
  exact (mul_le_mul_of_nonneg_right (abs_euclidean_coordinate_le_norm x i)
    (by positivity)).trans (by
      simpa only [pow_one, Nat.cast_one, show (1 : ℝ) / 2 + -(3 : ℝ) / 2 = -1 by norm_num]
        using norm_pow_mul_newtonian_power_le x 1 (-(3 : ℝ) / 2))

theorem fderiv_dilate_mul {f : Space → ℝ} (hf : Differentiable ℝ f)
    (r c : ℝ) (x v : Space) :
    fderiv ℝ (fun y : Space => c * f (r • y)) x v =
      c * r * fderiv ℝ f (r • x) v := by
  have hd := (((hf (r • x)).hasFDerivAt).comp x
    ((hasFDerivAt_id x).const_smul r)).const_mul c
  convert! congrArg (fun L : Space →L[ℝ] ℝ => L v) hd.fderiv using 1
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul, mul_assoc]

theorem newtonian_gradient_at_smul {r : ℝ} (hr : 0 < r) (i : Fin 3) (x : Space) :
    -((r • x) i * (r ^ 2 + ‖r • x‖ ^ 2) ^ (-(3 : ℝ) / 2)) =
      (r ^ 2)⁻¹ * -(x i * (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2)) := by
  have hp : (r ^ 2 + ‖r • x‖ ^ 2) ^ (-(3 : ℝ) / 2) =
      (r ^ 3)⁻¹ * (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) := by
    rw [norm_smul, Real.norm_of_nonneg hr.le]
    rw [show r ^ 2 + (r * ‖x‖) ^ 2 = r ^ 2 * (1 + ‖x‖ ^ 2) by ring,
      Real.mul_rpow (sq_nonneg r) (by positivity)]
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    norm_num [Real.rpow_neg hr.le]
  rw [hp, PiLp.smul_apply, smul_eq_mul]
  field_simp

theorem newtonian_gradient_eq_dilate {r : ℝ} (hr : 0 < r) (i : Fin 3) :
    (fun x : Space => -(x i * (r ^ 2 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2))) =
      (fun x : Space => (r ^ 2)⁻¹ * -((r⁻¹ • x) i *
        (1 + ‖r⁻¹ • x‖ ^ 2) ^ (-(3 : ℝ) / 2))) := by
  funext x
  simpa only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    using newtonian_gradient_at_smul hr i (r⁻¹ • x)

theorem contDiff_scaled_newtonian_gradient {r : ℝ} (hr : 0 < r) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x : Space => -(x i * (r ^ 2 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2))) := by
  rw [newtonian_gradient_eq_dilate hr i]
  convert! contDiff_const.mul ((contDiff_newtonian_gradient i).comp
    (contDiff_id.const_smul r⁻¹)) using 1

theorem fderiv_scaled_newtonian_gradient {r : ℝ} (hr : 0 < r)
    (i : Fin 3) (x v : Space) :
    fderiv ℝ (fun y : Space => -(y i * (r ^ 2 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2))) x v =
      (r ^ 3)⁻¹ * fderiv ℝ
        (fun y : Space => -(y i * (1 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2))) (r⁻¹ • x) v := by
  rw [newtonian_gradient_eq_dilate hr i,
    fderiv_dilate_mul ((contDiff_newtonian_gradient i).differentiable (by simp))]
  congr 1
  simp only [pow_succ, pow_zero, one_mul, mul_inv_rev]
  ring

theorem memLp_scaled_newtonian_gradient {r : ℝ} (hr : 0 < r) (i : Fin 3) :
    MemLp (fun x : Space => -(x i * (r ^ 2 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2))) 2 volume := by
  rw [newtonian_gradient_eq_dilate hr i]
  exact (memLp_two_comp_smul (contDiff_newtonian_gradient i).continuous
    (memLp_newtonian_gradient i) (inv_ne_zero hr.ne')).const_mul ((r ^ 2)⁻¹)

theorem memLp_fderiv_scaled_newtonian_gradient {r : ℝ} (hr : 0 < r)
    (i : Fin 3) (v : Space) :
    MemLp (fun x : Space => fderiv ℝ
      (fun y : Space => -(y i * (r ^ 2 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2))) x v) 2 volume := by
  simp only [fderiv_scaled_newtonian_gradient hr]
  have hc : Continuous (fun x : Space => fderiv ℝ
      (fun y : Space => -(y i * (1 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2))) x v) :=
    ((contDiff_newtonian_gradient i).fderiv_right (m := 0) (by simp)).continuous.clm_apply
      continuous_const
  exact (memLp_two_comp_smul hc (memLp_fderiv_newtonian_gradient i v)
    (inv_ne_zero hr.ne')).const_mul ((r ^ 3)⁻¹)

theorem fderiv_scaled_newtonian_gradient_symm {r : ℝ} (hr : 0 < r)
    (x : Space) (i j : Fin 3) :
    fderiv ℝ (fun y : Space => -(y i * (r ^ 2 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2))) x
        (EuclideanSpace.single j 1) =
      fderiv ℝ (fun y : Space => -(y j * (r ^ 2 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2))) x
        (EuclideanSpace.single i 1) := by
  simp only [fderiv_scaled_newtonian_gradient hr, fderiv_newtonian_gradient_apply,
    EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul, PiLp.single_apply]
  congr 1
  simp only [eq_comm (a := j) (b := i)]
  ring

theorem sum_fderiv_scaled_newtonian_gradient {r : ℝ} (hr : 0 < r) (x : Space) :
    (∑ i : Fin 3, fderiv ℝ
      (fun y : Space => -(y i * (r ^ 2 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2))) x
        (EuclideanSpace.single i 1)) =
      (r ^ 3)⁻¹ * (-3 * (1 + ‖r⁻¹ • x‖ ^ 2) ^ (-(5 : ℝ) / 2)) := by
  simp only [fderiv_scaled_newtonian_gradient hr, ← Finset.mul_sum,
    sum_fderiv_newtonian_gradient]

end ClockBarrier.Analysis
