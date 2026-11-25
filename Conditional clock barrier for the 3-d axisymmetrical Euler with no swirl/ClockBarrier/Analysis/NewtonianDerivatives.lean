/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Ring

/-! # Derivatives of the regularized Newtonian potential -/

public section

namespace ClockBarrier.Analysis

open scoped RealInnerProductSpace ContDiff

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The regularizing denominator is strictly positive, so all real powers are smooth. -/
theorem contDiff_newtonian_power (p : ℝ) :
    ContDiff ℝ ∞ (fun x : E₃ => (1 + ‖x‖ ^ 2) ^ p) := by
  exact (contDiff_const.add (contDiff_id.norm_sq ℝ)).rpow_const_of_ne
    (fun x => by positivity)

/-- Directional derivative of any power of the regularizing denominator. -/
theorem fderiv_newtonian_power_apply (p : ℝ) (x v : E₃) :
    fderiv ℝ (fun y : E₃ => (1 + ‖y‖ ^ 2) ^ p) x v =
      2 * p * (1 + ‖x‖ ^ 2) ^ (p - 1) * ⟪x, v⟫ := by
  have hd := ((hasFDerivAt_id x).norm_sq.const_add 1).rpow_const
    (p := p) (Or.inl (by positivity))
  change HasFDerivAt (fun y : E₃ => (1 + ‖y‖ ^ 2) ^ p) _ x at hd
  rw [hd.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul, id_eq]
  ring

/-- Multiplication by a Cartesian coordinate gives the regularized gradient kernels. -/
theorem fderiv_coordinate_mul_newtonian_power (p : ℝ) (i : Fin 3) (x v : E₃) :
    fderiv ℝ (fun y : E₃ => y i * (1 + ‖y‖ ^ 2) ^ p) x v =
      v i * (1 + ‖x‖ ^ 2) ^ p +
        x i * (2 * p * (1 + ‖x‖ ^ 2) ^ (p - 1) * ⟪x, v⟫) := by
  have hp := (contDiff_newtonian_power p).differentiable (by simp)
  have hc : DifferentiableAt ℝ (fun y : E₃ => y i) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt
  have he : fderiv ℝ (fun y : E₃ => y i) x = EuclideanSpace.proj i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.fderiv
  rw [fderiv_fun_mul hc (hp x)]
  simp only [add_apply, smul_apply, smul_eq_mul, he,
    fderiv_newtonian_power_apply]
  change x i * (2 * p * (1 + ‖x‖ ^ 2) ^ (p - 1) * ⟪x, v⟫) +
      (1 + ‖x‖ ^ 2) ^ p * v i = _
  ring

/-- The coordinate gradient kernels are smooth everywhere. -/
theorem contDiff_newtonian_gradient (i : Fin 3) :
    ContDiff ℝ ∞ (fun x : E₃ => -(x i * (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2))) := by
  exact ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.mul
    (contDiff_newtonian_power (-(3 : ℝ) / 2))).neg

/-- Hessian entries of the regularized Newtonian potential, including their sign. -/
theorem fderiv_newtonian_gradient_apply (i : Fin 3) (x v : E₃) :
    fderiv ℝ (fun y : E₃ => -(y i * (1 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2))) x v =
      3 * x i * (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) * ⟪x, v⟫ -
        v i * (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) := by
  rw [fderiv_fun_neg]
  simp only [neg_apply, fderiv_coordinate_mul_newtonian_power]
  norm_num
  ring

/-- Differentiating a Hessian entry differentiates only the smooth regularizer. -/
theorem fderiv_newtonian_hessian_apply (i : Fin 3) (x v w : E₃) :
    fderiv ℝ (fun y : E₃ => fderiv ℝ
      (fun a : E₃ => -(a i * (1 + ‖a‖ ^ 2) ^ (-(3 : ℝ) / 2))) y v) x w =
      3 * (w i * ⟪x, v⟫ + x i * ⟪w, v⟫ + v i * ⟪x, w⟫) *
        (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) -
      15 * x i * ⟪x, v⟫ * ⟪x, w⟫ * (1 + ‖x‖ ^ 2) ^ (-(7 : ℝ) / 2) := by
  simp only [fderiv_newtonian_gradient_apply]
  have hp (p : ℝ) := (contDiff_newtonian_power p).differentiable (by simp) x
  have hc : DifferentiableAt ℝ (fun y : E₃ => y i) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt
  have hi : DifferentiableAt ℝ (fun y : E₃ => ⟪y, v⟫) x :=
    differentiableAt_id.inner ℝ (differentiableAt_const v)
  rw [show (fun y : E₃ => 3 * y i * (1 + ‖y‖ ^ 2) ^ (-(5 : ℝ) / 2) * ⟪y, v⟫ -
      v i * (1 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2)) =
      (fun y : E₃ => 3 * ((y i * (1 + ‖y‖ ^ 2) ^ (-(5 : ℝ) / 2)) * ⟪y, v⟫) -
        v i * (1 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2)) by ext y; ring]
  have hcq : DifferentiableAt ℝ
      (fun y : E₃ => y i * (1 + ‖y‖ ^ 2) ^ (-(5 : ℝ) / 2)) x := hc.mul (hp _)
  have hcqi : DifferentiableAt ℝ
      (fun y : E₃ => (y i * (1 + ‖y‖ ^ 2) ^ (-(5 : ℝ) / 2)) * ⟪y, v⟫) x := hcq.mul hi
  have hiv : fderiv ℝ (fun y : E₃ => ⟪y, v⟫) x w = ⟪w, v⟫ := by
    simpa using fderiv_inner_apply ℝ (x := x) differentiableAt_id
      (differentiableAt_const v) w
  rw [fderiv_fun_sub (hcqi.const_mul 3) ((hp _).const_mul (v i)),
    fderiv_const_mul hcqi, fderiv_const_mul (hp _), fderiv_fun_mul hcq hi]
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul,
    fderiv_coordinate_mul_newtonian_power, fderiv_newtonian_power_apply,
    hiv]
  norm_num
  ring

/-- The gradient kernels are the actual derivatives of the regularized potential. -/
theorem fderiv_newtonian_potential_coordinate (i : Fin 3) (x : E₃) :
    fderiv ℝ (fun y : E₃ => (1 + ‖y‖ ^ 2) ^ (-(1 : ℝ) / 2)) x
      (EuclideanSpace.single i 1) = -(x i * (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2)) := by
  rw [fderiv_newtonian_power_apply]
  simp only [EuclideanSpace.inner_single_right, conj_trivial, one_mul]
  norm_num
  ring

/-- The negative Laplacian of the unnormalized regularized potential is
`3 (1 + |x|²)^(-5/2)`. -/
theorem sum_fderiv_newtonian_gradient (x : E₃) :
    (∑ i : Fin 3, fderiv ℝ
      (fun y : E₃ => -(y i * (1 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2))) x
        (EuclideanSpace.single i 1)) = -3 * (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) := by
  simp only [fderiv_newtonian_gradient_apply, EuclideanSpace.inner_single_right,
    conj_trivial, one_mul, PiLp.single_apply, ite_true]
  have hn := EuclideanSpace.real_norm_sq_eq x
  simp only [Fin.sum_univ_three] at hn ⊢
  rw [show (-3 : ℝ) / 2 = -5 / 2 + 1 by norm_num,
    Real.rpow_add (by positivity : 0 < 1 + ‖x‖ ^ 2), Real.rpow_one, hn]
  ring

end ClockBarrier.Analysis
