/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.SolenoidalSmooth
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Linarith

/-! # The quadratic divergence of smooth incompressible advection -/
public section
namespace ClockBarrier.Analysis
open Solenoidal
open scoped ContDiff
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem fderiv_derivative_coordinate {u : Space → Space} (hu : ContDiff ℝ ∞ u)
    (x v w : Space) (i : Fin 3) :
    fderiv ℝ (fun y => fderiv ℝ u y v i) x w =
      fderiv ℝ (fderiv ℝ u) x w v i := by
  have hD := (hu.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  rw [fderiv_coordinate _ _ ((hD x).clm_apply (differentiableAt_const v)),
    fderiv_clm_apply (hD x) (differentiableAt_const v)]
  simp

theorem sum_second_derivative_of_divergence_zero {u : Space → Space}
    (hu : ContDiff ℝ ∞ u)
    (hdiv : ∀ x, ∑ i : Fin 3, fderiv ℝ u x (EuclideanSpace.single i 1) i = 0)
    (x v : Space) :
    (∑ i : Fin 3, fderiv ℝ (fderiv ℝ u) x v (EuclideanSpace.single i 1) i) = 0 := by
  have hD := (hu.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hd (i : Fin 3) : DifferentiableAt ℝ
      (fun y => fderiv ℝ u y (EuclideanSpace.single i 1) i) x := by
    convert! (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp x
      ((hD x).clm_apply (differentiableAt_const (EuclideanSpace.single i 1))) using 1
  have he := congrArg (fun L : Space →L[ℝ] ℝ => L v)
    (fderiv_fun_sum (u := Finset.univ) (fun i _ => hd i))
  simp only [sum_apply, fderiv_derivative_coordinate hu] at he
  have hz : (fun y => ∑ i : Fin 3, fderiv ℝ u y (EuclideanSpace.single i 1) i) =
      fun _ => (0 : ℝ) := funext hdiv
  rw [hz, fderiv_const_apply] at he
  exact he.symm

theorem divergence_advection_eq_quadratic {u : Space → Space} (hu : ContDiff ℝ ∞ u)
    (hdiv : ∀ x, ∑ i : Fin 3, fderiv ℝ u x (EuclideanSpace.single i 1) i = 0)
    (x : Space) :
    (∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ u y (u y)) x
      (EuclideanSpace.single i 1) i) =
      ∑ i : Fin 3, fderiv ℝ u x (fderiv ℝ u x (EuclideanSpace.single i 1)) i := by
  have hD := (hu.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hs (v w : Space) := (hu.contDiffAt (x := x)).isSymmSndFDerivAt (by simpa using
    (ENat.natCast_le_of_coe_top_le_withTop (N := (∞ : ℕ∞ω)) le_rfl 2)) v w
  have hz := sum_second_derivative_of_divergence_zero hu hdiv x (u x)
  rw [fderiv_clm_apply (hD x) (hu.differentiable (by simp) x)]
  simp only [add_apply, PiLp.add_apply, ContinuousLinearMap.comp_apply,
    Finset.sum_add_distrib]
  simp_rw [ContinuousLinearMap.flip_apply, hs (EuclideanSpace.single _ 1) (u x)]
  rw [hz, add_zero]

theorem abs_sum_diagonal_square_le (L : Space →L[ℝ] Space) :
    |∑ i : Fin 3, L (L (EuclideanSpace.single i 1)) i| ≤ 3 * ‖L‖ ^ 2 := by
  have hi (i : Fin 3) : |L (L (EuclideanSpace.single i 1)) i| ≤ ‖L‖ ^ 2 := by
    calc
      _ ≤ ‖L (L (EuclideanSpace.single i 1))‖ := PiLp.norm_apply_le _ i
      _ ≤ ‖L‖ * ‖L (EuclideanSpace.single i 1)‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (‖L‖ * ‖(EuclideanSpace.single i 1 : Space)‖) :=
        mul_le_mul_of_nonneg_left (L.le_opNorm _) (norm_nonneg L)
      _ = _ := by simp [PiLp.norm_single, pow_two]
  calc
    _ ≤ ∑ i : Fin 3, |L (L (EuclideanSpace.single i 1)) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin 3, ‖L‖ ^ 2 := Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by simp

end ClockBarrier.Analysis
