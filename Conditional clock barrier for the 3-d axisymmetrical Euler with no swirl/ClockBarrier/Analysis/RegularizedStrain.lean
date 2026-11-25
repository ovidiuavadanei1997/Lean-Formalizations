/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.NewtonianIntegrationByParts
public import ClockBarrier.Geometry.CurlLinear
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! # The whole-space regularized signed strain identity -/

public section

namespace ClockBarrier.Analysis

open MeasureTheory Geometry
open scoped NNReal RealInnerProductSpace

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The signed curl kernel equals the regularized axial derivative for a
divergence-free finite-energy velocity with one Hölder continuous derivative. -/
theorem integral_regularized_axis_strain
    {u : E₃ → E₃} {H α : ℝ≥0} (hu : Differentiable ℝ u)
    (hα : 0 < α) (hD : HolderWith H α (fderiv ℝ u))
    (henergy : Integrable (fun x => ‖u x‖ ^ 2) volume)
    {B : ℝ} (hbound : ∀ x, ‖u x‖ ≤ B)
    (hdiv : ∀ x, ∑ i : Fin 3, fderiv ℝ u x (EuclideanSpace.single i 1) i = 0) :
    (∫ x : E₃, 3 * x 2 *
      (x 0 * curlLinearMap (fderiv ℝ u x) 1 - x 1 * curlLinearMap (fderiv ℝ u x) 0) *
        (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)) =
      ∫ x : E₃, 3 * (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) *
        fderiv ℝ u x (EuclideanSpace.single 2 1) 2 := by
  let e (i : Fin 3) : E₃ := EuclideanSpace.single i 1
  let A (x : E₃) (i j : Fin 3) : ℝ := fderiv ℝ
    (fun y : E₃ => -(y i * (1 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2))) x (e j)
  let D (x : E₃) (i j : Fin 3) : ℝ := fderiv ℝ u x (e i) j
  have he (i : Fin 3) : ‖e i‖ = 1 := by simp [e]
  have hA (x : E₃) (i j : Fin 3) : A x i j = A x j i := by
    simp only [A, e, fderiv_newtonian_gradient_apply, EuclideanSpace.inner_single_right,
      conj_trivial, one_mul, PiLp.single_apply]
    by_cases hij : i = j
    · subst j
      rfl
    · simp only [hij, Ne.symm hij, ite_false, zero_mul, sub_zero]
      ring
  have hint (i j k l : Fin 3) : Integrable (fun x => A x i j * D x k l) volume :=
    integrable_newtonian_hessian_mul_velocity_derivative hu hα hD henergy i l (e j) (e k) (he k)
  have hswap (i j k l : Fin 3) :
      (∫ x, A x i j * D x k l) = ∫ x, A x i k * D x j l :=
    integral_newtonian_derivative_swap hu hα hD henergy hbound i l (e j) (e k) (he j) (he k)
  have h0 : e 0 = (!₂[1, 0, 0] : E₃) := by ext i; fin_cases i <;> simp [e]
  have h1 : e 1 = (!₂[0, 1, 0] : E₃) := by ext i; fin_cases i <;> simp [e]
  have h2 : e 2 = (!₂[0, 0, 1] : E₃) := by ext i; fin_cases i <;> simp [e]
  have hcurl (x : E₃) :
      3 * x 2 * (x 0 * curlLinearMap (fderiv ℝ u x) 1 -
        x 1 * curlLinearMap (fderiv ℝ u x) 0) * (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) =
      ∑ i : Fin 3, (A x i 2 * D x 2 i - A x i 2 * D x i 2) := by
    simp only [Fin.sum_univ_three, A, D, h0, h1, h2, fderiv_newtonian_gradient_apply,
      curlLinearMap_apply]
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
    ring
  have hfirst (i : Fin 3) : (∫ x, A x i 2 * D x 2 i) = ∫ x, A x 2 2 * D x i i := by
    calc
      _ = ∫ x, A x 2 i * D x 2 i := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => congrArg (fun a => a * D x 2 i) (hA x i 2)
      _ = _ := hswap 2 i 2 i
  simp_rw [hcurl]
  rw [integral_finsetSum (f := fun i x => A x i 2 * D x 2 i - A x i 2 * D x i 2)
    _ (fun i _ => (hint i 2 2 i).sub (hint i 2 i 2))]
  have hrow (i : Fin 3) :
      (∫ x, A x i 2 * D x 2 i - A x i 2 * D x i 2) =
        ∫ x, A x 2 2 * D x i i - A x i i * D x 2 2 := by
    rw [integral_sub (hint i 2 2 i) (hint i 2 i 2), hfirst,
      hswap i 2 i 2, integral_sub (hint 2 2 i i) (hint i i 2 2)]
  simp_rw [hrow]
  rw [← integral_finsetSum (f := fun i x => A x 2 2 * D x i i - A x i i * D x 2 2)
    _ (fun i _ => (hint 2 2 i i).sub (hint i i 2 2))]
  apply integral_congr_ae
  filter_upwards with x
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have hd0 : ∑ i : Fin 3, D x i i = 0 := hdiv x
  have htr : ∑ i : Fin 3, A x i i = -3 * (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) :=
    sum_fderiv_newtonian_gradient x
  rw [hd0, htr]
  change _ = 3 * (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) * D x 2 2
  ring

end ClockBarrier.Analysis
