/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.NewtonianIntegrationByParts
public import ClockBarrier.Geometry.CurlLinear
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! # Cartesian components of the regularized strain identity

The existing Newtonian integration-by-parts theorem supplies the analytic step.
These component identities allow contraction with an arbitrary strain direction.
-/

public section
namespace ClockBarrier.Analysis
open MeasureTheory Geometry
open scoped NNReal InnerProductSpace
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The antisymmetric derivative contraction of the Newtonian Hessian gives
any Cartesian velocity derivative, with no second velocity derivatives. -/
theorem integral_newtonian_strain_component
    {u : E₃ → E₃} {H α : ℝ≥0} (hu : Differentiable ℝ u)
    (hα : 0 < α) (hD : HolderWith H α (fderiv ℝ u))
    (henergy : Integrable (fun x => ‖u x‖ ^ 2) volume)
    {B : ℝ} (hbound : ∀ x, ‖u x‖ ≤ B)
    (hdiv : ∀ x, ∑ i : Fin 3, fderiv ℝ u x (EuclideanSpace.single i 1) i = 0)
    (j k : Fin 3) :
    let A := fun (x : E₃) (i j : Fin 3) => fderiv ℝ
      (fun y : E₃ => -(y i * (1 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2))) x
        (EuclideanSpace.single j 1)
    let D := fun (x : E₃) (i j : Fin 3) =>
      fderiv ℝ u x (EuclideanSpace.single i 1) j
    (∫ x : E₃, ∑ i : Fin 3, (A x i j * D x k i - A x i j * D x i k)) =
      ∫ x : E₃, 3 * (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) * D x j k := by
  intro A D
  have he (i : Fin 3) : ‖(EuclideanSpace.single i 1 : E₃)‖ = 1 := by simp
  have hint (i j k l : Fin 3) : Integrable (fun x => A x i j * D x k l) volume :=
    integrable_newtonian_hessian_mul_velocity_derivative hu hα hD henergy i l
      (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) (he k)
  have hswap (i j k l : Fin 3) :
      (∫ x, A x i j * D x k l) = ∫ x, A x i k * D x j l :=
    integral_newtonian_derivative_swap hu hα hD henergy hbound i l
      (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) (he j) (he k)
  have hA (x : E₃) (i j : Fin 3) : A x i j = A x j i := by
    simp only [A, fderiv_newtonian_gradient_apply, EuclideanSpace.inner_single_right,
      conj_trivial, one_mul, PiLp.single_apply]
    simp only [eq_comm, mul_comm, mul_left_comm, mul_assoc]
  have hfirst (i : Fin 3) : (∫ x, A x i j * D x k i) = ∫ x, A x j k * D x i i :=
    (integral_congr_ae (ae_of_all _ fun x =>
      congrArg (fun a => a * D x k i) (hA x i j))).trans (hswap j i k i)
  have hrow (i : Fin 3) :
      (∫ x, A x i j * D x k i - A x i j * D x i k) =
        ∫ x, A x j k * D x i i - A x i i * D x j k := by
    rw [integral_sub (hint i j k i) (hint i j i k), hfirst,
      hswap i j i k, integral_sub (hint j k i i) (hint i i j k)]
  refine (integral_finsetSum _ (fun i _ => (hint i j k i).sub (hint i j i k))).trans
    ((Finset.sum_congr rfl (fun i _ => hrow i)).trans
      ((integral_finsetSum _ (fun i _ => (hint j k i i).sub (hint i i j k))).symm.trans ?_))
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    show ∑ i : Fin 3, D x i i = 0 from hdiv x,
    show ∑ i : Fin 3, A x i i = -3 * (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) from
      sum_fderiv_newtonian_gradient x, mul_zero, zero_sub, neg_mul, neg_neg]

/-- A quadratic form is its finite Cartesian component contraction. -/
theorem inner_apply_eq_sum_components (A : E₃ →L[ℝ] E₃) (e : E₃) :
    ⟪e, A e⟫_ℝ = ∑ j : Fin 3, ∑ k : Fin 3,
      e j * e k * A (EuclideanSpace.single j 1) k := by
  have he : (∑ j : Fin 3, e j • (EuclideanSpace.single j 1 : E₃)) = e := by
    simpa only [PiLp.basisFun_repr, PiLp.basisFun_apply] using
      (PiLp.basisFun 2 ℝ (Fin 3)).sum_repr e
  simpa only [map_sum, map_smul, inner_sum, real_inner_smul_right,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
    Finset.mul_sum, PiLp.smul_apply, smul_eq_mul, mul_assoc, mul_comm,
    mul_left_comm] using congrArg (fun v => ⟪e, A v⟫_ℝ) he.symm

/-- Contracting the antisymmetric derivative gives the directional curl kernel. -/
theorem sum_newtonian_strain_eq_curl_kernel (A : E₃ →L[ℝ] E₃) (x e : E₃) :
    let H := fun (i j : Fin 3) => fderiv ℝ
      (fun y : E₃ => -(y i * (1 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2))) x
        (EuclideanSpace.single j 1)
    let w := curlLinearMap A
    (∑ j : Fin 3, ∑ k : Fin 3, e j * e k *
      ∑ i : Fin 3, (H i j * A (EuclideanSpace.single k 1) i -
        H i j * A (EuclideanSpace.single i 1) k)) =
      3 * ⟪e, x⟫_ℝ *
        ⟪e, (!₂[x 1 * w 2 - x 2 * w 1, x 2 * w 0 - x 0 * w 2,
          x 0 * w 1 - x 1 * w 0] : E₃)⟫_ℝ *
        (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) := by
  intro H w
  have h0 : (EuclideanSpace.single 0 1 : E₃) = !₂[1, 0, 0] := by
    ext i; fin_cases i <;> simp
  have h1 : (EuclideanSpace.single 1 1 : E₃) = !₂[0, 1, 0] := by
    ext i; fin_cases i <;> simp
  have h2 : (EuclideanSpace.single 2 1 : E₃) = !₂[0, 0, 1] := by
    ext i; fin_cases i <;> simp
  simp only [Fin.sum_univ_three, H, h0, h1, h2, fderiv_newtonian_gradient_apply,
    w, curlLinearMap_apply]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  ring

/-- The regularized Biot–Savart identity for an arbitrary quadratic strain
direction. The assumptions only require first derivatives of the velocity. -/
theorem integral_regularized_directional_strain
    {u : E₃ → E₃} {H α : ℝ≥0} (hu : Differentiable ℝ u)
    (hα : 0 < α) (hD : HolderWith H α (fderiv ℝ u))
    (henergy : Integrable (fun x => ‖u x‖ ^ 2) volume)
    {B : ℝ} (hbound : ∀ x, ‖u x‖ ≤ B)
    (hdiv : ∀ x, ∑ i : Fin 3, fderiv ℝ u x (EuclideanSpace.single i 1) i = 0)
    (e : E₃) :
    (∫ x : E₃, 3 * ⟪e, x⟫_ℝ *
      ⟪e, (!₂[x 1 * curlLinearMap (fderiv ℝ u x) 2 -
          x 2 * curlLinearMap (fderiv ℝ u x) 1,
        x 2 * curlLinearMap (fderiv ℝ u x) 0 -
          x 0 * curlLinearMap (fderiv ℝ u x) 2,
        x 0 * curlLinearMap (fderiv ℝ u x) 1 -
          x 1 * curlLinearMap (fderiv ℝ u x) 0] : E₃)⟫_ℝ *
        (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)) =
      ∫ x : E₃, 3 * (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) *
        ⟪e, fderiv ℝ u x e⟫_ℝ := by
  let A (x : E₃) (i j : Fin 3) : ℝ := fderiv ℝ
    (fun y : E₃ => -(y i * (1 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2))) x
      (EuclideanSpace.single j 1)
  let D (x : E₃) (i j : Fin 3) : ℝ :=
    fderiv ℝ u x (EuclideanSpace.single i 1) j
  let ρ (x : E₃) : ℝ := 3 * (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)
  have hint (i j k l : Fin 3) : Integrable (fun x => A x i j * D x k l) volume :=
    integrable_newtonian_hessian_mul_velocity_derivative hu hα hD henergy i l
      (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) (by simp)
  have hright (j k : Fin 3) : Integrable (fun x => ρ x * D x j k) volume := by
    have hid (x : E₃) : (∑ i : Fin 3, A x i i * D x j k) = -(ρ x * D x j k) := by
      rw [← Finset.sum_mul]
      change (∑ i : Fin 3, fderiv ℝ
        (fun y : E₃ => -(y i * (1 + ‖y‖ ^ 2) ^ (-(3 : ℝ) / 2))) x
          (EuclideanSpace.single i 1)) * D x j k = _
      rw [sum_fderiv_newtonian_gradient]
      simp only [ρ, neg_mul]
    have hn : Integrable (fun x => -(∑ i : Fin 3, A x i i * D x j k)) volume :=
      (integrable_finsetSum Finset.univ (fun i _ => hint i i j k)).neg
    simpa only [hid, neg_neg] using hn
  have hleft (j k : Fin 3) : Integrable
      (fun x => ∑ i : Fin 3, (A x i j * D x k i - A x i j * D x i k)) volume :=
    integrable_finsetSum Finset.univ (fun i _ => (hint i j k i).sub (hint i j i k))
  have hrow (j k : Fin 3) :
      (∫ x, e j * e k * ∑ i : Fin 3, (A x i j * D x k i - A x i j * D x i k)) =
        ∫ x, e j * e k * (ρ x * D x j k) := by
    rw [integral_const_mul, integral_const_mul]
    exact congrArg (fun z => e j * e k * z)
      (integral_newtonian_strain_component hu hα hD henergy hbound hdiv j k)
  calc
    _ = ∫ x, ∑ j : Fin 3, ∑ k : Fin 3,
        e j * e k * ∑ i : Fin 3, (A x i j * D x k i - A x i j * D x i k) :=
      integral_congr_ae (ae_of_all _ fun x =>
        (sum_newtonian_strain_eq_curl_kernel (fderiv ℝ u x) x e).symm)
    _ = ∑ j : Fin 3, ∑ k : Fin 3, ∫ x,
        e j * e k * ∑ i : Fin 3, (A x i j * D x k i - A x i j * D x i k) := by
      rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _
        (fun k _ => (hleft j k).const_mul (e j * e k)))]
      exact Finset.sum_congr rfl fun j _ => integral_finsetSum _
        (fun k _ => (hleft j k).const_mul (e j * e k))
    _ = ∑ j : Fin 3, ∑ k : Fin 3, ∫ x, e j * e k * (ρ x * D x j k) :=
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hrow j k
    _ = ∫ x, ∑ j : Fin 3, ∑ k : Fin 3, e j * e k * (ρ x * D x j k) := by
      rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _
        (fun k _ => (hright j k).const_mul (e j * e k)))]
      exact Finset.sum_congr rfl fun j _ => (integral_finsetSum _
        (fun k _ => (hright j k).const_mul (e j * e k))).symm
    _ = _ := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      change (∑ j : Fin 3, ∑ k : Fin 3, e j * e k * (ρ x * D x j k)) =
        ρ x * ⟪e, fderiv ℝ u x e⟫_ℝ
      rw [inner_apply_eq_sum_components]
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
        dsimp only [ρ, D]
        ring

end ClockBarrier.Analysis
