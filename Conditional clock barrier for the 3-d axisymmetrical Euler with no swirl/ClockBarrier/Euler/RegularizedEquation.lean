/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.RegularizedField
public import ClockBarrier.Analysis.BoundedLpOperator
public import ClockBarrier.Dynamics.QuadraticFlow
import ClockBarrier.Analysis.ConvectiveCancellation
import Mathlib.MeasureTheory.Function.Holder

/-! # The concrete symmetric regularized Euler equation on L²

With `Sₙ = P Jₙ P`, the equation is `u' = -Sₙ (D(Sₙ u) (Sₙ u))`.
The bounded bilinear map below uses the actual convolution representatives.
-/

@[expose] public noncomputable section
namespace ClockBarrier.Euler.Regularized
open MeasureTheory ContinuousLinearMap ClockBarrier.Analysis ClockBarrier.Analysis.Solenoidal
open scoped ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

def advection (n : ℕ) : L2 →L[ℝ] L2 →L[ℝ] L2 :=
  ((ContinuousLinearMap.id ℝ (E₃ →L[ℝ] E₃)).holderL volume ∞ 2 2).bilinearComp
    (boundedToLpTop.comp (regularizedDerivative n)) (regularizerMap n)

theorem advection_ae (n : ℕ) (u v : L2) :
    advection n u v =ᵐ[volume]
      fun x => regularizedDerivative n u x (regularizedField n v x) := by
  filter_upwards [(ContinuousLinearMap.id ℝ (E₃ →L[ℝ] E₃)).coeFn_holder (r := 2)
      (boundedToLpTop (regularizedDerivative n u)) (regularizerMap n v),
    ((regularizedDerivative n u).memLp_top (μ := volume)).coeFn_toLp,
    regularizerMap_ae_field n v] with x hx hd hv
  change (advection n u v : E₃ → E₃) x =
    (((regularizedDerivative n u).memLp_top (μ := volume)).toLp
      (regularizedDerivative n u)) x ((regularizerMap n v) x) at hx
  simpa only [hd, hv] using hx

def quadratic (n : ℕ) : L2 →L[ℝ] L2 →L[ℝ] L2 :=
  (compL ℝ L2 L2 L2 (-regularizerMap n)).comp (advection n)

theorem quadratic_apply (n : ℕ) (u v : L2) :
    quadratic n u v = -regularizerMap n (advection n u v) := rfl

theorem integral_convective_eq_zero (n : ℕ) (u : L2) :
    (∫ x : E₃, inner ℝ (regularizedField n u x)
      (regularizedDerivative n u x (regularizedField n u x))) = 0 := by
  have he : fderiv ℝ (regularizedField n u : E₃ → E₃) =
      (regularizedDerivative n u : E₃ → E₃ →L[ℝ] E₃) :=
    funext (fun x => (regularizedField_hasFDerivAt n u x).fderiv)
  simpa only [he] using integral_inner_convective_eq_zero (regularizedField_memLp n u)
    (fun x => (regularizedField_hasFDerivAt n u x).differentiableAt)
    (he.symm ▸ (regularizedDerivative n u).continuous)
    (regularizedField n u).norm_coe_le_norm
    (fun x => (congrFun he x).symm ▸ (regularizedDerivative n u).norm_coe_le_norm x)
    (regularizedField_divergence n u)

theorem quadratic_energy (n : ℕ) (u : L2) : inner ℝ u (quadratic n u u) = 0 := by
  rw [quadratic_apply, inner_neg_right, ← regularizerMap_symmetric, L2.inner_def,
    neg_eq_zero]
  refine Eq.trans (integral_congr_ae ?_) (integral_convective_eq_zero n u)
  filter_upwards [regularizerMap_ae_field n u, advection_ae n u u] with x hx hy using
    congrArg₂ (inner ℝ) hx hy

/-- A trajectory of the concrete regularized Euler equation exists on every
prescribed finite positive interval and preserves its L² norm exactly. -/
theorem exists_solution_Icc (n : ℕ) (u₀ : L2) {T : ℝ} (hT : 0 ≤ T) :
    ∃ u : ℝ → L2, u 0 = u₀ ∧ ContinuousOn u (Set.Icc 0 T) ∧
      (∀ t ∈ Set.Ico 0 T,
        HasDerivWithinAt u (quadratic n (u t) (u t)) (Set.Ici t) t) ∧
      ∀ t ∈ Set.Icc 0 T, ‖u t‖ = ‖u₀‖ :=
  Dynamics.QuadraticFlow.exists_quadratic_solution_Icc (quadratic n) (quadratic_energy n) u₀ hT

end ClockBarrier.Euler.Regularized
