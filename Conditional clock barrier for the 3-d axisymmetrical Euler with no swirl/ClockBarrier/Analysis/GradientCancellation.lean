/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.WeakL2Pairing
public import ClockBarrier.Analysis.WeakPotential
public import ClockBarrier.Analysis.WeakDivergence
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! # Cancellation of finite-energy exact gradients against solenoidal fields -/

public section

namespace ClockBarrier.Analysis

open MeasureTheory SchwartzMap

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- An actual `C¹` potential whose gradient is bounded and in `L²` is
orthogonal to a bounded `C¹`, finite-energy divergence-free field.
The gradient itself need not be differentiable. -/
theorem integral_inner_exact_gradient_eq_zero {f g : E₃ → E₃} {q : E₃ → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hfc : Continuous f) (hq : ∀ x, HasFDerivAt q (innerSL ℝ (f x)) x)
    (hgd : Differentiable ℝ g) (hgD : Continuous (fderiv ℝ g))
    {F A B : ℝ} (hF : ∀ x, ‖f x‖ ≤ F) (hA : ∀ x, ‖g x‖ ≤ A)
    (hB : ∀ x, ‖fderiv ℝ g x‖ ≤ B)
    (hdiv : ∀ x, ∑ i : Fin 3, fderiv ℝ g x (EuclideanSpace.single i 1) i = 0) :
    (∫ x : E₃, inner ℝ (f x) (g x)) = 0 := by
  let Q : E₃ → ℂ := fun x => (q x : ℂ)
  have hd (x : E₃) : HasFDerivAt Q
      (Complex.ofRealCLM.comp (innerSL ℝ (f x))) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (hq x)
  have hDc : Continuous (fderiv ℝ Q) :=
    (continuous_const.clm_comp ((innerSL ℝ).continuous.comp hfc)).congr
      (fun x => (hd x).fderiv.symm)
  have hDb (x : E₃) : ‖fderiv ℝ Q x‖ ≤ ‖Complex.ofRealCLM‖ * F := by
    rw [(hd x).fderiv]
    exact (Complex.ofRealCLM.opNorm_comp_le (innerSL ℝ (f x))).trans
      (mul_le_mul_of_nonneg_left (by simpa only [innerSL_apply_norm] using hF x) (norm_nonneg _))
  apply integral_inner_eq_zero_of_weak_curl_div hf hg
  · intro i j φ
    have hc := integral_schwartz_fderiv_mul_swap (fun x => (hd x).differentiableAt)
      hDc hDb φ (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    simpa only [(hd _).fderiv, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
      innerSL_apply_apply, EuclideanSpace.inner_single_right, conj_trivial, one_mul] using hc
  · exact sum_integral_schwartz_fderiv_mul_eq_zero hgd hgD hA hB hdiv

end ClockBarrier.Analysis
