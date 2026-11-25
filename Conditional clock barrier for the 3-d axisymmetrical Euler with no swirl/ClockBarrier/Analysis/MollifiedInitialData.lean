/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.RegularizedField
public import ClockBarrier.Analysis.BoundedMollification
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Trace

/-! # Scale-independent C¹ Hölder estimates for smoothed initial data -/

public section
namespace ClockBarrier.Analysis.Solenoidal
open MeasureTheory ContinuousLinearMap Filter
open scoped Convolution BoundedContinuousFunction Topology NNReal
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem mollifierField_toLp_eq (n : ℕ) (u : E₃ →ᵇ E₃)
    (hu : MemLp (u : E₃ → E₃) 2 volume) :
    (mollifierField n (hu.toLp u) : E₃ → E₃) =
      (bump n).normed volume ⋆[lsmul ℝ ℝ, volume] (u : E₃ → E₃) := by
  exact (funext (mollifierField_apply n (hu.toLp u))).trans
    (convolution_congr (lsmul ℝ ℝ) (Filter.EventuallyEq.refl _ _) hu.coeFn_toLp)

/-- Mollification commutes with the actual bounded first derivative. -/
theorem mollifierDerivative_toLp_eq (n : ℕ) (u : E₃ →ᵇ E₃)
    (D : E₃ →ᵇ (E₃ →L[ℝ] E₃)) (hu : MemLp (u : E₃ → E₃) 2 volume)
    (hD : ∀ x, HasFDerivAt (u : E₃ → E₃) (D x) x) (x : E₃) :
    mollifierDerivative n (hu.toLp u) x =
      ((bump n).normed volume ⋆[lsmul ℝ ℝ, volume] (D : E₃ → E₃ →L[ℝ] E₃)) x := by
  have h := mollifierField_hasFDerivAt n (hu.toLp u) x
  rw [mollifierField_toLp_eq n u hu] at h
  exact h.unique (hasFDerivAt_normed_convolution (bump n) u D hD x)

theorem mollifierField_toLp_norm_le (n : ℕ) (u : E₃ →ᵇ E₃)
    (hu : MemLp (u : E₃ → E₃) 2 volume) : ‖mollifierField n (hu.toLp u)‖ ≤ ‖u‖ := by
  exact BoundedContinuousFunction.norm_le_of_nonempty.mpr (fun x =>
    (congrArg norm (congrFun (mollifierField_toLp_eq n u hu) x)).trans_le
      (norm_normed_convolution_le (bump n) u x))

theorem mollifierDerivative_toLp_norm_le (n : ℕ) (u : E₃ →ᵇ E₃)
    (D : E₃ →ᵇ (E₃ →L[ℝ] E₃)) (hu : MemLp (u : E₃ → E₃) 2 volume)
    (hD : ∀ x, HasFDerivAt (u : E₃ → E₃) (D x) x) :
    ‖mollifierDerivative n (hu.toLp u)‖ ≤ ‖D‖ := by
  exact BoundedContinuousFunction.norm_le_of_nonempty.mpr (fun x =>
    (congrArg norm (mollifierDerivative_toLp_eq n u D hu hD x)).trans_le
      (norm_normed_convolution_le (bump n) D x))

theorem mollifierDerivative_toLp_holder (n : ℕ) (u : E₃ →ᵇ E₃)
    (D : E₃ →ᵇ (E₃ →L[ℝ] E₃)) (hu : MemLp (u : E₃ → E₃) 2 volume)
    (hD : ∀ x, HasFDerivAt (u : E₃ → E₃) (D x) x)
    {H α : ℝ≥0} (hH : HolderWith H α (D : E₃ → E₃ →L[ℝ] E₃)) :
    HolderWith H α (mollifierDerivative n (hu.toLp u) : E₃ → E₃ →L[ℝ] E₃) := by
  simpa only [show (mollifierDerivative n (hu.toLp u) : E₃ → E₃ →L[ℝ] E₃) =
    (bump n).normed volume ⋆[lsmul ℝ ℝ, volume] (D : E₃ → E₃ →L[ℝ] E₃) from
      funext (mollifierDerivative_toLp_eq n u D hu hD)] using
        (holderWith_normed_convolution (bump n) D.continuous hH)

theorem mollifierDerivative_error_le (n : ℕ) (u : E₃ →ᵇ E₃)
    (D : E₃ →ᵇ (E₃ →L[ℝ] E₃)) (hu : MemLp (u : E₃ → E₃) 2 volume)
    (hD : ∀ x, HasFDerivAt (u : E₃ → E₃) (D x) x)
    {H α : ℝ≥0} (hH : HolderWith H α (D : E₃ → E₃ →L[ℝ] E₃)) :
    ‖mollifierDerivative n (hu.toLp u) - D‖ ≤
      (H : ℝ) * (2 * cutoffScale n) ^ (α : ℝ) := by
  apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
  exact fun x => by
    simpa only [BoundedContinuousFunction.sub_apply, mollifierDerivative_toLp_eq n u D hu hD,
      ← dist_eq_norm, bump] using
        (dist_normed_convolution_le_holder (μ := volume) (bump n) D.continuous hH x)

theorem mollifierField_error_le (n : ℕ) (u : E₃ →ᵇ E₃)
    (D : E₃ →ᵇ (E₃ →L[ℝ] E₃)) (hu : MemLp (u : E₃ → E₃) 2 volume)
    (hD : ∀ x, HasFDerivAt (u : E₃ → E₃) (D x) x) :
    ‖mollifierField n (hu.toLp u) - u‖ ≤ ‖D‖ * (2 * cutoffScale n) := by
  have hL : LipschitzWith ‖D‖₊ (u : E₃ → E₃) :=
    lipschitzWith_of_nnnorm_fderiv_le (fun x => (hD x).differentiableAt)
      (fun x => by simpa only [(hD x).fderiv] using D.nnnorm_coe_le_nnnorm x)
  apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
  exact fun x => by
    simpa only [BoundedContinuousFunction.sub_apply,
      show mollifierField n (hu.toLp u) x = _ from congrFun (mollifierField_toLp_eq n u hu) x,
      ← dist_eq_norm, bump, NNReal.coe_one, Real.rpow_one, coe_nnnorm] using
        (dist_normed_convolution_le_holder (μ := volume) (bump n) u.continuous hL.holderWith x)

theorem mollifierField_energy_le (n : ℕ) (u : L2) :
    (eLpNorm (mollifierField n u : E₃ → E₃) 2 volume).toReal ≤ ‖u‖ := by
  rw [← eLpNorm_congr_ae (mollify_ae_mollifierField n u), ← Lp.norm_def]
  exact mollify_norm_le n u

theorem mollifierField_tendsto (u : E₃ →ᵇ E₃) (D : E₃ →ᵇ (E₃ →L[ℝ] E₃))
    (hu : MemLp (u : E₃ → E₃) 2 volume)
    (hD : ∀ x, HasFDerivAt (u : E₃ → E₃) (D x) x) :
    Tendsto (fun n => mollifierField n (hu.toLp u)) atTop (𝓝 u) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => mollifierField_error_le n u D hu hD)
  simpa only [mul_zero] using (cutoffScale_tendsto.const_mul 2).const_mul ‖D‖

theorem mollifierDerivative_tendsto (u : E₃ →ᵇ E₃) (D : E₃ →ᵇ (E₃ →L[ℝ] E₃))
    (hu : MemLp (u : E₃ → E₃) 2 volume)
    (hD : ∀ x, HasFDerivAt (u : E₃ → E₃) (D x) x)
    {H α : ℝ≥0} (hα : 0 < α) (hH : HolderWith H α (D : E₃ → E₃ →L[ℝ] E₃)) :
    Tendsto (fun n => mollifierDerivative n (hu.toLp u)) atTop (𝓝 D) := by
  have hr : Tendsto (fun n => (2 * cutoffScale n) ^ (α : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, Real.zero_rpow (NNReal.coe_pos.mpr hα).ne'] using
      ((Real.continuous_rpow_const α.coe_nonneg).tendsto (2 * 0)).comp (cutoffScale_tendsto.const_mul 2)
  refine (tendsto_iff_norm_sub_tendsto_zero (f := fun n => mollifierDerivative n (hu.toLp u))
    (b := D)).mpr ?_
  apply squeeze_zero (fun n => norm_nonneg (mollifierDerivative n (hu.toLp u) - D))
    (fun n => mollifierDerivative_error_le n u D hu hD hH)
  simpa only [mul_zero] using hr.const_mul (H : ℝ)

end ClockBarrier.Analysis.Solenoidal
