/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.MixedConvectiveCancellation
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Module

/-! # Quadratic estimate for the difference of Euler convection terms -/

public section
namespace ClockBarrier.Analysis
open MeasureTheory
open scoped BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Bounded operator fields preserve finite energy. -/
theorem memLp_bounded_apply (D : E₃ →ᵇ (E₃ →L[ℝ] E₃))
    {u : E₃ →ᵇ E₃} (hu : MemLp u 2 volume) :
    MemLp (fun x => D x (u x)) 2 volume := by
  apply (hu.norm.const_mul ‖D‖).mono' (D.continuous.clm_apply u.continuous).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => ((D x).le_opNorm (u x)).trans
    (mul_le_mul_of_nonneg_right (D.norm_coe_le_norm x) (norm_nonneg _)))

/-- The skew-advection term cancels, leaving the familiar Lipschitz quadratic
bound. Neither spatial derivatives nor pressure need be square-integrable. -/
theorem integral_inner_convective_sub_ge
    {u v : E₃ →ᵇ E₃} {Du Dv : E₃ →ᵇ (E₃ →L[ℝ] E₃)}
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hdu : ∀ x, HasFDerivAt u (Du x) x) (hdv : ∀ x, HasFDerivAt v (Dv x) x)
    (hdiv : ∀ x, ∑ i : Fin 3, Du x (EuclideanSpace.single i 1) i = 0) :
    -‖Dv‖ * (∫ x : E₃, ‖u x - v x‖ ^ 2) ≤
      ∫ x : E₃, inner ℝ (Du x (u x) - Dv x (v x)) (u x - v x) := by
  let w : E₃ →ᵇ E₃ := u - v
  have hw : MemLp w 2 volume := hu.sub hv
  have hdw (x : E₃) : HasFDerivAt w ((Du - Dv) x) x := (hdu x).sub (hdv x)
  have hfw : fderiv ℝ w = Du - Dv := funext (fun x => (hdw x).fderiv)
  have hfu : fderiv ℝ u = Du := funext (fun x => (hdu x).fderiv)
  have hc := integral_inner_mixed_convective_eq_zero hw
    (fun x => (hdw x).differentiableAt) (by rw [hfw]; exact (Du - Dv).continuous)
    w.norm_coe_le_norm (fun x => by rw [hfw]; exact (Du - Dv).norm_coe_le_norm x)
    hu (fun x => (hdu x).differentiableAt) (by rw [hfu]; exact Du.continuous)
    u.norm_coe_le_norm (fun x => by rw [hfu]; exact Du.norm_coe_le_norm x)
    (fun x => by rw [hfu]; exact hdiv x)
  have hA : Integrable (fun x => inner ℝ ((Du - Dv) x (u x)) (w x)) :=
    memLp_one_iff_integrable.mp ((innerSL ℝ (E := E₃)).memLp_of_bilin 1
      (memLp_bounded_apply (Du - Dv) hu) hw)
  have hB : Integrable (fun x => inner ℝ (Dv x (w x)) (w x)) :=
    memLp_one_iff_integrable.mp ((innerSL ℝ (E := E₃)).memLp_of_bilin 1
      (memLp_bounded_apply Dv hw) hw)
  have he (x : E₃) : Du x (u x) - Dv x (v x) =
      (Du - Dv) x (u x) + Dv x (w x) := by
    simp only [w, BoundedContinuousFunction.sub_apply, sub_apply, map_sub]
    module
  change -‖Dv‖ * (∫ x : E₃, ‖w x‖ ^ 2) ≤
    ∫ x : E₃, inner ℝ (Du x (u x) - Dv x (v x)) (w x)
  simp_rw [he, inner_add_left]
  rw [integral_add hA hB]
  have hz : (∫ x : E₃, inner ℝ ((Du - Dv) x (u x)) (w x)) = 0 := by
    simpa only [hfw, real_inner_comm, BoundedContinuousFunction.sub_apply, Pi.sub_apply] using hc
  rw [hz, zero_add]
  have hsq : Integrable (fun x => ‖w x‖ ^ 2) := hw.norm.integrable_sq
  rw [← integral_const_mul]
  apply integral_mono (hsq.const_mul (-‖Dv‖)) hB
  intro x
  have hb := abs_real_inner_le_norm (Dv x (w x)) (w x)
  have hn := ((Dv x).le_opNorm (w x)).trans
    (mul_le_mul_of_nonneg_right (Dv.norm_coe_le_norm x) (norm_nonneg _))
  have hh := (neg_abs_le (inner ℝ (Dv x (w x)) (w x))).trans
    (le_refl _)
  change -‖Dv‖ * ‖w x‖ ^ 2 ≤ _
  nlinarith [mul_le_mul_of_nonneg_right hn (norm_nonneg (w x))]

end ClockBarrier.Analysis
