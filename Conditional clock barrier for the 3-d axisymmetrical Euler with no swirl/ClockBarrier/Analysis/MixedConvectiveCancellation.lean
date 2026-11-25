/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.GradientCancellation
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Module

/-! # Mixed convective cancellation for the Euler difference estimate -/

public section

namespace ClockBarrier.Analysis

open MeasureTheory

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Advection by a solenoidal field preserves the quadratic integral of any
bounded C¹ finite-energy field with bounded derivative. -/
theorem integral_inner_mixed_convective_eq_zero {u v : E₃ → E₃}
    (hu : MemLp u 2 volume) (hud : Differentiable ℝ u)
    (hD : Continuous (fderiv ℝ u)) {A B : ℝ}
    (hA : ∀ x, ‖u x‖ ≤ A) (hB : ∀ x, ‖fderiv ℝ u x‖ ≤ B)
    (hv : MemLp v 2 volume) (hvd : Differentiable ℝ v)
    (hvD : Continuous (fderiv ℝ v)) {C D : ℝ}
    (hC : ∀ x, ‖v x‖ ≤ C) (hDD : ∀ x, ‖fderiv ℝ v x‖ ≤ D)
    (hdiv : ∀ x, ∑ i : Fin 3, fderiv ℝ v x (EuclideanSpace.single i 1) i = 0) :
    (∫ x : E₃, inner ℝ (u x) (fderiv ℝ u x (v x))) = 0 := by
  let f : E₃ → E₃ := fun x => (fderiv ℝ u x).adjoint (u x)
  have hfc : Continuous f :=
    (ContinuousLinearMap.adjoint.continuous.comp hD).clm_apply hud.continuous
  have hfb (x : E₃) : ‖f x‖ ≤ B * ‖u x‖ := by
    exact ((fderiv ℝ u x).adjoint.le_opNorm (u x)).trans
      (mul_le_mul_of_nonneg_right (by simpa using hB x) (norm_nonneg _))
  have hf : MemLp f 2 volume := (hu.norm.const_mul B).mono' hfc.aestronglyMeasurable
    (Filter.Eventually.of_forall hfb)
  have hB0 : 0 ≤ B := (norm_nonneg (fderiv ℝ u 0)).trans (hB 0)
  have hq (x : E₃) : HasFDerivAt (fun y => (2 : ℝ)⁻¹ • ‖u y‖ ^ 2) (innerSL ℝ (f x)) x := by
    apply ((hud x).hasFDerivAt.norm_sq.const_smul (2 : ℝ)⁻¹).congr_fderiv
    simp only [ContinuousLinearMap.innerSL_apply_comp, two_smul, f]
    module
  have hz := integral_inner_exact_gradient_eq_zero hf hv hfc hq hvd hvD
    (fun x => (hfb x).trans (mul_le_mul_of_nonneg_left (hA x) hB0)) hC hDD hdiv
  simpa only [f, ContinuousLinearMap.adjoint_inner_left] using hz

end ClockBarrier.Analysis
