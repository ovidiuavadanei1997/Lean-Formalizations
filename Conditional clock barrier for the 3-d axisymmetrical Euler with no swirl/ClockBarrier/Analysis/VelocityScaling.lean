/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.DerivativeTail
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Spatial rescaling preserves the velocity regularity used by Biot–Savart -/

public section

namespace ClockBarrier.Analysis

open MeasureTheory
open scoped NNReal

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The amplitude normalization cancels the derivative of the spatial dilation. -/
theorem fderiv_rescaled_velocity {u : E₃ → E₃} (hu : Differentiable ℝ u)
    {ε : ℝ} (hε : ε ≠ 0) (x : E₃) :
    fderiv ℝ (fun y => ε⁻¹ • u (ε • y)) x = fderiv ℝ u (ε • x) := by
  have hd : Differentiable ℝ (fun y => u (ε • y)) :=
    hu.comp (differentiable_id.const_smul ε)
  rw [fderiv_fun_const_smul (hd x),
    fderiv_comp_smul, smul_smul, inv_mul_cancel₀ hε, one_smul]

/-- Rescaling retains a global Hölder bound on the actual derivative. -/
theorem exists_holderWith_fderiv_rescaled_velocity
    {u : E₃ → E₃} {H α : ℝ≥0} (hu : Differentiable ℝ u)
    (hD : HolderWith H α (fderiv ℝ u)) {ε : ℝ} (hε : ε ≠ 0) :
    ∃ Hε : ℝ≥0, HolderWith Hε α (fderiv ℝ (fun y => ε⁻¹ • u (ε • y))) := by
  have hs := (ε • ContinuousLinearMap.id ℝ E₃).lipschitz.holderWith
  have hc := hD.comp hs
  refine ⟨H * ‖ε • ContinuousLinearMap.id ℝ E₃‖₊ ^ (α : ℝ), ?_⟩
  have heq : fderiv ℝ (fun y => ε⁻¹ • u (ε • y)) = fun x => fderiv ℝ u (ε • x) :=
    funext (fderiv_rescaled_velocity hu hε)
  rw [heq]
  simpa only [mul_one, Function.comp_def, smul_apply, ContinuousLinearMap.id_apply] using hc

/-- Rescaling retains finite kinetic energy. -/
theorem integrable_sq_norm_rescaled_velocity
    {u : E₃ → E₃} (henergy : Integrable (fun x => ‖u x‖ ^ 2) volume)
    {ε : ℝ} (hε : ε ≠ 0) :
    Integrable (fun x => ‖ε⁻¹ • u (ε • x)‖ ^ 2) volume := by
  simpa only [norm_smul, mul_pow] using (henergy.comp_smul hε).const_mul (‖ε⁻¹‖ ^ 2)

end ClockBarrier.Analysis
