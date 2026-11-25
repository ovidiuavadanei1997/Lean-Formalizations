/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.SmoothTopology
public import ClockBarrier.Analysis.SmoothFieldScaling

/-! # Actual time derivatives in the bounded-field norm from spatial L² jets -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Sobolev
open MeasureTheory ContinuousLinearMap SmoothL2Field Filter Topology
open scoped BoundedContinuousFunction
local notation "Space" => EuclideanSpace ℝ (Fin 3)
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
theorem zeroField_jetLp (n : ℕ) : (zeroField : SmoothL2Field V).jetLp n = 0 := by
  apply Lp.ext
  filter_upwards [(zeroField : SmoothL2Field V).jetLp_ae n, Lp.coeFn_zero (E := Space [×n]→L[ℝ] V) (p := 2)
    (μ := (volume : Measure Space))] with x hj hz
  rw [hj, hz]
  change iteratedFDeriv ℝ n (0 : Space → V) x = 0
  rw [iteratedFDeriv_zero]
  rfl

theorem finiteField_zero : finiteField (zeroField : SmoothL2Field V) = 0 := by
  ext x
  rw [finiteField_apply]
  rfl

theorem finiteField_hasDerivWithinAt (A : ℝ → SmoothL2Field V) (B : SmoothL2Field V)
    (s : Set ℝ) (t : ℝ)
    (h : ∀ n, HasDerivWithinAt (fun r => (A r).jetLp n) (B.jetLp n) s t) :
    HasDerivWithinAt (fun r => finiteField (A r)) (finiteField B) s t := by
  let R (r : ℝ) := scaleField (‖r-t‖⁻¹) (fieldSub (fieldSub (A r) (A t)) (scaleField (r-t) B))
  have hj (n : ℕ) : Tendsto (fun r => (R r).jetLp n) (𝓝[s] t) (𝓝 ((zeroField : SmoothL2Field V).jetLp n)) := by
    rw [zeroField_jetLp]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [R, scaleField_jetLp, jetLp_fieldSub, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_norm, abs_abs] using (hasDerivWithinAt_iff_tendsto.mp (h n))
  have hR : Tendsto R (𝓝[s] t) (𝓝 (zeroField : SmoothL2Field V)) := by
    rw [nhds_induced, tendsto_comap_iff]
    exact tendsto_pi_nhds.mpr hj
  have hF := ((continuous_finiteField (fun a : SmoothL2Field V => a)
    continuous_smooth_jet).tendsto zeroField).comp hR
  rw [finiteField_zero] at hF
  have he (r : ℝ) : finiteField (R r) = ‖r-t‖⁻¹ •
      (finiteField (A r)-finiteField (A t)-(r-t) • finiteField B) := by
    ext x
    simp only [finiteField_apply, R, scaleField_field, fieldSub_field,
      BoundedContinuousFunction.smul_apply, BoundedContinuousFunction.sub_apply]
  apply hasDerivWithinAt_iff_tendsto.mpr
  simpa only [Function.comp_def, he, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, abs_abs, norm_zero] using hF.norm

theorem field_hasDerivWithinAt (A : ℝ → SmoothL2Field V) (B : SmoothL2Field V)
    (s : Set ℝ) (t : ℝ)
    (h : ∀ n, HasDerivWithinAt (fun r => (A r).jetLp n) (B.jetLp n) s t) (x : Space) :
    HasDerivWithinAt (fun r => (A r).field x) (B.field x) s t := by
  simpa only [Function.comp_def, BoundedContinuousFunction.evalCLM_apply, finiteField_apply] using
    (BoundedContinuousFunction.evalCLM ℝ x).hasFDerivAt.comp_hasDerivWithinAt t
      (finiteField_hasDerivWithinAt A B s t h)

end ClockBarrier.Analysis.Sobolev
