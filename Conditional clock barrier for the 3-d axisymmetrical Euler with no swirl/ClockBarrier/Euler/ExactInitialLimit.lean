/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.ExactMollifiedFamily
public import ClockBarrier.Euler.ExactSpatialLimit

/-! # The rough limit attains the original datum and its actual spatial derivative -/
public section
namespace ClockBarrier.Euler.Smooth
open Set Filter MeasureTheory ContinuousLinearMap ClockBarrier.Analysis
  Solenoidal SmoothL2Field Sobolev
open scoped Topology NNReal BoundedContinuousFunction
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem exact_initial_limit {T : ℝ} (hT : 0 ≤ T)
    (u₀ : Space →ᵇ Space) (D₀ : Space →ᵇ (Space →L[ℝ] Space))
    (hLp : MemLp (u₀ : Space → Space) 2 volume)
    (hd : ∀ x, HasFDerivAt (u₀ : Space → Space) (D₀ x) x)
    {H α : ℝ≥0} (hα : 0 < α) (hH : HolderWith H α (D₀ : Space → Space →L[ℝ] Space))
    (U : ℕ → ℝ → SmoothL2Field Space)
    (hUc : ∀ k m, Continuous (fun t => (U k t).jetLp m))
    (hinit : ∀ k, U k 0 = mollifiedSmoothField k (hLp.toLp u₀))
    (V : C(Icc (0 : ℝ) T, L2)) (v : C(Icc (0 : ℝ) T, Space →ᵇ Space))
    (D : C(Icc (0 : ℝ) T, Space →ᵇ (Space →L[ℝ] Space)))
    (hV : Tendsto (fun k => fieldPath (fun t : Icc (0 : ℝ) T => U k t)
      (fun m => (hUc k m).comp continuous_subtype_val)) atTop (𝓝 V))
    (hv : Tendsto (fun k => boundedFieldPath (fun t : Icc (0 : ℝ) T => U k t)
      (fun m => (hUc k m).comp continuous_subtype_val)) atTop (𝓝 v))
    (hD : Tendsto (fun k => boundedFieldPath (fun t : Icc (0 : ℝ) T => (U k t).derivative)
      (continuous_jetLp_derivative _ (fun m => (hUc k m).comp continuous_subtype_val)))
      atTop (𝓝 D)) :
    V ⟨0, le_rfl, hT⟩ = hLp.toLp u₀ ∧
      v ⟨0, le_rfl, hT⟩ = u₀ ∧ D ⟨0, le_rfl, hT⟩ = D₀ := by
  let z : Icc (0 : ℝ) T := ⟨0, le_rfl, hT⟩
  have hV0 := ((ContinuousMap.evalCLM ℝ z).continuous.tendsto V).comp hV
  have hv0 := ((ContinuousMap.evalCLM ℝ z).continuous.tendsto v).comp hv
  have hD0 := ((ContinuousMap.evalCLM ℝ z).continuous.tendsto D).comp hD
  have hV0' : Tendsto (fun k => (mollifiedSmoothField k (hLp.toLp u₀)).toLp)
      atTop (𝓝 (V z)) := by
    simpa only [Function.comp_def, ContinuousMap.evalCLM_apply, fieldPath_apply,
      z, hinit] using hV0
  have hv0' : Tendsto (fun k => mollifierField k (hLp.toLp u₀)) atTop (𝓝 (v z)) := by
    simpa only [Function.comp_def, ContinuousMap.evalCLM_apply, boundedFieldPath,
      ContinuousMap.coe_mk, z, hinit, finiteField_mollified] using hv0
  have hD0' : Tendsto (fun k => mollifierDerivative k (hLp.toLp u₀)) atTop (𝓝 (D z)) := by
    simpa only [Function.comp_def, ContinuousMap.evalCLM_apply, boundedFieldPath,
      ContinuousMap.coe_mk, z, hinit, finiteField_mollified_derivative] using hD0
  refine ⟨tendsto_nhds_unique hV0' (mollifiedSmoothField_tendsto _),
    tendsto_nhds_unique hv0' (mollifierField_tendsto u₀ D₀ hLp hd), ?_⟩
  apply BoundedContinuousFunction.ext
  intro x
  exact tendsto_nhds_unique
    ((BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hD0').tendsto_at x)
    ((BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      (mollifierDerivative_tendsto u₀ D₀ hLp hd hα hH)).tendsto_at x)

end ClockBarrier.Euler.Smooth
