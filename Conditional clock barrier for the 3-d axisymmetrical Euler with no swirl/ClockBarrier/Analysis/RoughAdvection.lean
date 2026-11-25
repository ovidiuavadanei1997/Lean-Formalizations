/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.L2Apply
public import ClockBarrier.Analysis.SolenoidalProjection
public import Mathlib.Topology.ContinuousMap.Compact

/-! # Strong L² passage to the Euler nonlinearity using only C¹ and L² convergence -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Solenoidal
open MeasureTheory ContinuousLinearMap Filter
open scoped Topology ENNReal BoundedContinuousFunction
local notation "Space" => EuclideanSpace ℝ (Fin 3)

def boundedApplyL2 (D : Space →ᵇ (Space →L[ℝ] Space)) (U : L2) : L2 :=
  ((ContinuousLinearMap.id ℝ (Space →L[ℝ] Space)).holderL (volume : Measure Space) ∞ 2 2)
    ((D.memLp_top (μ := volume)).toLp D) U

theorem boundedApplyL2_ae (D : Space →ᵇ (Space →L[ℝ] Space)) (U : L2) :
    boundedApplyL2 D U =ᵐ[volume] fun x => D x (U x) := by
  filter_upwards [(ContinuousLinearMap.id ℝ (Space →L[ℝ] Space)).coeFn_holder (r := 2)
    ((D.memLp_top (μ := volume)).toLp D) U,
    (D.memLp_top (μ := volume)).coeFn_toLp] with x hx hd
  simpa only [boundedApplyL2, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.id_apply, hd] using hx

theorem continuous_boundedApplyL2 :
    Continuous (fun p : (Space →ᵇ (Space →L[ℝ] Space)) × L2 => boundedApplyL2 p.1 p.2) := by
  exact (((ContinuousLinearMap.id ℝ (Space →L[ℝ] Space)).holderL
    (volume : Measure Space) ∞ 2 2).continuous.comp
      (continuous_bounded_toLp_top.comp continuous_fst)).clm_apply continuous_snd

variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K]

def advectionPath (D : C(K, Space →ᵇ (Space →L[ℝ] Space))) (U : C(K, L2)) : C(K, L2) :=
  ⟨fun t => boundedApplyL2 (D t) (U t), by
    have h := continuous_boundedApplyL2.comp (D.continuous.prodMk U.continuous)
    convert! h using 1⟩

theorem continuous_advectionPath :
    Continuous (fun p : C(K, Space →ᵇ (Space →L[ℝ] Space)) × C(K, L2) =>
      advectionPath p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hd : Continuous (fun p :
      (C(K, Space →ᵇ (Space →L[ℝ] Space)) × C(K, L2)) × K => p.1.1 p.2) :=
    ContinuousEval.continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd)
  have hu : Continuous (fun p :
      (C(K, Space →ᵇ (Space →L[ℝ] Space)) × C(K, L2)) × K => p.1.2 p.2) :=
    ContinuousEval.continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd)
  have h := continuous_boundedApplyL2.comp (hd.prodMk hu)
  convert! h using 1

theorem tendsto_advectionPath {D : ℕ → C(K, Space →ᵇ (Space →L[ℝ] Space))}
    {U : ℕ → C(K, L2)} {F : C(K, Space →ᵇ (Space →L[ℝ] Space))} {V : C(K, L2)}
    (hD : Tendsto D atTop (𝓝 F)) (hU : Tendsto U atTop (𝓝 V)) :
    Tendsto (fun n => advectionPath (D n) (U n)) atTop (𝓝 (advectionPath F V)) := by
  have h := (continuous_advectionPath.tendsto (F, V)).comp (hD.prodMk_nhds hU)
  convert! h using 1

end ClockBarrier.Analysis.Solenoidal
