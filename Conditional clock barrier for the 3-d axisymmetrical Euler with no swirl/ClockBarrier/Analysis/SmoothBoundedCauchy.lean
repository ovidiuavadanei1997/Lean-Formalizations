/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.SmoothJetOperations

/-! # Spatially uniform Cauchy convergence from the actual L² jets -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Sobolev
open MeasureTheory ContinuousLinearMap SmoothL2Field SmoothSobolev Filter Finset
open scoped Topology BoundedContinuousFunction
local notation "Space" => EuclideanSpace ℝ (Fin 3)
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

def scalarPath (A : K → SmoothL2Field ℝ) (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) :
    C(K, Space →ᵇ ℝ) := ⟨fun t => scalarField (A t), continuous_scalarField A hA⟩

theorem scalarPath_sub_norm_le (A B : K → SmoothL2Field ℝ)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
    (hB : ∀ n, Continuous (fun t => (B t).jetLp n)) :
    ‖scalarPath A hA-scalarPath B hB‖ ≤
      smoothEmbeddingConstant * ∑ j ∈ range 3, ‖jetPath A hA j-jetPath B hB j‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg smoothEmbeddingConstant_nonneg
    (sum_nonneg (fun _ _ => norm_nonneg _)))).mpr
  intro t
  exact (scalarField_sub_norm_le (A t) (B t)).trans
    (mul_le_mul_of_nonneg_left (sum_le_sum (fun j _ =>
      (jetPath A hA j-jetPath B hB j).norm_coe_le_norm t)) smoothEmbeddingConstant_nonneg)

theorem cauchySeq_scalarPath (A : ℕ → K → SmoothL2Field ℝ)
    (hA : ∀ k n, Continuous (fun t => (A k t).jetLp n))
    (hc : ∀ n, CauchySeq (fun k => jetPath (A k) (hA k) n)) :
    CauchySeq (fun k => scalarPath (A k) (hA k)) := by
  have ht := fun n => cauchySeq_iff_tendsto_dist_atTop_0.mp (hc n)
  have hs := (tendsto_finsetSum (range 3) (fun j _ => ht j)).const_mul smoothEmbeddingConstant
  have hz : Tendsto (fun p : ℕ × ℕ => smoothEmbeddingConstant *
      ∑ j ∈ range 3, ‖jetPath (A p.1) (hA p.1) j-jetPath (A p.2) (hA p.2) j‖) atTop (𝓝 0) := by
    simpa only [dist_eq_norm, sum_const_zero, mul_zero] using hs
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  exact squeeze_zero (fun _ => dist_nonneg) (fun p => by
    convert! (dist_eq_norm (scalarPath (A p.1) (hA p.1)) (scalarPath (A p.2) (hA p.2))).trans_le
      (scalarPath_sub_norm_le (A p.1) (A p.2) (hA p.1) (hA p.2)) using 1) hz

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def boundedFieldPath (A : K → SmoothL2Field V) (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) :
    C(K, Space →ᵇ V) := ⟨fun t => finiteField (A t), continuous_finiteField A hA⟩

theorem cauchySeq_boundedFieldPath (A : ℕ → K → SmoothL2Field V)
    (hA : ∀ k n, Continuous (fun t => (A k t).jetLp n))
    (hc : ∀ n, CauchySeq (fun k => jetPath (A k) (hA k) n)) :
    CauchySeq (fun k => boundedFieldPath (A k) (hA k)) := by
  let a (i : Fin (Module.finrank ℝ V)) (k : ℕ) : C(K, Space →ᵇ ℝ) :=
    scalarPath (fun t => mapField (coordinate i) (A k t))
      (continuous_jetLp_mapField (coordinate i) (A k) (hA k))
  have ha (i : Fin (Module.finrank ℝ V)) : CauchySeq (a i) :=
    cauchySeq_scalarPath (fun k t => mapField (coordinate i) (A k t))
      (fun k => continuous_jetLp_mapField (coordinate i) (A k) (hA k))
      (fun n => cauchySeq_jetPath_mapField (coordinate i) A hA n (hc n))
  have hex (i : Fin (Module.finrank ℝ V)) :
      ∃ f : C(K, Space →ᵇ ℝ), Tendsto (a i) atTop (𝓝 f) := cauchySeq_tendsto_of_complete (ha i)
  choose f hf using hex
  let F (i : Fin (Module.finrank ℝ V)) : C(K, Space →ᵇ ℝ) →L[ℝ] C(K, Space →ᵇ V) :=
    ((coordinateVector i).compLeftContinuousBounded Space).compLeftContinuous ℝ K
  have ht := tendsto_finsetSum univ (fun i _ => (F i).continuous.tendsto (f i) |>.comp (hf i))
  have he (k : ℕ) : (∑ i, F i (a i k)) = boundedFieldPath (A k) (hA k) := by
    apply ContinuousMap.ext
    intro t
    apply BoundedContinuousFunction.ext
    intro x
    simp only [ContinuousMap.sum_apply, F, a, scalarPath, boundedFieldPath,
      ContinuousMap.coe_mk, ContinuousLinearMap.compLeftContinuous_apply,
      ContinuousLinearMap.compLeftContinuousBounded_apply, finiteField, BoundedContinuousFunction.sum_apply]
    rfl
  have ht' : Tendsto (fun k => boundedFieldPath (A k) (hA k)) atTop (𝓝 (∑ i, F i (f i))) := by
    simpa only [Function.comp_def, he] using ht
  exact ht'.cauchySeq

end ClockBarrier.Analysis.Sobolev
