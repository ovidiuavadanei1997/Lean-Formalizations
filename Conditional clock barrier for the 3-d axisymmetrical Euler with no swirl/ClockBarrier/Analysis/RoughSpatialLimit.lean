/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.MollifiedCauchy
public import ClockBarrier.Analysis.BoundedC1Limit

/-! # Construction of a continuous C¹ and L² limit on a compact parameter space

The derivative retains the original spatial Hölder exponent and constant.
No continuity in the Hölder seminorm is assumed or asserted.
-/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Solenoidal
open MeasureTheory ContinuousLinearMap Filter
open scoped Topology NNReal BoundedContinuousFunction
local notation "Space" => EuclideanSpace ℝ (Fin 3)
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

theorem exists_bounded_c1_l2_limit (U : ℕ → C(K, L2))
    (u : ℕ → C(K, Space →ᵇ Space))
    (D : ℕ → C(K, Space →ᵇ (Space →L[ℝ] Space)))
    (hU : CauchySeq U)
    (hrep : ∀ n t, U n t =ᵐ[volume] (u n t : Space → Space))
    (hD : ∀ n t x, HasFDerivAt (u n t : Space → Space) (D n t x) x)
    (H α : ℝ≥0) (hα : 0 < α)
    (hbound : ∀ n t, ‖D n t‖ ≤ (H : ℝ))
    (hholder : ∀ n t, HolderWith H α (D n t : Space → Space →L[ℝ] Space)) :
    ∃ V : C(K, L2), ∃ v : C(K, Space →ᵇ Space),
    ∃ F : C(K, Space →ᵇ (Space →L[ℝ] Space)),
      Tendsto U atTop (𝓝 V) ∧ Tendsto u atTop (𝓝 v) ∧ Tendsto D atTop (𝓝 F) ∧
      ∀ t, V t =ᵐ[volume] (v t : Space → Space) ∧
        MemLp (v t : Space → Space) 2 volume ∧
        (∀ x, HasFDerivAt (v t : Space → Space) (F t x) x) ∧
        ‖F t‖ ≤ (H : ℝ) ∧ HolderWith H α (F t : Space → Space →L[ℝ] Space) := by
  have hc := cauchySeq_bounded_c1_of_l2 U u D hU hrep hD H α hα hbound hholder
  obtain ⟨V, hV⟩ := cauchySeq_tendsto_of_complete hU
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hc.1
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hc.2
  refine ⟨V, v, F, hV, hv, hF, fun t => ?_⟩
  have hVt := ((ContinuousMap.evalCLM ℝ t).continuous.tendsto V).comp hV
  have hvt := ((ContinuousMap.evalCLM ℝ t).continuous.tendsto v).comp hv
  have hFt := ((ContinuousMap.evalCLM ℝ t).continuous.tendsto F).comp hF
  have ha : V t =ᵐ[volume] (v t : Space → Space) :=
    l2_ae_eq_pointwise_limit (fun n => U n t) (fun n => (u n t : Space → Space))
      (fun n => hrep n t) hVt
      (fun x => (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hvt).tendsto_at x)
  refine ⟨ha, (Lp.memLp (V t)).ae_eq ha, ?_, ?_, ?_⟩
  · exact hasFDerivAt_bounded_limit (fun n => u n t) (fun n => D n t) (v t) (F t)
      hvt hFt (fun n => hD n t)
  · rw [BoundedContinuousFunction.norm_def]
    apply le_of_tendsto (hFt.dist (tendsto_const_nhds (x := (0 : Space →ᵇ (Space →L[ℝ] Space)))))
    exact Eventually.of_forall (fun n => by
      have hh := hbound n t
      rw [BoundedContinuousFunction.norm_def] at hh
      convert! hh using 1)
  · exact holderWith_bounded_limit (fun n => D n t) (F t) hFt H α (fun n => hholder n t)

end ClockBarrier.Analysis.Solenoidal
