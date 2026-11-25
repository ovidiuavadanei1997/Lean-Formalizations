/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.SmoothJetLimit
public import ClockBarrier.Analysis.SmoothJetCauchy
public import ClockBarrier.Analysis.SmoothBoundedCauchy

/-! # A genuine smooth limit from L² convergence and bounds at every derivative order -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Sobolev
open MeasureTheory ContinuousLinearMap SmoothL2Field Filter
open scoped Topology BoundedContinuousFunction
local notation "Space" => EuclideanSpace ℝ (Fin 3)
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]

theorem exists_smooth_limit (A : ℕ → K → SmoothL2Field Space)
    (hA : ∀ k n, Continuous (fun t => (A k t).jetLp n))
    (hb : ∀ q, ∃ M : ℝ, ∀ k t, WordBound q M (A k t))
    (h0 : CauchySeq (fun k => fieldPath (A k) (hA k))) :
    ∃ F : K → SmoothL2Field Space, ∃ hF : ∀ n, Continuous (fun t => (F t).jetLp n),
      Tendsto (fun k => fieldPath (A k) (hA k)) atTop (𝓝 (fieldPath F hF)) ∧
      (∀ n, Tendsto (fun k => jetPath (A k) (hA k) n) atTop (𝓝 (jetPath F hF n))) ∧
      ∀ n, Tendsto (fun k => boundedFieldPath (fun t => jetField n (A k t))
        (continuous_jetField_jet (A k) (hA k) n)) atTop
          (𝓝 (boundedFieldPath (fun t => jetField n (F t)) (continuous_jetField_jet F hF n))) := by
  have hc := cauchySeq_jetPath A hA hb h0
  have hj (n : ℕ) : ∃ J : C(K, Lp (Space [×n]→L[ℝ] Space) 2 (volume : Measure Space)),
      Tendsto (fun k => jetPath (A k) (hA k) n) atTop (𝓝 J) :=
    cauchySeq_tendsto_of_complete (hc n)
  choose J hJ using hj
  have hbc (n : ℕ) : CauchySeq (fun k => boundedFieldPath (fun t => jetField n (A k t))
      (continuous_jetField_jet (A k) (hA k) n)) :=
    cauchySeq_boundedFieldPath (fun k t => jetField n (A k t))
      (fun k => continuous_jetField_jet (A k) (hA k) n) (cauchySeq_jetField A hA hc n)
  have hbg (n : ℕ) : ∃ G : C(K, Space →ᵇ (Space [×n]→L[ℝ] Space)),
      Tendsto (fun k => boundedFieldPath (fun t => jetField n (A k t))
        (continuous_jetField_jet (A k) (hA k) n)) atTop (𝓝 G) :=
    cauchySeq_tendsto_of_complete (hbc n)
  choose G hG using hbg
  have hp (t : K) : ∃ F : SmoothL2Field Space,
      ∀ n, F.jetLp n = J n t ∧ finiteField (jetField n F) = G n t := by
    apply smooth_field_of_jet_limits (fun k => A k t) (fun n => G n t) _ (fun n => J n t) _
    · intro n
      exact ((ContinuousMap.evalCLM ℝ t).continuous.tendsto _).comp (hG n)
    · intro n
      exact ((ContinuousMap.evalCLM ℝ t).continuous.tendsto _).comp (hJ n)
  choose F hf using hp
  have hF (n : ℕ) : Continuous (fun t => (F t).jetLp n) :=
    (J n).continuous.congr (fun t => (hf t n).1.symm)
  have heJ (n : ℕ) : J n = jetPath F hF n := ContinuousMap.ext (fun t => (hf t n).1.symm)
  have heG (n : ℕ) : G n = boundedFieldPath (fun t => jetField n (F t))
      (continuous_jetField_jet F hF n) := ContinuousMap.ext (fun t => (hf t n).2.symm)
  have hjet (n : ℕ) : Tendsto (fun k => jetPath (A k) (hA k) n) atTop (𝓝 (jetPath F hF n)) := by
    rw [← heJ]
    exact hJ n
  refine ⟨F, hF, ?_, hjet, ?_⟩
  · let L := (continuousMultilinearCurryFin0 ℝ Space Space).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
      2 (volume : Measure Space)
    let B := L.compLeftContinuous ℝ K
    have he (U : K → SmoothL2Field Space) (hU : ∀ n, Continuous (fun t => (U t).jetLp n)) :
        B (jetPath U hU 0) = fieldPath U hU := by
      apply ContinuousMap.ext
      intro t
      exact (toLp_eq_jet_zero (U t)).symm
    simpa only [Function.comp_def, he] using (B.continuous.tendsto _).comp (hjet 0)
  · intro n
    rw [← heG]
    exact hG n

end ClockBarrier.Analysis.Sobolev
