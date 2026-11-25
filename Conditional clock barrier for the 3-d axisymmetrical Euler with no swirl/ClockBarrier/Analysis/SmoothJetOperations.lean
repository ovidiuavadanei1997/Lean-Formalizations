/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.SmoothPaths
public import ClockBarrier.Analysis.SmoothJetField

/-! # Cauchy convergence is preserved by actual spatial jet operations -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Sobolev
open MeasureTheory ContinuousLinearMap SmoothL2Field
local notation "Space" => EuclideanSpace ℝ (Fin 3)
universe u
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
variable {V : Type u} {W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem cauchySeq_jetPath_mapField (L : V →L[ℝ] W) (A : ℕ → K → SmoothL2Field V)
    (hA : ∀ k n, Continuous (fun t => (A k t).jetLp n)) (n : ℕ)
    (hc : CauchySeq (fun k => jetPath (A k) (hA k) n)) :
    CauchySeq (fun k => jetPath (fun t => mapField L (A k t))
      (continuous_jetLp_mapField L (A k) (hA k)) n) := by
  let F := ((jetPostcompose L n).compLpL 2 (volume : Measure Space)).compLeftContinuous ℝ K
  have he (k : ℕ) : F (jetPath (A k) (hA k) n) =
      jetPath (fun t => mapField L (A k t)) (continuous_jetLp_mapField L (A k) (hA k)) n := by
    apply ContinuousMap.ext
    intro t
    exact (jetLp_mapField L (A k t) n).symm
  simpa only [Function.comp_def, he] using F.uniformContinuous.comp_cauchySeq hc

theorem cauchySeq_jetPath_derivative (A : ℕ → K → SmoothL2Field V)
    (hA : ∀ k n, Continuous (fun t => (A k t).jetLp n)) (n : ℕ)
    (hc : CauchySeq (fun k => jetPath (A k) (hA k) (n+1))) :
    CauchySeq (fun k => jetPath (fun t => (A k t).derivative)
      (continuous_jetLp_derivative (A k) (hA k)) n) := by
  let L : (Space [×(n+1)]→L[ℝ] V) →L[ℝ] (Space [×n]→L[ℝ] (Space →L[ℝ] V)) :=
    (continuousMultilinearCurryRightEquiv' ℝ n Space V).toContinuousLinearEquiv.toContinuousLinearMap
  let F := (ContinuousLinearMap.compLpL (𝕜 := ℝ) (𝕜' := ℝ)
    (E := Space [×(n+1)]→L[ℝ] V) (F := Space [×n]→L[ℝ] (Space →L[ℝ] V))
    (σ := RingHom.id ℝ) 2 (volume : Measure Space) L).compLeftContinuous ℝ K
  have he (k : ℕ) : F (jetPath (A k) (hA k) (n+1)) =
      jetPath (fun t => (A k t).derivative) (continuous_jetLp_derivative (A k) (hA k)) n := by
    apply ContinuousMap.ext
    intro t
    exact (jetLp_derivative (A k t) n).symm
  simpa only [Function.comp_def, he] using F.uniformContinuous.comp_cauchySeq hc

private theorem cauchySeq_jetField_aux (n : ℕ) :
    ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V]
      (A : ℕ → K → SmoothL2Field V) (hA : ∀ k m, Continuous (fun t => (A k t).jetLp m)),
      (∀ m, CauchySeq (fun k => jetPath (A k) (hA k) m)) →
      ∀ m, CauchySeq (fun k => jetPath (fun t => jetField n (A k t))
        (continuous_jetField_jet (A k) (hA k) n) m) := by
  induction n with
  | zero =>
    intro V _ _ A hA hc m
    simpa only [jetField_zero] using cauchySeq_jetPath_mapField
      (continuousMultilinearCurryFin0 ℝ Space V).symm.toContinuousLinearEquiv.toContinuousLinearMap A hA m (hc m)
  | succ n ih =>
    intro V _ _ A hA hc m
    have hd := fun j => cauchySeq_jetPath_derivative A hA j (hc (j+1))
    have hj := ih (Space →L[ℝ] V) (fun k t => (A k t).derivative)
      (fun k => continuous_jetLp_derivative (A k) (hA k)) hd
    simpa only [jetField_succ] using cauchySeq_jetPath_mapField
      (continuousMultilinearCurryRightEquiv' ℝ n Space V).symm.toContinuousLinearEquiv.toContinuousLinearMap
      (fun k t => jetField n (A k t).derivative)
      (fun k => continuous_jetField_jet (fun t => (A k t).derivative)
        (continuous_jetLp_derivative (A k) (hA k)) n) m (hj m)

theorem cauchySeq_jetField (A : ℕ → K → SmoothL2Field V)
    (hA : ∀ k m, Continuous (fun t => (A k t).jetLp m))
    (hc : ∀ m, CauchySeq (fun k => jetPath (A k) (hA k) m)) (n m : ℕ) :
    CauchySeq (fun k => jetPath (fun t => jetField n (A k t))
      (continuous_jetField_jet (A k) (hA k) n) m) := cauchySeq_jetField_aux n V A hA hc m

end ClockBarrier.Analysis.Sobolev
