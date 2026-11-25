/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.SmoothConvergence
public import ClockBarrier.Analysis.RegularizerApproximation

/-! # Uniform all-jet convergence of the actual regularizer on smooth paths -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Sobolev
open MeasureTheory ContinuousLinearMap SmoothL2Field Filter Topology Solenoidal
local notation "Space" => EuclideanSpace ℝ (Fin 3)
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]

omit [Nonempty K] in
theorem compact_wordBound (F : K → SmoothL2Field Space)
    (hF : ∀ n, Continuous (fun t => (F t).jetLp n)) (q : ℕ) :
    ∃ M : ℝ, ∀ t, WordBound q M (F t) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (wordEnergy_continuous F hF q).continuousOn
  refine ⟨Real.sqrt C, fun t n hn w => (wordBound_sqrt_energy q (F t) n hn w).trans ?_⟩
  apply Real.sqrt_le_sqrt
  exact (le_abs_self _).trans (hC t (Set.mem_univ t))

def regularizerWordPath (A : K → SmoothL2Field Space)
    (hA : ∀ m, Continuous (fun t => (A t).jetLp m)) (k : ℕ) {n : ℕ} (w : Fin n → Fin 3) : C(K, L2) :=
  (regularizerMap k).compLeftContinuous ℝ K
    (((wordJetMap (V := Space) w).compLeftContinuous ℝ K) (jetPath A hA n))

def projectedWordPath (F : K → SmoothL2Field Space)
    (hF : ∀ m, Continuous (fun t => (F t).jetLp m)) {n : ℕ} (w : Fin n → Fin 3) : C(K, L2) :=
  solenoidalProjection.compLeftContinuous ℝ K
    (((wordJetMap (V := Space) w).compLeftContinuous ℝ K) (jetPath F hF n))

theorem regularizerWordPath_tendsto (A : ℕ → K → SmoothL2Field Space)
    (hA : ∀ k n, Continuous (fun t => (A k t).jetLp n))
    (F : K → SmoothL2Field Space) (hF : ∀ n, Continuous (fun t => (F t).jetLp n))
    (h : ∀ n, Tendsto (fun k => jetPath (A k) (hA k) n) atTop (𝓝 (jetPath F hF n)))
    {n : ℕ} (w : Fin n → Fin 3) :
    Tendsto (fun k => regularizerWordPath (A k) (hA k) k w) atTop (𝓝 (projectedWordPath F hF w)) := by
  obtain ⟨M, hM⟩ := compact_wordBound F hF (n+1)
  let J := (wordJetMap (V := Space) w).compLeftContinuous ℝ K
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hj := tendsto_iff_norm_sub_tendsto_zero.mp ((J.continuous.tendsto _).comp (h n))
  have hz : Tendsto (fun k => ‖J (jetPath (A k) (hA k) n)-J (jetPath F hF n)‖+
      regularizerError k*M) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul, add_zero] using hj.add (regularizerError_tendsto.mul_const M)
  apply squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hz
  apply (ContinuousMap.norm_le _ (add_nonneg (norm_nonneg _)
    (mul_nonneg (regularizerError_nonneg k) (wordBound_nonneg (hM (Classical.choice inferInstance)))))).mpr
  intro t
  change ‖regularizerMap k ((wordJetMap (V := Space) w) ((A k t).jetLp n)) -
    solenoidalProjection ((wordJetMap (V := Space) w) ((F t).jetLp n))‖ ≤ _
  simp only [wordJetMap_apply]
  calc
    _ ≤ ‖regularizerMap k ((wordField (A k t) w).toLp-(wordField (F t) w).toLp)‖+
        ‖regularizerMap k (wordField (F t) w).toLp-solenoidalProjection (wordField (F t) w).toLp‖ := by
      simpa only [map_sub] using norm_sub_le_norm_sub_add_norm_sub (regularizerMap k (wordField (A k t) w).toLp)
        (regularizerMap k (wordField (F t) w).toLp) (solenoidalProjection (wordField (F t) w).toLp)
    _ ≤ ‖J (jetPath (A k) (hA k) n)-J (jetPath F hF n)‖+regularizerError k*M := by
      apply add_le_add
      · apply (regularizerMap_contract k _).trans
        convert! (J (jetPath (A k) (hA k) n)-J (jetPath F hF n)).norm_coe_le_norm t using 1
        simp only [ContinuousMap.sub_apply]
        change ‖(wordField (A k t) w).toLp-(wordField (F t) w).toLp‖ =
          ‖wordJetMap (V := Space) w ((A k t).jetLp n)-wordJetMap (V := Space) w ((F t).jetLp n)‖
        rw [wordJetMap_apply, wordJetMap_apply]
      · exact regularizer_error_wordBound k _ M (wordBound_wordField (hM t) w)

theorem regularized_path_tendsto (A : ℕ → K → SmoothL2Field Space)
    (hA : ∀ k n, Continuous (fun t => (A k t).jetLp n))
    (F : K → SmoothL2Field Space) (hF : ∀ n, Continuous (fun t => (F t).jetLp n))
    (h : ∀ n, Tendsto (fun k => jetPath (A k) (hA k) n) atTop (𝓝 (jetPath F hF n))) (n : ℕ) :
    Tendsto (fun k => jetPath (fun t => regularizedSmoothField k (A k t).toLp)
      (fun m => continuous_regularizedSmoothField_jets k m (continuous_toLp (A k) (hA k 0))) n) atTop
      (𝓝 (jetPath (fun t => solenoidalField (F t)) (solenoidalField_continuous F hF) n)) := by
  let R (k : ℕ) (w : Fin n → Fin 3) : C(K, L2) :=
    (regularizerMap k).compLeftContinuous ℝ K
      (((wordJetMap (V := Space) w).compLeftContinuous ℝ K) (jetPath (A k) (hA k) n))
  let G (w : Fin n → Fin 3) : C(K, L2) :=
    solenoidalProjection.compLeftContinuous ℝ K
      (((wordJetMap (V := Space) w).compLeftContinuous ℝ K) (jetPath F hF n))
  have hw (w : Fin n → Fin 3) : Tendsto (fun k => R k w) atTop (𝓝 (G w)) :=
    regularizerWordPath_tendsto A hA F hF h w
  let combine := ContinuousMap.piEquiv K (fun _ : Fin n → Fin 3 => L2)
  have hc : Continuous combine := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply continuous_pi
    intro w
    exact continuous_eval.comp ((continuous_apply w |>.comp continuous_fst).prodMk continuous_snd)
  let L := (L2Tensor.tensorLpReassembly (V := Space) (volume : Measure Space) n).compLeftContinuous ℝ K
  have hh := (L.continuous.tendsto _).comp ((hc.tendsto _).comp (tendsto_pi_nhds.mpr hw))
  convert! hh using 1
  · funext k
    apply ContinuousMap.ext
    intro t
    simp only [jetPath_apply, jetLp_eq_word_reassembly, regularizedSmoothField_word]
    change _ = L2Tensor.tensorLpReassembly volume n (fun w => regularizerMap k (wordJetMap w ((A k t).jetLp n)))
    simp only [wordJetMap_apply]
  · congr 1
    apply ContinuousMap.ext
    intro t
    simp only [jetPath_apply, jetLp_eq_word_reassembly, solenoidalField_word]
    change _ = L2Tensor.tensorLpReassembly volume n (fun w => solenoidalProjection (wordJetMap w ((F t).jetLp n)))
    simp only [wordJetMap_apply]

end ClockBarrier.Analysis.Sobolev
