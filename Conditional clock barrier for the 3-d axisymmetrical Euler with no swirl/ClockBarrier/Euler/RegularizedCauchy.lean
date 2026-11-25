/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd.
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: concrete trajectories, direct L² time derivatives and coordinate gradient bound.
-/
module
public import ClockBarrier.Euler.PerturbedEulerEnergy
public import ClockBarrier.Euler.RegularizedEnergy
public import ClockBarrier.Analysis.SmoothPaths

/-! # Uniform L² comparison of the actual regularized Euler trajectories -/
@[expose] public noncomputable section
namespace ClockBarrier.Euler.Regularized
open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap ClockBarrier.Analysis
  Solenoidal SmoothL2Field Sobolev SmoothSobolev
open scoped Topology
local notation "Space" => EuclideanSpace ℝ (Fin 3)

def regularizedComparisonCost (T M : ℝ) : ℝ :=
  regularizationCost M*Real.sqrt (Real.exp ((2*((39*smoothEmbeddingConstant)*M)+1)*T))

theorem regularizedComparisonCost_nonneg (T M : ℝ) : 0 ≤ regularizedComparisonCost T M :=
  mul_nonneg (regularizationCost_nonneg M) (Real.sqrt_nonneg _)

theorem regularized_l2_comparison {T : ℝ} (hT : 0 ≤ T) {j k : ℕ}
    {U V : ℝ → SmoothL2Field Space}
    (hUc : ∀ m, Continuous (fun t => (U t).jetLp m))
    (hVc : ∀ m, Continuous (fun t => (V t).jetLp m))
    (hUd : ∀ m, ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => (U s).jetLp m) ((smoothRhs j (U t)).jetLp m) t)
    (hVd : ∀ m, ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => (V s).jetLp m) ((smoothRhs k (V t)).jetLp m) t)
    (hUs : ∀ t ∈ Icc 0 T, (U t).toLp ∈ solenoidalSpace)
    (hVs : ∀ t ∈ Icc 0 T, (V t).toLp ∈ solenoidalSpace)
    (M : ℝ) (hU : ∀ t ∈ Icc 0 T, WordBound 4 M (U t))
    (hV : ∀ t ∈ Icc 0 T, WordBound 4 M (V t)) (hinit : (V 0).toLp = (U 0).toLp)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖(V t).toLp-(U t).toLp‖ ≤
      (regularizerError j+regularizerError k)*regularizedComparisonCost T M := by
  let G := (39*smoothEmbeddingConstant)*M
  let C := 2*G+1
  let E := (regularizerError j+regularizerError k)*regularizationCost M
  have hM : 0 ≤ M := wordBound_nonneg (hU 0 ⟨le_rfl, hT⟩)
  have hG : 0 ≤ G := mul_nonneg (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg) hM
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hE : 0 ≤ E := mul_nonneg (add_nonneg (regularizerError_nonneg j) (regularizerError_nonneg k))
    (regularizationCost_nonneg M)
  let X (r : ℝ) := ‖(V r).toLp-(U r).toLp‖^2
  let X' (r : ℝ) := 2*⟪(V r).toLp-(U r).toLp,
    (smoothRhs k (V r)).toLp-(smoothRhs j (U r)).toLp⟫_ℝ
  have hc : ContinuousOn X (Icc 0 T) :=
    (((continuous_toLp V (hVc 0)).sub (continuous_toLp U (hUc 0))).norm.pow 2).continuousOn
  have hx0 : X 0 = 0 := by simp only [X,hinit,sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0)]
  have hd (r : ℝ) (hr : r ∈ Icc 0 T) : HasDerivWithinAt X (X' r) (Icc 0 T) r := by
    have hu := word_hasDerivAt (Fin.elim0 : Fin 0 → Fin 3) (hUd 0 r hr)
    have hv := word_hasDerivAt (Fin.elim0 : Fin 0 → Fin 3) (hVd 0 r hr)
    simpa only [X,X',wordField_zero,Pi.sub_apply] using (hv.sub hu).norm_sq.hasDerivWithinAt
  have hb (r : ℝ) (hr : r ∈ Icc 0 T) : X' r ≤ C*X r+E^2 := by
    have h := perturbed_difference_energy (U r) (V r) (hUs r hr) (hVs r hr)
      (smoothRhs j (U r)).toLp (smoothRhs k (V r)).toLp
      G (regularizerError j*regularizationCost M) (regularizerError k*regularizationCost M)
      (wordBound_gradient (wordBound_mono (hU r hr) (by omega)))
      (regularized_rhs_error j _ (hUs r hr) M (hU r hr))
      (regularized_rhs_error k _ (hVs r hr) M (hV r hr))
    simpa only [X,X',C,E,add_mul] using h
  have h := forced_linear_zero_bound T C E hC X X' hc hx0 hd hb t ht
  have hs := Real.sq_sqrt ((Real.exp_pos (C*T)).le)
  have he : 0 ≤ E*Real.sqrt (Real.exp (C*T)) := mul_nonneg hE (Real.sqrt_nonneg _)
  have hn : ‖(V t).toLp-(U t).toLp‖ ≤ E*Real.sqrt (Real.exp (C*T)) := by
    dsimp only [X] at h
    nlinarith [norm_nonneg ((V t).toLp-(U t).toLp)]
  exact hn.trans_eq (by dsimp [E,C,G,regularizedComparisonCost]; ring)

theorem regularized_cauchy {T : ℝ} (hT : 0 ≤ T) {U : ℕ → ℝ → SmoothL2Field Space}
    (hUc : ∀ k m, Continuous (fun t => (U k t).jetLp m))
    (hUd : ∀ k m, ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => (U k s).jetLp m) ((smoothRhs k (U k t)).jetLp m) t)
    (hUs : ∀ k, ∀ t ∈ Icc 0 T, (U k t).toLp ∈ solenoidalSpace)
    (M : ℝ) (hM : ∀ k, ∀ t ∈ Icc 0 T, WordBound 4 M (U k t))
    (hinit : ∀ j k, (U k 0).toLp = (U j 0).toLp) :
    CauchySeq (fun k => fieldPath (fun t : Icc (0 : ℝ) T => U k t)
      (fun m => (hUc k m).comp continuous_subtype_val)) := by
  have he : Tendsto (fun n => regularizerError n*regularizedComparisonCost T M) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul] using regularizerError_tendsto.mul_const (regularizedComparisonCost T M)
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hh : ∀ᶠ n in atTop, regularizerError n*regularizedComparisonCost T M < ε/2 :=
    (tendsto_order.mp he).2 _ (half_pos hε)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hh
  refine ⟨N,fun j hj k hk => ?_⟩
  rw [dist_eq_norm,norm_sub_rev]
  have hb : ‖fieldPath (fun t : Icc (0 : ℝ) T => U k t)
      (fun m => (hUc k m).comp continuous_subtype_val) -
      fieldPath (fun t : Icc (0 : ℝ) T => U j t)
      (fun m => (hUc j m).comp continuous_subtype_val)‖ ≤
        (regularizerError j+regularizerError k)*regularizedComparisonCost T M := by
    apply (ContinuousMap.norm_le _ (mul_nonneg
      (add_nonneg (regularizerError_nonneg j) (regularizerError_nonneg k))
      (regularizedComparisonCost_nonneg T M))).mpr
    intro t
    exact regularized_l2_comparison hT (hUc j) (hUc k) (hUd j) (hUd k)
      (hUs j) (hUs k) M (hM j) (hM k) (hinit j k) t t.property
  apply hb.trans_lt
  nlinarith [hN j hj, hN k hk]

end ClockBarrier.Euler.Regularized
