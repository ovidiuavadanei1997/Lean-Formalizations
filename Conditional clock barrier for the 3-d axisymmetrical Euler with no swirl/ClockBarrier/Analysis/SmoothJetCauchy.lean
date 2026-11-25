/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.SmoothJetInterpolation
public import ClockBarrier.Analysis.SmoothPaths

/-! # Uniform L² Cauchy convergence propagates to every spatial jet -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Sobolev
open MeasureTheory SmoothL2Field Filter
open scoped Topology
local notation "Space" => EuclideanSpace ℝ (Fin 3)
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]

theorem jetPath_sub_norm_le (A B : K → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
    (hB : ∀ n, Continuous (fun t => (B t).jetLp n)) (n : ℕ) (M : ℝ)
    (hM : ∀ t, WordBound (2*n) M (fieldSub (A t) (B t))) :
    ‖jetPath A hA n - jetPath B hB n‖ ≤
      Real.sqrt ((3 : ℝ)^(2*n) * M * ‖fieldPath A hA-fieldPath B hB‖) := by
  have hM0 : 0 ≤ M := wordBound_nonneg (hM (Classical.arbitrary K))
  apply (ContinuousMap.norm_le _ (Real.sqrt_nonneg _)).mpr
  intro t
  have hb := jet_norm_sq_interpolation (fieldSub (A t) (B t)) n M (hM t)
  rw [jetLp_fieldSub, toLp_fieldSub] at hb
  have hc : ‖(A t).toLp-(B t).toLp‖ ≤ ‖fieldPath A hA-fieldPath B hB‖ :=
    (fieldPath A hA-fieldPath B hB).norm_coe_le_norm t
  have hs := Real.sq_sqrt (mul_nonneg (mul_nonneg (by positivity : 0 ≤ (3 : ℝ)^(2*n)) hM0)
    (norm_nonneg (fieldPath A hA-fieldPath B hB)))
  have hbound := mul_le_mul_of_nonneg_left hc
    (mul_nonneg (by positivity : 0 ≤ (3 : ℝ)^(2*n)) hM0)
  change ‖(A t).jetLp n-(B t).jetLp n‖ ≤ _
  nlinarith [Real.sqrt_nonneg ((3 : ℝ)^(2*n) * M * ‖fieldPath A hA-fieldPath B hB‖)]

theorem cauchySeq_jetPath (A : ℕ → K → SmoothL2Field Space)
    (hA : ∀ k n, Continuous (fun t => (A k t).jetLp n))
    (hb : ∀ q, ∃ M : ℝ, ∀ k t, WordBound q M (A k t))
    (h0 : CauchySeq (fun k => fieldPath (A k) (hA k))) (n : ℕ) :
    CauchySeq (fun k => jetPath (A k) (hA k) n) := by
  obtain ⟨M, hM⟩ := hb (2*n)
  have ht := cauchySeq_iff_tendsto_dist_atTop_0.mp h0
  have hz : Tendsto (fun p : ℕ × ℕ =>
      Real.sqrt ((3 : ℝ)^(2*n)*(M+M)*
        dist (fieldPath (A p.1) (hA p.1)) (fieldPath (A p.2) (hA p.2)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto _).comp (ht.const_mul ((3 : ℝ)^(2*n)*(M+M)))
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  apply squeeze_zero (fun _ => dist_nonneg) _ hz
  intro p
  simp only [dist_eq_norm]
  exact jetPath_sub_norm_le (A p.1) (A p.2) (hA p.1) (hA p.2) n (M+M)
    (fun t => wordBound_sub (hM p.1 t) (hM p.2 t))

end ClockBarrier.Analysis.Sobolev
