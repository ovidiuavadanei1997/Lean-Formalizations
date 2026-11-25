/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.MollifiedInitialData
public import ClockBarrier.Analysis.UniformApproximationCauchy
public import Mathlib.Topology.ContinuousMap.Compact

/-! # Spatial C¹ Cauchy convergence from L² convergence and a common Hölder bound -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Solenoidal
open MeasureTheory ContinuousLinearMap Filter
open scoped Topology NNReal BoundedContinuousFunction
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem mollifier_errors_of_ae (n : ℕ) (U : L2)
    (u : Space →ᵇ Space) (D : Space →ᵇ (Space →L[ℝ] Space))
    (hrep : U =ᵐ[volume] (u : Space → Space))
    (hD : ∀ x, HasFDerivAt (u : Space → Space) (D x) x)
    {H α : ℝ≥0} (hH : HolderWith H α (D : Space → Space →L[ℝ] Space)) :
    ‖mollifierField n U - u‖ ≤ ‖D‖ * (2 * cutoffScale n) ∧
    ‖mollifierDerivative n U - D‖ ≤ (H : ℝ) * (2 * cutoffScale n) ^ (α : ℝ) := by
  have hu : MemLp (u : Space → Space) 2 volume := (Lp.memLp U).ae_eq hrep
  have he : hu.toLp u = U := by
    apply Lp.ext
    exact hu.coeFn_toLp.trans hrep.symm
  rw [← he]
  exact ⟨mollifierField_error_le n u D hu hD, mollifierDerivative_error_le n u D hu hD hH⟩

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

theorem cauchySeq_bounded_c1_of_l2 (U : ℕ → C(K, L2))
    (u : ℕ → C(K, Space →ᵇ Space))
    (D : ℕ → C(K, Space →ᵇ (Space →L[ℝ] Space)))
    (hU : CauchySeq U)
    (hrep : ∀ n t, U n t =ᵐ[volume] (u n t : Space → Space))
    (hD : ∀ n t x, HasFDerivAt (u n t : Space → Space) (D n t x) x)
    (H α : ℝ≥0) (hα : 0 < α)
    (hbound : ∀ n t, ‖D n t‖ ≤ (H : ℝ))
    (hholder : ∀ n t, HolderWith H α (D n t : Space → Space →L[ℝ] Space)) :
    CauchySeq u ∧ CauchySeq D := by
  let A (k : ℕ) : C(K, L2) →L[ℝ] C(K, Space →ᵇ Space) :=
    (mollifierField k).compLeftContinuous ℝ K
  let B (k : ℕ) : C(K, L2) →L[ℝ] C(K, Space →ᵇ (Space →L[ℝ] Space)) :=
    (mollifierDerivative k).compLeftContinuous ℝ K
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hU
  have ha (k : ℕ) : CauchySeq (fun n => A k (U n)) :=
    (((A k).continuous.tendsto F).comp hF).cauchySeq
  have hb (k : ℕ) : CauchySeq (fun n => B k (U n)) :=
    (((B k).continuous.tendsto F).comp hF).cauchySeq
  have he₀ : Tendsto (fun k => (H : ℝ) * (2 * cutoffScale k)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (cutoffScale_tendsto.const_mul 2).const_mul (H : ℝ)
  have he₁ : Tendsto (fun k => (H : ℝ) * (2 * cutoffScale k) ^ (α : ℝ)) atTop (𝓝 0) := by
    have hr := ((Real.continuous_rpow_const α.coe_nonneg).tendsto (2 * 0)).comp
      (cutoffScale_tendsto.const_mul 2)
    simpa only [Function.comp_def, mul_zero, Real.zero_rpow (NNReal.coe_pos.mpr hα).ne']
      using hr.const_mul (H : ℝ)
  have hea (k n : ℕ) : dist (u n) (A k (U n)) ≤ (H : ℝ) * (2 * cutoffScale k) := by
    apply (ContinuousMap.dist_le (mul_nonneg H.coe_nonneg
      (mul_nonneg (by norm_num) (cutoffScale_pos k).le))).mpr
    intro t
    change dist (u n t) (mollifierField k (U n t)) ≤ _
    rw [dist_eq_norm, norm_sub_rev]
    exact ((mollifier_errors_of_ae k (U n t) (u n t) (D n t)
      (hrep n t) (hD n t) (hholder n t)).1).trans
      (mul_le_mul_of_nonneg_right (hbound n t)
        (mul_nonneg (by norm_num) (cutoffScale_pos k).le))
  have heb (k n : ℕ) : dist (D n) (B k (U n)) ≤
      (H : ℝ) * (2 * cutoffScale k) ^ (α : ℝ) := by
    apply (ContinuousMap.dist_le (mul_nonneg H.coe_nonneg
      (Real.rpow_nonneg (mul_nonneg (by norm_num) (cutoffScale_pos k).le) _))).mpr
    intro t
    change dist (D n t) (mollifierDerivative k (U n t)) ≤ _
    have hh := (mollifier_errors_of_ae k (U n t) (u n t) (D n t)
      (hrep n t) (hD n t) (hholder n t)).2
    convert! (dist_eq_norm (mollifierDerivative k (U n t)) (D n t)).trans_le hh using 1
    exact dist_comm _ _
  exact ⟨cauchySeq_of_uniform_approximations u (fun k n => A k (U n)) _ he₀ hea ha,
    cauchySeq_of_uniform_approximations D (fun k n => B k (U n)) _ he₁ heb hb⟩

end ClockBarrier.Analysis.Solenoidal
