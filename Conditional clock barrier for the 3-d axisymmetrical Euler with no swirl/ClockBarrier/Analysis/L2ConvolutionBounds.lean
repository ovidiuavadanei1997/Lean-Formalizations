/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.SmoothL2Convolution
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Bounded L² spatial jets of compact convolutions
Quantitative version of the existing parameter-integral proof.
-/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.L2Convolution
open MeasureTheory ContinuousLinearMap Filter Set Solenoidal
open scoped Convolution ContDiff
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
omit [CompleteSpace G] in
private theorem translated_linear_ae (L : E₃ →L[ℝ] G) (u : L2) (y : E₃) :
    L.compLp (translation (-y) u) =ᵐ[volume] fun x => L (u (x-y)) := by
  filter_upwards [L.coeFn_compLp (translation (-y) u), translation_ae (-y) u]
    with x hx hy using hx.trans (congrArg L (by simpa only [sub_eq_add_neg] using hy))

omit [CompleteSpace G] in
private theorem translated_linear_bound (L : E₃ →L[ℝ] G) (u : L2) (y : E₃) :
    MemLp (fun x => L (u (x-y))) 2 volume ∧
      (eLpNorm (fun x => L (u (x-y))) 2 volume).toReal ≤ ‖L‖ * ‖u‖ := by
  refine ⟨(memLp_congr_ae (translated_linear_ae L u y)).mp (Lp.memLp _), ?_⟩
  rw [← eLpNorm_congr_ae (translated_linear_ae L u y), ← Lp.norm_def]
  simpa only [LinearIsometry.norm_map] using L.norm_compLp_le (translation (-y) u)

omit [CompleteSpace G] in
/-- A continuous compact kernel maps L² to L² for any continuous bilinear pairing. -/
theorem convolution_l2_bound (B : F →L[ℝ] E₃ →L[ℝ] G) (k : E₃ → F)
    (hk : Continuous k) (hc : HasCompactSupport k) (M : ℝ)
    (hM : ∀ x, ‖k x‖ ≤ M) (u : L2) :
    (eLpNorm (k ⋆[B, volume] (u : E₃ → E₃)) 2 volume).toReal ≤
      ((volume.real (tsupport k) * ‖B‖) * M) * ‖u‖ := by
  have hM0 : 0 ≤ M := (norm_nonneg (k 0)).trans (hM 0)
  letI : IsFiniteMeasure (volume.restrict (tsupport k)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hc.isCompact.measure_lt_top (μ := volume)⟩
  have hm : AEStronglyMeasurable (fun q : E₃ × E₃ => B (k q.1) (u (q.2-q.1)))
      ((volume.restrict (tsupport k)).prod volume) :=
    ((hk.aestronglyMeasurable.restrict).convolution_integrand B
      (Lp.aestronglyMeasurable u)).prod_swap
  have hb (y : E₃) : MemLp (fun x => B (k y) (u (x-y))) 2 volume ∧
      (eLpNorm (fun x => B (k y) (u (x-y))) 2 volume).toReal ≤ ‖B‖ * M * ‖u‖ :=
    ⟨(translated_linear_bound (B (k y)) u y).1,
      (translated_linear_bound (B (k y)) u y).2.trans
        (mul_le_mul_of_nonneg_right ((B.le_opNorm (k y)).trans
          (mul_le_mul_of_nonneg_left (hM y) (norm_nonneg B))) (norm_nonneg u))⟩
  have hi := (L2ParameterIntegral.integral_memLp_and_bound
    (volume.restrict (tsupport k)) volume _ hm (‖B‖ * M * ‖u‖)
    (mul_nonneg (mul_nonneg (norm_nonneg B) hM0) (norm_nonneg u))
    (Eventually.of_forall hb)).2
  have he (x : E₃) : (∫ y in tsupport k, B (k y) (u (x-y))) =
      (k ⋆[B, volume] (u : E₃ → E₃)) x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy => by simp only [image_eq_zero_of_notMem_tsupport hy, map_zero, zero_apply])
  rw [show (fun x => ∫ y in tsupport k, B (k y) (u (x-y))) =
    k ⋆[B, volume] (u : E₃ → E₃) from funext he] at hi
  simpa only [Measure.real, Measure.restrict_apply_univ, mul_assoc] using hi

theorem iteratedFDeriv_convolution_l2_bounded (m : ℕ)
    (B : F →L[ℝ] E₃ →L[ℝ] G) (k : E₃ → F)
    (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : L2,
      (eLpNorm (iteratedFDeriv ℝ m (k ⋆[B, volume] (u : E₃ → E₃))) 2 volume).toReal ≤ C * ‖u‖ := by
  induction m generalizing F G with
  | zero =>
    obtain ⟨M, hM⟩ := hk.continuous.bounded_above_of_compact_support hc
    have hM0 : 0 ≤ M := (norm_nonneg (k 0)).trans (hM 0)
    refine ⟨((volume.real (tsupport k) * ‖B‖) * M), by positivity, fun u => ?_⟩
    have hn : eLpNorm (iteratedFDeriv ℝ 0 (k ⋆[B, volume] (u : E₃ → E₃))) 2 volume =
        eLpNorm (k ⋆[B, volume] (u : E₃ → E₃)) 2 volume :=
      eLpNorm_congr_norm_ae (Eventually.of_forall (fun _ => norm_iteratedFDeriv_zero))
    simpa only [hn] using convolution_l2_bound B k hk.continuous hc M hM u
  | succ m ih =>
    obtain ⟨C, hC, hb⟩ := ih (B.precompL E₃) (fderiv ℝ k)
      (hk.fderiv_right (m := ∞) (by simp)) (hc.fderiv ℝ)
    refine ⟨C, hC, fun u => ?_⟩
    have he : fderiv ℝ (k ⋆[B, volume] (u : E₃ → E₃)) =
        fderiv ℝ k ⋆[B.precompL E₃, volume] (u : E₃ → E₃) :=
      funext (fun x => (hc.hasFDerivAt_convolution_left B (hk.of_le (by simp))
        ((Lp.memLp u).locallyIntegrable (by norm_num)) x).fderiv)
    have hn : eLpNorm (iteratedFDeriv ℝ (m+1) (k ⋆[B, volume] (u : E₃ → E₃))) 2 volume =
        eLpNorm (iteratedFDeriv ℝ m (fderiv ℝ (k ⋆[B, volume] (u : E₃ → E₃)))) 2 volume :=
      eLpNorm_congr_norm_ae (Eventually.of_forall (fun x =>
        (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := k ⋆[B, volume] (u : E₃ → E₃))
          (n := m) (x := x)).symm))
    simpa only [hn, he] using hb u

end ClockBarrier.Analysis.L2Convolution
