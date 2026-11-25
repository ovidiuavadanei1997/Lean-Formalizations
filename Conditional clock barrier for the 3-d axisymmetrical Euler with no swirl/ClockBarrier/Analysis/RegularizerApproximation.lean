/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd.
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: direct projection contraction avoids an auxiliary projected smooth field.
-/
module
public import ClockBarrier.Analysis.RegularizedWords
public import ClockBarrier.Analysis.SmoothWordBounds
import Mathlib.Analysis.Calculus.MeanValue

/-! # Quantitative approximation by the concrete symmetric regularizer -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Solenoidal
open Set Filter MeasureTheory ContinuousLinearMap SmoothL2Field Sobolev
open scoped Topology
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem translation_increment (A : SmoothL2Field E₃) (a : E₃) :
    ‖translation a A.toLp-A.toLp‖ ≤ ‖A.derivative.toLp‖*‖a‖ := by
  have h := (convex_univ : Convex ℝ (univ : Set E₃)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (A.translation_hasFDerivAt x).differentiableAt)
    (fun x _ => by
      rw [(A.translation_hasFDerivAt x).fderiv]
      exact (L2Derivative.derivativeMap_norm_le volume _).trans_eq
        ((L2Translation.translation x).norm_map A.derivative.toLp))
    (mem_univ (0 : E₃)) (mem_univ a)
  convert! (by simpa only [L2Translation.translation_zero, sub_zero] using h) using 1

theorem mollify_error (n : ℕ) (A : SmoothL2Field E₃) :
    ‖mollify n A.toLp-A.toLp‖ ≤ (2*cutoffScale n)*‖A.derivative.toLp‖ := by
  have he : mollify n A.toLp-A.toLp=
      ∫ y : E₃, kernel n y • (translation (-y) A.toLp-A.toLp) := by
    simp only [smul_sub,integral_sub (kernel_orbit_integrable n A.toLp)
      ((kernel_integrable n).smul_const A.toLp),integral_smul_const,kernel_integral,
      one_smul,mollify_eq_integral]
  rw [he]
  have h := norm_integral_le_of_norm_le
    ((kernel_integrable n).mul_const ((2*cutoffScale n)*‖A.derivative.toLp‖))
    (f := fun y : E₃ => kernel n y • (translation (-y) A.toLp-A.toLp)) ?_
  · simpa only [integral_mul_const,kernel_integral,one_mul] using h
  apply Eventually.of_forall
  intro y
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (kernel_nonneg n y)]
  by_cases hy : kernel n y=0
  · simp only [hy,zero_mul,le_refl]
  apply mul_le_mul_of_nonneg_left _ (kernel_nonneg n y)
  apply (translation_increment A (-y)).trans
  rw [norm_neg,mul_comm (2*cutoffScale n)]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hs : y ∈ Function.support ((bump n).normed volume) := hy
  rw [(bump n).support_normed_eq,Metric.mem_ball,dist_zero_right] at hs
  exact hs.le


theorem regularizer_error (n : ℕ) (A : SmoothL2Field E₃) :
    ‖regularizerMap n A.toLp-solenoidalProjection A.toLp‖ ≤
      (2*cutoffScale n)*‖A.derivative.toLp‖ := by
  have he : regularizerMap n A.toLp - solenoidalProjection A.toLp =
      solenoidalProjection (mollify n A.toLp - A.toLp) := by
    rw [map_sub, projection_mollify, regularizerMap_eq_mollify_projection]
  rw [he]
  exact (solenoidalProjection_apply_norm_le _).trans (mollify_error n A)

def regularizerError (n : ℕ) : ℝ := 6*cutoffScale n

theorem regularizerError_nonneg (n : ℕ) : 0 ≤ regularizerError n :=
  mul_nonneg (by norm_num) (cutoffScale_pos n).le

theorem regularizerError_tendsto : Tendsto regularizerError atTop (𝓝 (0 : ℝ)) := by
  change Tendsto (fun n => 6*cutoffScale n) atTop (𝓝 (0 : ℝ))
  simpa only [mul_zero] using cutoffScale_tendsto.const_mul 6

theorem regularizer_error_wordBound (n : ℕ) (A : SmoothL2Field E₃) (M : ℝ)
    (hM : WordBound 1 M A) :
    ‖regularizerMap n A.toLp-solenoidalProjection A.toLp‖ ≤ regularizerError n*M := by
  apply (regularizer_error n A).trans
  have hb := wordBound_jet_norm hM (le_refl 1)
  rw [← A.derivative.norm_jetLp_zero, A.norm_derivative_jetLp]
  exact (mul_le_mul_of_nonneg_left hb
    (mul_nonneg (by norm_num) (cutoffScale_pos n).le)).trans_eq (by
      simp only [regularizerError,pow_one]
      ring)

end ClockBarrier.Analysis.Solenoidal
