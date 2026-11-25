/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Compatibility of bounded continuous and Lebesgue-space representatives -/

public section

namespace ClockBarrier.Analysis

open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {F : Type*} [NormedAddCommGroup F]

/-- The canonical map from bounded continuous functions into `L∞` is continuous. -/
theorem continuous_bounded_toLp_top :
    Continuous (fun f : E₃ →ᵇ F => (f.memLp_top (μ := volume)).toLp f) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, Lp.norm_def]
  rw [eLpNorm_congr_ae (Lp.coeFn_sub _ _)]
  rw [eLpNorm_congr_ae ((f.memLp_top (μ := volume)).coeFn_toLp.sub
    (g.memLp_top (μ := volume)).coeFn_toLp)]
  have hb : eLpNorm (⇑f - ⇑g) ∞ volume ≤ ENNReal.ofReal ‖f - g‖ :=
    eLpNormEssSup_le_of_ae_bound (Eventually.of_forall (fun x => (f - g).norm_coe_le_norm x))
  simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hb

/-- Bochner integration in bounded continuous functions and in `L²` produces
compatible representatives. Local finite-measure restrictions justify the identity. -/
theorem ae_integral_lp_eq_integral_bounded [NormedSpace ℝ F] [CompleteSpace F]
    {S : Type*} [MeasurableSpace S] {ν : Measure S}
    {f : S → E₃ →ᵇ F} {g : S → Lp F 2 volume}
    (hf : Integrable f ν) (hg : Integrable g ν)
    (he : ∀ s, g s =ᵐ[volume] f s) :
    ⇑((∫ s, g s ∂ν) : Lp F 2 volume) =ᵐ[volume] ⇑((∫ s, f s ∂ν) : E₃ →ᵇ F) := by
  have hn (n : ℕ) : ⇑((∫ s, g s ∂ν) : Lp F 2 volume) =ᵐ[volume.restrict (Metric.ball (0 : E₃) n)]
      ⇑((∫ s, f s ∂ν) : E₃ →ᵇ F) := by
    let μ : Measure E₃ := volume.restrict (Metric.ball (0 : E₃) n)
    haveI : IsFiniteMeasure μ := ⟨by
      simpa only [μ, Measure.restrict_apply_univ] using (measure_ball_lt_top (μ := volume) (x := (0 : E₃)) (r := (n : ℝ)))⟩
    let b : (E₃ →ᵇ F) →L[ℝ] Lp F 2 μ := BoundedContinuousFunction.toLp 2 μ ℝ
    let r : Lp F 2 volume →L[ℝ] Lp F 2 μ :=
      LpToLpRestrictCLM E₃ F ℝ volume 2 (Metric.ball 0 n)
    have hsr (s : S) : r (g s) = b (f s) := by
      apply Lp.ext
      exact (LpToLpRestrictCLM_coeFn ℝ _ (g s)).trans
        (Filter.EventuallyEq.trans (ae_restrict_of_ae (he s))
          (BoundedContinuousFunction.coeFn_toLp 2 μ ℝ (f s)).symm)
    have hei : r (∫ s, g s ∂ν) = b (∫ s, f s ∂ν) := by
      rw [← r.integral_comp_comm hg, ← b.integral_comp_comm hf]
      exact integral_congr_ae (Eventually.of_forall hsr)
    exact (LpToLpRestrictCLM_coeFn ℝ _ (∫ s, g s ∂ν)).symm.trans
      ((Filter.EventuallyEq.of_eq (congrArg (fun z : Lp F 2 μ => (z : E₃ → F)) hei)).trans
        (BoundedContinuousFunction.coeFn_toLp 2 μ ℝ (∫ s, f s ∂ν)))
  have ha : ∀ᵐ x : E₃, ∀ n : ℕ, x ∈ Metric.ball (0 : E₃) n →
      ((∫ s, g s ∂ν) : Lp F 2 volume) x = ((∫ s, f s ∂ν) : E₃ →ᵇ F) x :=
    ae_all_iff.mpr fun n => (ae_restrict_iff' measurableSet_ball).mp (hn n)
  filter_upwards [ha] with x hx
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  exact hx n (by simpa only [Metric.mem_ball, dist_zero_right] using hn)

/-- The representative compatibility also holds for oriented time integrals. -/
theorem ae_intervalIntegral_lp_eq_integral_bounded [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℝ → E₃ →ᵇ F} {g : ℝ → Lp F 2 volume} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
    (he : ∀ s, g s =ᵐ[volume] f s) :
    ⇑((∫ s in a..b, g s) : Lp F 2 volume) =ᵐ[volume]
      ⇑((∫ s in a..b, f s) : E₃ →ᵇ F) := by
  simp only [intervalIntegral]
  exact (Lp.coeFn_sub _ _).trans
    ((ae_integral_lp_eq_integral_bounded hf.1 hg.1 he).sub
      (ae_integral_lp_eq_integral_bounded hf.2 hg.2 he))

end ClockBarrier.Analysis
