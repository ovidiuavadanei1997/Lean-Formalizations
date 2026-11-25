/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.VorticityGrowthEstimate
import ClockBarrier.Euler.EnergyConservation
import ClockBarrier.Analysis.BKMLogGrowth
import ClockBarrier.Analysis.VelocitySupEnergy
import ClockBarrier.Analysis.CurlDirectionalLogarithmic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Vorticity Hölder growth and BKM a priori bounds

Provider for the joint statement. Actual Euler flow transport and the
spatial curl estimates give growth; logarithmic Grönwall and energy conservation
give uniform full spatial norms under the BKM integral condition.
-/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The actual vorticity has exponential Hölder and supremum growth in the
integrated velocity gradient. Finite BKM integral gives uniform full spatial
`C_b^{1,α}` and `L²` bounds on the entire preterminal interval. -/
theorem exists_vorticity_holder_growth_and_bkm_bounds :
  ∀ (α : ℝ≥0), 0 < α → α < 1 →
  ∃ C : ℝ≥0, 0 < C ∧
    ∀ (T : ℝ) (u : ℝ → E₃ →ᵇ E₃) (p : ℝ → E₃ → ℝ)
      (h : classical_euler_on α T u p),
    ∃ D : ℝ → E₃ →ᵇ (E₃ →L[ℝ] E₃), ∃ W : ℝ → E₃ →ᵇ E₃,
      ContinuousOn D (Ico 0 T) ∧ ContinuousOn W (Ico 0 T) ∧
      (∀ t ∈ Ico 0 T, ∀ x, HasFDerivAt (u t : E₃ → E₃) (D t x) x) ∧
      (∀ t, ∀ ht : t ∈ Ico 0 T, ∀ x,
        W t x = vorticity (u t) (h.cartesian_partials t ht) x) ∧
      (∀ H₀ : ℝ≥0, HolderWith H₀ α (W 0 : E₃ → E₃) →
        ∀ t ∈ Ico 0 T,
          HolderWith (H₀ * ⟨Real.exp ((C : ℝ) * ∫ s in 0..t, ‖D s‖),
            (Real.exp_pos _).le⟩) α (W t : E₃ → E₃)) ∧
      (∀ t ∈ Ico 0 T,
        ‖W t‖ ≤ ‖W 0‖ * Real.exp (∫ s in 0..t, ‖D s‖)) ∧
      (IntegrableOn (fun t => ‖W t‖) (Ico 0 T) volume →
        ∃ M : ℝ≥0, 0 < M ∧ ∀ t ∈ Ico 0 T,
          ‖u t‖ ≤ M ∧ ‖D t‖ ≤ M ∧ ‖W t‖ ≤ M ∧
          HolderWith M α (D t : E₃ → E₃ →L[ℝ] E₃) ∧
          HolderWith M α (W t : E₃ → E₃) ∧
          (eLpNorm (u t : E₃ → E₃) 2 volume).toReal ≤ M) :=
by
  intro α hα hα1
  obtain ⟨C₀, hC₀, hspatial⟩ := Analysis.exists_curl_holder_logarithmic_constant α hα hα1
  let C : ℝ≥0 := 1 + α + C₀ * ‖Geometry.curlLinearMap‖₊
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro T u p h
  obtain ⟨D, hDc, hdata⟩ := h.exists_spatial_curl_data
  obtain ⟨W, hWc, hW, hWH⟩ := h.exists_boundedContinuous_vorticity
  have hD := fun t ht => (hdata t ht).1
  have hfinite (t : ℝ) (ht : t ∈ Ico 0 T) : MemHolder α (W t : E₃ → E₃) := by
    obtain ⟨H, hH⟩ := hWH t ht
    exact (hH t ⟨ht.1, le_rfl⟩).memHolder
  have hCZ (t : ℝ) (ht : t ∈ Ico 0 T) (H : ℝ≥0)
      (hH : HolderWith H α (W t : E₃ → E₃)) :
      HolderWith (C₀ * H) α (D t : E₃ → E₃ →L[ℝ] E₃) ∧
        ‖D t‖ ≤ (C₀ : ℝ) * (1 + (eLpNorm (u t : E₃ → E₃) 2 volume).toReal +
          ‖W t‖ * Real.log (Real.exp 1 + (H : ℝ))) := by
    have heq : Geometry.curlLinearMap.compLeftContinuousBounded E₃ (D t) = W t :=
      BoundedContinuousFunction.ext (fun x => ((hdata t ht).2.2.2.2 x).trans (hW t ht x).symm)
    have hz := hspatial (u t) (D t) (hD t ht) (hdata t ht).2.1
      (hdata t ht).2.2.1 (hdata t ht).2.2.2.1
    simpa only [heq] using hz H (by simpa only [heq] using hH)
  have hg (H₀ : ℝ≥0) (h0 : HolderWith H₀ α (W 0 : E₃ → E₃)) (t : ℝ) (ht : t ∈ Ico 0 T) :=
    h.holderWith_vorticity_realization hDc hWc hD hW hWH
      (fun s hs => (hCZ s hs _ (hfinite s hs).holderWith).1) h0 ht
  have hn (t : ℝ) (ht : t ∈ Ico 0 T) :=
    h.norm_vorticity_realization_le_exp_integral hDc hWc hD hW ht
  refine ⟨D, W, hDc, hWc, hD, hW, hg, hn, ?_⟩
  intro hBKM
  let E : ℝ := Real.sqrt (∫ x : E₃, ‖u 0 x‖ ^ 2)
  have hE0 : 0 ≤ E := Real.sqrt_nonneg _
  have hEn (t : ℝ) (ht : t ∈ Ico 0 T) : (eLpNorm (u t : E₃ → E₃) 2 volume).toReal = E :=
    (Analysis.sqrt_integral_sq_norm_eq_eLpNorm_toReal (hdata t ht).2.2.1).symm.trans
      (congrArg Real.sqrt (h.energy_eq_initial ht))
  obtain ⟨H₀, hH₀⟩ := hWH 0 ⟨le_rfl, h.1⟩
  have hzero := hH₀ 0 ⟨le_rfl, le_rfl⟩
  let A (t : ℝ) := ∫ s in 0..t, ‖D s‖
  have hlog (t : ℝ) (ht : t ∈ Ico 0 T) :
      ‖D t‖ ≤ (C₀ : ℝ) * (1 + E + ‖W t‖ *
        Real.log (Real.exp 1 + (H₀ : ℝ) * Real.exp ((C : ℝ) * A t))) := by
    have hz := (hCZ t ht _ (hg H₀ hzero t ht)).2
    change ‖D t‖ ≤ (C₀ : ℝ) * (1 + (eLpNorm (u t : E₃ → E₃) 2 volume).toReal +
      ‖W t‖ * Real.log (Real.exp 1 + (H₀ : ℝ) * Real.exp ((C : ℝ) * A t))) at hz
    rwa [hEn t ht] at hz
  obtain ⟨Mₐ, hMₐ, hA⟩ := Analysis.exists_uniform_integral_bound_of_logarithmic_growth
    hDc.norm hWc.norm (fun t _ => norm_nonneg (D t)) (fun t _ => norm_nonneg (W t)) hBKM
    C₀.coe_nonneg C.coe_nonneg hE0 H₀.coe_nonneg hlog
  let Hstar : ℝ≥0 := H₀ * ⟨Real.exp ((C : ℝ) * Mₐ), (Real.exp_pos _).le⟩
  let Wstar : ℝ := ‖W 0‖ * Real.exp Mₐ
  have hWstar : 0 ≤ Wstar := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hWHstar (t : ℝ) (ht : t ∈ Ico 0 T) : HolderWith Hstar α (W t : E₃ → E₃) := by
    apply (hg H₀ hzero t ht).mono
    apply NNReal.coe_le_coe.mp
    change (H₀ : ℝ) * Real.exp ((C : ℝ) * A t) ≤ (H₀ : ℝ) * Real.exp ((C : ℝ) * Mₐ)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (hA t ht) C.coe_nonneg)) H₀.coe_nonneg
  have hWbound (t : ℝ) (ht : t ∈ Ico 0 T) : ‖W t‖ ≤ Wstar :=
    (hn t ht).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hA t ht)) (norm_nonneg _))
  have hlogstar : 0 ≤ Real.log (Real.exp 1 + (Hstar : ℝ)) := Real.log_nonneg
    ((Real.one_le_exp_iff.mpr zero_le_one).trans (le_add_of_nonneg_right Hstar.coe_nonneg))
  let Dstar : ℝ := (C₀ : ℝ) * (1 + E + Wstar * Real.log (Real.exp 1 + (Hstar : ℝ)))
  have hDstar : 0 ≤ Dstar := by dsimp only [Dstar]; positivity
  have hDbound (t : ℝ) (ht : t ∈ Ico 0 T) : ‖D t‖ ≤ Dstar := by
    have hz := (hCZ t ht Hstar (hWHstar t ht)).2
    rw [hEn t ht] at hz
    exact hz.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (hWbound t ht) hlogstar)) C₀.coe_nonneg)
  let Vstar : ℝ := Dstar + 1 + (∫ x : E₃, ‖u 0 x‖ ^ 2) / (Real.pi * 4 / 3)
  have henergy0 : 0 ≤ ∫ x : E₃, ‖u 0 x‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have hVstar : 0 ≤ Vstar := by dsimp only [Vstar]; positivity
  have hVbound (t : ℝ) (ht : t ∈ Ico 0 T) : ‖u t‖ ≤ Vstar := by
    have hlip : LipschitzWith ‖D t‖₊ (u t : E₃ → E₃) :=
      lipschitzWith_of_nnnorm_fderiv_le (fun x => (hD t ht x).differentiableAt)
        (fun x => by simpa only [(hD t ht x).fderiv] using (D t).nnnorm_coe_le_nnnorm x)
    have hv := Analysis.norm_le_lipschitz_add_energy (u t) hlip
      ((memLp_two_iff_integrable_sq_norm (u t).continuous.aestronglyMeasurable).mp (hdata t ht).2.2.1)
    rw [h.energy_eq_initial ht] at hv
    exact hv.trans (add_le_add (add_le_add (hDbound t ht) le_rfl) le_rfl)
  let M : ℝ := 1 + Vstar + Dstar + Wstar + ((C₀ * Hstar : ℝ≥0) : ℝ) + (Hstar : ℝ) + E
  have hM : 0 < M := by dsimp only [M]; positivity
  have hbounds : Vstar ≤ M ∧ Dstar ≤ M ∧ Wstar ≤ M ∧
      ((C₀ * Hstar : ℝ≥0) : ℝ) ≤ M ∧ (Hstar : ℝ) ≤ M ∧ E ≤ M := by
    dsimp only [M]
    and_intros <;> linarith only [hVstar, hDstar, hWstar, hE0,
      Hstar.coe_nonneg, (C₀ * Hstar).coe_nonneg]
  refine ⟨⟨M, hM.le⟩, hM, ?_⟩
  intro t ht
  exact ⟨(hVbound t ht).trans hbounds.1, (hDbound t ht).trans hbounds.2.1,
    (hWbound t ht).trans hbounds.2.2.1,
    ((hCZ t ht Hstar (hWHstar t ht)).1).mono (NNReal.coe_le_coe.mp hbounds.2.2.2.1),
    (hWHstar t ht).mono (NNReal.coe_le_coe.mp hbounds.2.2.2.2.1),
    (hEn t ht).le.trans hbounds.2.2.2.2.2⟩

end ClockBarrier.Euler

