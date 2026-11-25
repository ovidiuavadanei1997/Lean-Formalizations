/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Frozen.VorticityHolderGrowth
public import ClockBarrier.Frozen.CurlHolderLogarithmic
import ClockBarrier.Euler.EnergyConservation
import ClockBarrier.Analysis.ExponentialFeedback
import ClockBarrier.Analysis.VelocitySupEnergy
import ClockBarrier.Analysis.CurlDirectionalLogarithmic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! # Uniform short-time bounds for actual classical Euler solutions

The time and bound are chosen before the solution and depend only on its
initial exponent and size. This is an a priori theorem for a supplied solution;
it does not assert existence or continuation of that solution.
-/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Uniform bounds on the portion of an existing solution before a common
time determined by the initial derivative and energy bounds. -/
theorem exists_uniform_short_time_bounds :
    ∀ (α : ℝ≥0), 0 < α → α < 1 → ∀ M : ℝ≥0,
    ∃ τ : ℝ, 0 < τ ∧ ∃ R : ℝ≥0, 0 < R ∧
      ∀ (T : ℝ) (u : ℝ → E₃ →ᵇ E₃) (p : ℝ → E₃ → ℝ)
        (_h : classical_euler_on α T u p) (D₀ : E₃ →ᵇ (E₃ →L[ℝ] E₃)),
        (∀ x, HasFDerivAt (u 0 : E₃ → E₃) (D₀ x) x) →
        ‖D₀‖ ≤ (M : ℝ) → HolderWith M α (D₀ : E₃ → E₃ →L[ℝ] E₃) →
        (eLpNorm (u 0 : E₃ → E₃) 2 volume).toReal ≤ (M : ℝ) →
        ∃ D : ℝ → E₃ →ᵇ (E₃ →L[ℝ] E₃), ContinuousOn D (Ico 0 T) ∧
          (∀ t ∈ Ico 0 T, ∀ x, HasFDerivAt (u t : E₃ → E₃) (D t x) x) ∧
          ∀ t ∈ Ico 0 T, t ≤ τ →
            ‖u t‖ ≤ (R : ℝ) ∧ ‖D t‖ ≤ (R : ℝ) ∧
            HolderWith R α (D t : E₃ → E₃ →L[ℝ] E₃) ∧
            (eLpNorm (u t : E₃ → E₃) 2 volume).toReal ≤ (M : ℝ) := by
  intro α hα hα1 M
  obtain ⟨C, hC, hCZ⟩ := Analysis.exists_curl_holder_logarithmic_constant α hα hα1
  obtain ⟨c, hc, hgrowth⟩ := vorticity_holder_growth_and_bkm_bounds α hα hα1
  let Q : ℝ≥0 := ‖Geometry.curlLinearMap‖₊ * M
  let K : ℝ := 1 + C * (1 + (M : ℝ) + (Q : ℝ) * (Real.exp 1 + Q))
  have hK : 0 < K := by dsimp only [K]; positivity
  let R : ℝ := 2 + 4 * K + 2 * C * Q + (M : ℝ) ^ 2 / (Real.pi * 4 / 3)
  have hR : 0 < R := by dsimp only [R]; positivity
  refine ⟨(2 * (1 + (c : ℝ)) * K)⁻¹, by positivity, ⟨R, hR.le⟩, hR, ?_⟩
  intro T u p h D₀ hd0 hDn0 hDH0 hE0
  obtain ⟨D, W, hDc, hWc, hD, hW, hWH, hWn, _⟩ := hgrowth T u p h
  obtain ⟨D', _, hdata⟩ := h.exists_spatial_curl_data
  have heqD (t : ℝ) (ht : t ∈ Ico 0 T) : D' t = D t :=
    BoundedContinuousFunction.ext (fun x => ((hdata t ht).1 x).unique (hD t ht x))
  have hdata (t : ℝ) (ht : t ∈ Ico 0 T) := (heqD t ht) ▸ hdata t ht
  have hcurl (t : ℝ) (ht : t ∈ Ico 0 T) :
      Geometry.curlLinearMap.compLeftContinuousBounded E₃ (D t) = W t :=
    BoundedContinuousFunction.ext (fun x => ((hdata t ht).2.2.2.2 x).trans (hW t ht x).symm)
  have hCZ (t : ℝ) (ht : t ∈ Ico 0 T) (H : ℝ≥0)
      (hH : HolderWith H α (W t : E₃ → E₃)) :
      HolderWith (C * H) α (D t : E₃ → E₃ →L[ℝ] E₃) ∧
        ‖D t‖ ≤ C * (1 + (eLpNorm (u t : E₃ → E₃) 2 volume).toReal +
          ‖W t‖ * Real.log (Real.exp 1 + H)) := by
    simpa only [hcurl t ht] using hCZ (u t) (D t) (hD t ht) (hdata t ht).2.1
      (hdata t ht).2.2.1 (hdata t ht).2.2.2.1 H (by simpa only [hcurl t ht] using hH)
  have h0 : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl, h.1⟩
  have hD0 : D 0 = D₀ :=
    BoundedContinuousFunction.ext (fun x => (hD 0 h0 x).unique (hd0 x))
  have hQ0 : HolderWith Q α (W 0 : E₃ → E₃) := fun x y => by
    simpa only [← hcurl 0 h0, hD0, ContinuousLinearMap.compLeftContinuousBounded_apply]
      using Geometry.holderWith_curlLinearMap hDH0 x y
  have hW0 : ‖W 0‖ ≤ (Q : ℝ) :=
    (h.norm_vorticity_realization_le h0 D₀ (W 0) hd0 (hW 0 h0)).trans
      (mul_le_mul_of_nonneg_left hDn0 (norm_nonneg Geometry.curlLinearMap))
  have hEn (t : ℝ) (ht : t ∈ Ico 0 T) :
      (eLpNorm (u t : E₃ → E₃) 2 volume).toReal =
        (eLpNorm (u 0 : E₃ → E₃) 2 volume).toReal :=
    (Analysis.sqrt_integral_sq_norm_eq_eLpNorm_toReal (hdata t ht).2.2.1).symm.trans
      ((congrArg Real.sqrt (h.energy_eq_initial ht)).trans
        (Analysis.sqrt_integral_sq_norm_eq_eLpNorm_toReal (hdata 0 h0).2.2.1))
  have henergy : (∫ x : E₃, ‖u 0 x‖ ^ 2) ≤ (M : ℝ) ^ 2 :=
    (Real.sq_sqrt (integral_nonneg (fun x : E₃ => sq_nonneg ‖u 0 x‖))).symm.trans_le
      ((sq_le_sq₀ (Real.sqrt_nonneg _) M.coe_nonneg).mpr
        ((Analysis.sqrt_integral_sq_norm_eq_eLpNorm_toReal (hdata 0 h0).2.2.1).trans_le hE0))
  let A (t : ℝ) := ∫ s in 0..t, ‖D s‖
  have hA0 (t : ℝ) (ht : t ∈ Ico 0 T) : 0 ≤ A t :=
    intervalIntegral.integral_nonneg ht.1 (fun s _ => norm_nonneg (D s))
  have hWbound (t : ℝ) (ht : t ∈ Ico 0 T) : ‖W t‖ ≤ (Q : ℝ) * Real.exp (A t) :=
    (hWn t ht).trans (mul_le_mul_of_nonneg_right hW0 (Real.exp_pos _).le)
  have hfeedback (t : ℝ) (ht : t ∈ Ico 0 T) :
      ‖D t‖ ≤ K * Real.exp ((1 + (c : ℝ)) * A t) := by
    have hz := (hCZ t ht _ (hWH Q hQ0 t ht)).2
    change ‖D t‖ ≤ C * (1 + (eLpNorm (u t : E₃ → E₃) 2 volume).toReal +
      ‖W t‖ * Real.log (Real.exp 1 + (Q : ℝ) * Real.exp ((c : ℝ) * A t))) at hz
    have hL : 0 ≤ Real.log (Real.exp 1 + (Q : ℝ) * Real.exp ((c : ℝ) * A t)) :=
      Real.log_nonneg ((Real.one_le_exp_iff.mpr zero_le_one).trans
        (le_add_of_nonneg_right (mul_nonneg Q.coe_nonneg (Real.exp_pos _).le)))
    have hm := hz.trans (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add le_rfl ((hEn t ht).trans_le hE0))
        (mul_le_mul_of_nonneg_right (hWbound t ht) hL)) C.coe_nonneg)
    exact (hm.trans (Analysis.logarithmic_feedback_le_exp C.coe_nonneg M.coe_nonneg
      Q.coe_nonneg Q.coe_nonneg c.coe_nonneg (hA0 t ht))).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (Real.exp_pos _).le)
  refine ⟨D, hDc, hD, ?_⟩
  intro t ht htau
  have hs : Icc 0 t ⊆ Ico 0 T := fun s hs => ⟨hs.1, hs.2.trans_lt ht.2⟩
  have htime : (1 + (c : ℝ)) * K * t ≤ 1 / 2 := by
    have hm := mul_le_mul_of_nonneg_left htau
      (show 0 ≤ 2 * (1 + (c : ℝ)) * K by positivity)
    rw [mul_inv_cancel₀ (show 2 * (1 + (c : ℝ)) * K ≠ 0 by positivity)] at hm
    nlinarith only [hm]
  have hAc : ContinuousOn A (Icc 0 t) := by
    simpa only [A, uIcc_of_le ht.1] using intervalIntegral.continuousOn_primitive_interval
      (a := 0) (b := t) (μ := volume) (f := fun s => ‖D s‖)
      (by simpa only [uIcc_of_le ht.1] using
        ((ContinuousOn.norm (f := D) hDc).mono hs).integrableOn_Icc (μ := volume))
  have hexp : Real.exp ((1 + (c : ℝ)) * A t) ≤ 2 :=
    Analysis.exp_mul_le_two_of_deriv_le ht.1 (by positivity) hAc
      (by simp only [A, intervalIntegral.integral_same])
      (fun s hs' => Analysis.hasDerivAt_primitive_of_continuousOn
        ((ContinuousOn.norm (f := D) hDc).mono hs) hs')
      (fun s hs' => hfeedback s (hs (Ioo_subset_Icc_self hs'))) htime
  have hDbound : ‖D t‖ ≤ 2 * K := (hfeedback t ht).trans
    (by simpa only [mul_comm K 2] using mul_le_mul_of_nonneg_left hexp hK.le)
  have hexpc : Real.exp ((c : ℝ) * A t) ≤ 2 :=
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left zero_le_one) (hA0 t ht))).trans hexp
  have hWH2 : HolderWith (2 * Q) α (W t : E₃ → E₃) :=
    (hWH Q hQ0 t ht).mono (NNReal.coe_le_coe.mp (by
      change (Q : ℝ) * Real.exp ((c : ℝ) * A t) ≤ 2 * Q
      simpa only [NNReal.coe_mul, NNReal.coe_ofNat, mul_comm (Q : ℝ) 2] using
        mul_le_mul_of_nonneg_left hexpc Q.coe_nonneg))
  have hlip : LipschitzWith ‖D t‖₊ (u t : E₃ → E₃) :=
    lipschitzWith_of_nnnorm_fderiv_le (fun x => (hD t ht x).differentiableAt)
      (fun x => by simpa only [(hD t ht x).fderiv] using (D t).nnnorm_coe_le_nnnorm x)
  have hv := Analysis.norm_le_lipschitz_add_energy (u t) hlip
    ((memLp_two_iff_integrable_sq_norm (u t).continuous.aestronglyMeasurable).mp (hdata t ht).2.2.1)
  rw [h.energy_eq_initial ht] at hv
  have hVbound : ‖u t‖ ≤ 2 * K + 1 + (M : ℝ) ^ 2 / (Real.pi * 4 / 3) :=
    hv.trans (add_le_add (add_le_add hDbound le_rfl)
      (div_le_div_of_nonneg_right henergy (by positivity)))
  have hRb : 2 * K + 1 + (M : ℝ) ^ 2 / (Real.pi * 4 / 3) ≤ R ∧
      2 * K ≤ R ∧ 2 * (C : ℝ) * Q ≤ R := by
    dsimp only [R]
    and_intros
    all_goals nlinarith only [hK, mul_nonneg C.coe_nonneg Q.coe_nonneg,
      div_nonneg (sq_nonneg (M : ℝ)) (show 0 ≤ Real.pi * 4 / 3 by positivity)]
  refine ⟨hVbound.trans hRb.1, hDbound.trans hRb.2.1,
    ((hCZ t ht (2 * Q) hWH2).1).mono ?_, (hEn t ht).trans_le hE0⟩
  apply NNReal.coe_le_coe.mp
  change (C : ℝ) * (2 * Q) ≤ R
  nlinarith only [hRb.2.2]

end ClockBarrier.Euler
