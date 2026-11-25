/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.CurlRadialIntegrals
public import ClockBarrier.Analysis.DirectionalStrainKernel
import ClockBarrier.Analysis.LogarithmicOptimization

/-! # Quantitative near-field curl estimates

The small ball uses the Hölder increment; the remaining annulus uses bounded
vorticity. A strictly positive cutoff works even when the Hölder constant is
zero. No limiting interchange is needed for this finite integral decomposition.
-/

public section
open Set Metric MeasureTheory
open scoped NNReal InnerProductSpace BoundedContinuousFunction

namespace ClockBarrier.Analysis
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- A supported Hölder radial majorant controls convergence and the integral. -/
theorem integrable_abs_integral_le_holder_radial
    {f : E₃ → ℝ} {α H R : ℝ} (hα : 0 < α) (hR : 0 < R)
    (hf : AEStronglyMeasurable f volume)
    (hzero : ∀ x, R ≤ ‖x‖ → f x = 0)
    (hbound : ∀ x, |f x| ≤ H * ‖x‖ ^ (α - 3)) :
    Integrable f volume ∧ |∫ x, f x| ≤
      (3 * volume.real (ball (0 : E₃) 1)) * H * R ^ α / α := by
  have hi := (integrable_indicator_iff measurableSet_ball).mpr ((integrableOn_holder_radial_ball hα R).const_mul H)
  have hm (x : E₃) : ‖f x‖ ≤ (ball 0 R).indicator (fun x : E₃ => H * ‖x‖ ^ (α - 3)) x := by
    by_cases hx : x ∈ ball (0 : E₃) R
    · simpa only [indicator_of_mem hx, Real.norm_eq_abs] using hbound x
    · simp only [indicator_of_notMem hx,
        hzero x (by simpa only [mem_ball, dist_zero_right, not_lt] using hx), norm_zero, le_refl]
  refine ⟨hi.mono' hf (Filter.Eventually.of_forall hm),
    (norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hm)).trans_eq ?_⟩
  rw [integral_indicator measurableSet_ball, integral_const_mul, integral_holder_radial_ball hα hR]
  ring

/-- The small-ball and annular majorants give the unoptimized logarithmic bound. -/
theorem integrable_abs_integral_le_holder_logarithmic_split
    {f : E₃ → ℝ} {α H W ε : ℝ} (hα : 0 < α) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hf : AEStronglyMeasurable f volume)
    (hzero : ∀ x, 1 ≤ ‖x‖ → f x = 0)
    (hholder : ∀ x, |f x| ≤ H * ‖x‖ ^ (α - 3))
    (hbounded : ∀ x, |f x| ≤ W * ‖x‖ ^ (-(3 : ℝ))) :
    Integrable f volume ∧ |∫ x, f x| ≤
      (3 * volume.real (ball (0 : E₃) 1)) *
        (H * ε ^ α / α + W * (-Real.log ε)) := by
  let A : Set E₃ := (fun x => ‖x‖) ⁻¹' Ico ε 1
  let g := fun x : E₃ =>
    (ball 0 ε).indicator (fun y : E₃ => H * ‖y‖ ^ (α - 3)) x +
      A.indicator (fun y : E₃ => W * ‖y‖ ^ (-(3 : ℝ))) x
  have hA : MeasurableSet A := measurableSet_Ico.preimage continuous_norm.measurable
  have hn := (integrable_indicator_iff measurableSet_ball).mpr
    ((integrableOn_holder_radial_ball hα ε).const_mul H)
  have ha := (integrable_indicator_iff hA).mpr
    ((integrableOn_inverse_cube_annulus hε).const_mul W)
  have hm (x : E₃) : ‖f x‖ ≤ g x := by
    by_cases hx : ‖x‖ < ε
    · simpa [g, A, mem_ball, hx, not_le_of_gt hx, Real.norm_eq_abs] using hholder x
    · by_cases hx₁ : ‖x‖ < 1
      · simpa [g, A, mem_ball, hx, hx₁, le_of_not_gt hx, Real.norm_eq_abs] using hbounded x
      · simp [g, A, mem_ball, hx, hx₁, hzero x (le_of_not_gt hx₁)]
  refine ⟨(hn.add ha).mono' hf (Filter.Eventually.of_forall hm),
    (norm_integral_le_of_norm_le (hn.add ha) (Filter.Eventually.of_forall hm)).trans_eq ?_⟩
  simp only [Pi.add_apply]
  rw [integral_add hn ha, integral_indicator measurableSet_ball, integral_indicator hA,
    integral_const_mul, integral_const_mul, integral_holder_radial_ball hα hε,
    integral_inverse_cube_annulus hε hε₁]
  ring

/-- Bounded vorticity controls the annular directional kernel by an inverse cube. -/
theorem abs_directional_strain_increment_le_bounded
    (ω : E₃ →ᵇ E₃) (e : E₃) (he : ‖e‖ = 1) (x : E₃) :
    let w := ω x - ω 0
    |⟪e, x⟫_ℝ *
      ⟪e, (!₂[x 1 * w 2 - x 2 * w 1, x 2 * w 0 - x 0 * w 2,
        x 0 * w 1 - x 1 * w 0] : E₃)⟫_ℝ / ‖x‖ ^ 5| ≤
      (2 * ‖ω‖) * ‖x‖ ^ (-(3 : ℝ)) := by
  have hb : ‖ω x - ω 0‖ ≤ 2 * ‖ω‖ :=
    (norm_sub_le _ _).trans ((add_le_add (ω.norm_coe_le_norm x) (ω.norm_coe_le_norm 0)).trans_eq
      (two_mul ‖ω‖).symm)
  simpa only [Real.rpow_neg_ofNat, zpow_neg, zpow_ofNat, div_eq_mul_inv] using
    (abs_directional_strain_kernel_le x (ω x - ω 0) e he).trans
      (div_le_div_of_nonneg_right hb (pow_nonneg (norm_nonneg x) 3))

/-- The actual smooth directional near field obeys the two-scale estimate. -/
theorem directional_smooth_near_holder_logarithmic_bound
    (ω : E₃ →ᵇ E₃) {H α : ℝ≥0} (hα : 0 < α)
    (hω : HolderWith H α (ω : E₃ → E₃))
    {χ : E₃ → ℝ} (hχ : Measurable χ)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1)
    (e : E₃) (he : ‖e‖ = 1) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    let f := fun x : E₃ =>
      let w := ω x - ω 0
      (1 - χ x) * (⟪e, x⟫_ℝ *
        ⟪e, (!₂[x 1 * w 2 - x 2 * w 1, x 2 * w 0 - x 0 * w 2,
          x 0 * w 1 - x 1 * w 0] : E₃)⟫_ℝ / ‖x‖ ^ 5)
    Integrable f volume ∧ |∫ x, f x| ≤
      (3 * volume.real (ball (0 : E₃) 1)) *
        ((H : ℝ) * ε ^ (α : ℝ) / (α : ℝ) + (2 * ‖ω‖) * (-Real.log ε)) := by
  have hcutoff (x : E₃) (v : ℝ) : |(1 - χ x) * v| ≤ |v| := by
    simpa only [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hχ₁ x))] using
      (mul_le_of_le_one_left (abs_nonneg v) (sub_le_self 1 (hχ₀ x)))
  apply integrable_abs_integral_le_holder_logarithmic_split (NNReal.coe_pos.mpr hα) hε hε₁
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · exact fun x hx => by simp only [houter x hx, sub_self, zero_mul]
  · exact fun x => (hcutoff x _).trans (abs_directional_strain_increment_le_rpow hω e he x)
  · exact fun x => (hcutoff x _).trans (abs_directional_strain_increment_le_bounded ω e he x)

/-- Optimizing the positive cutoff gives a logarithmic bound, including `H = 0`. -/
theorem directional_smooth_near_logarithmic_bound
    (ω : E₃ →ᵇ E₃) {H α : ℝ≥0} (hα : 0 < α)
    (hω : HolderWith H α (ω : E₃ → E₃))
    {χ : E₃ → ℝ} (hχ : Measurable χ)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1) (e : E₃) (he : ‖e‖ = 1) :
    let f := fun x : E₃ =>
      let w := ω x - ω 0
      (1 - χ x) * (⟪e, x⟫_ℝ *
        ⟪e, (!₂[x 1 * w 2 - x 2 * w 1, x 2 * w 0 - x 0 * w 2,
          x 0 * w 1 - x 1 * w 0] : E₃)⟫_ℝ / ‖x‖ ^ 5)
    Integrable f volume ∧ |∫ x, f x| ≤
      (3 * volume.real (ball (0 : E₃) 1) / (α : ℝ)) *
        (1 + (2 * ‖ω‖) * Real.log (Real.exp 1 + (H : ℝ))) := by
  obtain ⟨ε, hε, hε₁, hlog, hpow⟩ := exists_holder_logarithmic_cutoff
    (NNReal.coe_pos.mpr hα) H.coe_nonneg
  obtain ⟨hi, hb⟩ := directional_smooth_near_holder_logarithmic_bound
    ω hα hω hχ hχ₀ hχ₁ houter e he hε hε₁.le
  refine ⟨hi, hb.trans ?_⟩
  calc
    _ ≤ (3 * volume.real (ball (0 : E₃) 1)) *
        (1 / (α : ℝ) + (2 * ‖ω‖) * (-Real.log ε)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (div_le_div_of_nonneg_right hpow α.coe_nonneg) le_rfl) (by positivity)
    _ = _ := by rw [hlog]; ring

end ClockBarrier.Analysis
