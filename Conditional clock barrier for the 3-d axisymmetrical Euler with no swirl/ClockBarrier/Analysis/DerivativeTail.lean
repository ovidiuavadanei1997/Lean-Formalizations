/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.HolderDerivative
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Integrability of derivative tails from finite energy and Hölder regularity

Finite differences use a step that shrinks with the annulus radius. A quadratic
estimate controls their integrals by the velocity's energy.
-/

public section

namespace ClockBarrier.Analysis

open Set Metric MeasureTheory
open scoped NNReal

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Integrate the quadratic finite-difference bound over a compact set. -/
theorem integral_norm_fderiv_apply_le_of_holderWith
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E₃ → F} {H α : ℝ≥0} (hf : Differentiable ℝ f)
    (hα : 0 < α) (hD : HolderWith H α (fderiv ℝ f))
    (henergy : Integrable (fun x => ‖f x‖ ^ 2) volume)
    {s : Set E₃} (hs : IsCompact s) (v : E₃) (hv : ‖v‖ = 1)
    {h : ℝ} (hh : 0 < h) :
    ∫ x in s, ‖fderiv ℝ f x v‖ ≤
      (2 * ∫ x, ‖f x‖ ^ 2) / h ^ 3 + (h / 2 + H * h ^ (α : ℝ)) * volume.real s := by
  have hi := henergy.comp_add_right (h • v)
  have hd : IntegrableOn (fun x => ‖fderiv ℝ f x v‖) s volume :=
    ((hD.continuous hα).clm_apply continuous_const).norm.continuousOn.integrableOn_compact hs
  have hc : IntegrableOn (fun _ : E₃ => h / 2 + H * h ^ (α : ℝ)) s volume :=
    integrableOn_const hs.measure_lt_top.ne
  have hsum : IntegrableOn
      (fun x => (‖f (x + h • v)‖ ^ 2 + ‖f x‖ ^ 2) / h ^ 3) s volume := by
    simpa only [Pi.add_apply, IntegrableOn] using
      (hi.integrableOn.add henergy.integrableOn).div_const (h ^ 3)
  have hb := integral_mono_ae hd
    (hsum.add hc)
    (ae_of_all _ (fun x => by
      simpa only [Pi.add_apply, add_assoc] using
        norm_fderiv_apply_le_sq_finite_difference hf hD x v hv hh))
  simp only [Pi.add_apply] at hb
  rw [integral_add hsum hc, integral_div,
    integral_add hi.integrableOn henergy.integrableOn, setIntegral_const, smul_eq_mul] at hb
  have he₁ : ∫ x in s, ‖f (x + h • v)‖ ^ 2 ≤ ∫ x, ‖f x‖ ^ 2 := by
    exact (setIntegral_le_integral (s := s) hi
      (ae_of_all _ (fun x => sq_nonneg ‖f (x + h • v)‖))).trans_eq
        (integral_add_right_eq_self (fun x => ‖f x‖ ^ 2) (h • v))
  have he₂ := div_le_div_of_nonneg_right
    (add_le_add he₁ (setIntegral_le_integral (s := s) henergy
      (ae_of_all _ (fun x => sq_nonneg ‖f x‖)))) (pow_nonneg hh.le 3)
  exact hb.trans (by
    simpa only [← two_mul, mul_comm (volume.real s)] using
      (add_le_add he₂ (le_refl (volume.real s * (h / 2 + H * h ^ (α : ℝ))))))

/-- On a distant annulus, the order-three kernel times a coordinate derivative
is controlled by finite energy and a decaying Hölder remainder. -/
theorem integral_norm_fderiv_apply_div_cube_annulus_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E₃ → F} {H α : ℝ≥0} (hf : Differentiable ℝ f)
    (hα : 0 < α) (hD : HolderWith H α (fderiv ℝ f))
    (henergy : Integrable (fun x => ‖f x‖ ^ 2) volume)
    (v : E₃) (hv : ‖v‖ = 1) {R : ℝ} (hR : 0 < R) :
    ∫ x in closedBall 0 (4 * R ^ 2) \ ball 0 (R ^ 2), ‖fderiv ℝ f x v‖ / ‖x‖ ^ 3 ≤
      (2 * ∫ x, ‖f x‖ ^ 2) / R ^ 3 +
        (Real.pi * 256 / 3) * (R⁻¹ / 2 + H * (R⁻¹) ^ (α : ℝ)) := by
  let s : Set E₃ := closedBall 0 (4 * R ^ 2) \ ball 0 (R ^ 2)
  have hs : IsCompact s := (isCompact_closedBall _ _).diff isOpen_ball
  have hl (x : E₃) (hx : x ∈ s) : R ^ 2 ≤ ‖x‖ := by
    simpa only [mem_ball, dist_zero_right, not_lt] using hx.2
  have hbound (x : E₃) (hx : x ∈ s) :
      ‖fderiv ℝ f x v‖ / ‖x‖ ^ 3 ≤ ‖fderiv ℝ f x v‖ / R ^ 6 :=
    div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hR 6)
      (by simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg R) (hl x hx) 3)
  have hc : Continuous (fun x => ‖fderiv ℝ f x v‖) :=
    ((hD.continuous hα).clm_apply continuous_const).norm
  have hi : IntegrableOn (fun x => ‖fderiv ℝ f x v‖ / ‖x‖ ^ 3) s volume :=
    (hc.continuousOn.div (continuous_norm.pow 3).continuousOn
      (fun x hx => pow_ne_zero 3 ((sq_pos_of_pos hR).trans_le (hl x hx)).ne')).integrableOn_compact hs
  have hvol : volume.real s ≤ (Real.pi * 256 / 3) * R ^ 6 := by
    refine (measureReal_mono (show s ⊆ closedBall 0 (4 * R ^ 2) from sdiff_subset)
      (isCompact_closedBall _ _).measure_lt_top.ne).trans_eq ?_
    rw [Measure.real, EuclideanSpace.volume_closedBall_fin_three, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)]
    ring
  have hmono := setIntegral_mono_on hi
    ((hc.continuousOn.integrableOn_compact hs).div_const (R ^ 6)) hs.measurableSet hbound
  rw [integral_div] at hmono
  have hm := (integral_norm_fderiv_apply_le_of_holderWith hf hα hD henergy hs v hv
    (inv_pos.mpr hR)).trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hvol (by positivity : 0 ≤ R⁻¹ / 2 + H * (R⁻¹) ^ (α : ℝ))))
  refine (hmono.trans (div_le_div_of_nonneg_right hm (pow_nonneg hR.le 6))).trans_eq ?_
  field_simp

/-- Every positive power of the reciprocal dyadic scale is summable. -/
theorem summable_inv_two_pow_rpow {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => (((2 : ℝ) ^ n)⁻¹) ^ a) := by
  have hg := summable_geometric_of_lt_one
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) a)
    (Real.rpow_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num) ha)
  simpa only [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2⁻¹), inv_pow] using hg

/-- Positive Hölder regularity of the derivative and finite energy suffice for
absolute integrability of an order-three derivative kernel at spatial infinity. -/
theorem integrableOn_norm_fderiv_apply_div_cube_compl_ball
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E₃ → F} {H α : ℝ≥0} (hf : Differentiable ℝ f)
    (hα : 0 < α) (hD : HolderWith H α (fderiv ℝ f))
    (henergy : Integrable (fun x => ‖f x‖ ^ 2) volume)
    (v : E₃) (hv : ‖v‖ = 1) :
    IntegrableOn (fun x => ‖fderiv ℝ f x v‖ / ‖x‖ ^ 3) (ball 0 1)ᶜ volume := by
  let A (n : ℕ) : Set E₃ :=
    closedBall 0 (4 * ((2 : ℝ) ^ n) ^ 2) \ ball 0 (((2 : ℝ) ^ n) ^ 2)
  have hA (n : ℕ) : IsCompact (A n) := (isCompact_closedBall _ _).diff isOpen_ball
  have hpow (n : ℕ) : ((2 : ℝ) ^ n) ^ 2 = 4 ^ n := by
    rw [pow_two, ← mul_pow]
    norm_num
  have hcover : (ball (0 : E₃) 1)ᶜ ⊆ ⋃ n, A n := by
    intro x hx
    obtain ⟨n, hn₁, hn₂⟩ := exists_nat_pow_near
      (show 1 ≤ ‖x‖ by simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] using hx)
      (by norm_num : (1 : ℝ) < 4)
    refine mem_iUnion.mpr ⟨n, ?_⟩
    simpa only [A, mem_sdiff, mem_closedBall, mem_ball, dist_zero_right, not_lt,
      hpow, pow_succ, mul_comm ((4 : ℝ) ^ n)] using And.intro hn₂.le hn₁
  have hi (n : ℕ) : IntegrableOn (fun x => ‖fderiv ℝ f x v‖ / ‖x‖ ^ 3) (A n) volume := by
    apply (ContinuousOn.div
      ((hD.continuous hα).clm_apply continuous_const).norm.continuousOn
      (continuous_norm.pow 3).continuousOn ?_).integrableOn_compact (hA n)
    intro x hx
    have hl : ((2 : ℝ) ^ n) ^ 2 ≤ ‖x‖ := by
      simpa only [mem_ball, dist_zero_right, not_lt] using hx.2
    exact pow_ne_zero 3 ((by positivity : 0 < ((2 : ℝ) ^ n) ^ 2).trans_le hl).ne'
  have hs₃ : Summable (fun n : ℕ => (2 * ∫ x, ‖f x‖ ^ 2) / ((2 : ℝ) ^ n) ^ 3) := by
    simpa only [Real.rpow_ofNat, inv_pow, div_eq_mul_inv] using
      (summable_inv_two_pow_rpow (by norm_num : (0 : ℝ) < 3)).mul_left (2 * ∫ x, ‖f x‖ ^ 2)
  have hs₁ : Summable (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ / 2) := by
    simpa only [Real.rpow_one] using (summable_inv_two_pow_rpow zero_lt_one).div_const 2
  have hsum := hs₃.add ((hs₁.add
    ((summable_inv_two_pow_rpow (show 0 < (α : ℝ) from hα)).mul_left (H : ℝ))).mul_left
      (Real.pi * 256 / 3))
  have hI : Summable (fun n => ∫ x in A n, ‖fderiv ℝ f x v‖ / ‖x‖ ^ 3) :=
    hsum.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => by positivity))
      (fun n => integral_norm_fderiv_apply_div_cube_annulus_le hf hα hD henergy v hv
        (by positivity : (0 : ℝ) < 2 ^ n))
  exact (integrableOn_iUnion_of_summable_integral_norm hi
    (by simpa only [norm_div, norm_pow, norm_norm] using hI)).mono_set hcover

end ClockBarrier.Analysis
