/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.PowerComparison
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith

/-!
# Scalar clock estimates

Reusable analysis for the clock arguments in Sections 4 and 6 of arXiv:2605.31587v3.
These lemmas take scalar differential inequalities as inputs. They do not assert the Euler
driver estimates or either main theorem of the paper.
-/

public section

open Set MeasureTheory

namespace ClockBarrier.Analysis

/-- An integrable lower bound for the logarithmic derivative gives an exponential lower bound.
Only the coefficient is assumed integrable; its continuity is not required. -/
theorem mul_exp_neg_integral_le_of_deriv_ge
    {J J' B : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn J (Icc a b))
    (hpos : ∀ t ∈ Icc a b, 0 < J t)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivWithinAt J (J' t) (Ioi t) t)
    (hB : IntegrableOn B (Icc a b))
    (hbound : ∀ t ∈ Ioo a b, -B t * J t ≤ J' t) :
    J a * Real.exp (-(∫ t in a..b, B t)) ≤ J b := by
  have hlog := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hab
    (hcont.log (fun t ht => (hpos t ht).ne'))
    (fun t ht => (hderiv t ht).log (hpos t (Ioo_subset_Icc_self ht)).ne')
    hB.neg (fun t ht => (le_div_iff₀ (hpos t (Ioo_subset_Icc_self ht))).2 (hbound t ht))
  simp only [Pi.neg_apply, intervalIntegral.integral_neg, le_sub_iff_add_le] at hlog
  simpa only [Real.exp_add, Real.exp_log (hpos a (left_mem_Icc.mpr hab)),
    Real.exp_log (hpos b (right_mem_Icc.mpr hab)), mul_comm] using Real.exp_le_exp.mpr hlog

/-- An auxiliary estimate allowing coefficients of either sign. The source-facing
comparison below uses `exists_positive_power_comparison` and its equality solution.
Here the substitution is applied directly to the clock inequality. On `J ≤ 1`, the positive
scaled transform `H = -(p-1)g` is at least one, so its constant forcing is absorbed
in `(p-1)(B+C)H`. Grönwall bounds `H`, and inversion gives the lower bound for `J`.
No auxiliary equality solution or continuity of the integrable coefficient is needed. -/
theorem exp_neg_integral_le_of_supercritical_power_deriv_ge
    {J J' B : ℝ → ℝ} {a b C p : ℝ} (hab : a ≤ b) (hC : 0 ≤ C) (hp : 1 < p)
    (hcont : ContinuousOn J (Icc a b)) (ha : J a = 1)
    (hpos : ∀ t ∈ Icc a b, 0 < J t) (hsmall : ∀ t ∈ Icc a b, J t ≤ 1)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivWithinAt J (J' t) (Ioi t) t)
    (hB : IntegrableOn B (Icc a b))
    (hbound : ∀ t ∈ Ioo a b, -B t * J t - C * (J t) ^ p ≤ J' t) :
    Real.exp (-(∫ t in a..b, B t + C)) ≤ J b := by
  let H := fun t => J t ^ (1 - p)
  have hHcont : ContinuousOn H (Icc a b) :=
    hcont.rpow_const (fun t ht => Or.inl (hpos t ht).ne')
  have hHbound (t : ℝ) (ht : t ∈ Ioo a b) :
      J' t * (1 - p) * J t ^ ((1 - p) - 1) ≤
        ((p - 1) * (B t + C)) * H t := by
    have hone := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      (hpos t (Ioo_subset_Icc_self ht)) (hsmall t (Ioo_subset_Icc_self ht))
      (sub_nonpos.mpr hp.le)
    have hbase := negative_power_derivative_bound
      (hpos t (Ioo_subset_Icc_self ht)) hp (hbound t ht)
    dsimp only [H]
    nlinarith only [hbase, mul_nonneg (sub_nonneg.mpr hp.le)
      (mul_nonneg hC (sub_nonneg.mpr hone))]
  have hlog := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hab
    (hHcont.log (fun t ht => (Real.rpow_pos_of_pos (hpos t ht) (1 - p)).ne'))
    (fun t ht => ((hderiv t ht).rpow_const (p := 1 - p)
      (Or.inl (hpos t (Ioo_subset_Icc_self ht)).ne')).log
        (Real.rpow_pos_of_pos (hpos t (Ioo_subset_Icc_self ht)) (1 - p)).ne')
    ((hB.add (integrableOn_const (isCompact_Icc.measure_lt_top.ne))).const_mul (p - 1))
    (fun t ht => (div_le_iff₀
      (Real.rpow_pos_of_pos (hpos t (Ioo_subset_Icc_self ht)) (1 - p))).2 (hHbound t ht))
  simp only [H, ha, Real.one_rpow, Real.log_one, sub_zero,
    Real.log_rpow (hpos b (right_mem_Icc.mpr hab)),
    intervalIntegral.integral_const_mul, Pi.add_apply] at hlog
  have hlogJ : -(∫ t in a..b, B t + C) ≤ Real.log (J b) := by
    apply (mul_le_mul_iff_right₀ (sub_pos.mpr hp)).mp
    nlinarith only [hlog]
  simpa only [Real.exp_log (hpos b (right_mem_Icc.mpr hab))] using
    Real.exp_le_exp.mpr hlogJ

/-- A continuous clock that starts at one and ends at or below one has a last crossing of one.
After that crossing it stays at or below one. -/
theorem exists_last_eq_one {J : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn J (Icc a b)) (ha : J a = 1) (hb : J b ≤ 1) :
    ∃ s ∈ Icc a b, J s = 1 ∧ ∀ t ∈ Icc s b, J t ≤ 1 := by
  let S := Icc a b ∩ J ⁻¹' ({1} : Set ℝ)
  have hcompact : IsCompact S :=
    isCompact_Icc.of_isClosed_subset
      (hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  obtain ⟨s, hs, hmax⟩ := hcompact.exists_isMaxOn
    ⟨a, ⟨left_mem_Icc.mpr hab, ha⟩⟩ continuousOn_id
  refine ⟨s, hs.1, hs.2, fun t ht => le_of_not_gt fun hgt => ?_⟩
  obtain ⟨u, hu, hJu⟩ := intermediate_value_Ioc' ht.2
    (hcont.mono (Icc_subset_Icc (hs.1.1.trans ht.1) le_rfl)) ⟨hb, hgt⟩
  exact (not_lt_of_ge (hmax ⟨⟨hs.1.1.trans (ht.1.trans hu.1.le), hu.2⟩, hJu⟩))
    (ht.1.trans_lt hu.1)

/-- A clock starting at one cannot collapse under an integrable linear loss and a power loss
with exponent at least one. The differential bound is required only when the clock is at most
one; the clock may leave and re-enter that region. The critical case uses the
logarithmic estimate; the supercritical case constructs the paper’s auxiliary
equality solution through the negative-power transform. -/
theorem exp_neg_integral_le_of_power_deriv_ge
    {J J' B : ℝ → ℝ} {a b C p : ℝ} (hab : a ≤ b) (hC : 0 ≤ C) (hp : 1 ≤ p)
    (hcont : ContinuousOn J (Icc a b)) (ha : J a = 1)
    (hpos : ∀ t ∈ Icc a b, 0 < J t)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivWithinAt J (J' t) (Ioi t) t)
    (hB : IntegrableOn B (Icc a b)) (hBnonneg : ∀ t ∈ Icc a b, 0 ≤ B t)
    (hbound : ∀ t ∈ Ioo a b, J t ≤ 1 → -B t * J t - C * (J t) ^ p ≤ J' t) :
    Real.exp (-(∫ t in a..b, B t + C)) ≤ J b := by
  have hA : IntegrableOn (fun t => B t + C) (Icc a b) :=
    hB.add (integrableOn_const (isCompact_Icc.measure_lt_top.ne))
  have hAnonneg : ∀ t ∈ Icc a b, 0 ≤ B t + C := fun t ht => add_nonneg (hBnonneg t ht) hC
  rcases le_total (J b) 1 with hb | hb
  · obtain ⟨s, hs, hJs, hsmall⟩ := exists_last_eq_one hab hcont ha hb
    have hlocal : Real.exp (-(∫ t in s..b, B t + C)) ≤ J b := by
      rcases hp.eq_or_lt with hcrit | hsuper
      · have hlinear : ∀ t ∈ Ioo s b, -(B t + C) * J t ≤ J' t := by
          intro t ht
          have h := hbound t ⟨hs.1.trans_lt ht.1, ht.2⟩ (hsmall t ⟨ht.1.le, ht.2.le⟩)
          rw [← hcrit, Real.rpow_one] at h
          nlinarith only [h]
        simpa only [hJs, one_mul] using mul_exp_neg_integral_le_of_deriv_ge hs.2
          (hcont.mono (Icc_subset_Icc hs.1 le_rfl))
          (fun t ht => hpos t ⟨hs.1.trans ht.1, ht.2⟩)
          (fun t ht => hderiv t ⟨hs.1.trans_lt ht.1, ht.2⟩)
          (hA.mono_set (Icc_subset_Icc hs.1 le_rfl)) hlinear
      · obtain ⟨f, _, _, _, _, hfb, hfJ⟩ := exists_positive_power_comparison hs.2 hC hsuper
          (hcont.mono (Icc_subset_Icc hs.1 le_rfl)) hJs
          (fun t ht => hpos t ⟨hs.1.trans ht.1, ht.2⟩)
          (fun t ht => hderiv t ⟨hs.1.trans_lt ht.1, ht.2⟩)
          (hB.mono_set (Icc_subset_Icc hs.1 le_rfl))
          (fun t ht => hBnonneg t ⟨hs.1.trans ht.1, ht.2⟩)
          (fun t ht => hbound t ⟨hs.1.trans_lt ht.1, ht.2⟩ (hsmall t ⟨ht.1.le, ht.2.le⟩))
        exact hfb.trans hfJ
    have hint := intervalIntegral.integral_mono_interval hs.1 hs.2 le_rfl
      ((ae_restrict_iff' measurableSet_Ioc).mpr
        (ae_of_all volume (fun t ht => hAnonneg t ⟨ht.1.le, ht.2⟩)))
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hA)
    exact (Real.exp_le_exp.mpr (neg_le_neg hint)).trans
      hlocal
  · exact (Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (intervalIntegral.integral_nonneg hab hAnonneg))).trans hb

/-- A common integrable coefficient gives a positive lower bound uniform over every admissible
clock. The constant is chosen before the clock, its derivative, and time. -/
theorem exists_pos_lower_bound_of_power_deriv_ge
    {B : ℝ → ℝ} {T C p : ℝ} (hC : 0 ≤ C) (hp : 1 ≤ p)
    (hB : IntegrableOn B (Ico 0 T)) (hBnonneg : ∀ t ∈ Ico 0 T, 0 ≤ B t) :
    ∃ c : ℝ, 0 < c ∧ ∀ (J J' : ℝ → ℝ),
      ContinuousOn J (Ico 0 T) → J 0 = 1 →
      (∀ t ∈ Ico 0 T, 0 < J t) →
      (∀ t ∈ Ioo 0 T, HasDerivWithinAt J (J' t) (Ioi t) t) →
      (∀ t ∈ Ioo 0 T, J t ≤ 1 → -B t * J t - C * (J t) ^ p ≤ J' t) →
      ∀ t ∈ Ico 0 T, c ≤ J t := by
  refine ⟨Real.exp (-(∫ t in Ico 0 T, B t + C)), Real.exp_pos _, ?_⟩
  intro J J' hcont hzero hpos hderiv hbound t ht
  have hsub : Icc 0 t ⊆ Ico 0 T := fun s hs => ⟨hs.1, hs.2.trans_lt ht.2⟩
  have hlocal := exp_neg_integral_le_of_power_deriv_ge ht.1 hC hp (hcont.mono hsub) hzero
    (fun s hs => hpos s (hsub hs))
    (fun s hs => hderiv s ⟨hs.1, hs.2.trans ht.2⟩)
    (hB.mono_set hsub) (fun s hs => hBnonneg s (hsub hs))
    (fun s hs => hbound s ⟨hs.1, hs.2.trans ht.2⟩)
  have hA : IntegrableOn (fun s => B s + C) (Ico 0 T) :=
    hB.add (integrableOn_const
      ((measure_mono Ico_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top).ne)
  have hint := setIntegral_mono_set hA
    (ae_restrict_of_forall_mem measurableSet_Ico (fun s hs => add_nonneg (hBnonneg s hs) hC))
    (show Ioc 0 t ⊆ Ico 0 T from fun s hs => ⟨hs.1.le, hs.2.trans_lt ht.2⟩).eventuallyLE
  exact (Real.exp_le_exp.mpr (neg_le_neg hint)).trans
    (by simpa only [intervalIntegral.integral_of_le ht.1] using hlocal)

end ClockBarrier.Analysis
