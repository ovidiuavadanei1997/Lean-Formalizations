/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
/-! # Increments normalized by a moving separation

The estimates use only derivatives of the paths, and integrate against a merely
integrable majorant. No derivative of the majorant is required.
-/

public section
namespace ClockBarrier.Analysis
open Set MeasureTheory
/-- The inverse power of a positive separation has controlled relative derivative. -/
theorem norm_inverse_rpow_derivative_le {r r' α L : ℝ}
    (hr : 0 < r) (hα : 0 ≤ α) (hr' : |r'| ≤ L * r) :
    |r' * (-α) * r ^ (-α - 1)| ≤ α * L * r ^ (-α) := by
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hα,
    abs_of_nonneg (Real.rpow_nonneg hr.le _)]
  calc
    _ ≤ (L * r) * α * r ^ (-α - 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr' hα) (Real.rpow_nonneg hr.le _)
    _ = α * L * r ^ (-α) := by
      rw [Real.rpow_sub hr, Real.rpow_one]
      field_simp
/-- A normalized vector increment has a derivative bound independent of the separation. -/
theorem norm_normalized_increment_derivative_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v v' : E} {r r' α L K F : ℝ} (hr : 0 < r) (hα : 0 ≤ α) (hL : 0 ≤ L)
    (hr' : |r'| ≤ L * r) (hv : ‖v‖ ≤ K * r ^ α)
    (hv' : ‖v'‖ ≤ L * ‖v‖ + F * r ^ α) :
    ‖(r' * (-α) * r ^ (-α - 1)) • v + r ^ (-α) • v'‖ ≤
      (1 + α) * L * K + F := by
  have hw : r ^ (-α) * r ^ α = 1 := by
    rw [Real.rpow_neg hr.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hr α).ne']
  calc
    _ ≤ |r' * (-α) * r ^ (-α - 1)| * ‖v‖ + r ^ (-α) * ‖v'‖ := by
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hr.le (-α))]
        using norm_add_le ((r' * (-α) * r ^ (-α - 1)) • v) (r ^ (-α) • v')
    _ ≤ (α * L * r ^ (-α)) * (K * r ^ α) +
        r ^ (-α) * (L * (K * r ^ α) + F * r ^ α) := by
      exact add_le_add
        (mul_le_mul (norm_inverse_rpow_derivative_le hr hα hr') hv (norm_nonneg _)
          (mul_nonneg (mul_nonneg hα hL) (Real.rpow_nonneg hr.le _)))
        (mul_le_mul_of_nonneg_left (hv'.trans (add_le_add
          (mul_le_mul_of_nonneg_left hv hL) le_rfl)) (Real.rpow_nonneg hr.le _))
    _ = (1 + α) * L * K + F := by
      calc
        _ = ((1 + α) * L * K + F) * (r ^ (-α) * r ^ α) := by ring
        _ = _ := by rw [hw, mul_one]
/-- Differentiating a nonzero Hilbert-space path's norm does not enlarge its speed. -/
theorem exists_hasDerivAt_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : ℝ → E} {X' : E} {t : ℝ} (hX : HasDerivAt X X' t) (hne : X t ≠ 0) :
    ∃ d : ℝ, HasDerivAt (fun s => ‖X s‖) d t ∧ |d| ≤ ‖X'‖ := by
  have hn : HasFDerivAt (norm : E → ℝ) (fderiv ℝ norm (X t)) (X t) :=
    (differentiableAt_id.norm ℝ hne).hasFDerivAt
  refine ⟨_, hn.comp_hasDerivAt t hX, ?_⟩
  calc
    _ ≤ ‖fderiv ℝ norm (X t)‖ * ‖X'‖ := (fderiv ℝ norm (X t)).le_opNorm X'
    _ ≤ 1 * ‖X'‖ := mul_le_mul_of_nonneg_right
      (by simpa only [NNReal.coe_one] using
        (norm_fderiv_le_of_lipschitz (x₀ := X t) ℝ lipschitzWith_one_norm)) (norm_nonneg _)
    _ = _ := one_mul _
/-- The derivative of a vector increment normalized by the current separation. -/
theorem exists_hasDerivAt_normalized_increment_le
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {X : ℝ → E} {V : ℝ → F} {X' : E} {V' : F} {t α L K A : ℝ}
    (hX : HasDerivAt X X' t) (hV : HasDerivAt V V' t) (hne : X t ≠ 0)
    (hα : 0 ≤ α) (hL : 0 ≤ L) (hX' : ‖X'‖ ≤ L * ‖X t‖)
    (hVbound : ‖V t‖ ≤ K * ‖X t‖ ^ α)
    (hV' : ‖V'‖ ≤ L * ‖V t‖ + A * ‖X t‖ ^ α) :
    ∃ Q' : F, HasDerivAt (fun s => ‖X s‖ ^ (-α) • V s) Q' t ∧
      ‖Q'‖ ≤ (1 + α) * L * K + A := by
  obtain ⟨d, hd, hdb⟩ := exists_hasDerivAt_norm_le hX hne
  exact ⟨_, (hd.rpow_const (Or.inl (norm_ne_zero_iff.mpr hne))).smul hV,
    by simpa only [add_comm] using
      norm_normalized_increment_derivative_le (norm_pos_iff.mpr hne) hα hL
        (hdb.trans hX') hVbound hV'⟩
/-- Integrating the normalized increment estimate requires no derivative of a Hölder seminorm. -/
theorem normalized_increment_le_integral
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {X X' : ℝ → E} {V V' : ℝ → F} {L K A : ℝ → ℝ} {a b α : ℝ}
    (hab : a ≤ b) (hα : 0 ≤ α)
    (hXc : ContinuousOn X (Icc a b)) (hVc : ContinuousOn V (Icc a b))
    (hne : ∀ t ∈ Icc a b, X t ≠ 0)
    (hX : ∀ t ∈ Ioo a b, HasDerivAt X (X' t) t)
    (hV : ∀ t ∈ Ioo a b, HasDerivAt V (V' t) t)
    (hL : ∀ t ∈ Ioo a b, 0 ≤ L t)
    (hX' : ∀ t ∈ Ioo a b, ‖X' t‖ ≤ L t * ‖X t‖)
    (hVbound : ∀ t ∈ Ioo a b, ‖V t‖ ≤ K t * ‖X t‖ ^ α)
    (hV' : ∀ t ∈ Ioo a b, ‖V' t‖ ≤ L t * ‖V t‖ + A t * ‖X t‖ ^ α)
    (hi : IntervalIntegrable (fun t => (1 + α) * L t * K t + A t) volume a b) :
    ‖‖X b‖ ^ (-α) • V b‖ ≤ ‖‖X a‖ ^ (-α) • V a‖ +
      ∫ t in a..b, (1 + α) * L t * K t + A t := by
  have hc : ContinuousOn (fun t => ‖X t‖ ^ (-α) • V t) (Icc a b) :=
    (hXc.norm.rpow_const (fun t ht => Or.inl (norm_ne_zero_iff.mpr (hne t ht)))).smul hVc
  have hd (t : ℝ) (ht : t ∈ Ioo a b) := exists_hasDerivAt_normalized_increment_le
    (hX t ht) (hV t ht) (hne t (Ioo_subset_Icc_self ht)) hα (hL t ht)
    (hX' t ht) (hVbound t ht) (hV' t ht)
  have hb := norm_sub_le_integral_of_norm_deriv_le_of_le hab hc
    (fun t ht => (hd t ht).choose_spec.1.differentiableAt.differentiableWithinAt)
    (Filter.Eventually.of_forall (fun t ht => by
      rw [(hd t ht).choose_spec.1.deriv]
      exact (hd t ht).choose_spec.2)) hi
  linarith [norm_sub_norm_le (‖X b‖ ^ (-α) • V b) (‖X a‖ ^ (-α) • V a)]
end ClockBarrier.Analysis
