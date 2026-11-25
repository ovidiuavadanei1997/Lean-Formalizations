/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.LocalHolderIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Radial integrals for Hölder and logarithmic curl estimates

Polar integration gives the exact dependence on the cutoff radius. Every
integral used as a majorant has a separate integrability theorem.
-/

public section
open Set Metric MeasureTheory

namespace ClockBarrier.Analysis
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Polar integration on a measurable radial set in three dimensions. -/
theorem integral_radial_on_norm_preimage (f : ℝ → ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) :
    (∫ x : E₃ in (fun x => ‖x‖) ⁻¹' s, f ‖x‖) =
      (3 * volume.real (ball (0 : E₃) 1)) *
        ∫ r in s ∩ Ioi 0, r ^ 2 * f r := by
  rw [← integral_indicator (hs.preimage continuous_norm.measurable)]
  change (∫ x : E₃, s.indicator f ‖x‖) = _
  rw [integral_fun_norm_addHaar]
  simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul, show 3 - 1 = (2 : ℕ) by decide]
  simp_rw [← s.indicator_mul_right (fun r : ℝ => r ^ 2) f, integral_indicator hs, Measure.restrict_restrict hs, mul_assoc]

/-- Radial integrability reduces to the one-dimensional polar density. -/
theorem integrable_radial_on_norm_preimage_iff (f : ℝ → ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) :
    IntegrableOn (fun x : E₃ => f ‖x‖) ((fun x => ‖x‖) ⁻¹' s) ↔
      IntegrableOn (fun r : ℝ => r ^ 2 * f r) (s ∩ Ioi 0) := by
  rw [← integrable_indicator_iff (hs.preimage continuous_norm.measurable)]
  change Integrable (fun x : E₃ => s.indicator f ‖x‖) ↔ _
  simp only [integrable_fun_norm_addHaar, finrank_euclideanSpace, Fintype.card_fin, show 3 - 1 = (2 : ℕ) by decide, smul_eq_mul]
  simp_rw [← s.indicator_mul_right (fun r : ℝ => r ^ 2) f]
  exact integrableOn_indicator_iff hs

/-- The small-radius Hölder majorant has order `R ^ α`. -/
theorem integral_holder_radial_ball {α R : ℝ} (hα : 0 < α) (hR : 0 < R) :
    (∫ x : E₃ in ball 0 R, ‖x‖ ^ (α - 3)) =
      (3 * volume.real (ball (0 : E₃) 1)) * (R ^ α / α) := by
  have hp := integral_radial_on_norm_preimage (fun r => r ^ (α - 3))
    (s := Iio R) measurableSet_Iio
  have hp' : (∫ x : E₃ in ball 0 R, ‖x‖ ^ (α - 3)) =
      (3 * volume.real (ball (0 : E₃) 1)) * ∫ r in Ioo 0 R, r ^ 2 * r ^ (α - 3) := by
    simpa only [show ((fun x : E₃ => ‖x‖) ⁻¹' Iio R) = ball 0 R by ext x; simp, Iio_inter_Ioi] using hp
  have heq : (∫ r : ℝ in Ioo 0 R, r ^ 2 * r ^ (α - 3)) =
      ∫ r : ℝ in Ioo 0 R, r ^ (α - 1) :=
    setIntegral_congr_fun measurableSet_Ioo (fun r hr => by
      simpa only [show (2 : ℝ) + (α - 3) = α - 1 by ring, Real.rpow_ofNat] using
        (Real.rpow_add hr.1 2 (α - 3)).symm)
  rw [hp', heq, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le,
    integral_rpow (Or.inl (by linarith : -1 < α - 1))]
  simp only [sub_add_cancel, Real.zero_rpow hα.ne', sub_zero]

/-- A positive Hölder exponent makes the near-field singularity integrable. -/
theorem integrableOn_holder_radial_ball {α : ℝ} (hα : 0 < α) (R : ℝ) :
    IntegrableOn (fun x : E₃ => ‖x‖ ^ (α - 3)) (ball 0 R) := by
  apply integrableOn_ball_of_norm_le_rpow (by simp : 1 ≤ Module.finrank ℝ E₃)
    (α := 3 - α) (C := 1) (by simpa using sub_lt_self (3 : ℝ) hα)
  · exact Filter.Eventually.of_forall (fun x => by
      simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), neg_sub, one_mul, le_refl])
  · exact (by fun_prop : Measurable (fun x : E₃ => ‖x‖ ^ (α - 3))).aestronglyMeasurable

/-- The radial power integral on a set of positive radii. -/
theorem integral_radial_rpow_on_norm_preimage (p : ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) (hpos : s ⊆ Ioi 0) :
    (∫ x : E₃ in (fun x => ‖x‖) ⁻¹' s, ‖x‖ ^ p) =
      (3 * volume.real (ball (0 : E₃) 1)) * ∫ r in s, r ^ (p + 2) := by
  rw [integral_radial_on_norm_preimage (fun r => r ^ p) hs, inter_eq_left.mpr hpos]
  exact congrArg (fun q => (3 * volume.real (ball (0 : E₃) 1)) * q)
    (setIntegral_congr_fun hs (fun r hr => by
      simpa only [Real.rpow_ofNat, add_comm p 2] using (Real.rpow_add (hpos hr) 2 p).symm))

/-- Power-weight integrability on a set of positive radii. -/
theorem integrable_radial_rpow_on_norm_preimage_iff (p : ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) (hpos : s ⊆ Ioi 0) :
    IntegrableOn (fun x : E₃ => ‖x‖ ^ p) ((fun x => ‖x‖) ⁻¹' s) ↔
      IntegrableOn (fun r : ℝ => r ^ (p + 2)) s := by
  rw [integrable_radial_on_norm_preimage_iff (fun r => r ^ p) hs, inter_eq_left.mpr hpos]
  exact integrableOn_congr_fun (fun r hr => by
    simpa only [Real.rpow_ofNat, add_comm p 2] using (Real.rpow_add (hpos hr) 2 p).symm) hs

/-- The differentiated kernel with a Hölder increment is integrable at infinity
when the exponent is less than one. -/
theorem integrableOn_holder_radial_tail {α R : ℝ} (hα : α < 1) (hR : 0 < R) :
    IntegrableOn (fun x : E₃ => ‖x‖ ^ (α - 4)) ((fun x => ‖x‖) ⁻¹' Ioi R) := by
  apply (integrable_radial_rpow_on_norm_preimage_iff (α - 4) measurableSet_Ioi
    (Ioi_subset_Ioi hR.le)).mpr
  exact integrableOn_Ioi_rpow_of_lt (by linarith) hR

/-- The far Hölder majorant has order `R ^ (α - 1)`. -/
theorem integral_holder_radial_tail {α R : ℝ} (hα : α < 1) (hR : 0 < R) :
    (∫ x : E₃ in (fun x => ‖x‖) ⁻¹' Ioi R, ‖x‖ ^ (α - 4)) =
      (3 * volume.real (ball (0 : E₃) 1)) * (R ^ (α - 1) / (1 - α)) := by
  rw [integral_radial_rpow_on_norm_preimage (α - 4) measurableSet_Ioi
    (Ioi_subset_Ioi hR.le), integral_Ioi_rpow_of_lt (by linarith : α - 4 + 2 < -1) hR]
  rw [show α - 4 + 2 + 1 = α - 1 by ring, show 1 - α = -(α - 1) by ring, div_neg, neg_div]

/-- The critical inverse-cube annulus produces the logarithm. -/
theorem integral_inverse_cube_annulus {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    (∫ x : E₃ in (fun x => ‖x‖) ⁻¹' Ico ε 1, ‖x‖ ^ (-(3 : ℝ))) =
      (3 * volume.real (ball (0 : E₃) 1)) * (-Real.log ε) := by
  rw [integral_radial_rpow_on_norm_preimage (-(3 : ℝ)) measurableSet_Ico
    (fun r hr => hε.trans_le hr.1)]
  simp only [show -(3 : ℝ) + 2 = -1 by norm_num, Real.rpow_neg_one,
    integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hε₁,
    integral_inv_of_pos hε zero_lt_one, one_div, Real.log_inv]

/-- The annular inverse-cube kernel is integrable for every positive inner radius. -/
theorem integrableOn_inverse_cube_annulus {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun x : E₃ => ‖x‖ ^ (-(3 : ℝ))) ((fun x => ‖x‖) ⁻¹' Ico ε 1) := by
  apply (integrable_radial_rpow_on_norm_preimage_iff (-(3 : ℝ)) measurableSet_Ico
    (fun r hr => hε.trans_le hr.1)).mpr
  exact ((continuousOn_id.rpow_const (fun r (hr : r ∈ Icc ε 1) =>
    Or.inl (hε.trans_le hr.1).ne')).integrableOn_compact isCompact_Icc).mono_set Ico_subset_Icc_self

end ClockBarrier.Analysis
