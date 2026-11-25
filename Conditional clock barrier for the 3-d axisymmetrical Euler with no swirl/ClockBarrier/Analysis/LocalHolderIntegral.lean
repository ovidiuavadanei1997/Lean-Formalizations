/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Uniform local inverse-cube bounds from Hölder increments

The translated radial majorant is integrable for every positive Hölder
exponent. Constants are chosen before the center and the near-field integrand.
-/

public section
namespace ClockBarrier.Analysis
open Set Metric MeasureTheory Function
open scoped ENNReal
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- A Hölder numerator and a lower distance comparison give the radial majorant. -/
theorem div_cube_le_holder_radial {d r N C α : ℝ}
    (hd : 0 < d) (hC : 0 ≤ C) (hr : d / 2 ≤ r) (hN : N ≤ C * d ^ α) :
    N / r ^ 3 ≤ (8 * C) * d ^ (α - 3) := by
  have hrpos : 0 < r := (half_pos hd).trans_le hr
  refine ((div_le_div_of_nonneg_right hN (pow_nonneg hrpos.le 3)).trans
    (div_le_div_of_nonneg_left (mul_nonneg hC (Real.rpow_nonneg hd.le _))
      (pow_pos (half_pos hd) 3) (pow_le_pow_left₀ (half_pos hd).le hr 3))).trans_eq ?_
  rw [Real.rpow_sub hd, Real.rpow_ofNat]
  ring

/-- The integrable radial majorant has one finite bound for every translated center. -/
theorem exists_uniform_lintegral_holder_radial {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (R : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ aStar : E₃,
      (∫⁻ a in closedBall aStar R, ENNReal.ofReal (C * ‖a - aStar‖ ^ (α - 3))) ≤
        ENNReal.ofReal B := by
  have hi : IntegrableOn (fun a : E₃ => C * ‖a‖ ^ (α - 3)) (ball 0 (R + 1)) volume := by
    apply integrableOn_ball_of_norm_le_rpow (by simp : 1 ≤ Module.finrank ℝ E₃)
      (α := 3 - α) (C := C) (by simpa using sub_lt_self (3 : ℝ) hα)
    · exact Filter.Eventually.of_forall (fun x => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _) _)), neg_sub, le_refl])
    · exact (by fun_prop : Measurable (fun a : E₃ => C * ‖a‖ ^ (α - 3))).aestronglyMeasurable
  have hic := hi.mono_set (closedBall_subset_ball (lt_add_one R))
  refine ⟨‖∫ a in closedBall (0 : E₃) R, C * ‖a‖ ^ (α - 3)‖ + 1,
    add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one, fun aStar => ?_⟩
  have ht := (measurePreserving_add_right (volume : Measure E₃) (-aStar)).setLIntegral_comp_preimage_emb
    (Homeomorph.addRight (-aStar)).measurableEmbedding
    (fun a => ENNReal.ofReal (C * ‖a‖ ^ (α - 3))) (closedBall 0 R)
  simp only [← sub_eq_add_neg, closedBall, dist_eq_norm, sub_zero, preimage_setOf_eq] at ht
  calc
    _ = ∫⁻ a in closedBall (0 : E₃) R, ENNReal.ofReal (C * ‖a‖ ^ (α - 3)) := by
      simpa only [closedBall, dist_eq_norm, sub_zero] using ht
    _ = ENNReal.ofReal (∫ a in closedBall (0 : E₃) R, C * ‖a‖ ^ (α - 3)) :=
      (ofReal_integral_eq_lintegral_ofReal hic
        (Filter.Eventually.of_forall (fun _ => mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _) _)))).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_one))

/-- Disjoint measurable blocks share one radial budget; no per-block constant is summed. -/
theorem exists_uniform_disjoint_holder_budget {I : Type*} [Countable I]
    {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C) (R : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (aStar : E₃) (S : I → Set E₃) (f : I → E₃ → ℝ),
      (∀ i, MeasurableSet (S i)) → Pairwise (Disjoint on S) →
      (∀ i, S i ⊆ closedBall aStar R) →
      (∀ i, ∀ᵐ a ∂volume.restrict (S i), f i a ≤ C * ‖a - aStar‖ ^ (α - 3)) →
      (∑' i, ∫⁻ a in S i, ENNReal.ofReal (f i a)) ≤ ENNReal.ofReal B := by
  obtain ⟨B, hB, hb⟩ := exists_uniform_lintegral_holder_radial hα hC R
  refine ⟨B, hB, fun aStar S f hm hd hs hf => ?_⟩
  calc
    _ ≤ ∑' i, ∫⁻ a in S i, ENNReal.ofReal (C * ‖a - aStar‖ ^ (α - 3)) :=
      ENNReal.tsum_le_tsum (fun i => lintegral_mono_ae
        ((hf i).mono (fun _ ha => ENNReal.ofReal_le_ofReal ha)))
    _ = ∫⁻ a in ⋃ i, S i, ENNReal.ofReal (C * ‖a - aStar‖ ^ (α - 3)) :=
      (lintegral_iUnion hm hd _).symm
    _ ≤ _ := (lintegral_mono_set (iUnion_subset hs)).trans (hb aStar)

/-- Physical near fields lie in the label ball of radius `2 * L`. A uniform
Hölder numerator therefore gives one budget over any disjoint measurable blocks. -/
theorem exists_uniform_disjoint_nearField_budget {I : Type*} [Countable I]
    {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C) (L : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (Ψ : E₃ → E₃),
      (∀ a b, ‖a - b‖ / 2 ≤ ‖Ψ a - Ψ b‖) →
      ∀ (aStar : E₃) (S : I → Set E₃) (N : I → E₃ → ℝ),
      (∀ i, MeasurableSet (S i)) → Pairwise (Disjoint on S) →
      (∀ i, ∀ a ∈ S i, ‖Ψ a - Ψ aStar‖ ≤ L) →
      (∀ i, ∀ᵐ a ∂volume.restrict (S i), N i a ≤ C * ‖a - aStar‖ ^ α) →
      (∑' i, ∫⁻ a in S i,
        ENNReal.ofReal (N i a / ‖Ψ a - Ψ aStar‖ ^ 3)) ≤ ENNReal.ofReal B := by
  obtain ⟨B, hB, hb⟩ := exists_uniform_disjoint_holder_budget (I := I) hα
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hC) (2 * L)
  refine ⟨B, hB, fun Ψ hΨ aStar S N hm hd hL hN => hb aStar S _ hm hd ?_ ?_⟩
  · exact fun i a ha => Metric.mem_closedBall.mpr (by
      rw [dist_eq_norm]
      linarith [hΨ a aStar, hL i a ha])
  · intro i
    filter_upwards [hN i] with a ha
    by_cases he : a = aStar
    · subst a
      simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, div_zero]
      positivity
    · exact div_cube_le_holder_radial (norm_pos_iff.mpr (sub_ne_zero.mpr he)) hC
        (hΨ a aStar) ha

end ClockBarrier.Analysis
