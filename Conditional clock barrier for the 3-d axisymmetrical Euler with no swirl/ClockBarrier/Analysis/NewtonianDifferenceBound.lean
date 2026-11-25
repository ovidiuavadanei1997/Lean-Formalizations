/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.CurlRadialIntegrals
public import ClockBarrier.Analysis.NewtonianBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Integrability of the Newtonian gradient difference -/
public section
namespace ClockBarrier.Analysis
open Set MeasureTheory Filter Metric
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem inverse_three_halves_difference_le {a : ℝ} (ha : 0 < a) :
    a ^ (-(3 : ℝ) / 2) - (1 + a) ^ (-(3 : ℝ) / 2) ≤
      (3 / 2 : ℝ) * a ^ (-(5 : ℝ) / 2) := by
  have hd (x : ℝ) (hx : x ∈ Icc a (a + 1)) :
      HasDerivWithinAt (fun y : ℝ => y ^ (-(3 : ℝ) / 2))
        (-(3 : ℝ) / 2 * x ^ (-(5 : ℝ) / 2)) (Icc a (a + 1)) x := by
    convert! (Real.hasDerivAt_rpow_const (p := -(3 : ℝ) / 2)
      (Or.inl (ha.trans_le hx.1).ne')).hasDerivWithinAt using 1
    norm_num
  have hb (x : ℝ) (hx : x ∈ Ico a (a + 1)) :
      ‖-(3 : ℝ) / 2 * x ^ (-(5 : ℝ) / 2)‖ ≤
        (3 / 2 : ℝ) * a ^ (-(5 : ℝ) / 2) := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonpos (by norm_num : -(3 : ℝ) / 2 ≤ 0),
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (ha.trans_le hx.1).le _)]
    norm_num only [neg_div, neg_neg]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ha hx.1 (by norm_num)) (by norm_num)
  have hm := norm_image_sub_le_of_norm_deriv_le_segment' hd hb
    (a + 1) (by constructor <;> linarith)
  have hh := le_abs_self (a ^ (-(3 : ℝ) / 2) - (a + 1) ^ (-(3 : ℝ) / 2))
  rw [norm_sub_rev, Real.norm_eq_abs] at hm
  simpa only [add_sub_cancel_left, add_sub_cancel_right, mul_one, add_comm a 1]
    using hh.trans hm

theorem norm_mul_norm_sq_rpow (x : Space) (p : ℝ) (hx : x ≠ 0) :
    ‖x‖ * (‖x‖ ^ 2) ^ p = ‖x‖ ^ (1 + 2 * p) := by
  simpa only [Real.rpow_one, Real.rpow_ofNat, Real.rpow_mul (norm_nonneg x)]
    using (Real.rpow_add (norm_pos_iff.mpr hx) 1 (2 * p)).symm

theorem newtonian_difference_weight_nonneg (x : Space) :
    0 ≤ ‖x‖ * ((‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) -
      (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2)) := by
  by_cases hx : x = 0
  · simp [hx]
  · exact mul_nonneg (norm_nonneg x) (sub_nonneg.mpr
      (Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos (norm_pos_iff.mpr hx))
        (by linarith) (by norm_num)))

theorem newtonian_difference_weight_le_near (x : Space) :
    ‖x‖ * ((‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) -
      (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2)) ≤ ‖x‖ ^ (-(2 : ℝ)) := by
  by_cases hx : x = 0
  · norm_num [hx]
  · calc
      _ ≤ ‖x‖ * (‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (norm_nonneg x)
      _ = _ := by
        simpa only [show (1 + 2 * (-(3 : ℝ) / 2)) = -2 by norm_num]
          using norm_mul_norm_sq_rpow x (-(3 : ℝ) / 2) hx

theorem newtonian_difference_weight_le_far (x : Space) :
    ‖x‖ * ((‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) -
      (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2)) ≤ (3 / 2 : ℝ) * ‖x‖ ^ (-(4 : ℝ)) := by
  by_cases hx : x = 0
  · norm_num [hx]
  · calc
      _ ≤ ‖x‖ * ((3 / 2 : ℝ) * (‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left (inverse_three_halves_difference_le
          (sq_pos_of_pos (norm_pos_iff.mpr hx))) (norm_nonneg x)
      _ = _ := by
        rw [mul_left_comm, norm_mul_norm_sq_rpow x _ hx]
        norm_num

theorem integrable_newtonian_difference_weight :
    Integrable (fun x : Space => ‖x‖ * ((‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) -
      (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2))) volume := by
  have hm : Measurable (fun x : Space => ‖x‖ * ((‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) -
      (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2))) := by fun_prop
  have hn : IntegrableOn (fun x : Space => ‖x‖ ^ (-(2 : ℝ))) (ball 0 2) := by
    convert! integrableOn_holder_radial_ball (α := 1) (by norm_num) 2 using 1
    norm_num
  have ht : IntegrableOn (fun x : Space => (3 / 2 : ℝ) * ‖x‖ ^ (-(4 : ℝ)))
      ((fun x => ‖x‖) ⁻¹' Ioi 1) := by
    simpa only [IntegrableOn, zero_sub] using
      (integrableOn_holder_radial_tail (α := 0) (R := 1)
        (by norm_num) (by norm_num)).const_mul (3 / 2 : ℝ)
  have hnear : IntegrableOn (fun x : Space => ‖x‖ * ((‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) -
      (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2))) (ball 0 2) :=
    hn.mono' hm.aestronglyMeasurable.restrict (ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (newtonian_difference_weight_nonneg x)]
      using newtonian_difference_weight_le_near x)
  have hfar : IntegrableOn (fun x : Space => ‖x‖ * ((‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) -
      (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2))) ((fun x => ‖x‖) ⁻¹' Ioi 1) :=
    ht.mono' hm.aestronglyMeasurable.restrict (ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (newtonian_difference_weight_nonneg x)]
      using newtonian_difference_weight_le_far x)
  have hsub : (ball (0 : Space) 2)ᶜ ⊆ (fun x => ‖x‖) ⁻¹' Ioi 1 := by
    intro x hx
    have hn : 2 ≤ ‖x‖ := by simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] using hx
    exact lt_of_lt_of_le (by norm_num) hn
  simpa only [union_compl_self, integrableOn_univ] using
    hnear.union (hfar.mono_set hsub)

theorem abs_newtonian_gradient_difference_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (i : Fin 3) (x : Space) :
    |-(x i * (ε ^ 2 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2)) -
      -(x i * (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2))| ≤
      ‖x‖ * ((‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) -
        (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2)) := by
  by_cases hx : x = 0
  · simp [hx]
  · have hεsq : ε ^ 2 ≤ 1 := by nlinarith
    have hlo : (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) ≤
        (ε ^ 2 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
    have hhi : (ε ^ 2 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) ≤
        (‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos (norm_pos_iff.mpr hx))
        (le_add_of_nonneg_left (sq_nonneg ε)) (by norm_num)
    rw [show -(x i * (ε ^ 2 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2)) -
        -(x i * (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2)) =
        -(x i) * ((ε ^ 2 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2) -
          (1 + ‖x‖ ^ 2) ^ (-(3 : ℝ) / 2)) by ring,
      abs_mul, abs_neg, abs_of_nonneg (sub_nonneg.mpr hlo)]
    exact mul_le_mul (abs_euclidean_coordinate_le_norm x i)
      (sub_le_sub_right hhi _) (sub_nonneg.mpr hlo) (norm_nonneg x)

end ClockBarrier.Analysis
