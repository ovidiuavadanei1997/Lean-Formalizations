/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.IntegralGronwall
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # A uniform time interval for exponential feedback

The scalar change of variable `exp (-k * f)` gives a bound before the
explicit reciprocal time scale. Only interior derivatives are used.
-/

public section
namespace ClockBarrier.Analysis
open Set

/-- An exponential differential inequality has a uniform short-time bound. -/
theorem exp_mul_le_two_of_deriv_le {f d : ℝ → ℝ} {t k K : ℝ}
    (ht : 0 ≤ t) (hk : 0 ≤ k)
    (hf : ContinuousOn f (Icc 0 t)) (hf0 : f 0 = 0)
    (hd : ∀ s ∈ Ioo 0 t, HasDerivAt f (d s) s)
    (hbound : ∀ s ∈ Ioo 0 t, d s ≤ K * Real.exp (k * f s))
    (htime : k * K * t ≤ 1 / 2) : Real.exp (k * f t) ≤ 2 := by
  let g : ℝ → ℝ := fun s => Real.exp (-(k * f s))
  have hg (s : ℝ) (hs : s ∈ Ioo 0 t) :
      HasDerivAt g (Real.exp (-(k * f s)) * (-(k * d s))) s :=
    ((hd s hs).const_mul k).neg.exp
  have hge (s : ℝ) (hs : s ∈ Ioo 0 t) :
      -(k * K) ≤ Real.exp (-(k * f s)) * (-(k * d s)) := by
    have hb := mul_le_mul_of_nonneg_right (hbound s hs)
      (Real.exp_pos (-(k * f s))).le
    rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at hb
    nlinarith only [mul_le_mul_of_nonneg_left hb hk]
  have he := (convex_Icc (0 : ℝ) t).mul_sub_le_image_sub_of_le_deriv
    (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hf).neg)
    (fun s hs => (hg s (by simpa only [interior_Icc] using hs)).differentiableAt.differentiableWithinAt)
    (fun s hs => (hge s (by simpa only [interior_Icc] using hs)).trans_eq
      (hg s (by simpa only [interior_Icc] using hs)).deriv.symm)
    0 (left_mem_Icc.mpr ht) t (right_mem_Icc.mpr ht) ht
  simp only [Function.comp_apply, Pi.neg_apply, Pi.mul_apply, hf0, mul_zero, neg_zero,
    Real.exp_zero, sub_zero] at he
  have hl : 1 / 2 ≤ Real.exp (-(k * f t)) := by linarith only [he, htime]
  have hprod : Real.exp (-(k * f t)) * Real.exp (k * f t) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  nlinarith only [mul_le_mul_of_nonneg_right hl (Real.exp_pos (k * f t)).le, hprod]

/-- A rough exponential majorant for the logarithmic curl estimate after transport. -/
theorem logarithmic_feedback_le_exp {C E W H c A : ℝ}
    (hC : 0 ≤ C) (hE : 0 ≤ E) (hW : 0 ≤ W) (hH : 0 ≤ H)
    (hc : 0 ≤ c) (hA : 0 ≤ A) :
    C * (1 + E + W * Real.exp A * Real.log (Real.exp 1 + H * Real.exp (c * A))) ≤
      (C * (1 + E + W * (Real.exp 1 + H))) * Real.exp ((1 + c) * A) := by
  have hec : 1 ≤ Real.exp (c * A) := Real.one_le_exp_iff.mpr (mul_nonneg hc hA)
  have hlog : Real.log (Real.exp 1 + H * Real.exp (c * A)) ≤
      (Real.exp 1 + H) * Real.exp (c * A) :=
    (Real.log_le_self (by positivity)).trans (by
      nlinarith only [mul_le_mul_of_nonneg_left hec (Real.exp_pos 1).le])
  have he : 1 ≤ Real.exp ((1 + c) * A) :=
    Real.one_le_exp_iff.mpr (mul_nonneg (by positivity) hA)
  apply (mul_le_mul_of_nonneg_left
    (add_le_add (le_refl (1 + E)) (mul_le_mul_of_nonneg_left hlog
      (mul_nonneg hW (Real.exp_pos A).le))) hC).trans
  have hbase := mul_le_mul_of_nonneg_left he (mul_nonneg hC (show 0 ≤ 1 + E by positivity))
  simp only [add_mul, one_mul, Real.exp_add] at hbase ⊢
  nlinarith only [hbase]

end ClockBarrier.Analysis
