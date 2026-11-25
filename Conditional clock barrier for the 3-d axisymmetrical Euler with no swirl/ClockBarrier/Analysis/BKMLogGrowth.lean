/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.IntegralGronwall
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
/-! # Logarithmic feedback under an integrable vorticity majorant -/

public section
namespace ClockBarrier.Analysis
open Set MeasureTheory
/-- An exponentially growing Hölder constant has at most affine logarithmic growth. -/
theorem log_exp_add_mul_exp_le {H x : ℝ} (hH : 0 ≤ H) (hx : 0 ≤ x) :
    Real.log (Real.exp 1 + H * Real.exp x) ≤ Real.log (Real.exp 1 + H) + x := by
  have he : Real.exp 1 ≤ Real.exp 1 * Real.exp x :=
    le_mul_of_one_le_right (Real.exp_pos 1).le (Real.one_le_exp_iff.mpr hx)
  calc
    _ ≤ Real.log ((Real.exp 1 + H) * Real.exp x) :=
      Real.log_le_log (by positivity) (by nlinarith only [he])
    _ = _ := by rw [Real.log_mul (by positivity) (Real.exp_pos x).ne', Real.log_exp]
/-- Logarithmic feedback and an integrable vorticity bound control the accumulated gradient. -/
theorem exists_uniform_integral_bound_of_logarithmic_growth
    {d w : ℝ → ℝ} {T C c E H : ℝ}
    (hd : ContinuousOn d (Ico 0 T)) (hw : ContinuousOn w (Ico 0 T))
    (hd0 : ∀ t ∈ Ico 0 T, 0 ≤ d t) (hw0 : ∀ t ∈ Ico 0 T, 0 ≤ w t)
    (hwi : IntegrableOn w (Ico 0 T))
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hE : 0 ≤ E) (hH : 0 ≤ H)
    (hlog : ∀ t ∈ Ico 0 T, d t ≤ C * (1 + E + w t *
      Real.log (Real.exp 1 + H * Real.exp (c * ∫ s in 0..t, d s)))) :
    ∃ M : ℝ, 0 < M ∧ ∀ t ∈ Ico 0 T, ∫ s in 0..t, d s ≤ M := by
  let L := Real.log (Real.exp 1 + H)
  let k (t : ℝ) := C * (1 + E + w t * (L + c))
  have hL : 0 ≤ L := Real.log_nonneg
    ((Real.one_le_exp_iff.mpr zero_le_one).trans (le_add_of_nonneg_right hH))
  have hki : IntegrableOn k (Ico 0 T) :=
    ((integrableOn_const ((measure_mono Ico_subset_Icc_self).trans_lt
      isCompact_Icc.measure_lt_top).ne).add (hwi.mul_const (L + c))).const_mul C
  have hkc : ContinuousOn k (Ico 0 T) :=
    continuousOn_const.mul (continuousOn_const.add (hw.mul continuousOn_const))
  have hk0 (t : ℝ) (ht : t ∈ Ico 0 T) : 0 ≤ k t := by
    exact mul_nonneg hC (add_nonneg (add_nonneg zero_le_one hE)
      (mul_nonneg (hw0 t ht) (add_nonneg hL hc)))
  refine ⟨Real.exp (∫ s in Ico 0 T, k s), Real.exp_pos _, ?_⟩
  intro t ht
  have hs : Icc 0 t ⊆ Ico 0 T := fun s hs => ⟨hs.1, hs.2.trans_lt ht.2⟩
  let A (s : ℝ) := ∫ r in 0..s, d r
  have hA0 (s : ℝ) (hs' : s ∈ Icc 0 t) : 0 ≤ A s :=
    intervalIntegral.integral_nonneg hs'.1
      (fun r hr => hd0 r (hs ⟨hr.1, hr.2.trans hs'.2⟩))
  have hAc : ContinuousOn A (Icc 0 t) := by
    simpa only [uIcc_of_le ht.1] using intervalIntegral.continuousOn_primitive_interval
      (a := 0) (b := t) (μ := volume) (f := d)
      (by simpa only [uIcc_of_le ht.1] using (hd.mono hs).integrableOn_Icc (μ := volume))
  have hdiff (s : ℝ) (hs' : s ∈ Ioo 0 t) : d s ≤ k s * (1 + A s) := by
    have ha := hA0 s (Ioo_subset_Icc_self hs')
    have hw' := hw0 s (hs (Ioo_subset_Icc_self hs'))
    have hl : Real.log (Real.exp 1 + H * Real.exp (c * A s)) ≤ (L + c) * (1 + A s) :=
      (log_exp_add_mul_exp_le hH (mul_nonneg hc ha)).trans (by
        dsimp only [L]; nlinarith only [mul_nonneg hL ha, hc])
    calc
      _ ≤ C * (1 + E + w s * Real.log (Real.exp 1 + H * Real.exp (c * A s))) :=
        hlog s (hs (Ioo_subset_Icc_self hs'))
      _ ≤ C * ((1 + E) * (1 + A s) + w s * ((L + c) * (1 + A s))) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (le_mul_of_one_le_right (by positivity) (by linarith only [ha]))
          (mul_le_mul_of_nonneg_left hl hw')) hC
      _ = _ := by dsimp only [k]; ring
  have hg := le_mul_exp_integral_of_deriv_le ht.1 (continuousOn_const.add hAc) (hkc.mono hs)
    (fun s hs' => (hasDerivAt_primitive_of_continuousOn (hd.mono hs) hs').const_add 1) hdiff
  have hi := setIntegral_mono_set hki
    (ae_restrict_of_forall_mem measurableSet_Ico hk0)
    (show Ioc 0 t ⊆ Ico 0 T from fun s hs' => ⟨hs'.1.le, hs'.2.trans_lt ht.2⟩).eventuallyLE
  have hg' : 1 + A t ≤ Real.exp (∫ s in 0..t, k s) := by
    simpa only [A, Pi.add_apply, intervalIntegral.integral_same, add_zero, one_mul] using hg
  exact (le_add_of_nonneg_left zero_le_one).trans
    (hg'.trans (Real.exp_le_exp.mpr (by
      simpa only [intervalIntegral.integral_of_le ht.1] using hi)))
end ClockBarrier.Analysis
