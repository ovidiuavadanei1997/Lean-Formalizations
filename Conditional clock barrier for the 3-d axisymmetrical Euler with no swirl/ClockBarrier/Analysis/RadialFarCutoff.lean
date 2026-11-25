/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.AxisFarCutoff
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic.Linarith

/-! # A radial smooth cutoff for directional strain cancellation

The explicit inner-product bump construction supplies invariance under equal
norms, in addition to the support and smoothness properties of the axis cutoff.
-/

public section
namespace ClockBarrier.Analysis
open Set Metric Filter
open scoped Topology ContDiff
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- There is a smooth radial far cutoff with transition between radii `1/2`
and `1`. Radiality is an explicit part of the conclusion. -/
theorem exists_radial_far_cutoff :
    ∃ χ : E₃ → ℝ, ContDiff ℝ ∞ χ ∧ (χ =ᶠ[𝓝 (0 : E₃)] 0) ∧
      (∀ x, 0 ≤ χ x) ∧ (∀ x, χ x ≤ 1) ∧
      (∀ x, ‖x‖ ≤ 1 / 2 → χ x = 0) ∧ (∀ x, 1 ≤ ‖x‖ → χ x = 1) ∧
      (∀ x y, ‖x‖ = ‖y‖ → χ x = χ y) := by
  let b := ContDiffBumpBase.ofInnerProductSpace E₃
  have hs : ContDiff ℝ ∞ (fun x : E₃ => b.toFun 2 ((2 : ℝ) • x)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    have hp : (2, (2 : ℝ) • x) ∈ Ioi (1 : ℝ) ×ˢ (univ : Set E₃) :=
      ⟨by norm_num, mem_univ _⟩
    have hc := (b.smooth _ hp).contDiffAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds hp)
    simpa only [Function.comp_def, Function.uncurry] using
      hc.comp x (show ContDiffAt ℝ ∞ (fun y : E₃ => ((2 : ℝ), (2 : ℝ) • y)) x from
        contDiffAt_const.prodMk (contDiffAt_id.const_smul (2 : ℝ)))
  have hinner (x : E₃) (hx : ‖x‖ ≤ 1 / 2) : b.toFun 2 ((2 : ℝ) • x) = 1 := by
    apply b.eq_one 2 (by norm_num)
    simp only [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  refine ⟨fun x => 1 - b.toFun 2 ((2 : ℝ) • x), contDiff_const.sub hs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hn : ∀ᶠ x : E₃ in 𝓝 0, ‖x‖ < 1 / 2 :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds (by norm_num)
    exact hn.mono fun x hx => by simp only [hinner x hx.le, sub_self, Pi.zero_apply]
  · exact fun x => sub_nonneg.mpr (b.mem_Icc 2 ((2 : ℝ) • x)).2
  · exact fun x => sub_le_self _ (b.mem_Icc 2 ((2 : ℝ) • x)).1
  · exact fun x hx => by simp only [hinner x hx, sub_self]
  · intro x hx
    have hout : (2 : ℝ) • x ∉ Function.support (b.toFun 2) := by
      rw [b.support 2 (by norm_num)]
      simp only [mem_ball, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), not_lt]
      linarith
    have hz : b.toFun 2 ((2 : ℝ) • x) = 0 := by
      simpa only [Function.mem_support, not_not] using hout
    simp only [hz, sub_zero]
  · intro x y hxy
    simp only [b, ContDiffBumpBase.ofInnerProductSpace, norm_smul, hxy]

end ClockBarrier.Analysis
