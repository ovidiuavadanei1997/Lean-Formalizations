/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Right derivatives of compact minima

Uniform differentiability on a compact parameter space implies that the right
derivative of the minimum is the least derivative among its minimizing points.
Minimizers need not be unique. These are independent general analytic lemmas.
The source-facing proof of Lemma 4.1 uses `SpectralMinimum` and its spectral-gap
argument; only attainment of minima is shared with this module.
-/

public section
namespace ClockBarrier.Analysis
open Set Filter
open scoped Topology

/-- On a compact domain, strict positivity on the zero set persists on a small
sublevel set of a nonnegative continuous function. -/
theorem exists_pos_sublevel_of_pos_on_zero
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f g : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x)
    (hg : ∀ x, f x = 0 → 0 < g x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, f x < δ → 0 < g x := by
  by_cases hb : ({x | g x ≤ 0} : Set X).Nonempty
  · obtain ⟨x₀, hx₀, hmin⟩ := (isClosed_le g.continuous continuous_const).isCompact.exists_isMinOn
      hb f.continuous.continuousOn
    have hp : 0 < f x₀ := lt_of_le_of_ne (hf x₀)
      (fun he => (not_lt_of_ge hx₀) (hg x₀ he.symm))
    exact ⟨f x₀, hp, fun x hx => lt_of_not_ge (fun h => (not_le_of_gt hx) (hmin h))⟩
  · exact ⟨1, zero_lt_one, fun x _ => lt_of_not_ge (fun h => hb ⟨x, h⟩)⟩

/-- Uniform lower bounds for the slopes of affine perturbations, allowing any
number of minimizing points. -/
theorem eventually_forall_le_affine_div
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f g : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) {τ b : ℝ}
    (hg : ∀ x, f x = 0 → τ ≤ g x) (hb : b < τ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ x, b ≤ f x / h + g x := by
  obtain ⟨δ, hδ, hsub⟩ := exists_pos_sublevel_of_pos_on_zero f
    (g - ContinuousMap.const X b) hf (fun x hx => sub_pos.mpr (hb.trans_le (hg x hx)))
  have hM : 0 < ‖g‖ + |b| + 1 := by positivity
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (gt_mem_nhds (div_pos hδ hM))] with h hh hsmall
  intro x
  by_cases hx : f x < δ
  · exact (sub_pos.mp (hsub x hx)).le.trans
      (le_add_of_nonneg_left (div_nonneg (hf x) hh.le))
  · rw [← sub_le_iff_le_add, le_div_iff₀ hh]
    nlinarith [show 0 < h from hh, (lt_div_iff₀ hM).mp hsmall,
      g.neg_norm_le_apply x, le_abs_self b]


/-- A continuous real function on a nonempty compact space attains its infimum. -/
theorem isLeast_sInf_range_continuousMap
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (f : C(X, ℝ)) : IsLeast (range f) (sInf (range f)) :=
  (isCompact_range f.continuous).isLeast_sInf (range_nonempty _)


/-- The right derivative of a compact minimum is the smallest derivative among
its minimizers. No uniqueness of the minimizing point is assumed. -/
theorem hasDerivWithinAt_sInf_range_of_minimizer
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    {f : ℝ → C(X, ℝ)} {g : C(X, ℝ)} {t₀ : ℝ}
    (hf : HasDerivWithinAt f g (Ici t₀) t₀) (x₀ : X)
    (hmin : ∀ x, f t₀ x₀ ≤ f t₀ x)
    (hgmin : ∀ x, f t₀ x = f t₀ x₀ → g x₀ ≤ g x) :
    HasDerivWithinAt (fun t => sInf (range (f t))) (g x₀) (Ici t₀) t₀ := by
  have hm : sInf (range (f t₀)) = f t₀ x₀ :=
    (show IsLeast (range (f t₀)) (f t₀ x₀) from
      ⟨mem_range_self x₀, fun _ ⟨x, hx⟩ => hx ▸ hmin x⟩).csInf_eq
  have hs : Tendsto (slope f t₀) (𝓝[>] t₀) (𝓝 g) :=
    (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp hf.Ioi_of_Ici
  have herr : Tendsto (fun t => ‖slope f t₀ t - g‖) (𝓝[>] t₀) (𝓝 0) := by
    simpa using (hs.sub_const g).norm
  have hshift : Tendsto (fun t : ℝ => t - t₀) (𝓝[>] t₀) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨sub_self t₀ ▸ (tendsto_id.mono_left nhdsWithin_le_nhds).sub_const t₀,
        (show ∀ᶠ t : ℝ in 𝓝[>] t₀, t₀ < t from self_mem_nhdsWithin).mono
          (fun _ ht => sub_pos.mpr ht)⟩
  have heval (t : ℝ) (x : X) :
      slope f t₀ t x = (f t x - f t₀ x) / (t - t₀) := by
    simp [slope_def_module, div_eq_mul_inv, mul_comm]
  apply HasDerivWithinAt.Ici_of_Ioi
  refine (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mpr (tendsto_order.mpr ⟨?_, ?_⟩)
  · intro b hb
    obtain ⟨c, hbc, hc⟩ := exists_between hb
    have ha := hshift.eventually (eventually_forall_le_affine_div
      (f t₀ - ContinuousMap.const X (f t₀ x₀)) g
      (fun x => sub_nonneg.mpr (hmin x))
      (fun x hx => hgmin x (sub_eq_zero.mp hx)) hc)
    filter_upwards [ha, herr.eventually (gt_mem_nhds (sub_pos.mpr hbc))]
      with t ht he
    obtain ⟨x, hx⟩ := (isLeast_sInf_range_continuousMap (f t)).1
    have herrx : -(c - b) < slope f t₀ t x - g x :=
      (neg_lt_neg he).trans_le ((slope f t₀ t - g).neg_norm_le_apply x)
    rw [slope_def_field, hm, ← hx]
    have halgebra : (f t x - f t₀ x₀) / (t - t₀) =
        (f t₀ x - f t₀ x₀) / (t - t₀) + slope f t₀ t x := by
      rw [heval, ← add_div, add_comm (f t₀ x - f t₀ x₀), sub_add_sub_cancel]
    linarith [show c ≤ (f t₀ x - f t₀ x₀) / (t - t₀) + g x from ht x]
  · intro b hb
    have hev : Tendsto (fun t => slope f t₀ t x₀) (𝓝[>] t₀) (𝓝 (g x₀)) :=
      ((ContinuousMap.evalCLM ℝ x₀).continuous.tendsto g).comp hs
    filter_upwards [hev.eventually (gt_mem_nhds hb), self_mem_nhdsWithin] with t ht hpos
    rw [slope_def_field, hm]
    exact (div_le_div_of_nonneg_right
      (sub_le_sub_right ((isLeast_sInf_range_continuousMap (f t)).2 (mem_range_self x₀)) _)
      (sub_nonneg.mpr hpos.le)).trans_lt ((heval t x₀) ▸ ht)

/-- There is a minimizer whose derivative is minimal among all minimizers. -/
theorem exists_minimizer_minimizing
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (f g : C(X, ℝ)) :
    ∃ x₀, (∀ x, f x₀ ≤ f x) ∧ (∀ x, f x = f x₀ → g x₀ ≤ g x) := by
  obtain ⟨x, hx⟩ := (isLeast_sInf_range_continuousMap f).1
  obtain ⟨y, hy, hgy⟩ := (isClosed_eq f.continuous continuous_const).isCompact.exists_isMinOn
    (show ({z | f z = sInf (range f)} : Set X).Nonempty from ⟨x, hx⟩)
    g.continuous.continuousOn
  exact ⟨y, fun z => (show f y = sInf (range f) from hy) ▸
    (isLeast_sInf_range_continuousMap f).2 (mem_range_self z),
    fun z hz => hgy (hz.trans hy)⟩

/-- Right differentiation of a compact minimum, with an attained minimum rate. -/
theorem exists_hasDerivWithinAt_sInf_range
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    {f : ℝ → C(X, ℝ)} {g : C(X, ℝ)} {t₀ : ℝ}
    (hf : HasDerivWithinAt f g (Ici t₀) t₀) :
    ∃ x₀, (∀ x, f t₀ x₀ ≤ f t₀ x) ∧
      (∀ x, f t₀ x = f t₀ x₀ → g x₀ ≤ g x) ∧
      HasDerivWithinAt (fun t => sInf (range (f t))) (g x₀) (Ici t₀) t₀ := by
  obtain ⟨x₀, hm, hg⟩ := exists_minimizer_minimizing (f t₀) g
  exact ⟨x₀, hm, hg, hasDerivWithinAt_sInf_range_of_minimizer hf x₀ hm hg⟩

end ClockBarrier.Analysis
