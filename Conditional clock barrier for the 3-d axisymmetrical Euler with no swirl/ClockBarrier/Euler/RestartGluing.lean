/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.OverlapUniqueness
import ClockBarrier.Analysis.IntervalOverlap
import Mathlib.Tactic.Linarith

/-! # Gluing a classical solution to an overlapping restart -/
public section
namespace ClockBarrier.Euler
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- A restart reaching past the old endpoint gives a classical extension.
Only pressure gradients are matched; no terminal data or pressure gauge is assumed. -/
theorem classical_euler_on.glue_restart
    {α : ℝ≥0} {T a τ : ℝ} {u v : ℝ → E₃ →ᵇ E₃} {p q : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (hv : classical_euler_on α τ v q)
    (ha : a ∈ Ico 0 T) (hreach : T < a + τ) (hi : v 0 = u a) :
    ∃ w : ℝ → E₃ →ᵇ E₃, ∃ r : ℝ → E₃ → ℝ,
      classical_euler_on α (a + τ) w r ∧ ∀ t ∈ Ico 0 T, w t = u t := by
  have hm : MapsTo (fun t => t - a) (Ioo a (a + τ)) (Ico 0 τ) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have ho (t : ℝ) (ht : t ∈ Ioo a T) : t - a ∈ Ico 0 τ :=
    hm ⟨ht.1, ht.2.trans hreach⟩
  have heq : EqOn u (fun t => v (t - a)) (Ioo a T) := by
    intro t ht
    exact h.restart_eq hv ha hi ⟨ht.1.le, by simpa [min_eq_left hreach.le] using ht.2⟩
  have hgeq (t : ℝ) (ht : t ∈ Ioo a T) :
      gradient (p t) = gradient (q (t - a)) := by
    funext x
    exact h.restart_gradient_eq hv ha hi
      ⟨ht.1, by simpa [min_eq_left hreach.le] using ht.2⟩ x
  rcases h with ⟨hT, hα, hα1, hu, ⟨D, hD, hd, hH⟩, hL, hLt, hp, hg, he, hz⟩
  rcases hv with ⟨hτ, _, _, hv, ⟨E, hE, hed, hEH⟩, hvL, hvLt, hq, hqg, hve, hvz⟩
  have hdeq : EqOn D (fun t => E (t - a)) (Ioo a T) := by
    intro t ht
    apply BoundedContinuousFunction.ext
    intro x
    have hd₁ := hd t ⟨ha.1.trans ht.1.le, ht.2⟩ x
    rw [heq ht] at hd₁
    exact hd₁.unique (hed _ (ho t ht) x)
  let w (t : ℝ) := if t < T then u t else v (t - a)
  let r (t : ℝ) := if t < T then p t else q (t - a)
  let F (t : ℝ) := if t < T then D t else E (t - a)
  refine ⟨w, r, ?_, fun t ht => if_pos ht.2⟩
  refine ⟨hT.trans hreach, hα, hα1, ?hu, ⟨F, ?hD, ?hd, ?hH⟩,
    ?hL, ?hLt, ?hp, ?hg, ?he, ?hz⟩
  case he =>
    intro t ht x
    by_cases hcut : t < T
    · have hder := (he t ⟨ht.1, hcut⟩ x).mono_of_mem_nhdsWithin
        (Analysis.Ico_mem_nhdsWithin_Ico (S := a + τ) hcut)
      have hevent : (fun s => w s x) =ᶠ[𝓝[Ico 0 (a + τ)] t] (fun s => u s x) := by
        filter_upwards [(Analysis.eventuallyEq_patch_left u (fun s => v (s - a)) hcut).filter_mono nhdsWithin_le_nhds] with s hs
        exact congrArg (fun f : E₃ →ᵇ E₃ => f x) hs
      simpa only [w, r, if_pos hcut] using
        hder.congr_of_eventuallyEq_of_mem hevent ht
    · have hat : a < t := ha.2.trans_le (le_of_not_gt hcut)
      have hnt : t - a ∈ Ioo 0 τ := ⟨sub_pos.mpr hat, by linarith [ht.2]⟩
      have hder := ((hve _ ⟨hnt.1.le, hnt.2⟩ x).hasDerivAt
        (Ico_mem_nhds hnt.1 hnt.2)).scomp t ((hasDerivAt_id t).sub_const a)
      have hevent : (fun s => w s x) =ᶠ[𝓝 t] (fun s => v (s - a) x) := by
        filter_upwards [Analysis.eventuallyEq_patch_right heq hat] with s hs
        exact congrArg (fun f : E₃ →ᵇ E₃ => f x) hs
      simpa only [w, r, if_neg hcut, one_smul] using
        (hder.congr_of_eventuallyEq hevent).hasDerivWithinAt (s := Ico 0 (a + τ))
  case hLt =>
    intro t ht
    by_cases hcut : t < T
    · have hlim := (hLt t ⟨ht.1, hcut⟩).mono_left
        (nhdsWithin_le_of_mem (Analysis.Ico_mem_nhdsWithin_Ico (S := a + τ) hcut))
      apply hlim.congr'
      filter_upwards [(Analysis.eventuallyEq_patch_left u (fun s => v (s - a)) hcut).filter_mono
        nhdsWithin_le_nhds] with s hs
      simp only [w, if_pos hcut] at hs ⊢
      rw [hs]
    · have hat : a < t := ha.2.trans_le (le_of_not_gt hcut)
      have hnt : t - a ∈ Ioo 0 τ := ⟨sub_pos.mpr hat, by linarith [ht.2]⟩
      have hlim := hvLt (t - a) ⟨hnt.1.le, hnt.2⟩
      rw [nhdsWithin_eq_nhds.mpr (Ico_mem_nhds hnt.1 hnt.2)] at hlim
      have hc := hlim.comp (continuous_id.sub continuous_const).continuousAt
      apply (hc.mono_left nhdsWithin_le_nhds).congr'
      filter_upwards [(Analysis.eventuallyEq_patch_right heq hat).filter_mono
        nhdsWithin_le_nhds] with s hs
      change eLpNorm (fun x => v (s - a) x - v (t - a) x) 2 volume =
        eLpNorm (fun x => w s x - w t x) 2 volume
      rw [show w s = v (s - a) from hs, show w t = v (t - a) from if_neg hcut]
  case hH =>
    intro b hb
    let c : ℝ := (a + T) / 2
    have hac : a < c := by dsimp [c]; linarith [ha.2]
    have hcT : c < T := by dsimp [c]; linarith [ha.2]
    obtain ⟨H₁, h₁⟩ := hH c ⟨ha.1.trans hac.le, hcT⟩
    have hbτ : max 0 (b - a) ∈ Ico 0 τ :=
      ⟨le_max_left _ _, max_lt hτ (by linarith [hb.2])⟩
    obtain ⟨H₂, h₂⟩ := hEH _ hbτ
    refine ⟨max H₁ H₂, fun t ht => ?_⟩
    by_cases htc : t ≤ c
    · have htT : t < T := htc.trans_lt hcT
      simpa only [F, if_pos htT] using (h₁ t ⟨ht.1, htc⟩).mono (le_max_left H₁ H₂)
    · have hat : a < t := hac.trans (lt_of_not_ge htc)
      have hFt : F t = E (t - a) := Analysis.patch_eq_right hdeq hat
      rw [hFt]
      apply (h₂ (t - a) ?_).mono (le_max_right H₁ H₂)
      exact ⟨(sub_pos.mpr hat).le, (sub_le_sub_right ht.2 a).trans (le_max_right _ _)⟩
  case hu =>
    exact Analysis.continuousOn_patch ha.2 hu
      (hv.comp (continuous_id.sub continuous_const).continuousOn hm) heq
  case hD =>
    exact Analysis.continuousOn_patch ha.2 hD
      (hE.comp (continuous_id.sub continuous_const).continuousOn hm) hdeq
  case hg =>
    have hc := Analysis.continuousOn_patch_prod ha.2 hg
      (hqg.comp ((continuous_fst.sub continuous_const).prodMk continuous_snd).continuousOn
        (fun z hz => ⟨hm hz.1, mem_univ _⟩)) hgeq
    convert hc using 1
    funext z
    dsimp only [r]
    split_ifs <;> rfl
  case hd =>
    intro t ht x
    by_cases hc : t < T
    · simpa only [w, F, if_pos hc] using hd t ⟨ht.1, hc⟩ x
    · simpa only [w, F, if_neg hc] using
        hed (t - a) (hm ⟨ha.2.trans_le (le_of_not_gt hc), ht.2⟩) x
  case hL =>
    intro t ht
    by_cases hc : t < T
    · simpa only [w, if_pos hc] using hL t ⟨ht.1, hc⟩
    · simpa only [w, if_neg hc] using
        hvL (t - a) (hm ⟨ha.2.trans_le (le_of_not_gt hc), ht.2⟩)
  case hp =>
    intro t ht
    by_cases hc : t < T
    · simpa only [r, if_pos hc] using hp t ⟨ht.1, hc⟩
    · simpa only [r, if_neg hc] using
        hq (t - a) (hm ⟨ha.2.trans_le (le_of_not_gt hc), ht.2⟩)
  case hz =>
    intro t ht x
    by_cases hc : t < T
    · simpa only [w, if_pos hc] using hz t ⟨ht.1, hc⟩ x
    · simpa only [w, if_neg hc] using
        hvz (t - a) (hm ⟨ha.2.trans_le (le_of_not_gt hc), ht.2⟩) x

end ClockBarrier.Euler
