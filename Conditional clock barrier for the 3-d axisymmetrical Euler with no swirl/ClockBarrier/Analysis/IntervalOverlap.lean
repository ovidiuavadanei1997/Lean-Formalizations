/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.ContinuousOn

/-! # Local identities for patching functions on overlapping time intervals -/
public section
namespace ClockBarrier.Analysis
open Set Filter
open scoped Topology

/-- Before the cut, the patched path locally equals its first branch. -/
theorem eventuallyEq_patch_left {X : Type*} (f g : ℝ → X) {T t : ℝ} (ht : t < T) :
    (fun s => if s < T then f s else g s) =ᶠ[𝓝 t] f := by
  filter_upwards [Iio_mem_nhds ht] with s hs
  exact if_pos hs

/-- Agreement on the open overlap makes the patch equal to its second branch. -/
theorem patch_eq_right {X : Type*} {f g : ℝ → X} {a T t : ℝ}
    (heq : EqOn f g (Ioo a T)) (ht : a < t) :
    (if t < T then f t else g t) = g t := by
  split_ifs with h
  · exact heq ⟨ht, h⟩
  · rfl

/-- The patched path locally equals its second branch everywhere after the
left endpoint of the overlap, including the cut itself. -/
theorem eventuallyEq_patch_right {X : Type*} {f g : ℝ → X} {a T t : ℝ}
    (heq : EqOn f g (Ioo a T)) (ht : a < t) :
    (fun s => if s < T then f s else g s) =ᶠ[𝓝 t] g := by
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact patch_eq_right heq hs

/-- The old lifespan is a relative neighborhood before its right endpoint. -/
theorem Ico_mem_nhdsWithin_Ico {T S t : ℝ} (ht : t < T) :
    Ico 0 T ∈ 𝓝[Ico 0 S] t := by
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht)] with s hs hT
  exact ⟨hs.1, hT⟩

/-- Continuous paths glue through an open overlap without an endpoint limit. -/
theorem continuousOn_patch {X : Type*} [TopologicalSpace X]
    {f g : ℝ → X} {a T S : ℝ} (haT : a < T)
    (hf : ContinuousOn f (Ico 0 T)) (hg : ContinuousOn g (Ioo a S))
    (heq : EqOn f g (Ioo a T)) :
    ContinuousOn (fun s => if s < T then f s else g s) (Ico 0 S) := by
  intro t ht
  by_cases hT : t < T
  · exact ((hf t ⟨ht.1, hT⟩).mono_of_mem_nhdsWithin
      (Ico_mem_nhdsWithin_Ico hT)).congr_of_eventuallyEq_of_mem
        ((eventuallyEq_patch_left f g hT).filter_mono nhdsWithin_le_nhds) ht
  · have hat : a < t := haT.trans_le (le_of_not_gt hT)
    exact ((hg t ⟨hat, ht.2⟩).continuousAt
      (Ioo_mem_nhds hat ht.2)).continuousWithinAt.congr_of_eventuallyEq_of_mem
        ((eventuallyEq_patch_right heq hat).filter_mono nhdsWithin_le_nhds) ht

/-- Joint continuity also patches when the cut concerns only time. -/
theorem continuousOn_patch_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : ℝ → X → Y} {a T S : ℝ} (haT : a < T)
    (hf : ContinuousOn (fun q : ℝ × X => f q.1 q.2) (Ico 0 T ×ˢ univ))
    (hg : ContinuousOn (fun q : ℝ × X => g q.1 q.2) (Ioo a S ×ˢ univ))
    (heq : ∀ t ∈ Ioo a T, f t = g t) :
    ContinuousOn (fun q : ℝ × X => if q.1 < T then f q.1 q.2 else g q.1 q.2)
      (Ico 0 S ×ˢ univ) := by
  intro q hq
  by_cases hT : q.1 < T
  · have hm : Ico 0 T ×ˢ (univ : Set X) ∈ 𝓝[Ico 0 S ×ˢ univ] q := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds
          (continuous_fst.continuousAt.eventually (Iio_mem_nhds hT))] with z hz hzT
      exact ⟨⟨hz.1.1, hzT⟩, mem_univ _⟩
    apply ((hf q ⟨⟨hq.1.1, hT⟩, mem_univ _⟩).mono_of_mem_nhdsWithin hm).congr_of_eventuallyEq_of_mem _ hq
    filter_upwards [mem_nhdsWithin_of_mem_nhds
      (continuous_fst.continuousAt.eventually (Iio_mem_nhds hT))] with z hz
    exact if_pos hz
  · have hat : a < q.1 := haT.trans_le (le_of_not_gt hT)
    have hc := (hg q ⟨⟨hat, hq.1.2⟩, mem_univ _⟩).continuousAt
      (prod_mem_nhds (Ioo_mem_nhds hat hq.1.2) univ_mem)
    apply hc.continuousWithinAt.congr_of_eventuallyEq_of_mem _ hq
    filter_upwards [mem_nhdsWithin_of_mem_nhds
      (continuous_fst.continuousAt.eventually (Ioi_mem_nhds hat))] with z hz
    split_ifs with h
    · exact congrFun (heq z.1 ⟨hz, h⟩) z.2
    · rfl

end ClockBarrier.Analysis
