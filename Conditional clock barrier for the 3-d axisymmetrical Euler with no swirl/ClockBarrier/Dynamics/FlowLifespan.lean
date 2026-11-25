/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Dynamics.FlowExistence
public import ClockBarrier.Dynamics.FlowRegularity

/-!
# Compatible trajectories before a terminal time

Uniqueness identifies the compact-interval constructions. Their common restriction
gives a flow throughout `[0,T)`, without any assumptions at the terminal time.
The existential functions are specified only on their stated time domains.
-/

public section

namespace ClockBarrier.Dynamics

open Set
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {T : ℝ}

/-- A solution family can be assembled on `[0,T)` from compact-interval trajectories. -/
theorem exists_flow_Ico (hT : 0 < T) {u : ℝ → E → E}
    (hu : ContinuousOn (Function.uncurry u) (Ico 0 T ×ˢ (univ : Set E)))
    (hLip : ∀ b ∈ Ico 0 T, ∃ K : ℝ≥0, ∀ t ∈ Icc 0 b, LipschitzWith K (u t)) :
    ∃ Φ : ℝ → E → E, (∀ x, Φ 0 x = x) ∧
      (∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T)) ∧
      ∀ x, ∀ t ∈ Ico 0 T,
        HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t := by
  have hex (b : Ico 0 T) : ∃ Φ : ℝ → E → E, (∀ x, Φ 0 x = x) ∧
      (∀ x, ContinuousOn (fun t => Φ t x) (Icc 0 b.1)) ∧
      ∀ x, ∀ t ∈ Ico 0 b.1,
        HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t := by
    obtain ⟨K, hK⟩ := hLip b.1 b.2
    exact exists_flow_Icc b.2.1
      (hu.mono (prod_mono (fun _ ht => ⟨ht.1, ht.2.trans_lt b.2.2⟩) subset_rfl)) hK
  choose F hinit hcont hode using hex
  have hcompat (b c : Ico 0 T) {t : ℝ} (ht : 0 ≤ t) (htb : t ≤ b.1) (htc : t ≤ c.1) :
      F b t = F c t := by
    obtain ⟨K, hK⟩ := hLip b.1 b.2
    exact funext fun x => ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ)
      (fun s hs => (hK s ⟨hs.1, hs.2.le.trans htb⟩).lipschitzOnWith)
      ((hcont b x).mono (Icc_subset_Icc le_rfl htb))
      (fun s hs => hode b x s ⟨hs.1, hs.2.trans_le htb⟩) (fun _ _ => mem_univ _)
      ((hcont c x).mono (Icc_subset_Icc le_rfl htc))
      (fun s hs => hode c x s ⟨hs.1, hs.2.trans_le htc⟩) (fun _ _ => mem_univ _)
      (by simp only [hinit]) ⟨ht, le_rfl⟩
  have hvalues (t : ℝ) : ∃ v : E → E, ∀ b : Ico 0 T, t ∈ Icc 0 b.1 → v = F b t := by
    classical
    by_cases hs : ∃ b : Ico 0 T, t ∈ Icc 0 b.1
    · obtain ⟨b, hb⟩ := hs
      exact ⟨F b t, fun c hc => hcompat b c hb.1 hb.2 hc.2⟩
    · exact ⟨id, fun b hb => False.elim (hs ⟨b, hb⟩)⟩
  choose Φ hΦ using hvalues
  have hc (b : Ico 0 T) (x : E) : ContinuousOn (fun t => Φ t x) (Icc 0 b.1) :=
    (hcont b x).congr (fun t ht => congrFun (hΦ t b ht) x)
  refine ⟨Φ, fun x => (congrFun (hΦ 0 ⟨0, ⟨le_rfl, hT⟩⟩ ⟨le_rfl, le_rfl⟩) x).trans
    (hinit _ x), ?_, ?_⟩
  · intro x t ht
    obtain ⟨b, htb, hbT⟩ := exists_between ht.2
    apply (hc ⟨b, ⟨ht.1.trans htb.le, hbT⟩⟩ x t ⟨ht.1, htb.le⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds htb)] with s hs hsb
    exact ⟨hs.1, hsb.le⟩
  · intro x t ht
    obtain ⟨b, htb, hbT⟩ := exists_between ht.2
    let B : Ico 0 T := ⟨b, ⟨ht.1.trans htb.le, hbT⟩⟩
    have he : (fun s => Φ s x) =ᶠ[𝓝[≥] t] (fun s => F B s x) := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds htb)] with s hs hsb
      exact congrFun (hΦ s B ⟨ht.1.trans hs, hsb.le⟩) x
    simpa only [hΦ t B ⟨ht.1, htb.le⟩] using
      (hode B x t ⟨ht.1, htb⟩).congr_of_eventuallyEq_of_mem he (le_refl t)

/-- Construct the flow and supply every trajectory premise of the spatial regularity theorem. -/
theorem exists_regular_flow_Ico [FiniteDimensional ℝ E] (hT : 0 < T) {u : ℝ → E → E}
    (hu : ContinuousOn (Function.uncurry u) (Ico 0 T ×ˢ (univ : Set E)))
    (hdiff : ∀ t ∈ Ico 0 T, Differentiable ℝ (u t))
    (hD : ContinuousOn (fun p : ℝ × E => fderiv ℝ (u p.1) p.2)
      (Ico 0 T ×ˢ (univ : Set E)))
    (hbound : ∀ b ∈ Ico 0 T, ∃ K : ℝ≥0,
      ∀ t ∈ Ico 0 b, ∀ x, ‖fderiv ℝ (u t) x‖₊ ≤ K) :
    ∃ Φ : ℝ → E → E, (∀ x, Φ 0 x = x) ∧
      (∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T)) ∧
      (∀ x, ∀ t ∈ Ico 0 T,
        HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t) ∧
      ∀ t ∈ Ico 0 T, ContDiff ℝ 1 (Φ t) ∧ ∀ x,
        HasDerivWithinAt (fun s => fderiv ℝ (Φ s) x)
          ((fderiv ℝ (u t) (Φ t x)).comp (fderiv ℝ (Φ t) x)) (Ici t) t := by
  have hLip : ∀ b ∈ Ico 0 T, ∃ K : ℝ≥0, ∀ t ∈ Icc 0 b, LipschitzWith K (u t) := by
    intro b hb
    obtain ⟨c, hbc, hcT⟩ := exists_between hb.2
    obtain ⟨K, hK⟩ := hbound c ⟨hb.1.trans hbc.le, hcT⟩
    exact ⟨K, fun t ht => lipschitzWith_of_nnnorm_fderiv_le
      (hdiff t ⟨ht.1, ht.2.trans_lt hb.2⟩) (hK t ⟨ht.1, ht.2.trans_lt hbc⟩)⟩
  obtain ⟨Φ, hinit, hcont, hode⟩ := exists_flow_Ico hT hu hLip
  exact ⟨Φ, hinit, hcont, hode, flow_spatial_regularity_Ico hu hdiff hD hbound hcont hode hinit⟩

end ClockBarrier.Dynamics
