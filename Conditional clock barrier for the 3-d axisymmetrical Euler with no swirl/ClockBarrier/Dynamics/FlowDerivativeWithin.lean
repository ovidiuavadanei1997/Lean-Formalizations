/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Dynamics.FlowRegularity

/-! # Spatial derivative continuity and differentiation within the full lifespan -/

public section

namespace ClockBarrier.Dynamics

open Set
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {u Φ : ℝ → E → E} {T : ℝ}
  (hu : ContinuousOn (Function.uncurry u) (Ico 0 T ×ˢ (univ : Set E)))
  (hdiff : ∀ t ∈ Ico 0 T, Differentiable ℝ (u t))
  (hD : ContinuousOn (fun p : ℝ × E => fderiv ℝ (u p.1) p.2) (Ico 0 T ×ˢ univ))
  (hbound : ∀ b ∈ Ico 0 T, ∃ K : ℝ≥0,
    ∀ t ∈ Ico 0 b, ∀ x, ‖fderiv ℝ (u t) x‖₊ ≤ K)
  (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
  (hode : ∀ x, ∀ t ∈ Ico 0 T,
    HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
  (hinit : ∀ x, Φ 0 x = x)

include hu hdiff hD hbound hcont hode hinit

/-- The spatial derivative is continuous on every earlier closed time interval. -/
theorem continuousOn_fderiv_flow_Icc (x : E) {b : ℝ} (hb : b ∈ Ico 0 T) :
    ContinuousOn (fun t => fderiv ℝ (Φ t) x) (Icc 0 b) := by
  obtain ⟨K, hK⟩ := hbound b hb
  have hsub : Icc 0 b ⊆ Ico 0 T := fun _ hs => ⟨hs.1, hs.2.trans_lt hb.2⟩
  exact continuousOn_iff_continuous_restrict.mpr
    ((continuous_fderiv_flow hb.1 (hu.mono (prod_mono hsub subset_rfl))
      (fun s hs => hdiff s (hsub hs)) (hD.mono (prod_mono hsub subset_rfl)) hK
      (fun y => (hcont y).mono hsub)
      (fun y s hs => hode y s (hsub (Ico_subset_Icc_self hs))) hinit).comp
      (continuous_id.prodMk continuous_const))

/-- The variational equation within `[0,T)` gives ordinary interior derivatives and
the initial right derivative in one statement. -/
theorem hasDerivWithinAt_fderiv_flow_Ico (x : E) {t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (fun s => fderiv ℝ (Φ s) x)
      ((fderiv ℝ (u t) (Φ t x)).comp (fderiv ℝ (Φ t) x)) (Ico 0 T) t := by
  obtain ⟨b, htb, hbT⟩ := exists_between ht.2
  obtain ⟨K, hK⟩ := hbound b ⟨ht.1.trans htb.le, hbT⟩
  have hsub : Icc 0 b ⊆ Ico 0 T := fun _ hs => ⟨hs.1, hs.2.trans_lt hbT⟩
  apply (hasDerivWithinAt_fderiv_flow (ht.1.trans htb.le)
    (hu.mono (prod_mono hsub subset_rfl)) (fun s hs => hdiff s (hsub hs))
    (hD.mono (prod_mono hsub subset_rfl)) hK (fun y => (hcont y).mono hsub)
    (fun y s hs => hode y s (hsub (Ico_subset_Icc_self hs))) hinit x
    ⟨ht.1, htb.le⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds htb)]
    with s hs hsb using ⟨hs.1, hsb.le⟩

end ClockBarrier.Dynamics
