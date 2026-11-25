/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Dynamics.FlowLifespan

/-!
# Uniqueness and injectivity of trajectories

Continuity of the velocity upgrades the right-sided trajectory equation to
ordinary time differentiability in the interior. Backward uniqueness then
prevents distinct initial labels from meeting.
-/

public section

namespace ClockBarrier.Dynamics

open ClockBarrier.Analysis Set
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {T : ℝ}

/-- A continuous trajectory satisfying the right ODE satisfies the ODE within the
whole closed interval, including its left derivative at the terminal endpoint. -/
theorem hasDerivWithinAt_trajectory_Icc (hT : 0 ≤ T) {u : ℝ → E → E} {γ : ℝ → E}
    (hu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set E)))
    (hcont : ContinuousOn γ (Icc 0 T))
    (hode : ∀ t ∈ Ico 0 T, HasDerivWithinAt γ (u t (γ t)) (Ici t) t)
    {t : ℝ} (ht : t ∈ Icc 0 T) : HasDerivWithinAt γ (u t (γ t)) (Icc 0 T) t := by
  let U : C(Icc 0 T × E, E) :=
    ⟨fun p => u p.1.1 p.2, hu.comp_continuous (continuous_subtype_val.prodMap continuous_id)
      (fun p => ⟨p.1.2, mem_univ _⟩)⟩
  let c : C(Icc 0 T, E) := ⟨fun s => γ s.1, hcont.restrict⟩
  have hfix : Function.IsFixedPt (pathPicard hT U (γ 0)) c := by
    apply ContinuousMap.ext
    intro a
    change γ 0 + ∫ s in 0..a.1,
      u (projIcc 0 T hT s).1 (γ (projIcc 0 T hT s).1) = γ a.1
    rw [eq_add_integral_of_trajectory hu hcont hode a.2]
    congr 1
    exact intervalIntegral.integral_congr fun s hs => by
      rw [projIcc_of_mem hT (uIcc_subset_Icc ⟨le_rfl, hT⟩ a.2 hs)]
  have hd := (trajectory_of_fixedPoint_pathPicard hT U (γ 0) hfix).2 t ht
  exact hd.congr_of_mem (fun s hs => by simp only [projIcc_of_mem hT hs, c, ContinuousMap.coe_mk]) ht

/-- Distinct initial labels cannot meet under a uniformly Lipschitz velocity. -/
theorem injective_flow_of_velocity (hT : 0 ≤ T) {u Φ : ℝ → E → E} {K : ℝ≥0}
    (hu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set E)))
    (hLip : ∀ t ∈ Icc 0 T, LipschitzWith K (u t))
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Icc 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Function.Injective (Φ t) := by
  have hleft (x : E) (r : ℝ) (hr : r ∈ Ioc 0 t) :
      HasDerivWithinAt (fun s => Φ s x) (u r (Φ r x)) (Iic r) r := by
    apply (hasDerivWithinAt_trajectory_Icc hT hu (hcont x) (hode x)
      ⟨hr.1.le, hr.2.trans ht.2⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds hr.1)] with s hs hs0
    exact ⟨hs0.le, hs.trans (hr.2.trans ht.2)⟩
  intro x y hxy
  have heq := ODE_solution_unique_of_mem_Icc_left (s := fun _ => univ)
    (fun r hr => (hLip r ⟨hr.1.le, hr.2.trans ht.2⟩).lipschitzOnWith)
    ((hcont x).mono (Icc_subset_Icc le_rfl ht.2)) (hleft x) (fun _ _ => mem_univ _)
    ((hcont y).mono (Icc_subset_Icc le_rfl ht.2)) (hleft y) (fun _ _ => mem_univ _)
    hxy (show 0 ∈ Icc 0 t from ⟨le_rfl, ht.1⟩)
  simpa only [hinit] using heq

/-- Spatial derivative bounds on compact time intervals imply injectivity throughout `[0,T)`. -/
theorem injective_flow_Ico_of_fderiv_bound {u Φ : ℝ → E → E}
    (hu : ContinuousOn (Function.uncurry u) (Ico 0 T ×ˢ (univ : Set E)))
    (hdiff : ∀ t ∈ Ico 0 T, Differentiable ℝ (u t))
    (hbound : ∀ b ∈ Ico 0 T, ∃ K : ℝ≥0,
      ∀ t ∈ Ico 0 b, ∀ x, ‖fderiv ℝ (u t) x‖₊ ≤ K)
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x) {t : ℝ} (ht : t ∈ Ico 0 T) :
    Function.Injective (Φ t) := by
  obtain ⟨b, htb, hbT⟩ := exists_between ht.2
  obtain ⟨K, hK⟩ := hbound b ⟨ht.1.trans htb.le, hbT⟩
  have hsub : Icc 0 t ⊆ Ico 0 T := fun _ hs => ⟨hs.1, hs.2.trans_lt ht.2⟩
  exact injective_flow_of_velocity ht.1 (hu.mono (prod_mono hsub subset_rfl))
    (fun s hs => lipschitzWith_of_nnnorm_fderiv_le (hdiff s (hsub hs))
      (hK s ⟨hs.1, hs.2.trans_lt htb⟩))
    (fun x => (hcont x).mono hsub)
    (fun x s hs => hode x s (hsub (Ico_subset_Icc_self hs))) hinit ⟨ht.1, le_rfl⟩

omit [CompleteSpace E] in
/-- Two trajectories with the same initial value agree throughout the lifespan. -/
theorem eqOn_trajectories_Ico_of_fderiv_bound {u : ℝ → E → E} {γ δ : ℝ → E}
    (hdiff : ∀ t ∈ Ico 0 T, Differentiable ℝ (u t))
    (hbound : ∀ b ∈ Ico 0 T, ∃ K : ℝ≥0,
      ∀ t ∈ Ico 0 b, ∀ x, ‖fderiv ℝ (u t) x‖₊ ≤ K)
    (hγ : ContinuousOn γ (Ico 0 T))
    (hγ' : ∀ t ∈ Ico 0 T, HasDerivWithinAt γ (u t (γ t)) (Ici t) t)
    (hδ : ContinuousOn δ (Ico 0 T))
    (hδ' : ∀ t ∈ Ico 0 T, HasDerivWithinAt δ (u t (δ t)) (Ici t) t)
    (hinit : γ 0 = δ 0) : EqOn γ δ (Ico 0 T) := by
  intro t ht
  obtain ⟨K, hK⟩ := hbound t ht
  have hsub : Icc 0 t ⊆ Ico 0 T := fun _ hs => ⟨hs.1, hs.2.trans_lt ht.2⟩
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ)
    (fun s hs => (lipschitzWith_of_nnnorm_fderiv_le
      (hdiff s (hsub (Ico_subset_Icc_self hs))) (hK s hs)).lipschitzOnWith)
    (hγ.mono hsub) (fun s hs => hγ' s (hsub (Ico_subset_Icc_self hs))) (fun _ _ => mem_univ _)
    (hδ.mono hsub) (fun s hs => hδ' s (hsub (Ico_subset_Icc_self hs))) (fun _ _ => mem_univ _)
    hinit ⟨ht.1, le_rfl⟩

end ClockBarrier.Dynamics
