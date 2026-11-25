/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Dynamics.FlowUniqueness
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add

/-! # Terminal trajectories and surjectivity of the flow

Time reversal constructs a trajectory ending at any prescribed point.
Uniqueness identifies it with a trajectory of the given flow.
-/

public section

namespace ClockBarrier.Dynamics

open Set Filter
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {T : ℝ}

/-- A continuous uniformly spatially Lipschitz velocity has a trajectory ending
at any prescribed point. Its ODE holds within the entire closed interval. -/
theorem exists_trajectory_terminal_Icc (hT : 0 ≤ T) {u : ℝ → E → E} {K : ℝ≥0}
    (hu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set E)))
    (hLip : ∀ t ∈ Icc 0 T, LipschitzWith K (u t)) (y : E) :
    ∃ γ : ℝ → E, ContinuousOn γ (Icc 0 T) ∧ γ T = y ∧
      ∀ s ∈ Icc 0 T, HasDerivWithinAt γ (u s (γ s)) (Icc 0 T) s := by
  let v : ℝ → E → E := fun s x => -u (T - s) x
  have hm : MapsTo (fun s : ℝ => T - s) (Icc 0 T) (Icc 0 T) :=
    fun s hs => ⟨sub_nonneg.mpr hs.2, sub_le_self T hs.1⟩
  have hv : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ (univ : Set E)) :=
    (hu.comp ((continuousOn_const.sub continuousOn_fst).prodMk continuousOn_snd)
      (fun q hq => ⟨hm hq.1, mem_univ _⟩)).neg
  obtain ⟨Ψ, hi, hc, ho⟩ := exists_flow_Icc hT hv (fun s hs => (hLip _ (hm hs)).neg)
  refine ⟨fun s => Ψ (T - s) y,
    (hc y).comp (continuousOn_const.sub continuousOn_id) hm,
    by simpa only [sub_self] using hi y, fun s hs => ?_⟩
  have hd := (hasDerivWithinAt_trajectory_Icc hT hv (hc y) (ho y) (hm hs)).scomp s
    ((hasDerivAt_id s).const_sub T).hasDerivWithinAt hm
  simpa only [v, Function.comp_def, sub_sub_cancel, neg_smul, one_smul, neg_neg] using hd

/-- Every terminal point belongs to the image of an initialized flow under a
continuous uniformly spatially Lipschitz velocity. -/
theorem surjective_flow_of_velocity (hT : 0 ≤ T) {u Φ : ℝ → E → E} {K : ℝ≥0}
    (hu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set E)))
    (hLip : ∀ t ∈ Icc 0 T, LipschitzWith K (u t))
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Icc 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x) : Function.Surjective (Φ T) := by
  intro y
  obtain ⟨γ, hc, hterminal, hd⟩ := exists_trajectory_terminal_Icc hT hu hLip y
  have hright (s : ℝ) (hs : s ∈ Ico 0 T) :
      HasDerivWithinAt γ (u s (γ s)) (Ici s) s := by
    apply (hd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hs.2)] with r hr hrT
    exact ⟨hs.1.trans hr, hrT.le⟩
  refine ⟨γ 0, ?_⟩
  exact (ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ)
    (fun s hs => (hLip s (Ico_subset_Icc_self hs)).lipschitzOnWith)
    (hcont (γ 0)) (hode (γ 0)) (fun _ _ => mem_univ _)
    hc hright (fun _ _ => mem_univ _) (hinit (γ 0)) ⟨hT, le_rfl⟩).trans hterminal

/-- Bounds on each earlier compact interval imply surjectivity throughout the
half-open lifespan. No bound or regularity at the terminal time is assumed. -/
theorem surjective_flow_Ico_of_fderiv_bound {u Φ : ℝ → E → E}
    (hu : ContinuousOn (Function.uncurry u) (Ico 0 T ×ˢ (univ : Set E)))
    (hdiff : ∀ t ∈ Ico 0 T, Differentiable ℝ (u t))
    (hbound : ∀ b ∈ Ico 0 T, ∃ K : ℝ≥0,
      ∀ t ∈ Ico 0 b, ∀ x, ‖fderiv ℝ (u t) x‖₊ ≤ K)
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x) {t : ℝ} (ht : t ∈ Ico 0 T) :
    Function.Surjective (Φ t) := by
  obtain ⟨b, htb, hbT⟩ := exists_between ht.2
  obtain ⟨K, hK⟩ := hbound b ⟨ht.1.trans htb.le, hbT⟩
  have hsub : Icc 0 t ⊆ Ico 0 T := fun _ hs => ⟨hs.1, hs.2.trans_lt ht.2⟩
  exact surjective_flow_of_velocity ht.1 (hu.mono (prod_mono hsub subset_rfl))
    (fun s hs => lipschitzWith_of_nnnorm_fderiv_le (hdiff s (hsub hs))
      (hK s ⟨hs.1, hs.2.trans_lt htb⟩))
    (fun x => (hcont x).mono hsub)
    (fun x s hs => hode x s (hsub (Ico_subset_Icc_self hs))) hinit

end ClockBarrier.Dynamics
