/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Dynamics.VariationalEquation

/-!
# Spatial regularity and endpoint forms of the variational equation

These results concern the actual Fréchet derivative of existing ODE trajectories.
The hypotheses describe the velocity and the trajectory equation, rather than
assuming spatial differentiability or the variational equation of the flow.
-/

public section

namespace ClockBarrier.Dynamics

open ClockBarrier.Analysis Set
open scoped Topology NNReal

section ClosedInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {T : ℝ} (hT : 0 ≤ T) {u Φ : ℝ → E → E} {K : ℝ≥0}
  (hu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set E)))
  (hdiff : ∀ τ ∈ Icc 0 T, Differentiable ℝ (u τ))
  (hD : ContinuousOn (fun p : ℝ × E => fderiv ℝ (u p.1) p.2)
    (Icc 0 T ×ˢ (univ : Set E)))
  (hbound : ∀ τ ∈ Ico 0 T, ∀ x, ‖fderiv ℝ (u τ) x‖₊ ≤ K)
  (hcont : ∀ x, ContinuousOn (fun τ => Φ τ x) (Icc 0 T))
  (hode : ∀ x, ∀ τ ∈ Ico 0 T,
    HasDerivWithinAt (fun τ => Φ τ x) (u τ (Φ τ x)) (Ici τ) τ)
  (hinit : ∀ x, Φ 0 x = x)

include hT hu hdiff hD hbound hcont hode hinit

/-- Each fixed-time flow map is continuously differentiable in its initial position. -/
theorem contDiff_flow {t : ℝ} (ht : t ∈ Icc 0 T) : ContDiff ℝ 1 (Φ t) := by
  exact (ContinuousMap.evalCLM ℝ (M := E) ⟨t, ht⟩).contDiff.comp
    (contDiff_flow_paths hT hu hdiff hD hbound hcont hode hinit)

/-- The spatial derivative is jointly continuous in time and initial position. -/
theorem continuous_fderiv_flow [FiniteDimensional ℝ E] :
    Continuous (fun p : Icc 0 T × E => fderiv ℝ (Φ p.1.1) p.2) := by
  let F : E → C(Icc 0 T, E) := fun x => ⟨fun s => Φ s.1 x, (hcont x).restrict⟩
  have hF : ContDiff ℝ 1 F := contDiff_flow_paths hT hu hdiff hD hbound hcont hode hinit
  have hJ : Continuous (fun x => linearMapPath (fderiv ℝ F x)) :=
    (linearMapPathL (S := Icc 0 T) (E := E) (F := E)).continuous.comp
      (hF.continuous_fderiv (by decide))
  have hjoint : Continuous (fun p : Icc 0 T × E => linearMapPath (fderiv ℝ F p.2) p.1) :=
    continuous_eval.comp ((hJ.comp continuous_snd).prodMk continuous_fst)
  apply hjoint.congr
  intro p
  exact ((ContinuousMap.evalCLM ℝ (M := E) p.1).hasFDerivAt.comp p.2
    (hF.differentiable (by decide) p.2).hasFDerivAt).fderiv.symm

/-- In the interior, the variational equation is an ordinary time derivative. -/
theorem hasDerivAt_fderiv_flow [FiniteDimensional ℝ E] (x : E) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => fderiv ℝ (Φ s) x)
      ((fderiv ℝ (u t) (Φ t x)).comp (fderiv ℝ (Φ t) x)) t := by
  exact (hasDerivWithinAt_fderiv_flow hT hu hdiff hD hbound hcont hode hinit x
    (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- The variational equation also holds as a right derivative, including at the initial time. -/
theorem hasDerivWithinAt_fderiv_flow_right [FiniteDimensional ℝ E]
    (x : E) {t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (fun s => fderiv ℝ (Φ s) x)
      ((fderiv ℝ (u t) (Φ t x)).comp (fderiv ℝ (Φ t) x)) (Ici t) t := by
  have h := hasDerivWithinAt_fderiv_flow hT hu hdiff hD hbound hcont hode hinit x
    (Ico_subset_Icc_self ht)
  apply h.mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds ht.2)] with s hs hsT
  exact ⟨ht.1.trans hs, hsT.le⟩

omit hT hu hdiff hD hbound hcont hode [CompleteSpace E] in
/-- The spatial derivative initially equals the identity operator. -/
theorem fderiv_flow_zero (x : E) : fderiv ℝ (Φ 0) x = ContinuousLinearMap.id ℝ E := by
  have h : Φ 0 = id := funext hinit
  rw [h, fderiv_id]

end ClosedInterval

/-- Spatial `C¹` dependence and the variational equation hold throughout `[0,T)`
using derivative bounds on each earlier interval. No bound or continuity at `T` is assumed. -/
theorem flow_spatial_regularity_Ico
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {u Φ : ℝ → E → E} {T : ℝ}
    (hu : ContinuousOn (Function.uncurry u) (Ico 0 T ×ˢ (univ : Set E)))
    (hdiff : ∀ τ ∈ Ico 0 T, Differentiable ℝ (u τ))
    (hD : ContinuousOn (fun p : ℝ × E => fderiv ℝ (u p.1) p.2)
      (Ico 0 T ×ˢ (univ : Set E)))
    (hbound : ∀ b ∈ Ico 0 T, ∃ K : ℝ≥0,
      ∀ τ ∈ Ico 0 b, ∀ x, ‖fderiv ℝ (u τ) x‖₊ ≤ K)
    (hcont : ∀ x, ContinuousOn (fun τ => Φ τ x) (Ico 0 T))
    (hode : ∀ x, ∀ τ ∈ Ico 0 T,
      HasDerivWithinAt (fun τ => Φ τ x) (u τ (Φ τ x)) (Ici τ) τ)
    (hinit : ∀ x, Φ 0 x = x) :
    ∀ t ∈ Ico 0 T, ContDiff ℝ 1 (Φ t) ∧ ∀ x,
      HasDerivWithinAt (fun s => fderiv ℝ (Φ s) x)
        ((fderiv ℝ (u t) (Φ t x)).comp (fderiv ℝ (Φ t) x)) (Ici t) t := by
  intro t ht
  obtain ⟨b, htb, hbT⟩ := exists_between ht.2
  have hb0 : 0 ≤ b := ht.1.trans htb.le
  obtain ⟨K, hK⟩ := hbound b ⟨hb0, hbT⟩
  have hsub : Icc 0 b ⊆ Ico 0 T := fun _ hs => ⟨hs.1, hs.2.trans_lt hbT⟩
  constructor
  · exact contDiff_flow hb0 (hu.mono (prod_mono hsub subset_rfl))
      (fun s hs => hdiff s (hsub hs)) (hD.mono (prod_mono hsub subset_rfl)) hK
      (fun x => (hcont x).mono hsub)
      (fun x s hs => hode x s (hsub (Ico_subset_Icc_self hs))) hinit ⟨ht.1, htb.le⟩
  · intro x
    exact hasDerivWithinAt_fderiv_flow_right hb0 (hu.mono (prod_mono hsub subset_rfl))
      (fun s hs => hdiff s (hsub hs)) (hD.mono (prod_mono hsub subset_rfl)) hK
      (fun x => (hcont x).mono hsub)
      (fun x s hs => hode x s (hsub (Ico_subset_Icc_self hs))) hinit x ⟨ht.1, htb⟩

end ClockBarrier.Dynamics
