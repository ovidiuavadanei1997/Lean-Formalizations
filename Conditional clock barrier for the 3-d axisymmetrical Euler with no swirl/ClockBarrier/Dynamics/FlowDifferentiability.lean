/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.PathIntegral
public import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Spatial differentiability of flows

The Picard equation is differentiated as an equation on continuous paths. Its
linearized Volterra operator is invertible on each compact time interval.
-/

public section

namespace ClockBarrier.Dynamics

open ClockBarrier.Analysis Filter Set
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {T : ℝ}

/-- A continuous family satisfying the Picard integral equation is `C¹` in its
initial value, when the velocity has a jointly continuous spatial derivative. -/
theorem contDiffAt_of_path_integral_eq (hT : 0 ≤ T)
    (u : C(Icc 0 T × E, E)) (D : C(Icc 0 T × E, E →L[ℝ] E))
    (hD : ∀ s x, HasFDerivAt (fun y => u (s, y)) (D (s, x)) x)
    {Φ : E → C(Icc 0 T, E)} {x : E}
    (hcont : ContinuousAt Φ x)
    (hfix : ∀ᶠ y in 𝓝 x,
      Φ y = ContinuousMap.const (Icc 0 T) y + pathIntegral hT (pathSuperposition u (Φ y))) :
    ContDiffAt ℝ 1 Φ x := by
  let H : E × C(Icc 0 T, E) → C(Icc 0 T, E) := fun p =>
    p.2 - ContinuousMap.const (Icc 0 T) p.1 - pathIntegral hT (pathSuperposition u p.2)
  have hH : ContDiff ℝ 1 H :=
    (contDiff_snd.sub ((ContinuousLinearMap.const ℝ (Icc 0 T)).contDiff.comp contDiff_fst)).sub
      ((pathIntegral hT).contDiff.comp ((contDiff_pathSuperposition u D hD).comp contDiff_snd))
  have hH' := (hasFDerivAt_snd (𝕜 := ℝ) (p := (x, Φ x))).sub
    ((ContinuousLinearMap.const ℝ (Icc 0 T)).hasFDerivAt.comp (x, Φ x) hasFDerivAt_fst)
    |>.sub ((pathIntegral hT).hasFDerivAt.comp (x, Φ x)
      ((hasFDerivAt_pathSuperposition u D hD (Φ x)).comp (x, Φ x) hasFDerivAt_snd))
  have hpartial : (fderiv ℝ H (x, Φ x)).comp
      (ContinuousLinearMap.inr ℝ E C(Icc 0 T, E)) =
        ContinuousLinearMap.id ℝ C(Icc 0 T, E) - pathVolterra hT (pathSuperposition D (Φ x)) := by
    rw [show fderiv ℝ H (x, Φ x) = _ from hH'.fderiv]
    ext γ
    simp [ContinuousLinearMap.comp_apply, pathVolterra]
  have hinv : ((fderiv ℝ H (x, Φ x)).comp
      (ContinuousLinearMap.inr ℝ E C(Icc 0 T, E))).IsInvertible :=
    hpartial ▸ isInvertible_id_sub_pathVolterra hT (pathSuperposition D (Φ x))
  have heq := (continuousAt_id.prodMk hcont).eventually
    (hH.contDiffAt.eventually_apply_eq_iff_implicitFunction (by decide) hinv)
  apply (hH.contDiffAt.contDiffAt_implicitFunction (by decide) hinv).congr_of_eventuallyEq
  filter_upwards [heq, hfix] with y hy hfy
  apply (hy.mp ?_).symm
  dsimp only [H, id_eq]
  rw [sub_sub, sub_sub, ← hfy, ← hfix.self_of_nhds, sub_self, sub_self]

omit [CompleteSpace E] in
/-- Trajectory uniqueness estimates control the entire path uniformly in the label. -/
theorem lipschitzWith_flow_paths
    {u Φ : ℝ → E → E} {K : ℝ≥0}
    (hu : ∀ τ ∈ Ico 0 T, LipschitzWith K (u τ))
    (hcont : ∀ x, ContinuousOn (fun τ => Φ τ x) (Icc 0 T))
    (hode : ∀ x, ∀ τ ∈ Ico 0 T,
      HasDerivWithinAt (fun τ => Φ τ x) (u τ (Φ τ x)) (Ici τ) τ)
    (hinit : ∀ x, Φ 0 x = x) :
    LipschitzWith ⟨Real.exp (K * T), (Real.exp_pos _).le⟩
      (fun x => (⟨fun t : Icc 0 T => Φ t.1 x, (hcont x).restrict⟩ : C(Icc 0 T, E))) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro t
  have hg := dist_le_of_trajectories_ODE_of_mem (s := fun _ => univ)
    (fun τ hτ => (hu τ hτ).lipschitzOnWith)
    (hcont x) (hode x) (fun _ _ => mem_univ _)
    (hcont y) (hode y) (fun _ _ => mem_univ _)
    (show dist (Φ 0 x) (Φ 0 y) ≤ dist x y by simp only [hinit, le_refl]) t.1 t.2
  refine hg.trans ?_
  change dist x y * Real.exp (K * (t.1 - 0)) ≤ Real.exp (K * T) * dist x y
  rw [mul_comm (Real.exp _), sub_zero]
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left t.2.2 K.2)) dist_nonneg

/-- The trajectory equation gives the Picard identity on every closed initial subinterval. -/
theorem eq_add_integral_of_trajectory
    {u : ℝ → E → E} {γ : ℝ → E}
    (hu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set E)))
    (hcont : ContinuousOn γ (Icc 0 T))
    (hode : ∀ τ ∈ Ico 0 T, HasDerivWithinAt γ (u τ (γ τ)) (Ici τ) τ)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    γ t = γ 0 + ∫ s in 0..t, u s (γ s) := by
  have hc : ContinuousOn (fun s => u s (γ s)) (Icc 0 T) :=
    ODE.continuousOn_comp hu hcont (fun _ _ => mem_univ _)
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
    (hcont.mono (Icc_subset_Icc le_rfl ht.2))
    (fun s hs => (hode s ⟨hs.1.le, hs.2.trans_le ht.2⟩).mono Ioi_subset_Ici_self)
    ((hc.mono (uIcc_subset_Icc ⟨le_rfl, ht.1.trans ht.2⟩ ht)).intervalIntegrable)]
  abel

/-- Existing trajectories depend `C¹` on their initial value as entire continuous paths.
The velocity is differentiated only in space; no spatial derivative of the flow is assumed. -/
theorem contDiff_flow_paths (hT : 0 ≤ T)
    {u Φ : ℝ → E → E} {K : ℝ≥0}
    (hu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set E)))
    (hdiff : ∀ τ ∈ Icc 0 T, Differentiable ℝ (u τ))
    (hD : ContinuousOn (fun p : ℝ × E => fderiv ℝ (u p.1) p.2)
      (Icc 0 T ×ˢ (univ : Set E)))
    (hbound : ∀ τ ∈ Ico 0 T, ∀ x, ‖fderiv ℝ (u τ) x‖₊ ≤ K)
    (hcont : ∀ x, ContinuousOn (fun τ => Φ τ x) (Icc 0 T))
    (hode : ∀ x, ∀ τ ∈ Ico 0 T,
      HasDerivWithinAt (fun τ => Φ τ x) (u τ (Φ τ x)) (Ici τ) τ)
    (hinit : ∀ x, Φ 0 x = x) :
    ContDiff ℝ 1
      (fun x => (⟨fun t : Icc 0 T => Φ t.1 x, (hcont x).restrict⟩ : C(Icc 0 T, E))) := by
  let U : C(Icc 0 T × E, E) :=
    ⟨fun p => u p.1.1 p.2, hu.comp_continuous (continuous_subtype_val.prodMap continuous_id)
      (fun p => ⟨p.1.2, mem_univ _⟩)⟩
  let D : C(Icc 0 T × E, E →L[ℝ] E) :=
    ⟨fun p => fderiv ℝ (u p.1.1) p.2,
      hD.comp_continuous (continuous_subtype_val.prodMap continuous_id)
        (fun p => ⟨p.1.2, mem_univ _⟩)⟩
  have hLip := lipschitzWith_flow_paths
    (fun τ hτ => lipschitzWith_of_nnnorm_fderiv_le
      (hdiff τ (Ico_subset_Icc_self hτ)) (hbound τ hτ)) hcont hode hinit
  apply contDiff_iff_contDiffAt.mpr
  intro x
  apply contDiffAt_of_path_integral_eq hT U D
    (fun s y => (hdiff s.1 s.2 y).hasFDerivAt) hLip.continuous.continuousAt
  apply Filter.Eventually.of_forall
  intro y
  ext t
  change Φ t.1 y = y + ∫ s in 0..t.1,
    u (projIcc 0 T hT s).1 (Φ (projIcc 0 T hT s).1 y)
  rw [eq_add_integral_of_trajectory hu (hcont y) (hode y) t.2, hinit]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  simp only [projIcc_of_mem hT (uIcc_subset_Icc ⟨le_rfl, hT⟩ t.2 hs)]

/-- Differentiating the Picard identity gives its linear integral equation in path space. -/
theorem fderiv_path_integral_eq (hT : 0 ≤ T)
    (u : C(Icc 0 T × E, E)) (D : C(Icc 0 T × E, E →L[ℝ] E))
    (hD : ∀ s x, HasFDerivAt (fun y => u (s, y)) (D (s, x)) x)
    {Φ : E → C(Icc 0 T, E)} {x : E}
    (hdiff : DifferentiableAt ℝ Φ x)
    (hfix : ∀ᶠ y in 𝓝 x,
      Φ y = ContinuousMap.const (Icc 0 T) y + pathIntegral hT (pathSuperposition u (Φ y))) :
    fderiv ℝ Φ x = ContinuousLinearMap.const ℝ (Icc 0 T) +
      (pathVolterra hT (pathSuperposition D (Φ x))).comp (fderiv ℝ Φ x) := by
  have h := (ContinuousLinearMap.const ℝ (Icc 0 T)).hasFDerivAt.add
    ((pathIntegral hT).hasFDerivAt.comp x
      ((hasFDerivAt_pathSuperposition u D hD (Φ x)).comp x hdiff.hasFDerivAt))
  exact (h.congr_of_eventuallyEq hfix).fderiv

end ClockBarrier.Dynamics
