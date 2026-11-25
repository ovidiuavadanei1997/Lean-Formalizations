/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Symmetry propagation for trajectories

Velocity covariance is transported to existing solutions of the trajectory ODE by
uniqueness. The Lipschitz bound is needed only on the selected finite time interval.
These results do not assume symmetry of the flow or construct an Euler solution.
-/

public section

namespace ClockBarrier.Dynamics

open Set
open scoped NNReal

/-- A linear symmetry of the velocity field carries one trajectory to the trajectory
with the transformed initial value. Derivatives at the initial time are one-sided. -/
theorem eqOn_linearMap_of_ode
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ → E → E} {γ δ : ℝ → E} {s t : ℝ} {K : ℝ≥0} (R : E →L[ℝ] E)
    (hu : ∀ τ ∈ Ico s t, LipschitzWith K (u τ))
    (hcov : ∀ τ ∈ Ico s t, Function.Semiconj (u τ) R R)
    (hγ : ContinuousOn γ (Icc s t))
    (hγ' : ∀ τ ∈ Ico s t, HasDerivWithinAt γ (u τ (γ τ)) (Ici τ) τ)
    (hδ : ContinuousOn δ (Icc s t))
    (hδ' : ∀ τ ∈ Ico s t, HasDerivWithinAt δ (u τ (δ τ)) (Ici τ) τ)
    (hstart : δ s = R (γ s)) : EqOn δ (fun τ => R (γ τ)) (Icc s t) := by
  have hRγ : ContinuousOn (fun τ => R (γ τ)) (Icc s t) :=
    R.continuous.comp_continuousOn hγ
  have hRγ' : ∀ τ ∈ Ico s t,
      HasDerivWithinAt (fun τ => R (γ τ)) (u τ (R (γ τ))) (Ici τ) τ := fun τ hτ =>
    (R.hasFDerivAt.comp_hasDerivWithinAt τ (hγ' τ hτ)).congr_deriv (hcov τ hτ (γ τ)).symm
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ)
    (fun τ hτ => (hu τ hτ).lipschitzOnWith) hδ hδ' (fun _ _ => mem_univ _)
    hRγ hRγ' (fun _ _ => mem_univ _) hstart

/-- An existing flow inherits each linear symmetry of its velocity field. Flow symmetry
is concluded from the trajectory equations and initial identity, not assumed. -/
theorem semiconj_flow_of_velocity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u Φ : ℝ → E → E} {s t : ℝ} {K : ℝ≥0} (R : E →L[ℝ] E)
    (hu : ∀ τ ∈ Ico s t, LipschitzWith K (u τ))
    (hcov : ∀ τ ∈ Ico s t, Function.Semiconj (u τ) R R)
    (hcont : ∀ x, ContinuousOn (fun τ => Φ τ x) (Icc s t))
    (hode : ∀ x, ∀ τ ∈ Ico s t,
      HasDerivWithinAt (fun τ => Φ τ x) (u τ (Φ τ x)) (Ici τ) τ)
    (hinit : ∀ x, Φ s x = x) :
    ∀ τ ∈ Icc s t, Function.Semiconj (Φ τ) R R := by
  intro τ hτ x
  exact eqOn_linearMap_of_ode R hu hcov (hcont x) (hode x)
    (hcont (R x)) (hode (R x)) (by simp only [hinit]) hτ

/-- A uniform spatial derivative bound supplies the Lipschitz estimate used to propagate
velocity symmetry. The bound is local in time to the chosen finite interval. -/
theorem semiconj_flow_of_fderiv_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u Φ : ℝ → E → E} {s t : ℝ} {K : ℝ≥0} (R : E →L[ℝ] E)
    (hdiff : ∀ τ ∈ Ico s t, Differentiable ℝ (u τ))
    (hbound : ∀ τ ∈ Ico s t, ∀ x, ‖fderiv ℝ (u τ) x‖₊ ≤ K)
    (hcov : ∀ τ ∈ Ico s t, Function.Semiconj (u τ) R R)
    (hcont : ∀ x, ContinuousOn (fun τ => Φ τ x) (Icc s t))
    (hode : ∀ x, ∀ τ ∈ Ico s t,
      HasDerivWithinAt (fun τ => Φ τ x) (u τ (Φ τ x)) (Ici τ) τ)
    (hinit : ∀ x, Φ s x = x) :
    ∀ τ ∈ Icc s t, Function.Semiconj (Φ τ) R R := by
  exact semiconj_flow_of_velocity R
    (fun τ hτ => lipschitzWith_of_nnnorm_fderiv_le (hdiff τ hτ) (hbound τ hτ))
    hcov hcont hode hinit

/-- Symmetry propagates on `[0,T)` using bounds on each earlier time interval.
No derivative bound or continuity through the terminal time is required. -/
theorem semiconj_flow_Ico_of_fderiv_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u Φ : ℝ → E → E} {T : ℝ} (R : E →L[ℝ] E)
    (hdiff : ∀ τ ∈ Ico 0 T, Differentiable ℝ (u τ))
    (hbound : ∀ b ∈ Ico 0 T, ∃ K : ℝ≥0,
      ∀ τ ∈ Ico 0 b, ∀ x, ‖fderiv ℝ (u τ) x‖₊ ≤ K)
    (hcov : ∀ τ ∈ Ico 0 T, Function.Semiconj (u τ) R R)
    (hcont : ∀ x, ContinuousOn (fun τ => Φ τ x) (Ico 0 T))
    (hode : ∀ x, ∀ τ ∈ Ico 0 T,
      HasDerivWithinAt (fun τ => Φ τ x) (u τ (Φ τ x)) (Ici τ) τ)
    (hinit : ∀ x, Φ 0 x = x) :
    ∀ τ ∈ Ico 0 T, Function.Semiconj (Φ τ) R R := by
  intro b hb
  obtain ⟨K, hK⟩ := hbound b hb
  have hclosed : Icc 0 b ⊆ Ico 0 T := fun _ hτ => ⟨hτ.1, hτ.2.trans_lt hb.2⟩
  exact semiconj_flow_of_fderiv_bound R
    (fun τ hτ => hdiff τ (hclosed (Ico_subset_Icc_self hτ))) hK
    (fun τ hτ => hcov τ (hclosed (Ico_subset_Icc_self hτ)))
    (fun x => (hcont x).mono hclosed)
    (fun x τ hτ => hode x τ (hclosed (Ico_subset_Icc_self hτ))) hinit b ⟨hb.1, le_rfl⟩

end ClockBarrier.Dynamics
