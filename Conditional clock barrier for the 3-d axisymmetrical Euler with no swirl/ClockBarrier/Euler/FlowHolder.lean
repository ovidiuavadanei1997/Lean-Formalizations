/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisFlow
import ClockBarrier.Dynamics.FlowHolder

/-! # Spatial Hölder regularity of the Euler deformation

The compact-time velocity hypotheses imply the deformation estimate
used in the local averaged Dini argument of Proposition 3.1.
-/

public section
namespace ClockBarrier.Euler
open Set
open scoped Topology NNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The actual Euler flow derivative has a spatial Hölder constant uniform on
each compact initial time interval and over all labels. -/
theorem classical_euler_on.exists_uniform_holder_bound_fderiv_flow
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ a, ContinuousOn (fun t => Φ t a) (Ico 0 T))
    (hode : ∀ a, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s a) (u t (Φ t a)) (Ici t) t)
    (hinit : ∀ a, Φ 0 a = a) {b : ℝ} (hb : b ∈ Ico 0 T) :
    ∃ C : ℝ≥0, ∀ t ∈ Icc 0 b, ∀ a aStar,
      ‖fderiv ℝ (Φ t) a - fderiv ℝ (Φ t) aStar‖ ≤ C * ‖a - aStar‖ ^ (α : ℝ) := by
  obtain ⟨hu, hdiff, hD, hbound, _⟩ := h.velocity_regular
  obtain ⟨D, _, hd, hHolder⟩ := h.2.2.2.2.1
  obtain ⟨H, hH⟩ := hHolder b hb
  obtain ⟨K, hK⟩ := hbound b hb
  have hsub : Icc 0 b ⊆ Ico 0 T := fun _ hs => ⟨hs.1, hs.2.trans_lt hb.2⟩
  exact Dynamics.exists_uniform_holder_bound_fderiv_flow (u := fun s a => u s a) hb.1
    (hu.mono (prod_mono hsub subset_rfl)) (fun s hs => hdiff s (hsub hs))
    (hD.mono (prod_mono hsub subset_rfl)) hK
    (fun s hs => by simpa only [funext (fun a => (hd s (hsub hs) a).fderiv)] using hH s hs)
    (fun a => (hcont a).mono hsub)
    (fun a s hs => hode a s (hsub (Ico_subset_Icc_self hs))) hinit

end ClockBarrier.Euler
