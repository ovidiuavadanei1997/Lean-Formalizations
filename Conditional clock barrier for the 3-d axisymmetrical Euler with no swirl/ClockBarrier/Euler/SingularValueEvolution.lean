/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.SingularValueEvolution
public import ClockBarrier.Euler.GeneralCoherenceWellDefined
/-! # Euler-flow smallest-singular-value evolution

Ordinary implementation of Lemma 4.1 on the classical Euler interface.
The variational equation and positivity of the actual flow derivative are
proved dependencies. The public statement is in `ClockBarrier.Frozen.SingularValueEvolution`.
-/

public section
namespace ClockBarrier.Euler
open Set
open scoped Topology NNReal InnerProductSpace BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Lemma 4.1: the smallest singular value of the actual Euler flow has a right
derivative, including at repeated singular values. The strain infimum over
the complete left singular eigenspace is attained. -/
theorem classical_euler_on.smallest_singularValue_evolution
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x) (a : E₃) {t : ℝ} (ht : t ∈ Ico 0 T) :
    let F := fun s => fderiv ℝ (Φ s) a
    let ν := fun s => (F s).toLinearMap.singularValues 2
    let L := fderiv ℝ (u t) (Φ t a)
    let S := (1 / 2 : ℝ) • (L + L.adjoint)
    let G := {r : ℝ | ∃ e : E₃, ‖e‖ = 1 ∧
      F t ((F t).adjoint e) = ν t ^ 2 • e ∧ r = ⟪e, S e⟫_ℝ}
    IsLeast G (sInf G) ∧ HasDerivWithinAt ν (ν t * sInf G) (Ici t) t := by
  obtain ⟨hu, hdiff, hD, hbound, _⟩ := h.velocity_regular
  have hF := (Dynamics.flow_spatial_regularity_Ico (u := fun s x => u s x)
    hu hdiff hD hbound hcont hode hinit t ht).2 a
  obtain ⟨m, hm, hd⟩ := Analysis.exists_hasDerivWithinAt_smallest_singularValue
    (n := 2) (by simp) hF (h.singularValues_fderiv_flow_pos hcont hode hinit ht a (2 : Fin 3))
  exact ⟨hm.csInf_eq.symm ▸ hm, hm.csInf_eq.symm ▸ hd⟩

end ClockBarrier.Euler
