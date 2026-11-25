/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.GeneralCoherenceWellDefined
public import ClockBarrier.Geometry.SingularBlockGeometry

/-! # Singular-value geometry of the actual Euler flow -/

public section
namespace ClockBarrier.Euler
open Set
open scoped Topology NNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Volume preservation supplies the singular-value product used in the general driver. -/
theorem classical_euler_on.prod_singularValues_fderiv_flow
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x) {t : ℝ} (ht : t ∈ Ico 0 T) (a : E₃) :
    let σ := (fderiv ℝ (Φ t) a).toLinearMap.singularValues
    σ 0 * σ 1 * σ 2 = 1 := by
  apply Geometry.prod_singularValues_eq_one
  obtain ⟨hu, hdiff, hD, hbound, hdiv⟩ := h.velocity_regular
  exact Dynamics.det_fderiv_flow_eq_one_Ico (u := fun s x => u s x)
    hu hdiff hD hbound hcont hode hinit hdiv a ht

end ClockBarrier.Euler
