/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.WeberPotential
public import ClockBarrier.Euler.VorticityRegularity
public import ClockBarrier.Geometry.WeberCurl
public import ClockBarrier.Geometry.CurlTransport

/-! # Cauchy vorticity transport at the classical Euler regularity

The proof integrates the momentum equation and uses symmetry of the corrected
Weber potential at a point. It never differentiates the vorticity spatially or
assumes a second derivative of the velocity or flow.
-/

public section

namespace ClockBarrier.Euler

open Set Geometry
open scoped Topology NNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Cauchy's identity for the partial-derivative vorticity along any
actual Euler flow. Spatial flow regularity and determinant one are consequences
of the hypotheses, not assumptions. The initial time is included. -/
theorem classical_euler_on.vorticity_flow_eq_fderiv_apply
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x) (t : ℝ) (ht : t ∈ Ico 0 T) (a : E₃) :
    vorticity (u t) (h.cartesian_partials t ht) (Φ t a) =
      fderiv ℝ (Φ t) a (vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩) a) := by
  obtain ⟨hu, hdiff, hD, hbound, hdiv⟩ := h.velocity_regular
  obtain ⟨G, hG⟩ := h.exists_weber_potential hcont hode hinit ht
  have hΦ := (Dynamics.flow_spatial_regularity_Ico hu hdiff hD hbound hcont hode hinit t ht).1
  have hdet := Dynamics.det_fderiv_flow_eq_one_Ico (u := fun s x => u s x)
    hu hdiff hD hbound hcont hode hinit hdiv a ht
  rw [h.vorticity_eq_curlLinearMap t ht, h.vorticity_eq_curlLinearMap 0 ⟨le_rfl, h.1⟩]
  exact curl_eq_map_of_skew_eq _ _ _ hdet
    (skew_deriv_eq_of_weber_potential hΦ (hdiff 0 ⟨le_rfl, h.1⟩ a)
      (hdiff t ht (Φ t a)) hG)

/-- The Euler interface alone constructs a spatially C¹ flow carrying
the actual Cartesian vorticity by Cauchy's formula. -/
theorem classical_euler_on.exists_flow_vorticity_transport
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) :
    ∃ Φ : ℝ → E₃ → E₃,
      (∀ x, Φ 0 x = x) ∧ (∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T)) ∧
      (∀ x, ∀ t ∈ Ico 0 T,
        HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t) ∧
      ∀ t, ∀ ht : t ∈ Ico 0 T, ContDiff ℝ 1 (Φ t) ∧ ∀ a,
        vorticity (u t) (h.cartesian_partials t ht) (Φ t a) =
          fderiv ℝ (Φ t) a (vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩) a) := by
  obtain ⟨hu, hdiff, hD, hbound, _⟩ := h.velocity_regular
  obtain ⟨Φ, hinit, hcont, hode, hreg⟩ :=
    Dynamics.exists_regular_flow_Ico h.1 hu hdiff hD hbound
  exact ⟨Φ, hinit, hcont, hode, fun t ht => ⟨(hreg t ht).1,
    h.vorticity_flow_eq_fderiv_apply hcont hode hinit t ht⟩⟩

/-- Cauchy transport yields the actual vorticity stretching estimate in terms
of the spatial operator norm of the flow. -/
theorem classical_euler_on.norm_vorticity_flow_le
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x) (t : ℝ) (ht : t ∈ Ico 0 T) (a : E₃) :
    ‖vorticity (u t) (h.cartesian_partials t ht) (Φ t a)‖ ≤
      ‖fderiv ℝ (Φ t) a‖ * ‖vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩) a‖ := by
  rw [h.vorticity_flow_eq_fderiv_apply hcont hode hinit t ht]
  exact (fderiv ℝ (Φ t) a).le_opNorm _

end ClockBarrier.Euler
