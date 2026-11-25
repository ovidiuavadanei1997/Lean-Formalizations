/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisBiotSavart
public import ClockBarrier.Euler.FlowChangeOfVariables
public import ClockBarrier.Euler.CauchyTransport
import ClockBarrier.Euler.AxisFlow

/-! # The signed axis strain in Lagrangian coordinates

The observation height is the current height of the axis trajectory, whereas
the center of the label-space clock region is its initial height.
-/

public section

namespace ClockBarrier.Euler

open Set MeasureTheory Geometry
open scoped NNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
  (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
  (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
  (hode : ∀ x, ∀ t ∈ Ico 0 T,
    HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
  (hinit : ∀ x, Φ 0 x = x)
  (haxis : ∀ t ∈ Ico 0 T, axisymmetric_no_swirl (u t))

include h hcont hode hinit haxis

/-- Axis preservation follows from the velocity symmetry and uniqueness of the flow. -/
theorem classical_euler_on.flow_axis_eq (t : ℝ) (ht : t ∈ Ico 0 T) (z : ℝ) :
    Φ t !₂[0, 0, z] = !₂[0, 0, Φ t !₂[0, 0, z] 2] := by
  obtain ⟨_, hdiff, _, hbound, _⟩ := h.velocity_regular
  have hs := Dynamics.transverse_symmetries_flow_of_cylindrical_velocity
    hdiff hbound haxis hcont hode hinit ht
  exact map_axis_of_transverse_reflections hs.1 hs.2.1

/-- The signed kernel remains absolutely integrable after pulling back by the
constructed Euler flow. No label-space decay assumption is added. -/
theorem classical_euler_on.integrable_axis_strain_vorticity_flow
    (t : ℝ) (ht : t ∈ Ico 0 T) (z : ℝ) :
    Integrable (fun a : E₃ =>
      (Φ t !₂[0, 0, z] 2 - Φ t a 2) *
        (Φ t a 0 * vorticity (u t) (h.cartesian_partials t ht) (Φ t a) 1 -
          Φ t a 1 * vorticity (u t) (h.cartesian_partials t ht) (Φ t a) 0) /
            ‖Φ t a - Φ t !₂[0, 0, z]‖ ^ 5) volume := by
  have hi := (h.integrable_comp_flow_iff hcont hode hinit ht).2
    (h.integrable_axis_strain_vorticity t ht (haxis t ht) (Φ t !₂[0, 0, z] 2))
  simpa only [← h.flow_axis_eq hcont hode hinit haxis t ht z] using hi

/-- Global volume preservation gives the signed Biot–Savart formula over labels. -/
theorem classical_euler_on.deriv_axis_eq_biot_savart_flow
    (t : ℝ) (ht : t ∈ Ico 0 T) (z : ℝ) :
    deriv (fun s : ℝ => u t !₂[0, 0, s] 2) (Φ t !₂[0, 0, z] 2) =
      -(3 / (4 * Real.pi)) * ∫ a : E₃,
        (Φ t !₂[0, 0, z] 2 - Φ t a 2) *
          (Φ t a 0 * vorticity (u t) (h.cartesian_partials t ht) (Φ t a) 1 -
            Φ t a 1 * vorticity (u t) (h.cartesian_partials t ht) (Φ t a) 0) /
              ‖Φ t a - Φ t !₂[0, 0, z]‖ ^ 5 := by
  rw [h.deriv_axis_eq_biot_savart t ht (haxis t ht)]
  rw [← h.flow_axis_eq hcont hode hinit haxis t ht z,
    ← h.integral_comp_flow hcont hode hinit ht]

end ClockBarrier.Euler
