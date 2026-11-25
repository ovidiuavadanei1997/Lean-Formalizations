/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.CauchyTransport
public import ClockBarrier.Geometry.AxisOperatorNorm

/-! # Actual vorticity stretching from the axis deformation comparison

Cauchy transport supplies the velocity-dependent vector in the operator estimate.
The comparison of spatial derivatives is the remaining geometric hypothesis.
-/

public section

namespace ClockBarrier.Euler

open Set Geometry
open scoped Topology NNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Cauchy transport and comparison with the actual axis derivative give the
vorticity stretching bound in the collapse regime, with the same comparison constant. -/
theorem classical_euler_on.norm_vorticity_flow_le_of_axis_comparison
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x) (t : ℝ) (ht : t ∈ Ico 0 T)
    {J CF z : ℝ} (hJ : 0 < J) (hJ₁ : J ≤ 1)
    (hA : euclideanMatrix (fderiv ℝ (Φ t) !₂[0, 0, z]) =
      Matrix.diagonal ![J⁻¹, J⁻¹, J ^ 2]) (a : E₃)
    (hF : ‖fderiv ℝ (Φ t) a‖ ≤ CF * ‖fderiv ℝ (Φ t) !₂[0, 0, z]‖) :
    ‖vorticity (u t) (h.cartesian_partials t ht) (Φ t a)‖ ≤
      CF * J⁻¹ * ‖vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩) a‖ := by
  rw [h.vorticity_flow_eq_fderiv_apply hcont hode hinit t ht]
  exact norm_apply_le_of_axis_comparison hJ hJ₁ hA hF _

end ClockBarrier.Euler
