/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.LocalFlowGeometry
public import ClockBarrier.Geometry.AxisLocalGeometry
import ClockBarrier.Euler.FlowCylindrical

/-! # Short-time radial geometry of the Euler flow -/

public section
namespace ClockBarrier.Euler
open Set
open scoped NNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Half-turn covariance in Cartesian coordinates, valid at every label. -/
theorem classical_euler_on.flow_axis_halfTurn
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hc : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (ho : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hi : ∀ x, Φ 0 x = x)
    (ha : ∀ t ∈ Ico 0 T, axisymmetric_no_swirl (u t))
    {t : ℝ} (ht : t ∈ Ico 0 T) (a : E₃) :
    Φ t !₂[-a 0, -a 1, a 2] = !₂[-Φ t a 0, -Φ t a 1, Φ t a 2] := by
  simpa [Real.cos_pi, Real.sin_pi, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.mulVec, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] using
    h.rotation_semiconj_flow hc ho hi ha t ht Real.pi a

end ClockBarrier.Euler
