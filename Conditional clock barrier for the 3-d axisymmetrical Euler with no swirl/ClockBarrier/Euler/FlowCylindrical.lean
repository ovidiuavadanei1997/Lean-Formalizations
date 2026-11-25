/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.FlowChangeOfVariables
public import ClockBarrier.Geometry.CylindricalCurl
import ClockBarrier.Euler.AxisFlow
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-! # Global meridional geometry of the Euler flow

Rotations and transverse reflections follow from uniqueness. Injectivity and
time continuity then keep a positive-radius label on the positive meridional ray.
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

/-- Every proper transverse rotation commutes with the actual Euler flow. -/
theorem classical_euler_on.rotation_semiconj_flow (t : ℝ) (ht : t ∈ Ico 0 T) (β : ℝ) :
    Function.Semiconj (Φ t)
      (Matrix.toEuclideanLin
        !![Real.cos β, -Real.sin β, 0; Real.sin β, Real.cos β, 0; 0, 0, 1])
      (Matrix.toEuclideanLin
        !![Real.cos β, -Real.sin β, 0; Real.sin β, Real.cos β, 0; 0, 0, 1]) := by
  obtain ⟨_, hd, _, hb, _⟩ := h.velocity_regular
  refine Dynamics.semiconj_flow_Ico_of_fderiv_bound
    (Matrix.toEuclideanLin
      !![Real.cos β, -Real.sin β, 0; Real.sin β, Real.cos β, 0; 0, 0, 1]).toContinuousLinearMap
    hd hb ?_ hcont hode hinit t ht
  exact fun s hs => (haxis s hs).elim (fun _ hv =>
    hv.elim (fun _ hrep => rotation_semiconj_of_cylindrical_representation hrep β))

/-- A meridional label stays in the meridional plane. -/
theorem classical_euler_on.flow_meridional_second_eq_zero
    (t : ℝ) (ht : t ∈ Ico 0 T) (r z : ℝ) : Φ t !₂[r, 0, z] 1 = 0 := by
  exact second_coordinate_eq_zero_of_reflection
    (Dynamics.transverse_symmetries_flow_of_cylindrical_velocity
      h.velocity_regular.2.1 h.velocity_regular.2.2.2.1 haxis hcont hode hinit ht).2.1

/-- Injectivity and transverse reflection prevent a nonzero meridional radial
coordinate from reaching zero. -/
theorem classical_euler_on.flow_meridional_first_ne_zero
    (t : ℝ) (ht : t ∈ Ico 0 T) {r : ℝ} (hr : r ≠ 0) (z : ℝ) :
    Φ t !₂[r, 0, z] 0 ≠ 0 := by
  have hx := (Dynamics.transverse_symmetries_flow_of_cylindrical_velocity
    h.velocity_regular.2.1 h.velocity_regular.2.2.2.1 haxis hcont hode hinit ht).1
  intro hzero
  have hfix : Matrix.toEuclideanLin (Matrix.diagonal ![-1, 1, 1]) (Φ t !₂[r, 0, z]) =
      Φ t !₂[r, 0, z] := by
    ext i
    fin_cases i <;> simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      Matrix.mulVec_diagonal, Matrix.cons_val_two, hzero]
  have he := (h.contDiff_bijective_measurePreserving_flow hcont hode hinit ht).2.1.1
    ((hx !₂[r, 0, z]).trans hfix)
  have he0 : -r = r := by
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]
      using congrArg (fun x : E₃ => x 0) he
  exact hr (by linarith only [he0])

/-- A particle starting at positive meridional radius has positive radial
coordinate throughout the lifespan. This follows from continuity and injectivity. -/
theorem classical_euler_on.flow_meridional_first_pos
    (t : ℝ) (ht : t ∈ Ico 0 T) {r : ℝ} (hr : 0 < r) (z : ℝ) :
    0 < Φ t !₂[r, 0, z] 0 := by
  by_contra hn
  have hc : ContinuousOn (fun s => Φ s !₂[r, 0, z] 0) (Ico 0 T) :=
    (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous.comp_continuousOn (hcont !₂[r, 0, z])
  obtain ⟨s, hs, he⟩ := isPreconnected_Ico.intermediate_value ht
    (show (0 : ℝ) ∈ Ico 0 T from ⟨le_rfl, h.1⟩) hc
    (show (0 : ℝ) ∈ Icc (Φ t !₂[r, 0, z] 0) (Φ 0 !₂[r, 0, z] 0) from
      ⟨le_of_not_gt hn, by simpa only [hinit, Matrix.cons_val_zero] using hr.le⟩)
  exact h.flow_meridional_first_ne_zero hcont hode hinit haxis s hs hr.ne' z he

/-- On a positive meridional label, the signed first flow coordinate is the
physical cylindrical radius globally, not only near the axis. -/
theorem classical_euler_on.flow_meridional_radius_eq
    (t : ℝ) (ht : t ∈ Ico 0 T) {r : ℝ} (hr : 0 < r) (z : ℝ) :
    Real.sqrt ((Φ t !₂[r, 0, z] 0)^2 + (Φ t !₂[r, 0, z] 1)^2) = Φ t !₂[r, 0, z] 0 := by
  simpa only [h.flow_meridional_second_eq_zero hcont hode hinit haxis t ht r z,
    zero_pow (by decide : 2 ≠ 0), add_zero] using
    Real.sqrt_sq (h.flow_meridional_first_pos hcont hode hinit haxis t ht hr z).le

end ClockBarrier.Euler
