/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.CauchyTransport
import Mathlib.Tactic.Abel

/-! # Transported vorticity increments for the general clock estimate -/

public section
namespace ClockBarrier.Euler
open Set
open scoped Topology NNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
  (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
  (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
  (hode : ∀ x, ∀ t ∈ Ico 0 T,
    HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
  (hinit : ∀ x, Φ 0 x = x)

include hcont hode hinit

/-- Cauchy transport splits a vorticity increment into a deformation error
and the initial-vorticity increment transported by the center deformation. -/
theorem classical_euler_on.vorticity_flow_sub_eq_deformation_add
    (t : ℝ) (ht : t ∈ Ico 0 T) (aStar a : E₃) :
    let F := fderiv ℝ (Φ t)
    let w₀ := vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩)
    vorticity (u t) (h.cartesian_partials t ht) (Φ t a) -
      vorticity (u t) (h.cartesian_partials t ht) (Φ t aStar) =
        (F a - F aStar) (w₀ a) + F aStar (w₀ a - w₀ aStar) := by
  dsimp only
  rw [h.vorticity_flow_eq_fderiv_apply hcont hode hinit t ht a,
    h.vorticity_flow_eq_fderiv_apply hcont hode hinit t ht aStar]
  simp only [sub_apply, map_sub]
  abel

/-- Inserting any slice value separates the transverse increment from the
longitudinal one. The actual coherence slice average can be substituted later. -/
theorem classical_euler_on.vorticity_flow_sub_eq_deformation_add_slice
    (t : ℝ) (ht : t ∈ Ico 0 T) (aStar a m : E₃) :
    let F := fderiv ℝ (Φ t)
    let w₀ := vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩)
    vorticity (u t) (h.cartesian_partials t ht) (Φ t a) -
      vorticity (u t) (h.cartesian_partials t ht) (Φ t aStar) =
        (F a - F aStar) (w₀ a) + F aStar (w₀ a - m) + F aStar (m - w₀ aStar) := by
  dsimp only
  rw [h.vorticity_flow_sub_eq_deformation_add hcont hode hinit t ht aStar a]
  simp only [map_sub]
  abel

/-- The three transported increments give a pointwise majorant without any
spatial derivative of the vorticity or second derivative of the flow. -/
theorem classical_euler_on.norm_vorticity_flow_sub_le_deformation_add_slice
    (t : ℝ) (ht : t ∈ Ico 0 T) (aStar a m : E₃) :
    let F := fderiv ℝ (Φ t)
    let w₀ := vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩)
    ‖vorticity (u t) (h.cartesian_partials t ht) (Φ t a) -
      vorticity (u t) (h.cartesian_partials t ht) (Φ t aStar)‖ ≤
        ‖(F a - F aStar) (w₀ a)‖ + ‖F aStar‖ * (‖w₀ a - m‖ + ‖m - w₀ aStar‖) := by
  intro F w₀
  rw [h.vorticity_flow_sub_eq_deformation_add_slice hcont hode hinit t ht aStar a m]
  change ‖(F a - F aStar) (w₀ a) + F aStar (w₀ a - m) + F aStar (m - w₀ aStar)‖ ≤ _
  have hv : ‖F aStar (w₀ a - m)‖ ≤ ‖F aStar‖ * ‖w₀ a - m‖ :=
    (F aStar).le_opNorm (w₀ a - m)
  have hz : ‖F aStar (m - w₀ aStar)‖ ≤ ‖F aStar‖ * ‖m - w₀ aStar‖ :=
    (F aStar).le_opNorm (m - w₀ aStar)
  calc
    _ ≤ (‖(F a - F aStar) (w₀ a)‖ + ‖F aStar (w₀ a - m)‖) +
        ‖F aStar (m - w₀ aStar)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (‖(F a - F aStar) (w₀ a)‖ + ‖F aStar‖ * ‖w₀ a - m‖) +
        ‖F aStar‖ * ‖m - w₀ aStar‖ :=
      add_le_add (add_le_add le_rfl hv) hz
    _ = _ := by rw [mul_add, add_assoc]

end ClockBarrier.Euler
