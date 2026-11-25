/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisFlow
public import ClockBarrier.Geometry.MeasurableSingularFrame
import ClockBarrier.Dynamics.FlowJacobian
import Mathlib.Tactic.FinCases

/-! # Measurable singular frames for the actual Euler flow

Spatial regularity and determinant one supply the hypotheses of the measurable
frame theorem throughout the lifespan, including repeated singular values.
-/

public section
namespace ClockBarrier.Euler
open Set
open scoped Topology NNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- At each lifespan time, the actual flow derivative admits a spatially measurable
right singular frame, with the ordered singular values used in general coherence. -/
theorem classical_euler_on.exists_measurable_singular_frame_at
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x) {t : ℝ} (ht : t ∈ Ico 0 T) :
    ∃ V : E₃ → E₃ ≃ₗᵢ[ℝ] E₃,
      (∀ i j : Fin 3, Measurable (fun a => V a (EuclideanSpace.single j 1) i)) ∧
      ∀ a, ∃ U : E₃ ≃ₗᵢ[ℝ] E₃, ∀ η : E₃,
        (fderiv ℝ (Φ t) a) (V a η) = U !₂[
          (fderiv ℝ (Φ t) a).toLinearMap.singularValues 0 * η 0,
          (fderiv ℝ (Φ t) a).toLinearMap.singularValues 1 * η 1,
          (fderiv ℝ (Φ t) a).toLinearMap.singularValues 2 * η 2] := by
  obtain ⟨hu, hdiff, hD, hbound, hdiv⟩ := h.velocity_regular
  have hc : Continuous (fderiv ℝ (Φ t)) :=
    (Dynamics.flow_spatial_regularity_Ico hu hdiff hD hbound hcont hode hinit t ht).1.continuous_fderiv
      (by decide)
  have hi : ∀ a, Function.Injective (fderiv ℝ (Φ t) a) := fun a =>
    LinearMap.ker_eq_bot.mp (by
      simpa [Dynamics.det_fderiv_flow_eq_one_Ico (u := fun s x => u s x)
        hu hdiff hD hbound hcont hode hinit hdiv a ht]
        using (LinearMap.det_eq_zero_iff_ker_ne_bot (f := (fderiv ℝ (Φ t) a).toLinearMap)))
  obtain ⟨V, hm, hV⟩ := Geometry.exists_measurable_singular_frame
    (fderiv ℝ (Φ t)) hc hi (by simp : Module.finrank ℝ E₃ = 3)
  refine ⟨V, fun i j => (EuclideanSpace.proj i).continuous.measurable.comp (hm j), ?_⟩
  exact fun a => (hV a).imp (fun U hU η =>
    (hU η).trans (congrArg U (by ext i; fin_cases i <;> rfl)))

/-- One family of spatially measurable right singular frames works at every lifespan time.
This is exactly the singular-frame clause of the general coherence class. -/
theorem classical_euler_on.exists_measurable_singular_frame
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x) :
    ∃ V : ℝ → E₃ → E₃ ≃ₗᵢ[ℝ] E₃,
      (∀ t ∈ Ico 0 T, ∀ i j : Fin 3,
        Measurable (fun a => V t a (EuclideanSpace.single j 1) i)) ∧
      ∀ t ∈ Ico 0 T, ∀ a, ∃ U : E₃ ≃ₗᵢ[ℝ] E₃, ∀ η : E₃,
        (fderiv ℝ (Φ t) a) (V t a η) = U !₂[
          (fderiv ℝ (Φ t) a).toLinearMap.singularValues 0 * η 0,
          (fderiv ℝ (Φ t) a).toLinearMap.singularValues 1 * η 1,
          (fderiv ℝ (Φ t) a).toLinearMap.singularValues 2 * η 2] := by
  classical
  choose V hm hV using fun t : Ico 0 T =>
    h.exists_measurable_singular_frame_at hcont hode hinit t.property
  exact ⟨fun t a => if ht : t ∈ Ico 0 T then V ⟨t, ht⟩ a else LinearIsometryEquiv.refl ℝ E₃,
    fun t ht i j => by simpa only [dif_pos ht] using hm ⟨t, ht⟩ i j,
    fun t ht a => by simpa only [dif_pos ht] using hV ⟨t, ht⟩ a⟩

end ClockBarrier.Euler
