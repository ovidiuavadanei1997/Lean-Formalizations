/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisFlow
public import ClockBarrier.Dynamics.FlowMeasurePreserving
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Global change of variables for the classical Euler flow

The Euler regularity and the trajectory ODE imply that each time slice
is a C¹ measure-preserving bijection. Integrability and integrals can therefore
be transferred between label space and physical space, including on subsets.
-/

public section

namespace ClockBarrier.Euler

open Set MeasureTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
  (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
  (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
  (hode : ∀ x, ∀ t ∈ Ico 0 T,
    HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
  (hinit : ∀ x, Φ 0 x = x)

include h hcont hode hinit

/-- Every initialized classical Euler flow is a spatially C¹, measure-preserving
bijection at every time before the end of its lifespan. -/
theorem classical_euler_on.contDiff_bijective_measurePreserving_flow
    {t : ℝ} (ht : t ∈ Ico 0 T) :
    ContDiff ℝ 1 (Φ t) ∧ Function.Bijective (Φ t) ∧
      MeasurePreserving (Φ t) volume volume := by
  obtain ⟨hu, hdiff, hD, hbound, hdiv⟩ := h.velocity_regular
  have hreg := (Dynamics.flow_spatial_regularity_Ico (u := fun s x => u s x)
    hu hdiff hD hbound hcont hode hinit t ht).1
  have hbij : Function.Bijective (Φ t) :=
    ⟨Dynamics.injective_flow_Ico_of_fderiv_bound (u := fun s x => u s x)
      hu hdiff hbound hcont hode hinit ht,
      Dynamics.surjective_flow_Ico_of_fderiv_bound (u := fun s x => u s x)
        hu hdiff hbound hcont hode hinit ht⟩
  exact ⟨hreg, hbij, Dynamics.measurePreserving_of_bijective_det_fderiv_eq_one
    (hreg.differentiable (by decide)) hbij
    (fun x => Dynamics.det_fderiv_flow_eq_one_Ico (u := fun s x => u s x)
      hu hdiff hD hbound hcont hode hinit hdiv x ht)⟩

variable {F : Type*} [NormedAddCommGroup F]

/-- Integrability is equivalent in label space and physical space. In particular,
integrability proved after pullback can be transferred to the original field. -/
theorem classical_euler_on.integrable_comp_flow_iff
    {t : ℝ} (ht : t ∈ Ico 0 T) {g : E₃ → F} :
    Integrable (fun a => g (Φ t a)) volume ↔ Integrable g volume :=
  let hr := h.contDiff_bijective_measurePreserving_flow hcont hode hinit ht
  hr.2.2.integrable_comp_emb (hr.1.continuous.measurableEmbedding hr.2.1.1)

/-- Localized integrability is equivalent on a physical set and its label preimage.
The measurable embedding makes a separate measurability premise on the set unnecessary. -/
theorem classical_euler_on.integrableOn_comp_flow_preimage
    {t : ℝ} (ht : t ∈ Ico 0 T) {g : E₃ → F} {s : Set E₃} :
    IntegrableOn (fun a => g (Φ t a)) (Φ t ⁻¹' s) volume ↔ IntegrableOn g s volume :=
  let hr := h.contDiff_bijective_measurePreserving_flow hcont hode hinit ht
  hr.2.2.integrableOn_comp_preimage (hr.1.continuous.measurableEmbedding hr.2.1.1)

variable [NormedSpace ℝ F]

/-- Global Bochner change of variables under the actual Euler flow. Use
`integrable_comp_flow_iff` to transfer integrability in either direction. -/
theorem classical_euler_on.integral_comp_flow [CompleteSpace F]
    {t : ℝ} (ht : t ∈ Ico 0 T) (g : E₃ → F) :
    ∫ a, g (Φ t a) ∂volume = ∫ x, g x ∂volume :=
  let hr := h.contDiff_bijective_measurePreserving_flow hcont hode hinit ht
  hr.2.2.integral_comp (hr.1.continuous.measurableEmbedding hr.2.1.1) g

/-- Bochner change of variables on a physical set and its label preimage. -/
theorem classical_euler_on.setIntegral_flow_preimage [CompleteSpace F]
    {t : ℝ} (ht : t ∈ Ico 0 T) (g : E₃ → F) (s : Set E₃) :
    ∫ a in Φ t ⁻¹' s, g (Φ t a) ∂volume = ∫ x in s, g x ∂volume :=
  let hr := h.contDiff_bijective_measurePreserving_flow hcont hode hinit ht
  hr.2.2.setIntegral_preimage_emb (hr.1.continuous.measurableEmbedding hr.2.1.1) g s

/-- Nonnegative change of variables allows infinite integrals as well. -/
theorem classical_euler_on.lintegral_comp_flow
    {t : ℝ} (ht : t ∈ Ico 0 T) (g : E₃ → ℝ≥0∞) :
    ∫⁻ a, g (Φ t a) ∂volume = ∫⁻ x, g x ∂volume :=
  let hr := h.contDiff_bijective_measurePreserving_flow hcont hode hinit ht
  hr.2.2.lintegral_comp_emb (hr.1.continuous.measurableEmbedding hr.2.1.1) g

/-- Localized nonnegative change of variables on any physical set. -/
theorem classical_euler_on.setLIntegral_flow_preimage
    {t : ℝ} (ht : t ∈ Ico 0 T) (g : E₃ → ℝ≥0∞) (s : Set E₃) :
    ∫⁻ a in Φ t ⁻¹' s, g (Φ t a) ∂volume = ∫⁻ x in s, g x ∂volume :=
  let hr := h.contDiff_bijective_measurePreserving_flow hcont hode hinit ht
  hr.2.2.setLIntegral_comp_preimage_emb
    (hr.1.continuous.measurableEmbedding hr.2.1.1) g s

omit hcont hode hinit in
/-- The Euler interface alone constructs one flow whose time slices
are C¹ measure-preserving bijections throughout the half-open lifespan. -/
theorem classical_euler_on.exists_measurePreserving_flow :
    ∃ Φ : ℝ → E₃ → E₃,
      (∀ x, Φ 0 x = x) ∧ (∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T)) ∧
      (∀ x, ∀ t ∈ Ico 0 T,
        HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t) ∧
      ∀ t ∈ Ico 0 T, ContDiff ℝ 1 (Φ t) ∧ Function.Bijective (Φ t) ∧
        MeasurePreserving (Φ t) volume volume := by
  obtain ⟨hu, hdiff, hD, hbound, _⟩ := h.velocity_regular
  obtain ⟨Ψ, hi, hc, ho, _⟩ := Dynamics.exists_regular_flow_Ico
    (u := fun s x => u s x) h.1 hu hdiff hD hbound
  exact ⟨Ψ, hi, hc, ho, fun _ ht =>
    h.contDiff_bijective_measurePreserving_flow hc ho hi ht⟩

end ClockBarrier.Euler
