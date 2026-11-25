/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.CauchyTransport
import Mathlib.Analysis.Calculus.Deriv.Mul
import ClockBarrier.Dynamics.FlowDerivativeWithin
/-! # The material vorticity derivative at classical Hölder regularity

The derivative within the lifespan includes the initial right derivative and
ordinary interior derivatives, without spatially differentiating vorticity.
-/

public section
namespace ClockBarrier.Euler
open Set Filter
open scoped Topology NNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Cauchy transport and the variational equation give the time derivative
of actual vorticity on trajectories, without a spatial derivative of vorticity. -/
theorem classical_euler_on.hasDerivWithinAt_vorticity_flow
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ a, ContinuousOn (fun t => Φ t a) (Ico 0 T))
    (hode : ∀ a, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s a) (u t (Φ t a)) (Ici t) t)
    (hinit : ∀ a, Φ 0 a = a) {W : ℝ → E₃ →ᵇ E₃}
    (hW : ∀ t, ∀ ht : t ∈ Ico 0 T, ∀ x,
      W t x = vorticity (u t) (h.cartesian_partials t ht) x)
    (a : E₃) {t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (fun s => W s (Φ s a))
      (fderiv ℝ (u t) (Φ t a) (W t (Φ t a))) (Ico 0 T) t := by
  have heq (s : ℝ) (hs : s ∈ Ico 0 T) :
      W s (Φ s a) = fderiv ℝ (Φ s) a (W 0 a) := by
    simpa only [hW s hs, hW 0 ⟨le_rfl, h.1⟩] using
      h.vorticity_flow_eq_fderiv_apply hcont hode hinit s hs a
  obtain ⟨hu, hdiff, hD, hbound, _⟩ := h.velocity_regular
  have hd := Dynamics.hasDerivWithinAt_fderiv_flow_Ico hu hdiff hD hbound hcont hode hinit a ht
  have hdv : HasDerivWithinAt (fun s => fderiv ℝ (Φ s) a (W 0 a))
      (fderiv ℝ (u t) (Φ t a) (W t (Φ t a))) (Ico 0 T) t := by
    simpa only [ContinuousLinearMap.comp_apply, zero_apply, ContinuousLinearMap.map_zero,
      add_zero, ← heq t ht] using hd.clm_apply (hasDerivWithinAt_const t (Ico 0 T) (W 0 a))
  apply hdv.congr_of_eventuallyEq_of_mem _ ht
  filter_upwards [self_mem_nhdsWithin] with s hs using heq s hs
end ClockBarrier.Euler
