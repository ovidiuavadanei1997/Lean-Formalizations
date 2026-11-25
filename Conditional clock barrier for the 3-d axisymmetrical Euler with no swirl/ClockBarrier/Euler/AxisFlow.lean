/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.Classical
public import ClockBarrier.Euler.Axisymmetry
public import ClockBarrier.Dynamics.AxisFlow
import ClockBarrier.Dynamics.VelocityRegularity

/-!
# Axis clocks of classical Euler solutions

The solution predicate supplies the velocity regularity used by the
constructed flow. Axisymmetry is assumed at every time in the lifespan.
The uniform clock barrier and its driver estimate remain separate theorems.
-/

public section

namespace ClockBarrier.Euler

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The solution regularity supplies all hypotheses for flow construction. -/
theorem classical_euler_on.velocity_regular
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) :
    ContinuousOn (fun q : ℝ × E₃ => u q.1 q.2) (Ico 0 T ×ˢ univ) ∧
    (∀ t ∈ Ico 0 T, Differentiable ℝ (u t)) ∧
    ContinuousOn (fun q : ℝ × E₃ => fderiv ℝ (u q.1) q.2) (Ico 0 T ×ˢ univ) ∧
    (∀ b ∈ Ico 0 T, ∃ K : ℝ≥0,
      ∀ t ∈ Ico 0 b, ∀ x, ‖fderiv ℝ (u t) x‖₊ ≤ K) ∧
    ∀ t ∈ Ico 0 T, ∀ x, LinearMap.trace ℝ E₃ (fderiv ℝ (u t) x).toLinearMap = 0 := by
  obtain ⟨_, _, _, hu, ⟨D, hD, hd, _⟩, _, _, _, _, _, hdiv⟩ := h
  have hfd (t : ℝ) (ht : t ∈ Ico 0 T) (x : E₃) :
      fderiv ℝ (u t) x = D t x := (hd t ht x).fderiv
  refine ⟨Dynamics.continuousOn_uncurry_of_boundedContinuousFunction hu,
    fun t ht x => (hd t ht x).differentiableAt,
    (Dynamics.continuousOn_uncurry_of_boundedContinuousFunction hD).congr
      (fun q hq => hfd q.1 hq.1 q.2), ?_, hdiv⟩
  intro b hb
  obtain ⟨K, hK⟩ := Dynamics.exists_bound_Ico_of_boundedContinuousFunction hD b hb
  exact ⟨K, fun t ht x => (hfd t ⟨ht.1, ht.2.trans hb.2⟩ x) ▸ hK t ht x⟩


open ClockBarrier.Geometry
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

/-- Construct a spatially C¹ flow and its positive physical axis clocks from an
axisymmetric no-swirl solution of the classical Euler equations. -/
theorem classical_euler_on.exists_axis_flow
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p)
    (haxis : ∀ t ∈ Ico 0 T, axisymmetric_no_swirl (u t)) :
    ∃ Φ : ℝ → E₃ → E₃,
      (∀ x, Φ 0 x = x) ∧ (∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T)) ∧
      (∀ x, ∀ t ∈ Ico 0 T,
        HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t) ∧
      (∀ t ∈ Ico 0 T, ContDiff ℝ 1 (Φ t) ∧ Function.Injective (Φ t) ∧
        ∀ s : Set E₃, MeasurableSet s → MeasureTheory.volume (Φ t '' s) = MeasureTheory.volume s) ∧
      ∀ z : ℝ,
        let J : ℝ → ℝ := fun t =>
          (fderiv ℝ (fun p : E₂ =>
            (!₂[Φ t !₂[p 0, 0, p 1] 0, Φ t !₂[p 0, 0, p 1] 2] : E₂)) !₂[0, z]).toLinearMap.det
        J 0 = 1 ∧ ∀ t ∈ Ico 0 T,
          Φ t !₂[0, 0, z] = !₂[0, 0, Φ t !₂[0, 0, z] 2] ∧
          0 < J t ∧
          euclideanMatrix (fderiv ℝ (Φ t) !₂[0, 0, z]) =
            Matrix.diagonal ![(J t)⁻¹, (J t)⁻¹, (J t)^2] ∧
          Tendsto (fun r : ℝ =>
            (fderiv ℝ (fun p : E₂ =>
              (!₂[Real.sqrt ((Φ t !₂[p 0, 0, p 1] 0)^2 + (Φ t !₂[p 0, 0, p 1] 1)^2),
                Φ t !₂[p 0, 0, p 1] 2] : E₂)) !₂[r, z]).toLinearMap.det)
            (𝓝[>] 0) (𝓝 (J t)) ∧
          HasDerivWithinAt J
            ((1 / 2 : ℝ) * J t *
              deriv (fun ζ : ℝ => u t !₂[0, 0, ζ] 2) (Φ t !₂[0, 0, z] 2)) (Ico 0 T) t := by
  obtain ⟨hu, hdiff, hD, hbound, hdiv⟩ := h.velocity_regular
  exact Dynamics.exists_flow_axis_clock_Ico hu hdiff hD hbound haxis hdiv h.1

end ClockBarrier.Euler

