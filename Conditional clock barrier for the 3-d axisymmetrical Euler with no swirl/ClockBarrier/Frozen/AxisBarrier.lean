/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisCoherent
public import ClockBarrier.Euler.Reflection
import ClockBarrier.Euler.AxisCoherentBarrier

/-! # Theorem 1.2: the uniform physical axis barrier

Source: arXiv:2605.31587v3, Theorem 1.2, with specified conventions.
-/

public section

namespace ClockBarrier.Euler

open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)


/-- Theorem 1.2 with the reflection and maximal-coherence conventions. -/
theorem axis_clock_barrier :
  ∀ {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃}
    (_hα : (1 / 3 : ℝ) ≤ (α : ℝ)) (_hcoh : axis_coherent_on α T u)
    (_hreflection : ∀ t ∈ Ico 0 T, z_reflection_symmetric (u t))
    (_hmaximal : ∀ T' : ℝ, T < T' →
      ¬ ∃ v : ℝ → E₃ →ᵇ E₃,
        axis_coherent_on α T' v ∧ ∀ t ∈ Ico 0 T, v t = u t),
    ∃ c : ℝ, 0 < c ∧ ∀ Φ : ℝ → E₃ → E₃,
      (∀ x, Φ 0 x = x) →
      (∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T)) →
      (∀ x, ∀ t ∈ Ico 0 T,
        HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t) →
      ∀ z : ℝ, ∀ t ∈ Ico 0 T, ∃ j : ℝ,
        c ≤ j ∧ Tendsto (fun r : ℝ =>
          (fderiv ℝ (fun q : E₂ =>
            (!₂[Real.sqrt ((Φ t !₂[q 0, 0, q 1] 0)^2 + (Φ t !₂[q 0, 0, q 1] 1)^2),
              Φ t !₂[q 0, 0, q 1] 2] : E₂)) !₂[r, z]).toLinearMap.det)
          (𝓝[>] 0) (𝓝 j) :=

by exact ClockBarrier.Euler.axis_coherent_on.uniform_physical_axis_barrier



end ClockBarrier.Euler


