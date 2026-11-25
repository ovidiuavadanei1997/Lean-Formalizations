/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.MetricSpace.Holder

/-! # Classical finite-energy Euler solutions

See docs/ERRATA-AND-DEVIATIONS.md for the conventions.
-/

@[expose] public section

namespace ClockBarrier.Euler

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Classical finite-energy Euler regularity on a half-open lifespan.
The temporal norm convention is explicit. -/
def classical_euler_on (α : ℝ≥0) (T : ℝ)
    (u : ℝ → E₃ →ᵇ E₃) (p : ℝ → E₃ → ℝ) : Prop :=
  0 < T ∧ 0 < α ∧ α < 1 ∧
  ContinuousOn u (Ico 0 T) ∧
  (∃ D : ℝ → E₃ →ᵇ (E₃ →L[ℝ] E₃),
    ContinuousOn D (Ico 0 T) ∧
    (∀ t ∈ Ico 0 T, ∀ x, HasFDerivAt (u t) (D t x) x) ∧
    ∀ b ∈ Ico 0 T, ∃ H : ℝ≥0, ∀ t ∈ Icc 0 b, HolderWith H α (D t)) ∧
  (∀ t ∈ Ico 0 T, MemLp (u t) 2 volume) ∧
  (∀ t ∈ Ico 0 T, Tendsto
    (fun s => eLpNorm (fun x => u s x - u t x) 2 volume)
    (𝓝[Ico 0 T] t) (𝓝 0)) ∧
  (∀ t ∈ Ico 0 T, Differentiable ℝ (p t)) ∧
  ContinuousOn (fun q : ℝ × E₃ => gradient (p q.1) q.2) (Ico 0 T ×ˢ univ) ∧
  (∀ t ∈ Ico 0 T, ∀ x,
    HasDerivWithinAt (fun s => u s x)
      (-(fderiv ℝ (u t) x) (u t x) - gradient (p t) x) (Ico 0 T) t) ∧
  ∀ t ∈ Ico 0 T, ∀ x,
    LinearMap.trace ℝ E₃ (fderiv ℝ (u t) x).toLinearMap = 0

end ClockBarrier.Euler

