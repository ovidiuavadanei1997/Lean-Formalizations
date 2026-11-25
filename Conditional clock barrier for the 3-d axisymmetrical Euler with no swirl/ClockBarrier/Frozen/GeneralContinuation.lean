/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.GeneralCoherent
import ClockBarrier.Euler.GeneralContinuation

/-! # Theorem 1.1: classical continuation from general coherence

Source: arXiv:2605.31587v3, Theorem 1.1, with specified conventions.
-/

public section

namespace ClockBarrier.Euler

open Set
open scoped NNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)


/-- Theorem 1.1: uniformly finite general coherence gives an actual classical Euler
extension of the same regularity. Coherence beyond the original lifespan is not required. -/
theorem general_clock_continuation :
  ∀ {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃},
    (1 / 3 : ℝ) ≤ (α : ℝ) → general_coherent_on α T u →
    ∃ T' : ℝ, T < T' ∧ ∃ v : ℝ → E₃ →ᵇ E₃, ∃ p : ℝ → E₃ → ℝ,
      classical_euler_on α T' v p ∧
      (∀ t ∈ Ico 0 T', axisymmetric_no_swirl (v t)) ∧
      ∀ t ∈ Ico 0 T, v t = u t :=

by exact ClockBarrier.Euler.general_coherent_on.exists_classical_extension



end ClockBarrier.Euler


