/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.GeneralCoherent
import ClockBarrier.Euler.BKMIntegrability
import ClockBarrier.Euler.BKMContinuation
import ClockBarrier.Euler.SymmetryPreservation

/-! # Theorem 1.1: continuation from general coherence

The clock and transport estimates supply the BKM integral. The proved
continuation criterion extends the actual classical velocity; uniqueness
preserves initial axisymmetry and absence of swirl beyond the old lifespan.
-/
public section
namespace ClockBarrier.Euler
open Set
open scoped NNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Uniform general coherence gives an actual classical extension. Coherence
of the extended solution is not an assumption or a conclusion. -/
theorem general_coherent_on.exists_classical_extension :
  ∀ {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃},
    (1 / 3 : ℝ) ≤ (α : ℝ) → general_coherent_on α T u →
    ∃ T' : ℝ, T < T' ∧ ∃ v : ℝ → E₃ →ᵇ E₃, ∃ p : ℝ → E₃ → ℝ,
      classical_euler_on α T' v p ∧
      (∀ t ∈ Ico 0 T', axisymmetric_no_swirl (v t)) ∧
      ∀ t ∈ Ico 0 T, v t = u t := by
  intro α T u hα hcoh
  obtain ⟨p, h, W, _, hW, _, hi, _⟩ :=
    hcoh.exists_finite_vorticity_eLpNorm_integral hα
  obtain ⟨T', hT', v, q, hv, heq⟩ := h.exists_extension_of_bkm W hW hi
  obtain ⟨_, _, haxis, _⟩ := hcoh
  have hzero : v 0 = u 0 := heq 0 ⟨le_rfl, h.1⟩
  refine ⟨T', hT', v, q, hv, ?_, heq⟩
  intro t ht
  exact hv.axisymmetric_no_swirl (by rw [hzero]; exact haxis 0 ⟨le_rfl, h.1⟩) ht

end ClockBarrier.Euler
