/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.UniformLocalExistence

/-! # Uniform local existence in the Holder and finite-energy class

Supporting theorem for classical Euler continuation; see THEOREM_GUIDE.md.
-/

public section
namespace ClockBarrier.Euler
open MeasureTheory
open scoped NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)


/-- A lifespan uniform over bounded divergence-free `C_b^{1,α} ∩ L²` initial
data, with the temporal convention and the same Holder exponent. -/
theorem uniform_local_classical_euler :
  ∀ (α : ℝ≥0), 0 < α → α < 1 →
  ∀ M : ℝ≥0, ∃ τ : ℝ, 0 < τ ∧
    ∀ (u₀ : E₃ →ᵇ E₃) (D₀ : E₃ →ᵇ (E₃ →L[ℝ] E₃)),
      (∀ x, HasFDerivAt (u₀ : E₃ → E₃) (D₀ x) x) →
      ‖u₀‖ ≤ (M : ℝ) → ‖D₀‖ ≤ (M : ℝ) →
      HolderWith M α (D₀ : E₃ → E₃ →L[ℝ] E₃) →
      MemLp (u₀ : E₃ → E₃) 2 volume →
      (eLpNorm (u₀ : E₃ → E₃) 2 volume).toReal ≤ (M : ℝ) →
      (∀ x, LinearMap.trace ℝ E₃ (D₀ x).toLinearMap = 0) →
      ∃ v : ℝ → E₃ →ᵇ E₃, ∃ p : ℝ → E₃ → ℝ,
        classical_euler_on α τ v p ∧ v 0 = u₀ :=

by exact ClockBarrier.Euler.exists_uniform_local_classical_euler



end ClockBarrier.Euler


