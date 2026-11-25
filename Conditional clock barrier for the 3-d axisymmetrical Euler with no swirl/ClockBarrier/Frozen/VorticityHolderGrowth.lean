/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.VorticityHolderGrowth

/-! # Vorticity Hölder growth and uniform bounds under BKM integrability

Supporting theorem for classical Euler continuation; see THEOREM_GUIDE.md.
-/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)


/-- The actual vorticity has exponential Hölder and supremum growth in the
integrated velocity gradient. Finite BKM integral gives uniform full spatial
`C_b^{1,α}` and `L²` bounds on the entire preterminal interval. -/
theorem vorticity_holder_growth_and_bkm_bounds :
  ∀ (α : ℝ≥0), 0 < α → α < 1 →
  ∃ C : ℝ≥0, 0 < C ∧
    ∀ (T : ℝ) (u : ℝ → E₃ →ᵇ E₃) (p : ℝ → E₃ → ℝ)
      (h : classical_euler_on α T u p),
    ∃ D : ℝ → E₃ →ᵇ (E₃ →L[ℝ] E₃), ∃ W : ℝ → E₃ →ᵇ E₃,
      ContinuousOn D (Ico 0 T) ∧ ContinuousOn W (Ico 0 T) ∧
      (∀ t ∈ Ico 0 T, ∀ x, HasFDerivAt (u t : E₃ → E₃) (D t x) x) ∧
      (∀ t, ∀ ht : t ∈ Ico 0 T, ∀ x,
        W t x = vorticity (u t) (h.cartesian_partials t ht) x) ∧
      (∀ H₀ : ℝ≥0, HolderWith H₀ α (W 0 : E₃ → E₃) →
        ∀ t ∈ Ico 0 T,
          HolderWith (H₀ * ⟨Real.exp ((C : ℝ) * ∫ s in 0..t, ‖D s‖),
            (Real.exp_pos _).le⟩) α (W t : E₃ → E₃)) ∧
      (∀ t ∈ Ico 0 T,
        ‖W t‖ ≤ ‖W 0‖ * Real.exp (∫ s in 0..t, ‖D s‖)) ∧
      (IntegrableOn (fun t => ‖W t‖) (Ico 0 T) volume →
        ∃ M : ℝ≥0, 0 < M ∧ ∀ t ∈ Ico 0 T,
          ‖u t‖ ≤ M ∧ ‖D t‖ ≤ M ∧ ‖W t‖ ≤ M ∧
          HolderWith M α (D t : E₃ → E₃ →L[ℝ] E₃) ∧
          HolderWith M α (W t : E₃ → E₃) ∧
          (eLpNorm (u t : E₃ → E₃) 2 volume).toReal ≤ M) :=

by exact ClockBarrier.Euler.exists_vorticity_holder_growth_and_bkm_bounds



end ClockBarrier.Euler


