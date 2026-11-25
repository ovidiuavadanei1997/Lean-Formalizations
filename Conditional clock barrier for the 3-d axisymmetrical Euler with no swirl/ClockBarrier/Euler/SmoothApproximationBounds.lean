/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.UniformShortTimeBounds
public import ClockBarrier.Analysis.SmoothInitialData

/-! # Uniform Hölder bounds for exact Euler solutions from smoothed data

The time and bound precede the initial datum and the smoothing index. This is
an a priori application to actual Euler solutions. Their construction and
continuation to this time are separate obligations.
-/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory Analysis.Solenoidal
open scoped NNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- All exact Euler solutions from these mollified data obey the same bound
up to the same time, wherever they are defined. No regularized PDE is used. -/
theorem exists_uniform_mollified_solution_bounds :
    ∀ (α : ℝ≥0), 0 < α → α < 1 → ∀ M : ℝ≥0,
    ∃ τ : ℝ, 0 < τ ∧ ∃ R : ℝ≥0, 0 < R ∧
      ∀ (u₀ : E₃ →ᵇ E₃) (D₀ : E₃ →ᵇ (E₃ →L[ℝ] E₃))
        (hLp : MemLp (u₀ : E₃ → E₃) 2 volume),
        (∀ x, HasFDerivAt (u₀ : E₃ → E₃) (D₀ x) x) →
        ‖D₀‖ ≤ (M : ℝ) → HolderWith M α (D₀ : E₃ → E₃ →L[ℝ] E₃) →
        (eLpNorm (u₀ : E₃ → E₃) 2 volume).toReal ≤ (M : ℝ) →
        ∀ (n : ℕ) (T : ℝ) (u : ℝ → E₃ →ᵇ E₃) (p : ℝ → E₃ → ℝ),
          classical_euler_on α T u p → u 0 = mollifierField n (hLp.toLp u₀) →
          ∃ D : ℝ → E₃ →ᵇ (E₃ →L[ℝ] E₃), ContinuousOn D (Ico 0 T) ∧
            (∀ t ∈ Ico 0 T, ∀ x, HasFDerivAt (u t : E₃ → E₃) (D t x) x) ∧
            ∀ t ∈ Ico 0 T, t ≤ τ →
              ‖u t‖ ≤ (R : ℝ) ∧ ‖D t‖ ≤ (R : ℝ) ∧
              HolderWith R α (D t : E₃ → E₃ →L[ℝ] E₃) ∧
              (eLpNorm (u t : E₃ → E₃) 2 volume).toReal ≤ (M : ℝ) := by
  intro α hα hα1 M
  obtain ⟨τ, hτ, R, hR, hbound⟩ := exists_uniform_short_time_bounds α hα hα1 M
  refine ⟨τ, hτ, R, hR, ?_⟩
  intro u₀ D₀ hLp hD hDn hDH hE n T u p h hi
  apply hbound T u p h (mollifierDerivative n (hLp.toLp u₀))
  · simpa only [hi] using mollifierField_hasFDerivAt n (hLp.toLp u₀)
  · exact (mollifierDerivative_toLp_norm_le n u₀ D₀ hLp hD).trans hDn
  · exact mollifierDerivative_toLp_holder n u₀ D₀ hLp hD hDH
  · have he0 : (eLpNorm (u 0 : E₃ → E₃) 2 volume).toReal ≤
        (eLpNorm (u₀ : E₃ → E₃) 2 volume).toReal := by
      simpa only [hi, Lp.norm_toLp] using mollifierField_energy_le n (hLp.toLp u₀)
    exact he0.trans hE

end ClockBarrier.Euler
