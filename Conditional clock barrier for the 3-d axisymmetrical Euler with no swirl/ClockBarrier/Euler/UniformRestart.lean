/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.RestartGluing
import ClockBarrier.Frozen.UniformLocalExistence
import Mathlib.Tactic.Linarith

/-! # Continuation from uniform bounds in the initial-data norms -/
public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Uniform bounds give a common restart lifespan; restarting sufficiently late
and using overlap uniqueness extends the original velocity. -/
theorem classical_euler_on.exists_extension_of_uniform_bounds
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p)
    (D : ℝ → E₃ →ᵇ (E₃ →L[ℝ] E₃)) (M : ℝ≥0)
    (hD : ∀ t ∈ Ico 0 T, ∀ x, HasFDerivAt (u t : E₃ → E₃) (D t x) x)
    (hbound : ∀ t ∈ Ico 0 T, ‖u t‖ ≤ M ∧ ‖D t‖ ≤ M ∧
      HolderWith M α (D t : E₃ → E₃ →L[ℝ] E₃) ∧
      (eLpNorm (u t : E₃ → E₃) 2 volume).toReal ≤ M) :
    ∃ T' : ℝ, T < T' ∧ ∃ v : ℝ → E₃ →ᵇ E₃, ∃ q : ℝ → E₃ → ℝ,
      classical_euler_on α T' v q ∧ ∀ t ∈ Ico 0 T, v t = u t := by
  obtain ⟨τ, hτ, hlocal⟩ := uniform_local_classical_euler α h.2.1 h.2.2.1 M
  let a : ℝ := max 0 (T - τ / 2)
  have ha : a ∈ Ico 0 T := ⟨le_max_left _ _, max_lt h.1 (by linarith)⟩
  have hreach : T < a + τ := by
    have he : T - τ / 2 ≤ a := le_max_right _ _
    linarith
  obtain ⟨hu, hd, hH, hL⟩ := hbound a ha
  have hz (x : E₃) : LinearMap.trace ℝ E₃ (D a x).toLinearMap = 0 := by
    rw [← (hD a ha x).fderiv]
    exact h.2.2.2.2.2.2.2.2.2.2 a ha x
  obtain ⟨v, q, hv, hi⟩ := hlocal (u a) (D a) (hD a ha) hu hd hH
    (h.2.2.2.2.2.1 a ha) hL hz
  obtain ⟨w, r, hw, heq⟩ := h.glue_restart hv ha hreach hi
  exact ⟨a + τ, hreach, w, r, hw, heq⟩

end ClockBarrier.Euler
