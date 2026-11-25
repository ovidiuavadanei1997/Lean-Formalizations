/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.GeneralCoherent
import ClockBarrier.Euler.GeneralDriver

/-! # Proposition 4.2: the uniform general-label driver estimate

Source: arXiv:2605.31587v3, Proposition 4.2, with the general coherence class.
-/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped Topology NNReal InnerProductSpace BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)


/-- Uniform strain control on the complete smallest left singular eigenspace.
The same positive integrable bound and positive constant work for every label,
time, unit eigenvector, and initialized Euler flow. -/
theorem general_driver_bound :
  ∀ {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃},
    (1 / 3 : ℝ) ≤ (α : ℝ) → general_coherent_on α T u →
    ∃ B : ℝ → ℝ, ∃ C : ℝ,
      IntegrableOn B (Ico 0 T) volume ∧
      (∀ t ∈ Ico 0 T, 0 < B t) ∧ 0 < C ∧
      ∀ Φ : ℝ → E₃ → E₃,
        (∀ x, Φ 0 x = x) →
        (∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T)) →
        (∀ x, ∀ t ∈ Ico 0 T,
          HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t) →
        ∀ a : E₃, ∀ t ∈ Ico 0 T,
          let F := fderiv ℝ (Φ t) a
          let ν := F.toLinearMap.singularValues 2
          let L := fderiv ℝ (u t) (Φ t a)
          let S := (1 / 2 : ℝ) • (L + L.adjoint)
          ∀ e : E₃, ‖e‖ = 1 → F (F.adjoint e) = ν ^ 2 • e →
            |⟪e, S e⟫_ℝ| ≤ B t + C * ν ^ ((3 * (α : ℝ) - 1) / 2) :=

by
  exact ClockBarrier.Euler.general_coherent_on.exists_uniform_general_driver_bound



end ClockBarrier.Euler


