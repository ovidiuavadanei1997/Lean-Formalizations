/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.UniformSmoothExistence
public import ClockBarrier.Analysis.SmoothInitialData

/-! # Concrete exact smooth Euler approximations on one common lifespan -/
@[expose] public noncomputable section
namespace ClockBarrier.Euler.Smooth
open Set MeasureTheory ContinuousLinearMap ClockBarrier.Analysis
  Sobolev Solenoidal SmoothL2Field Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem finiteField_mollified (n : ℕ) (u : L2) :
    finiteField (mollifiedSmoothField n u) = mollifierField n u := by
  apply BoundedContinuousFunction.ext
  intro x
  exact finiteField_apply _ x

theorem finiteField_mollified_derivative (n : ℕ) (u : L2) :
    finiteField (mollifiedSmoothField n u).derivative = mollifierDerivative n u := by
  apply BoundedContinuousFunction.ext
  intro x
  rw [finiteField_apply]
  exact (mollifierField_hasFDerivAt n u x).fderiv

/-- The lifespan and uniform C¹,α bound are chosen before the initial datum and
before either approximation index. Each trajectory solves the exact Euler PDE. -/
theorem exists_exact_mollified_family (α : ℝ≥0) (hα : 0 < α) (hα1 : α < 1) (M : ℝ≥0) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ R : ℝ≥0, 0 < R ∧
      ∀ (u₀ : Space →ᵇ Space) (D₀ : Space →ᵇ (Space →L[ℝ] Space))
        (hLp : MemLp (u₀ : Space → Space) 2 volume),
        (∀ x, HasFDerivAt (u₀ : Space → Space) (D₀ x) x) →
        (∀ x, LinearMap.trace ℝ Space (D₀ x).toLinearMap = 0) →
        ‖D₀‖ ≤ (M : ℝ) → HolderWith M α (D₀ : Space → Space →L[ℝ] Space) →
        (eLpNorm (u₀ : Space → Space) 2 volume).toReal ≤ (M : ℝ) →
      ∃ U : ℕ → ℝ → SmoothL2Field Space, ∀ n,
        U n 0 = mollifiedSmoothField n (hLp.toLp u₀) ∧
        (∀ m, Continuous (fun t => (U n t).jetLp m)) ∧
        (∀ m, ∀ t ∈ Icc 0 τ, HasDerivWithinAt (fun r => (U n r).jetLp m)
          ((rhs (U n t)).jetLp m) (Icc 0 τ) t) ∧
        (∀ t ∈ Icc 0 τ, (U n t).toLp ∈ solenoidalSpace) ∧
        classical_euler_on α τ (fun t => finiteField (U n t)) (fun t => pressure (U n t)) ∧
        ∀ t ∈ Ico 0 τ,
          ‖finiteField (U n t)‖ ≤ (R : ℝ) ∧ ‖finiteField (U n t).derivative‖ ≤ (R : ℝ) ∧
          HolderWith R α (finiteField (U n t).derivative : Space → Space →L[ℝ] Space) ∧
          ‖(U n t).toLp‖ ≤ (M : ℝ) := by
  obtain ⟨τ, hτ, R, hR, hex⟩ := exists_uniform_smooth_lifespan α hα hα1 M
  refine ⟨τ, hτ, R, hR, ?_⟩
  intro u₀ D₀ hLp hD htr hDn hDH hE
  have hs := toLp_mem_solenoidal_of_hasFDerivAt u₀ D₀ hLp hD htr
  have hn (n : ℕ) := hex (mollifiedSmoothField n (hLp.toLp u₀))
    (mollifiedSmoothField_solenoidal n _ hs)
    (by rw [finiteField_mollified_derivative]; exact (mollifierDerivative_toLp_norm_le n u₀ D₀ hLp hD).trans hDn)
    (by rw [finiteField_mollified_derivative]; exact mollifierDerivative_toLp_holder n u₀ D₀ hLp hD hDH)
    (by rw [mollifiedSmoothField_toLp]; exact (mollify_norm_le n _).trans ((Lp.norm_toLp _ hLp).trans_le hE))
  choose U hU using hn
  exact ⟨U, hU⟩

end ClockBarrier.Euler.Smooth
