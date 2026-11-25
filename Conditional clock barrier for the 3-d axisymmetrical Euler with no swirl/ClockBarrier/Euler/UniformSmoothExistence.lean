/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.SmoothBoundedContinuation
public import ClockBarrier.Euler.SmoothClassical
public import ClockBarrier.Euler.UniformShortTimeBounds

/-! # A common lifespan controlled only by the Hölder exponent and initial size

The exact smooth solutions are constructed by the local solver and repeated
H³-controlled restarts. The already proved Hölder estimates supply the
uniform gradient bound that prevents these restarts from accumulating.
-/
@[expose] public noncomputable section
namespace ClockBarrier.Euler.Smooth
open Set MeasureTheory ContinuousLinearMap ClockBarrier.Analysis
  Sobolev Solenoidal SmoothL2Field Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem exists_uniform_smooth_lifespan (α : ℝ≥0) (hα : 0 < α) (hα1 : α < 1) (M : ℝ≥0) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ R : ℝ≥0, 0 < R ∧
      ∀ A : SmoothL2Field Space, A.toLp ∈ solenoidalSpace →
        ‖finiteField A.derivative‖ ≤ (M : ℝ) →
        HolderWith M α (finiteField A.derivative : Space → Space →L[ℝ] Space) →
        ‖A.toLp‖ ≤ (M : ℝ) →
      ∃ U : ℝ → SmoothL2Field Space,
        U 0 = A ∧ (∀ n, Continuous (fun t => (U t).jetLp n)) ∧
        (∀ n, ∀ t ∈ Icc 0 τ, HasDerivWithinAt (fun r => (U r).jetLp n)
          ((rhs (U t)).jetLp n) (Icc 0 τ) t) ∧
        (∀ t ∈ Icc 0 τ, (U t).toLp ∈ solenoidalSpace) ∧
        classical_euler_on α τ (fun t => finiteField (U t)) (fun t => pressure (U t)) ∧
        ∀ t ∈ Ico 0 τ,
          ‖finiteField (U t)‖ ≤ (R : ℝ) ∧ ‖finiteField (U t).derivative‖ ≤ (R : ℝ) ∧
          HolderWith R α (finiteField (U t).derivative : Space → Space →L[ℝ] Space) ∧
          ‖(U t).toLp‖ ≤ (M : ℝ) := by
  obtain ⟨τ, hτ, R, hR, hbounds⟩ := exists_uniform_short_time_bounds α hα hα1 M
  refine ⟨τ, hτ, R, hR, ?_⟩
  intro A hAs hDn hDH hE
  have hdata (S : ℝ) (U : ℝ → SmoothL2Field Space) (hi : U 0 = A)
      (hcl : classical_euler_on α S (fun t => finiteField (U t)) (fun t => pressure (U t))) :=
    hbounds S (fun t => finiteField (U t)) (fun t => pressure (U t)) hcl (finiteField A.derivative)
      (fun x => by
        rw [hi, show (finiteField A : Space → Space) = A.field from funext (finiteField_apply A), finiteField_apply]
        exact (A.smooth.differentiable (by simp) x).hasFDerivAt)
      hDn hDH (by
        rw [hi, show (finiteField A : Space → Space) = A.field from funext (finiteField_apply A)]
        exact (Lp.norm_toLp A.field A.memLp).symm.trans_le hE)
  obtain ⟨U, hi, hc, hd, hs⟩ := exists_smooth_on_of_gradient_bound A hAs τ R hτ R.coe_nonneg
    (fun S hS hSτ V hi hc hd hs => by
      have hcl := classical_of_smooth α hα hα1 S hS V hc hd hs
      obtain ⟨D, _, hD, hb⟩ := hdata S V hi hcl
      intro t ht x
      have he := (hD t ht x).fderiv
      have hu : (finiteField (V t) : Space → Space) = (V t).field := funext (finiteField_apply _)
      rw [hu] at he
      rw [he]
      exact ((D t).norm_coe_le_norm x).trans (hb t ht (ht.2.le.trans hSτ)).2.1)
  have hcl := classical_of_smooth α hα hα1 τ hτ U hc hd hs
  refine ⟨U, hi, hc, hd, hs, hcl, ?_⟩
  obtain ⟨D, _, hD, hb⟩ := hdata τ U hi hcl
  intro t ht
  have he : D t = finiteField (U t).derivative := by
    apply BoundedContinuousFunction.ext
    intro x
    have hh := (hD t ht x).fderiv
    have hu : (finiteField (U t) : Space → Space) = (U t).field := funext (finiteField_apply _)
    rw [hu] at hh
    exact hh.symm.trans (finiteField_apply (U t).derivative x).symm
  have hbt := hb t ht ht.2.le
  rw [he] at hbt
  refine ⟨hbt.1, hbt.2.1, hbt.2.2.1, ?_⟩
  have hu : (finiteField (U t) : Space → Space) = (U t).field := funext (finiteField_apply _)
  rw [hu] at hbt
  exact (Lp.norm_toLp (U t).field (U t).memLp).trans_le hbt.2.2.2

end ClockBarrier.Euler.Smooth
