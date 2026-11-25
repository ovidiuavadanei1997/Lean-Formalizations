/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.GeneralVorticityBound
import ClockBarrier.Analysis.BoundedLInfinity

/-! # The essential-supremum integrability premise of BKM

This module proves the actual vorticity has a finite time integral of its
essential L∞ norm. It does not assert an Euler continuation theorem.
-/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped ENNReal NNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- General coherence supplies the precise finite essential-L∞ vorticity
integral, with the bounded continuous representative identified everywhere. -/
theorem general_coherent_on.exists_finite_vorticity_eLpNorm_integral
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃}
    (hα : (1 / 3 : ℝ) ≤ (α : ℝ)) (hcoh : general_coherent_on α T u) :
    ∃ p : ℝ → E₃ → ℝ, ∃ h : classical_euler_on α T u p,
    ∃ W : ℝ → E₃ →ᵇ E₃,
      ContinuousOn W (Ico 0 T) ∧
      (∀ t, ∀ ht : t ∈ Ico 0 T, ∀ x,
        W t x = vorticity (u t) (h.cartesian_partials t ht) x) ∧
      (∀ t ∈ Ico 0 T, eLpNorm (W t) ∞ volume < ∞) ∧
      IntegrableOn (fun t => (eLpNorm (W t) ∞ volume).toReal) (Ico 0 T) volume ∧
      (∫⁻ t in Ico 0 T, eLpNorm (W t) ∞ volume) < ∞ := by
  obtain ⟨_, _, _, p, h, W, hW, heq, _, hi, _⟩ :=
    hcoh.exists_uniform_deformation_vorticity_bounds hα
  refine ⟨p, h, W, hW, heq, fun t _ => (W t).memLp_top.eLpNorm_lt_top, ?_, ?_⟩
  · simpa only [Analysis.eLpNorm_top_eq_enorm_bounded, toReal_enorm] using hi
  · simpa only [Analysis.eLpNorm_top_eq_enorm_bounded, HasFiniteIntegral, enorm_norm]
      using hi.hasFiniteIntegral

end ClockBarrier.Euler
