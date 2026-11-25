/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # Volume bounds from rotated Cartesian boxes -/

public section
namespace ClockBarrier.Analysis
open Set MeasureTheory
open scoped ENNReal
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Any set with fixed rotated coordinate bounds has at most the box volume. -/
theorem volume_le_rotated_box (aStar : E₃) (V : E₃ ≃ₗᵢ[ℝ] E₃)
    (r : Fin 3 → ℝ) {S : Set E₃}
    (hS : ∀ a ∈ S, ∀ i, |V.symm (a - aStar) i| ≤ r i) :
    volume S ≤ ∏ i, ENNReal.ofReal (2 * r i) := by
  have hp := (PiLp.volume_preserving_ofLp (Fin 3)).comp
    (V.symm.measurePreserving.comp (measurePreserving_add_right volume (-aStar)))
  calc
    volume S ≤ volume ((fun a : E₃ => (V.symm (a - aStar)).ofLp) ⁻¹'
        (Set.pi univ (fun i => Icc (-r i) (r i)))) :=
      measure_mono (fun a ha i _ => abs_le.mp (hS a ha i))
    _ = volume (Set.pi univ (fun i => Icc (-r i) (r i))) :=
      hp.measure_preimage
        (MeasurableSet.pi (Set.to_countable univ) (fun _ _ => measurableSet_Icc)).nullMeasurableSet
    _ = _ := by
      rw [volume_pi_pi]
      simp only [Real.volume_Icc, sub_neg_eq_add, two_mul]

/-- The enclosing box supplies a fixed volume factor for a three-dimensional shell. -/
theorem volume_le_rotated_shell_box (aStar : E₃) (V : E₃ ≃ₗᵢ[ℝ] E₃)
    (r : Fin 3 → ℝ) (hr : ∀ i, 0 ≤ r i) {S : Set E₃}
    (hS : ∀ a ∈ S, ∀ i, |V.symm (a - aStar) i| ≤ 2 * r i) :
    volume S ≤ ENNReal.ofReal (64 * r 0 * r 1 * r 2) := by
  refine (volume_le_rotated_box aStar V (fun i => 2 * r i) hS).trans_eq ?_
  rw [Fin.prod_univ_three, ← ENNReal.ofReal_mul (by have := hr 0; positivity : 0 ≤ 2 * (2 * r 0)),
    ← ENNReal.ofReal_mul (by have := hr 0; have := hr 1; positivity : 0 ≤ 2 * (2 * r 0) * (2 * (2 * r 1)))]
  congr 1
  ring

end ClockBarrier.Analysis
