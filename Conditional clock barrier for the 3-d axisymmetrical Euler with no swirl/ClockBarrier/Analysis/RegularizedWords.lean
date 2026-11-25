/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd.
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: concrete regularizer and ordinary spatial field interface.
-/
module
public import ClockBarrier.Analysis.RegularizedJets
public import ClockBarrier.Analysis.SmoothWordConstraints

/-! # Spatial derivative words commute with the concrete regularizer -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Solenoidal
open MeasureTheory ContinuousLinearMap SmoothL2Field Sobolev DirectionalWords Finset
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem regularizedSmoothField_word (n : ℕ) (A : SmoothL2Field E₃)
    {m : ℕ} (w : Fin m → Fin 3) :
    (wordField (regularizedSmoothField n A.toLp) w).toLp =
      regularizerMap n (wordField A w).toLp := by
  rw [word_toLp_eq_orbit, regularizedSmoothField_toLp, word_toLp_eq_orbit,
    ← wordDerivative_comp_clm axis (regularizerMap n) _ A.translation_contDiff]
  congr 2
  funext a
  exact regularizerMap_translation n a A.toLp

theorem regularizedSmoothField_wordBound (n : ℕ) (A : SmoothL2Field E₃)
    (s : ℕ) (M : ℝ) (hA : WordBound s M A) :
    WordBound s M (regularizedSmoothField n A.toLp) := by
  intro m hm w
  rw [regularizedSmoothField_word]
  exact (regularizerMap_contract n _).trans (hA m hm w)

theorem regularizedSmoothField_energy_le (n : ℕ) (A : SmoothL2Field E₃) (m : ℕ) :
    wordEnergy m (regularizedSmoothField n A.toLp) ≤ wordEnergy m A := by
  unfold wordEnergy
  apply sum_le_sum
  intro k _
  apply sum_le_sum
  intro w _
  rw [regularizedSmoothField_word]
  exact pow_le_pow_left₀ (norm_nonneg _) (regularizerMap_contract n _) 2

end ClockBarrier.Analysis.Solenoidal
