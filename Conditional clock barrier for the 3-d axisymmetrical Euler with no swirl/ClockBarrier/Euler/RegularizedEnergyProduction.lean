/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd.
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: concrete regularizer and ordinary spatial field interface.
-/
module
public import ClockBarrier.Analysis.RegularizedWords
public import ClockBarrier.Analysis.SmoothTameEnergy
public import ClockBarrier.Euler.RegularizedSmoothTrajectory

/-! # Uniform spatial energy production of the concrete regularized Euler equation -/
@[expose] public noncomputable section
namespace ClockBarrier.Euler.Regularized
open MeasureTheory InnerProductSpace ContinuousLinearMap ClockBarrier.Analysis
  Solenoidal SmoothL2Field Sobolev Finset
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem advection_toLp (n : ℕ) (u : L2) :
    (advectionField (regularizedSmoothField n u) (regularizedSmoothField n u)).toLp =
      advection n u u := by
  apply Lp.ext
  filter_upwards [(advectionField (regularizedSmoothField n u)
    (regularizedSmoothField n u)).toLp_ae, advection_ae n u u] with x ha hb
  rw [ha, hb, advectionField_field, regularizedSmoothField_field,
    (regularizedField_hasFDerivAt n u x).fderiv]

theorem smoothRhs_eq (n : ℕ) (A : SmoothL2Field E₃) :
    smoothRhs n A = fieldNeg (regularizedSmoothField n
      (advectionField (regularizedSmoothField n A.toLp) (regularizedSmoothField n A.toLp)).toLp) := by
  rw [advection_toLp]
  apply field_ext
  funext x
  simp only [smoothRhs, scaleField_field, fieldNeg_field, neg_smul, one_smul]

theorem smoothRhs_pairing (k : ℕ) (A : SmoothL2Field E₃) {n : ℕ} (w : Fin n → Fin 3) :
    ⟪(wordField A w).toLp, (wordField (smoothRhs k A) w).toLp⟫_ℝ =
      ⟪(wordField (regularizedSmoothField k A.toLp) w).toLp,
        (wordField (fieldNeg (advectionField (regularizedSmoothField k A.toLp)
          (regularizedSmoothField k A.toLp))) w).toLp⟫_ℝ := by
  simp only [smoothRhs_eq, wordField_neg, toLp_fieldNeg, inner_neg_right,
    regularizedSmoothField_word, regularizerMap_symmetric]

theorem smoothRhs_energy (k : ℕ) (A : SmoothL2Field E₃) (m : ℕ) (hm : 3 ≤ m)
    (M : ℝ) (hM : WordBound 3 M A) :
    integerEnergyProduction m A (smoothRhs k A) ≤ tameEnergyConstant m * M * wordEnergy m A := by
  let B := regularizedSmoothField k A.toLp
  have he : fieldNeg (advectionField B B) = eulerRhs B (fieldSub B B) := by
    apply field_ext
    funext x
    simp only [fieldNeg_field, advectionField_field, eulerRhs_field, fieldSub_field, sub_self, sub_zero]
  have hp : (fieldSub B B).toLp ∈ gradientSpace := by
    rw [toLp_fieldSub, sub_self]
    exact gradientSpace.zero_mem
  have hb : B.toLp ∈ solenoidalSpace := by
    rw [regularizedSmoothField_toLp]
    exact regularizerMap_mem _ _
  have hx : integerEnergyProduction m A (smoothRhs k A) =
      integerEnergyProduction m B (eulerRhs B (fieldSub B B)) := by
    simp only [integerEnergyProduction, smoothRhs_pairing, ← he, B]
  rw [hx]
  apply (integer_energy_tame B (fieldSub B B) m hm M
    (regularizedSmoothField_wordBound k A 3 M hM)
    (regularizedField_divergence k A.toLp) hb hp).trans
  exact mul_le_mul_of_nonneg_left (regularizedSmoothField_energy_le k A m)
    (mul_nonneg (tameEnergyConstant_nonneg m) (wordBound_nonneg hM))

end ClockBarrier.Euler.Regularized
