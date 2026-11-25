/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd.
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: focused imports, namespaces, module interface and pinned Mathlib compatibility.
-/
module
public import ClockBarrier.Analysis.SmoothWords
public import ClockBarrier.Analysis.SmoothL2Translation
public import ClockBarrier.Analysis.SolenoidalTranslation

/-! # Derivative words preserve the Helmholtz constraints
Port of Euler/OrdinaryWordConstraints.lean, using the existing canonical projection.
-/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Sobolev
open MeasureTheory InnerProductSpace ContinuousLinearMap SmoothL2Field DirectionalWords Solenoidal
open scoped ContDiff
local notation "Space" => EuclideanSpace ℝ (Fin 3)
theorem word_toLp_eq_orbit (A : SmoothL2Field Space) {n : ℕ} (w : Fin n → Fin 3) :
    (wordField A w).toLp = wordDerivative axis
      (fun a : Space => L2Translation.translation a A.toLp) w 0 := by
  apply Lp.ext
  filter_upwards [(wordField A w).toLp_ae,A.iteratedFDeriv_translation_ae n 0 (axis ∘ w)]
    with x ha hb
  rw [ha,wordField_field]
  simpa only [wordDerivative,Function.comp_def,add_zero] using hb.symm

theorem projection_word (A : SmoothL2Field Space) {n : ℕ} (w : Fin n → Fin 3) :
    solenoidalProjection (wordField A w).toLp = wordDerivative axis
      (fun a : Space => L2Translation.translation a (solenoidalProjection A.toLp)) w 0 := by
  rw [word_toLp_eq_orbit,← wordDerivative_comp_clm axis solenoidalProjection _ A.translation_contDiff]
  congr 2
  funext a
  exact (solenoidalProjection_translation a A.toLp).symm

theorem word_solenoidal (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace)
    {n : ℕ} (w : Fin n → Fin 3) : (wordField A w).toLp ∈ solenoidalSpace := by
  apply solenoidalSpace.starProjection_eq_self_iff.mp
  change solenoidalProjection (wordField A w).toLp = _
  rw [projection_word]
  have he : solenoidalProjection A.toLp=A.toLp := solenoidalSpace.starProjection_eq_self_iff.mpr hA
  rw [he,word_toLp_eq_orbit]

theorem word_gradient (A : SmoothL2Field Space) (hA : A.toLp ∈ gradientSpace)
    {n : ℕ} (w : Fin n → Fin 3) : (wordField A w).toLp ∈ gradientSpace := by
  apply (solenoidalProjection_eq_zero_iff _).mp
  rw [projection_word,(solenoidalProjection_eq_zero_iff _).mpr hA]
  simp only [map_zero]
  change (iteratedFDeriv ℝ n (0 : Space → L2) 0) (fun j => axis (w j))=0
  rw [iteratedFDeriv_zero]
  rfl

theorem word_pressure_pairing_zero (P U : SmoothL2Field Space)
    (hP : P.toLp ∈ gradientSpace) (hU : U.toLp ∈ solenoidalSpace)
    {n : ℕ} (w : Fin n → Fin 3) :
    ⟪(wordField P w).toLp,(wordField U w).toLp⟫_ℝ=0 :=
  pressure_pairing_zero (word_gradient P hP w) (word_solenoidal U hU w)

end ClockBarrier.Analysis.Sobolev
