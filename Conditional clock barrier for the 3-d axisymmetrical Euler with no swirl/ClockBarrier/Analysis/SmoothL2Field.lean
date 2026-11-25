/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd,
Euler/LpSmoothField.lean, Euler/LpSmoothFieldJets.lean,
Euler/OrdinarySmoothWords.lean and Euler/OrdinaryEulerUniqueness.lean. See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: ordinary Euclidean carrier, focused imports and module interface.
-/
module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Smooth fields with all spatial derivatives in L²

This is the ordinary spatial-data carrier used by the smooth Euler
construction. It contains only the actual function and its regularity.
-/

@[expose] public noncomputable section
namespace ClockBarrier.Analysis
open MeasureTheory Filter
open scoped ContDiff
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
universe u
variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The hypotheses are ordinary derivatives of a concrete smooth function, not translation-orbit regularity. -/
structure SmoothL2Field (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  field : E₃ → V
  smooth : ContDiff ℝ ∞ field
  integrable : ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n field) 2 volume

namespace SmoothL2Field

theorem memLp (A : SmoothL2Field V) : MemLp A.field 2 volume :=
  (A.integrable 0).congr_norm A.smooth.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun _ => norm_iteratedFDeriv_zero))

def toLp (A : SmoothL2Field V) : Lp V 2 (volume : Measure E₃) := A.memLp.toLp A.field

theorem toLp_ae (A : SmoothL2Field V) : A.toLp =ᵐ[volume] A.field := A.memLp.coeFn_toLp

def jetLp (A : SmoothL2Field V) (n : ℕ) : Lp (E₃ [×n]→L[ℝ] V) 2 (volume : Measure E₃) :=
  (A.integrable n).toLp (iteratedFDeriv ℝ n A.field)

def derivative (A : SmoothL2Field V) : SmoothL2Field (E₃ →L[ℝ] V) where
  field := fderiv ℝ A.field
  smooth := A.smooth.fderiv_right (m := ∞) (by simp)
  integrable n := (A.integrable (n+1)).congr_norm
    ((A.smooth.fderiv_right (m := ∞) (by simp)).continuous_iteratedFDeriv (m := n) (WithTop.coe_le_coe.mpr le_top)).aestronglyMeasurable
    (Eventually.of_forall (fun x => (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := A.field) (n := n) (x := x)).symm))


theorem jetLp_ae (A : SmoothL2Field V) (n : ℕ) :
    A.jetLp n =ᵐ[volume] iteratedFDeriv ℝ n A.field := (A.integrable n).coeFn_toLp

@[ext] theorem field_ext {A B : SmoothL2Field V} (h : A.field = B.field) : A = B := by
  cases A
  cases B
  cases h
  rfl

theorem toLp_injective : Function.Injective (toLp (V := V)) := by
  intro A B h
  apply field_ext
  exact Measure.eq_of_ae_eq (A.toLp_ae.symm.trans (h ▸ B.toLp_ae))
    A.smooth.continuous B.smooth.continuous

end SmoothL2Field
end ClockBarrier.Analysis
