/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd.
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: focused imports, namespaces, module interface and pinned Mathlib compatibility.
-/
module
public import ClockBarrier.Analysis.SmoothL2Algebra
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Tactic.Linarith

/-! # Integration by parts for smooth L² fields
Port of the pairing lemmas in Euler/OrdinaryL2Integration.lean.
-/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Sobolev
open MeasureTheory InnerProductSpace ContinuousLinearMap SmoothL2Field
open scoped ContDiff ENNReal
local notation "Space" => EuclideanSpace ℝ (Fin 3)
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
theorem field_inner_integrable (A B : SmoothL2Field V) :
    Integrable (fun x => ⟪A.field x,B.field x⟫_ℝ) := by
  apply (MeasureTheory.L2.integrable_inner A.toLp B.toLp).congr
  filter_upwards [A.toLp_ae,B.toLp_ae] with x ha hb
  rw [ha,hb]

theorem field_inner (A B : SmoothL2Field V) :
    ⟪A.toLp,B.toLp⟫_ℝ=∫ x,⟪A.field x,B.field x⟫_ℝ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [A.toLp_ae,B.toLp_ae] with x ha hb
  rw [ha,hb]

theorem field_directional_ibp (A B : SmoothL2Field V) (v : Space) :
    (∫ x,⟪fderiv ℝ A.field x v,B.field x⟫_ℝ) =
      -∫ x,⟪A.field x,fderiv ℝ B.field x v⟫_ℝ := by
  have h := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (μ := (volume : Measure Space)) (B := innerSL ℝ) (v := v)
    (field_inner_integrable (A.directionalField v) B)
    (field_inner_integrable A (B.directionalField v)) (field_inner_integrable A B)
    (fun x _ => A.smooth.differentiable (by simp) x)
    (fun x _ => B.smooth.differentiable (by simp) x)
  change (∫ x,⟪A.field x,fderiv ℝ B.field x v⟫_ℝ)=
    -∫ x,⟪fderiv ℝ A.field x v,B.field x⟫_ℝ at h
  linarith

theorem field_directional_inner (A B : SmoothL2Field V) (v : Space) :
    ⟪(A.directionalField v).toLp,B.toLp⟫_ℝ =
      -⟪A.toLp,(B.directionalField v).toLp⟫_ℝ := by
  rw [field_inner,field_inner]
  exact field_directional_ibp A B v

theorem field_zero_of_toLp_zero (A : SmoothL2Field V) (h : A.toLp=0) : A.field=0 := by
  have hae : A.field=ᵐ[volume] 0 := A.toLp_ae.symm.trans (by rw [h]; exact Lp.coeFn_zero V 2 volume)
  exact Measure.eq_of_ae_eq hae A.smooth.continuous continuous_const

end ClockBarrier.Analysis.Sobolev
