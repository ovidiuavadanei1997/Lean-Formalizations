/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.SmoothConvergence
public import ClockBarrier.Analysis.SmoothPressurePotential
public import ClockBarrier.Analysis.SmoothTimeEvaluation

/-! # The ordinary projected Euler equation with actual scalar pressure -/
@[expose] public noncomputable section
namespace ClockBarrier.Euler.Smooth
open MeasureTheory InnerProductSpace ContinuousLinearMap ClockBarrier.Analysis
  Sobolev Solenoidal SmoothL2Field SmoothPressure Filter Topology
open scoped ContDiff
local notation "Space" => EuclideanSpace ℝ (Fin 3)

def rhs (A : SmoothL2Field Space) : SmoothL2Field Space :=
  scaleField (-1) (solenoidalField (advectionField A A))

def pressureForce (A : SmoothL2Field Space) : SmoothL2Field Space :=
  fieldSub (solenoidalField (advectionField A A)) (advectionField A A)

def pressure (A : SmoothL2Field Space) : Space → ℝ := radialPotential (pressureForce A).field

theorem rhs_toLp (A : SmoothL2Field Space) :
    (rhs A).toLp = -solenoidalProjection (advectionField A A).toLp := by
  simp only [rhs, scaleField_toLp, neg_smul, one_smul, solenoidalField_toLp]

theorem continuous_rhs : Continuous rhs :=
  (continuous_scaleField (-1)).comp (continuous_solenoidalField.comp continuous_self_advection)

theorem continuous_pressureForce : Continuous pressureForce := by
  apply continuous_smooth_iff.mpr
  intro n
  simp only [pressureForce, jetLp_fieldSub]
  exact ((continuous_smooth_jet n).comp (continuous_solenoidalField.comp continuous_self_advection)).sub
    ((continuous_smooth_jet n).comp continuous_self_advection)

theorem pressureForce_gradient (A : SmoothL2Field Space) :
    (pressureForce A).toLp ∈ gradientSpace := by
  rw [pressureForce, toLp_fieldSub, solenoidalField_toLp]
  convert! gradientSpace.neg_mem (sub_solenoidalProjection_mem_gradient (advectionField A A).toLp) using 1
  rw [neg_sub]

theorem pressure_smooth (A : SmoothL2Field Space) : ContDiff ℝ ∞ (pressure A) :=
  (gradientSpace_radial_potential _ (pressureForce_gradient A) _
    (pressureForce A).toLp_ae (pressureForce A).smooth).1

theorem pressure_zero (A : SmoothL2Field Space) : pressure A 0 = 0 := radialPotential_zero _

theorem pressure_gradient (A : SmoothL2Field Space) (x : Space) :
    gradient (pressure A) x = (pressureForce A).field x :=
  (gradientSpace_radial_potential _ (pressureForce_gradient A) _
    (pressureForce A).toLp_ae (pressureForce A).smooth).2.2 x

theorem equation (A : SmoothL2Field Space) (x : Space) :
    (rhs A).field x + fderiv ℝ A.field x (A.field x) + gradient (pressure A) x = 0 := by
  rw [pressure_gradient, pressureForce, fieldSub_field, rhs, scaleField_field, neg_smul, one_smul,
    ← advectionField_field A A x]
  abel

theorem solenoidal_divergence (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace) (x : Space) :
    ∑ i : Fin 3, fderiv ℝ A.field x (EuclideanSpace.single i 1) i = 0 :=
  solenoidal_representative_divergence A.toLp hA A.field A.smooth A.toLp_ae x

end ClockBarrier.Euler.Smooth
