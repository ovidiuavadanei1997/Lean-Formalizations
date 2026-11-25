/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd,
Euler/MeanSobolevBoundedField.lean. See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: direct scalar H² embedding, with no cylinder or Sobolev-space carrier.
-/
module
public import ClockBarrier.Analysis.SmoothAdvectionBounds
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Bounded continuous representatives of actual smooth finite-dimensional fields -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Sobolev
open MeasureTheory ContinuousLinearMap SmoothL2Field SmoothSobolev Finset Filter
open scoped Topology BoundedContinuousFunction
local notation "Space" => EuclideanSpace ℝ (Fin 3)

def scalarField (A : SmoothL2Field ℝ) : Space →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup A.field A.smooth.continuous
    (smoothEmbeddingConstant * ∑ j ∈ range 3, ‖A.jetLp j‖) (scalar_pointwise_H2 A)

@[simp] theorem scalarField_apply (A : SmoothL2Field ℝ) (x : Space) : scalarField A x = A.field x := rfl

theorem scalarField_sub (A B : SmoothL2Field ℝ) : scalarField (fieldSub A B) = scalarField A-scalarField B := by
  ext x
  rfl

theorem scalarField_norm_le (A : SmoothL2Field ℝ) :
    ‖scalarField A‖ ≤ smoothEmbeddingConstant * ∑ j ∈ range 3, ‖A.jetLp j‖ := by
  apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
  exact scalar_pointwise_H2 A

theorem scalarField_sub_norm_le (A B : SmoothL2Field ℝ) :
    ‖scalarField A-scalarField B‖ ≤ smoothEmbeddingConstant * ∑ j ∈ range 3, ‖A.jetLp j-B.jetLp j‖ := by
  simpa only [scalarField_sub, jetLp_fieldSub] using scalarField_norm_le (fieldSub A B)

theorem continuous_scalarField {K : Type*} [TopologicalSpace K]
    (A : K → SmoothL2Field ℝ) (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) :
    Continuous (fun t => scalarField (A t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsum := tendsto_finsetSum (range 3) (fun j _ =>
    (((hA j).tendsto t).sub_const ((A t).jetLp j)).norm)
  have hzero : Tendsto (fun s => smoothEmbeddingConstant *
      ∑ j ∈ range 3, ‖(A s).jetLp j-(A t).jetLp j‖) (𝓝 t) (𝓝 0) := by
    simpa only [sub_self, norm_zero, sum_const_zero, mul_zero] using hsum.const_mul smoothEmbeddingConstant
  exact squeeze_zero (fun _ => norm_nonneg _) (fun s => scalarField_sub_norm_le (A s) (A t)) hzero

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def coordinate (i : Fin (Module.finrank ℝ V)) : V →L[ℝ] ℝ :=
  ((Module.finBasis ℝ V).coord i).toContinuousLinearMap

def coordinateVector (i : Fin (Module.finrank ℝ V)) : ℝ →L[ℝ] V :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (Module.finBasis ℝ V i)

/-- Reconstruct the actual bounded field from its finitely many scalar coordinates. -/
def finiteField (A : SmoothL2Field V) : Space →ᵇ V :=
  ∑ i : Fin (Module.finrank ℝ V), (coordinateVector i).compLeftContinuousBounded Space
    (scalarField (mapField (coordinate i) A))

@[simp] theorem finiteField_apply (A : SmoothL2Field V) (x : Space) : finiteField A x = A.field x := by
  simp only [finiteField, BoundedContinuousFunction.sum_apply]
  change (∑ i : Fin (Module.finrank ℝ V), coordinateVector i (scalarField (mapField (coordinate i) A) x)) = _
  simp only [scalarField_apply, mapField_field]
  exact (Module.finBasis ℝ V).sum_repr (A.field x)

theorem continuous_finiteField {K : Type*} [TopologicalSpace K]
    (A : K → SmoothL2Field V) (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) :
    Continuous (fun t => finiteField (A t)) := by
  apply continuous_finsetSum
  intro i _
  exact ((coordinateVector (V := V) i).compLeftContinuousBounded Space).continuous.comp
    (continuous_scalarField (fun t => mapField (coordinate i) (A t))
      (continuous_jetLp_mapField (coordinate i) A hA))

end ClockBarrier.Analysis.Sobolev
