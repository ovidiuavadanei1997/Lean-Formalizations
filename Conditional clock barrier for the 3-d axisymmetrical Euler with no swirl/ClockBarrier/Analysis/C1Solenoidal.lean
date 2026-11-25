/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd,
through ClockBarrier.Analysis.SolenoidalSmooth.
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: C¹ representatives with an explicitly supplied continuous derivative.
-/
module
public import ClockBarrier.Analysis.SolenoidalSmooth
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Recovering classical divergence zero from the closed L² solenoidal space -/
public section
namespace ClockBarrier.Analysis.Solenoidal
open MeasureTheory InnerProductSpace
open scoped BoundedContinuousFunction RealInnerProductSpace
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem c1_solenoidal_trace (U : L2) (hU : U ∈ solenoidalSpace)
    (u : Space →ᵇ Space) (D : Space →ᵇ (Space →L[ℝ] Space))
    (hrep : U =ᵐ[volume] (u : Space → Space))
    (hD : ∀ x, HasFDerivAt (u : Space → Space) (D x) x) (x : Space) :
    LinearMap.trace ℝ Space (D x).toLinearMap = 0 := by
  have hC : ContDiff ℝ 1 (u : Space → Space) :=
    contDiff_one_iff_hasFDerivAt.mpr ⟨D, D.continuous, hD⟩
  let d (y : Space) := ∑ i : Fin 3, D y (EuclideanSpace.single i 1) i
  have hc : Continuous d := continuous_finsetSum _ (fun i _ =>
    (EuclideanSpace.proj i).continuous.comp (D.continuous.clm_apply continuous_const))
  have hz : d =ᵐ[volume] 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hc.locallyIntegrable
    intro φ hφ hcφ
    have hw := weak_divergence_test hU φ hcφ hφ
    have hi := gradient_test_integration_by_parts u hC φ hcφ hφ
    have heq : (∫ y, ⟪gradient φ y, U y⟫_ℝ) = ∫ y, ⟪gradient φ y, u y⟫_ℝ := by
      apply integral_congr_ae
      filter_upwards [hrep] with y hy
      rw [hy]
    rw [heq, hi] at hw
    simpa only [d, (hD _).fderiv, smul_eq_mul] using neg_eq_zero.mp hw
  have hx : d x = 0 := congrFun (Measure.eq_of_ae_eq hz hc continuous_const) x
  simpa [LinearMap.trace_eq_matrix_trace ℝ (PiLp.basisFun 2 ℝ (Fin 3)),
    Matrix.trace, LinearMap.toMatrix_apply, d] using hx

end ClockBarrier.Analysis.Solenoidal
