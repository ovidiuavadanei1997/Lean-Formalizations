/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.SmoothL2Convolution
public import ClockBarrier.Analysis.SmoothL2Field
public import ClockBarrier.Analysis.MollifiedInitialData
public import Mathlib.LinearAlgebra.Trace

/-! # Concrete smooth finite-energy approximations of classical initial data -/

@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Solenoidal
open MeasureTheory Filter ContinuousLinearMap
open scoped ContDiff Convolution BoundedContinuousFunction Topology NNReal
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem mollifierField_iteratedFDeriv_memLp (n m : ℕ) (u : L2) :
    MemLp (iteratedFDeriv ℝ m (mollifierField n u : E₃ → E₃)) 2 volume := by
  simpa only [show (mollifierField n u : E₃ → E₃) =
    kernel n ⋆[lsmul ℝ ℝ, volume] (u : E₃ → E₃) from funext (mollifierField_apply n u)] using
      L2Convolution.iteratedFDeriv_convolution_memLp m (lsmul ℝ ℝ) (kernel n)
        (kernel_smooth n) (kernel_compact n) u

/-- The literal compact convolution, with all-order L² spatial regularity. -/
def mollifiedSmoothField (n : ℕ) (u : L2) : SmoothL2Field E₃ where
  field := mollifierField n u
  smooth := mollifierField_smooth n u
  integrable m := mollifierField_iteratedFDeriv_memLp n m u

@[simp] theorem mollifiedSmoothField_field (n : ℕ) (u : L2) :
    (mollifiedSmoothField n u).field = mollifierField n u := rfl

theorem mollifiedSmoothField_toLp (n : ℕ) (u : L2) :
    (mollifiedSmoothField n u).toLp = mollify n u := by
  exact Lp.ext ((mollifiedSmoothField n u).toLp_ae.trans (mollify_ae_mollifierField n u).symm)

theorem toLp_mem_solenoidal_of_hasFDerivAt (u : E₃ →ᵇ E₃)
    (D : E₃ →ᵇ (E₃ →L[ℝ] E₃)) (hu : MemLp (u : E₃ → E₃) 2 volume)
    (hD : ∀ x, HasFDerivAt (u : E₃ → E₃) (D x) x)
    (htr : ∀ x, LinearMap.trace ℝ E₃ (D x).toLinearMap = 0) :
    hu.toLp u ∈ solenoidalSpace := by
  exact c1_mem_solenoidal u (contDiff_one_iff_hasFDerivAt.mpr ⟨D, D.continuous, hD⟩) hu
    (fun x => by
      simpa [(hD x).fderiv, LinearMap.trace_eq_matrix_trace ℝ (PiLp.basisFun 2 ℝ (Fin 3)),
        Matrix.trace, LinearMap.toMatrix_apply] using htr x)

theorem mollifiedSmoothField_solenoidal (n : ℕ) (u : L2) (hu : u ∈ solenoidalSpace) :
    (mollifiedSmoothField n u).toLp ∈ solenoidalSpace := by
  rw [mollifiedSmoothField_toLp]
  exact solenoidalSpace.starProjection_eq_self_iff.mp
    ((projection_mollify n u).trans
      (congrArg (mollify n) (solenoidalSpace.starProjection_eq_self_iff.mpr hu)))

theorem mollifierDerivative_trace (n : ℕ) (u : L2) (hu : u ∈ solenoidalSpace) (x : E₃) :
    LinearMap.trace ℝ E₃ (mollifierDerivative n u x).toLinearMap = 0 := by
  have h := solenoidal_representative_divergence (mollifiedSmoothField n u).toLp
    (mollifiedSmoothField_solenoidal n u hu) (mollifiedSmoothField n u).field
    (mollifiedSmoothField n u).smooth (mollifiedSmoothField n u).toLp_ae x
  simpa [mollifiedSmoothField_field, (mollifierField_hasFDerivAt n u x).fderiv,
    LinearMap.trace_eq_matrix_trace ℝ (PiLp.basisFun 2 ℝ (Fin 3)),
    Matrix.trace, LinearMap.toMatrix_apply] using h

theorem mollifiedSmoothField_tendsto (u : L2) :
    Tendsto (fun n => (mollifiedSmoothField n u).toLp) atTop (𝓝 u) := by
  simpa only [mollifiedSmoothField_toLp] using mollify_tendsto u

end ClockBarrier.Analysis.Solenoidal
