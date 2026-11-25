/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.MollifiedField
public import ClockBarrier.Analysis.SolenoidalRegularizer
public import ClockBarrier.Analysis.SolenoidalSmooth
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Smooth representatives of the concrete solenoidal regularizer -/

@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Solenoidal
open MeasureTheory ContinuousLinearMap
open scoped Convolution ContDiff BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem projection_mollify (n : ℕ) (u : L2) :
    solenoidalProjection (mollify n u) = mollify n (solenoidalProjection u) := by
  rw [mollify_eq_integral, mollify_eq_integral,
    ← solenoidalProjection.integral_comp_comm (kernel_orbit_integrable n u)]
  simp only [map_smul, solenoidalProjection_translation]

theorem regularizerMap_eq_mollify_projection (n : ℕ) (u : L2) :
    regularizerMap n u = mollify n (solenoidalProjection u) := by
  rw [regularizerMap_apply, projection_mollify, projection_idempotent]

def regularizedField (n : ℕ) : L2 →L[ℝ] (E₃ →ᵇ E₃) :=
  (mollifierField n).comp solenoidalProjection

def regularizedDerivative (n : ℕ) : L2 →L[ℝ] (E₃ →ᵇ (E₃ →L[ℝ] E₃)) :=
  (mollifierDerivative n).comp solenoidalProjection

theorem regularizedField_smooth (n : ℕ) (u : L2) :
    ContDiff ℝ ∞ (regularizedField n u : E₃ → E₃) :=
  mollifierField_smooth n (solenoidalProjection u)

theorem regularizedField_hasFDerivAt (n : ℕ) (u : L2) (x : E₃) :
    HasFDerivAt (regularizedField n u : E₃ → E₃) (regularizedDerivative n u x) x :=
  mollifierField_hasFDerivAt n (solenoidalProjection u) x

theorem regularizerMap_ae_field (n : ℕ) (u : L2) :
    regularizerMap n u =ᵐ[volume] (regularizedField n u : E₃ → E₃) := by
  rw [regularizerMap_eq_mollify_projection]
  exact mollify_ae_mollifierField n (solenoidalProjection u)

theorem regularizedField_memLp (n : ℕ) (u : L2) :
    MemLp (regularizedField n u : E₃ → E₃) 2 volume :=
  mollifierField_memLp n (solenoidalProjection u)

theorem regularizedField_divergence (n : ℕ) (u : L2) (x : E₃) :
    ∑ i : Fin 3,
      fderiv ℝ (regularizedField n u : E₃ → E₃) x (EuclideanSpace.single i 1) i = 0 :=
  solenoidal_representative_divergence (regularizerMap n u) (regularizerMap_mem n u)
    (regularizedField n u) (regularizedField_smooth n u) (regularizerMap_ae_field n u) x

end ClockBarrier.Analysis.Solenoidal
