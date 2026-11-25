/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.L2MollifierRepresentative
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! # Smooth bounded velocity and derivative representatives of mollified L² fields -/

@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Solenoidal
open MeasureTheory ContinuousLinearMap
open scoped Convolution ContDiff BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem kernel_memLp (n : ℕ) : MemLp (kernel n) 2 volume :=
  (kernel_smooth n).continuous.memLp_of_hasCompactSupport (kernel_compact n)

theorem kernel_derivative_memLp (n : ℕ) : MemLp (fderiv ℝ (kernel n)) 2 volume :=
  ((kernel_smooth n).continuous_fderiv (by simp)).memLp_of_hasCompactSupport
    ((kernel_compact n).fderiv ℝ)

def mollifierField (n : ℕ) : L2 →L[ℝ] (E₃ →ᵇ E₃) :=
  L2Convolution.operator (lsmul ℝ ℝ) ((kernel_memLp n).toLp (kernel n))

def mollifierDerivative (n : ℕ) : L2 →L[ℝ] (E₃ →ᵇ (E₃ →L[ℝ] E₃)) :=
  L2Convolution.operator ((lsmul ℝ ℝ).precompL E₃)
    ((kernel_derivative_memLp n).toLp (fderiv ℝ (kernel n)))

theorem mollifierField_apply (n : ℕ) (u : L2) (x : E₃) :
    mollifierField n u x = (kernel n ⋆[lsmul ℝ ℝ, volume] (u : E₃ → E₃)) x :=
  L2Convolution.value_eq_convolution (lsmul ℝ ℝ) (kernel_memLp n) u x

theorem mollifierDerivative_apply (n : ℕ) (u : L2) (x : E₃) :
    mollifierDerivative n u x =
      (fderiv ℝ (kernel n) ⋆[(lsmul ℝ ℝ).precompL E₃, volume] (u : E₃ → E₃)) x :=
  L2Convolution.value_eq_convolution _ (kernel_derivative_memLp n) u x

theorem mollifierField_smooth (n : ℕ) (u : L2) :
    ContDiff ℝ ∞ (mollifierField n u : E₃ → E₃) := by
  simpa only [show (mollifierField n u : E₃ → E₃) =
      kernel n ⋆[lsmul ℝ ℝ, volume] (u : E₃ → E₃) from
        funext (mollifierField_apply n u)] using
    (kernel_compact n).contDiff_convolution_left (lsmul ℝ ℝ) (kernel_smooth n)
      ((Lp.memLp u).locallyIntegrable (by norm_num))

theorem mollifierField_hasFDerivAt (n : ℕ) (u : L2) (x : E₃) :
    HasFDerivAt (mollifierField n u : E₃ → E₃) (mollifierDerivative n u x) x := by
  rw [show (mollifierField n u : E₃ → E₃) =
    kernel n ⋆[lsmul ℝ ℝ, volume] (u : E₃ → E₃) from
      funext (mollifierField_apply n u), mollifierDerivative_apply]
  exact (kernel_compact n).hasFDerivAt_convolution_left (lsmul ℝ ℝ)
    ((kernel_smooth n).of_le (by simp)) ((Lp.memLp u).locallyIntegrable (by norm_num)) x

theorem mollify_ae_mollifierField (n : ℕ) (u : L2) :
    mollify n u =ᵐ[volume] (mollifierField n u : E₃ → E₃) := by
  simpa only [show (mollifierField n u : E₃ → E₃) =
    kernel n ⋆[lsmul ℝ ℝ, volume] (u : E₃ → E₃) from
      funext (mollifierField_apply n u)] using mollify_ae_convolution n u

theorem mollifierField_memLp (n : ℕ) (u : L2) :
    MemLp (mollifierField n u : E₃ → E₃) 2 volume :=
  (memLp_congr_ae (mollify_ae_mollifierField n u)).mp (Lp.memLp (mollify n u))

end ClockBarrier.Analysis.Solenoidal
