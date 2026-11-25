/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.Classical
public import ClockBarrier.Geometry.CurlLinear
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import ClockBarrier.Analysis.CurlHolder
import ClockBarrier.Analysis.CurlLogarithmic

/-! # Uniform Hölder and logarithmic curl estimates

A common constant combines the homogeneous Hölder and logarithmic estimates.
The public theorem is assembled from the spatial estimates.
-/

public section
namespace ClockBarrier.Analysis
open MeasureTheory
open scoped NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- One constant depending only on the Hölder exponent controls both the
homogeneous Hölder seminorm and the logarithmic supremum norm of the actual
velocity derivative. The supplied curl Hölder constant may be zero. -/
theorem exists_uniform_curl_holder_logarithmic_constant :
  ∀ (α : ℝ≥0), 0 < α → α < 1 →
  ∃ C : ℝ≥0, 0 < C ∧
    ∀ (u : E₃ →ᵇ E₃) (D : E₃ →ᵇ (E₃ →L[ℝ] E₃)),
      (∀ x, HasFDerivAt (u : E₃ → E₃) (D x) x) →
      (∃ K : ℝ≥0, HolderWith K α (D : E₃ → E₃ →L[ℝ] E₃)) →
      MemLp (u : E₃ → E₃) 2 volume →
      (∀ x, LinearMap.trace ℝ E₃ (D x).toLinearMap = 0) →
      let ω : E₃ →ᵇ E₃ := Geometry.curlLinearMap.compLeftContinuousBounded E₃ D
      ∀ H : ℝ≥0, HolderWith H α (ω : E₃ → E₃) →
        HolderWith (C * H) α (D : E₃ → E₃ →L[ℝ] E₃) ∧
        ‖D‖ ≤ (C : ℝ) *
          (1 + (eLpNorm (u : E₃ → E₃) 2 volume).toReal +
            ‖ω‖ * Real.log (Real.exp 1 + (H : ℝ))) :=
by
  intro α hα hα₁
  obtain ⟨Ch, hCh, hholder⟩ := exists_uniform_curl_holder_constant hα hα₁
  obtain ⟨Cl, _, hlog⟩ := exists_uniform_curl_logarithmic_constant hα
  refine ⟨max Ch Cl, hCh.trans_le (le_max_left _ _), ?_⟩
  intro u D hd hK hL2 hdiv ω H hω
  refine ⟨(hholder u D hd hK hL2 hdiv H hω).mono
    (mul_le_mul_of_nonneg_right (le_max_left Ch Cl) zero_le), ?_⟩
  exact (hlog u D hd hK hL2 hdiv H hω).trans
    (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr (le_max_right Ch Cl))
      (add_nonneg (add_nonneg zero_le_one ENNReal.toReal_nonneg)
        (mul_nonneg (norm_nonneg ω) (Real.log_nonneg
          ((Real.one_lt_exp_iff.mpr zero_lt_one).le.trans (le_add_of_nonneg_right H.coe_nonneg))))))

end ClockBarrier.Analysis

