/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.CurlHolderLogarithmic

/-! # Uniform Hölder and logarithmic curl estimates

Supporting theorem for classical Euler continuation; see THEOREM_GUIDE.md.
-/

public section
namespace ClockBarrier.Analysis
open MeasureTheory
open scoped NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)


/-- One constant depending only on the Hölder exponent controls both the
homogeneous Hölder seminorm and the logarithmic supremum norm of the actual
velocity derivative. The supplied curl Hölder constant may be zero. -/
theorem exists_curl_holder_logarithmic_constant :
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

by exact ClockBarrier.Analysis.exists_uniform_curl_holder_logarithmic_constant



end ClockBarrier.Analysis


