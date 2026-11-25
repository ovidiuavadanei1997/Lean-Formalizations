/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.CurlDirectionalLogarithmic
public import ClockBarrier.Geometry.CurlOperatorNorm

/-! # The uniform logarithmic curl estimate

This proves the supremum-norm half of the joint Hölder/logarithmic
target. Its constant is selected before the velocity, derivative and supplied
curl Hölder bound. The homogeneous Hölder conclusion remains a separate obligation.
-/

public section
namespace ClockBarrier.Analysis
open MeasureTheory Geometry
open scoped NNReal ENNReal BoundedContinuousFunction InnerProductSpace
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- A divergence-free bounded `C¹` finite-energy field with a globally Hölder
derivative satisfies the logarithmic derivative bound. The constant depends
only on the positive exponent, and the supplied curl Hölder constant may be zero. -/
theorem exists_uniform_curl_logarithmic_constant {α : ℝ≥0} (hα : 0 < α) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (u : E₃ →ᵇ E₃) (D : E₃ →ᵇ (E₃ →L[ℝ] E₃)),
        (∀ x, HasFDerivAt (u : E₃ → E₃) (D x) x) →
        (∃ K : ℝ≥0, HolderWith K α (D : E₃ → E₃ →L[ℝ] E₃)) →
        MemLp (u : E₃ → E₃) 2 volume →
        (∀ x, LinearMap.trace ℝ E₃ (D x).toLinearMap = 0) →
        let ω : E₃ →ᵇ E₃ := curlLinearMap.compLeftContinuousBounded E₃ D
        ∀ H : ℝ≥0, HolderWith H α (ω : E₃ → E₃) →
          ‖D‖ ≤ (C : ℝ) * (1 + (eLpNorm (u : E₃ → E₃) 2 volume).toReal +
            ‖ω‖ * Real.log (Real.exp 1 + (H : ℝ))) := by
  obtain ⟨c, hc, hdir⟩ := exists_directional_logarithmic_constant hα
  refine ⟨⟨3 * c + 1, by positivity⟩, (by change (0 : ℝ) < 3 * c + 1; positivity), ?_⟩
  intro u D hd hK hL2 hdiv ω H hω
  have hlog : 1 ≤ Real.log (Real.exp 1 + (H : ℝ)) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right H.coe_nonneg)
  let R := 1 + (eLpNorm (u : E₃ → E₃) 2 volume).toReal + ‖ω‖ * Real.log (Real.exp 1 + (H : ℝ))
  have hWR : ‖ω‖ ≤ R := by
    dsimp only [R]
    linarith only [mul_le_mul_of_nonneg_left hlog (norm_nonneg ω),
      ENNReal.toReal_nonneg (a := eLpNorm (u : E₃ → E₃) 2 volume)]
  apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
  intro a
  have hq (e : E₃) (he : ‖e‖ = 1) : |⟪e, D a e⟫_ℝ| ≤ c * R := by
    simpa only [R, sqrt_integral_sq_norm_eq_eLpNorm_toReal hL2] using hdir u D hd hK hL2 hdiv H hω a e he
  have hop := norm_le_of_quadratic_curl_bound (D a)
    (mul_nonneg hc ((norm_nonneg ω).trans hWR)) hq
  have hw : ‖curlLinearMap (D a)‖ ≤ ‖ω‖ := by
    simpa only [ω, ContinuousLinearMap.compLeftContinuousBounded_apply] using ω.norm_coe_le_norm a
  change ‖D a‖ ≤ (3 * c + 1) * R
  nlinarith only [hop, hw, hWR]

end ClockBarrier.Analysis
