/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.CurlFreeInterpolation
public import ClockBarrier.Analysis.SmoothPressurePotential
public import ClockBarrier.Analysis.SmoothBoundedField
import ClockBarrier.Analysis.L2ParameterIntegral
import Mathlib.Tactic.Linarith

/-! # The pressure-gradient interpolation estimate for smooth approximations -/
public section
namespace ClockBarrier.Analysis
open MeasureTheory SmoothL2Field Sobolev Solenoidal
open scoped ContDiff BoundedContinuousFunction
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem norm_euclidean_le_three_mul_of_coordinates (x : Space) {B : ℝ}
    (hB : ∀ i, |x i| ≤ B) : ‖x‖ ≤ 3 * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hi (i : Fin 3) : x i ^ 2 ≤ B ^ 2 := by
    have h := hB i
    nlinarith [sq_abs (x i), abs_nonneg (x i)]
  have hn := EuclideanSpace.real_norm_sq_eq x
  simp only [Fin.sum_univ_three] at hn
  nlinarith [hi 0, hi 1, hi 2, norm_nonneg x, sq_nonneg B]

theorem sqrt_coordinate_energy_le_norm (A : SmoothL2Field Space) (i : Fin 3) :
    Real.sqrt (∫ x : Space, ‖A.field x i‖ ^ 2) ≤ ‖A.toLp‖ := by
  have hi : MemLp (fun x : Space => A.field x i) 2 volume := by
    convert! (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' A.memLp using 1
  have hle : (∫ x : Space, ‖A.field x i‖ ^ 2) ≤ ∫ x : Space, ‖A.field x‖ ^ 2 := by
    apply integral_mono hi.norm.integrable_sq A.memLp.norm.integrable_sq
    intro x
    exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (A.field x) i) 2
  have he : (∫ x : Space, ‖A.field x‖ ^ 2) = ‖A.toLp‖ ^ 2 := by
    rw [L2ParameterIntegral.integral_norm_sq_eq volume A.field A.memLp,
      SmoothL2Field.toLp, Lp.norm_toLp]
  simpa only [he, Real.sqrt_sq (norm_nonneg A.toLp)] using Real.sqrt_le_sqrt hle

theorem exists_smooth_gradient_interpolation_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ A : SmoothL2Field Space, A.toLp ∈ gradientSpace →
      ∀ B : ℝ, (∀ x, |∑ i : Fin 3,
        fderiv ℝ A.field x (EuclideanSpace.single i 1) i| ≤ B) →
      ∀ r : ℝ, 0 < r →
        ‖finiteField A‖ ≤ C * (r * B + r ^ (-(3 : ℝ) / 2) * ‖A.toLp‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_curl_free_component_interpolation_constant
  refine ⟨3 * C, by positivity, ?_⟩
  intro A hA B hB r hr
  let F (i : Fin 3) (x : Space) := A.field x i
  have hAd := A.smooth.differentiable (by simp)
  have hF (i : Fin 3) : ContDiff ℝ ∞ (F i) :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp A.smooth
  have hF0 (i : Fin 3) : MemLp (F i) 2 volume := by
    convert! (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' A.memLp using 1
  have hF1 (i j : Fin 3) :
      MemLp (fun x => fderiv ℝ (F i) x (EuclideanSpace.single j 1)) 2 volume := by
    simp only [F, fderiv_coordinate _ _ (hAd _)]
    convert! ((EuclideanSpace.proj (𝕜 := ℝ) i).comp
      (ContinuousLinearMap.apply ℝ Space (EuclideanSpace.single j 1))).comp_memLp'
        A.derivative.memLp using 1
  have hFs (x : Space) (i j : Fin 3) :
      fderiv ℝ (F i) x (EuclideanSpace.single j 1) =
        fderiv ℝ (F j) x (EuclideanSpace.single i 1) := by
    simpa only [F, fderiv_coordinate _ _ (hAd _)] using
      SmoothPressure.gradientSpace_classical_curl_zero A.toLp hA A.field A.toLp_ae A.smooth x j i
  have hBF (x : Space) :
      |∑ i : Fin 3, fderiv ℝ (F i) x (EuclideanSpace.single i 1)| ≤ B := by
    simpa only [F, fderiv_coordinate _ _ (hAd _)] using hB x
  apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
  intro x
  have hb (i : Fin 3) : |A.field x i| ≤
      C * (r * B + r ^ (-(3 : ℝ) / 2) * ‖A.toLp‖) := by
    have hsup (y : Space) : |F i y| ≤ ‖finiteField A‖ :=
      (abs_euclidean_coordinate_le_norm (A.field y) i).trans
        (by simpa only [finiteField_apply] using (finiteField A).norm_coe_le_norm y)
    exact (hbound F hF hF0 hF1 hFs B hBF i _ hsup r hr x).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (sqrt_coordinate_energy_le_norm A i)
          (Real.rpow_nonneg hr.le _))) hC.le)
  simpa only [finiteField_apply, mul_assoc] using
    norm_euclidean_le_three_mul_of_coordinates (A.field x) hb

end ClockBarrier.Analysis
