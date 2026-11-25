/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.CurlUnitHolder
public import ClockBarrier.Analysis.CurlDirectionalLogarithmic
import ClockBarrier.Analysis.VelocityScaling
/-! # The homogeneous Hölder Calderón–Zygmund estimate

The unit comparison is rescaled using the actual velocity and derivative.
-/

public section
namespace ClockBarrier.Analysis
open MeasureTheory Geometry
open scoped NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Construct a Hölder bound from its real-distance inequality. -/
theorem holderWith_of_dist_le_mul_rpow {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {f : X → Y} {C α : ℝ≥0}
    (h : ∀ x y, dist (f x) (f y) ≤ C * dist x y ^ (α : ℝ)) : HolderWith C α f := by
  intro x y
  rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ α.coe_nonneg,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  simpa only [NNReal.coe_mul, NNReal.coe_rpow, coe_nndist] using h x y

/-- Exact Hölder-constant scaling under a spatial dilation and translation. -/
theorem holderWith_dilate_translate {Y : Type*} [PseudoMetricSpace Y]
    {f : E₃ → Y} {H α : ℝ≥0} (hf : HolderWith H α f) (r : ℝ) (a : E₃) :
    HolderWith (H * ‖r‖₊ ^ (α : ℝ)) α (fun z => f (r • z + a)) := by
  apply holderWith_of_dist_le_mul_rpow
  exact fun x y => by
    simpa only [dist_add_right, dist_smul₀, NNReal.coe_mul, NNReal.coe_rpow, coe_nnnorm,
      Real.mul_rpow (norm_nonneg r) (dist_nonneg (x := x) (y := y)), mul_assoc] using
      hf.dist_le (r • x + a) (r • y + a)

/-- The homogeneous Hölder seminorm of the actual derivative is bounded by
that of the curl, with a constant depending only on the exponent. -/
theorem exists_uniform_curl_holder_constant {α : ℝ≥0} (hα : 0 < α) (hα₁ : α < 1) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (u : E₃ →ᵇ E₃) (D : E₃ →ᵇ (E₃ →L[ℝ] E₃)),
        (∀ x, HasFDerivAt (u : E₃ → E₃) (D x) x) →
        (∃ K : ℝ≥0, HolderWith K α (D : E₃ → E₃ →L[ℝ] E₃)) →
        MemLp (u : E₃ → E₃) 2 volume →
        (∀ x, LinearMap.trace ℝ E₃ (D x).toLinearMap = 0) →
        let ω : E₃ →ᵇ E₃ := curlLinearMap.compLeftContinuousBounded E₃ D
        ∀ H : ℝ≥0, HolderWith H α (ω : E₃ → E₃) →
          HolderWith (C * H) α (D : E₃ → E₃ →L[ℝ] E₃) := by
  obtain ⟨c, hc, hunit⟩ := exists_unit_curl_holder_constant hα hα₁
  refine ⟨⟨c + 1, by positivity⟩, (by change (0 : ℝ) < c + 1; positivity), ?_⟩
  rintro u D hd ⟨K, hK⟩ hL2 hdiv ω H hω
  have hdf : fderiv ℝ (u : E₃ → E₃) = (D : E₃ → E₃ →L[ℝ] E₃) :=
    funext (fun x => (hd x).fderiv)
  have hw : HolderWith H α (fun x => curlLinearMap (D x)) := fun x y => by
    simpa only [ω, ContinuousLinearMap.compLeftContinuousBounded_apply] using hω x y
  have hdivD (x : E₃) : ∑ i : Fin 3, D x (EuclideanSpace.single i 1) i = 0 := by
    simpa [LinearMap.trace_eq_matrix_trace ℝ (PiLp.basisFun 2 ℝ (Fin 3)),
      Matrix.trace, LinearMap.toMatrix_apply] using hdiv x
  apply holderWith_of_dist_le_mul_rpow
  intro x y
  by_cases hxy : x = y
  · simp only [hxy, dist_self]; positivity
  let r : ℝ := ‖x - y‖
  have hr : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  let v : E₃ → E₃ := fun z => r⁻¹ • u (r • z + y)
  have hua : Differentiable ℝ (fun z => u (z + y)) :=
    fun z => (differentiableAt_comp_add_right y).mpr (hd (z + y)).differentiableAt
  have hv : Differentiable ℝ v :=
    (hua.comp (differentiable_id.const_smul r)).const_smul r⁻¹
  have hdv (z : E₃) : fderiv ℝ v z = D (r • z + y) := by
    simpa only [fderiv_comp_add_right, hdf] using fderiv_rescaled_velocity hua hr.ne' z
  have hKv : HolderWith (K * ‖r‖₊ ^ (α : ℝ)) α (fderiv ℝ v) := fun z z' => by
    simpa only [hdv] using (holderWith_dilate_translate hK r y) z z'
  have hHv : HolderWith (H * ‖r‖₊ ^ (α : ℝ)) α
      (fun z => curlLinearMap (fderiv ℝ v z)) := fun z z' => by
    simpa only [hdv] using (holderWith_dilate_translate hw r y) z z'
  have hvenergy : Integrable (fun z => ‖v z‖ ^ 2) volume :=
    integrable_sq_norm_rescaled_velocity
      (((memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).mp hL2).comp_add_right y) hr.ne'
  have hvbound : ∃ B : ℝ, ∀ z, ‖v z‖ ≤ B :=
    ⟨‖r⁻¹‖ * ‖u‖, fun z => by simpa only [v, norm_smul] using
      mul_le_mul_of_nonneg_left (u.norm_coe_le_norm (r • z + y)) (norm_nonneg r⁻¹)⟩
  have hDvbound : ∃ B : ℝ, ∀ z, ‖fderiv ℝ v z‖ ≤ B :=
    ⟨‖D‖, fun z => by simpa only [hdv] using D.norm_coe_le_norm (r • z + y)⟩
  have hb : ‖r⁻¹ • (x - y)‖ ≤ 1 := by
    simp only [norm_smul, norm_inv, Real.norm_of_nonneg hr.le, show ‖x - y‖ = r from rfl, inv_mul_cancel₀ hr.ne', le_refl]
  have hcomp := hunit hv hKv hvenergy hvbound hDvbound
    (fun z => by simpa only [hdv] using hdivD (r • z + y)) hHv (r⁻¹ • (x - y)) hb
  simp only [hdv, smul_inv_smul₀ hr.ne', sub_add_cancel, smul_zero, zero_add,
    NNReal.coe_mul, NNReal.coe_rpow, coe_nnnorm, Real.norm_of_nonneg hr.le] at hcomp
  simp only [dist_eq_norm, NNReal.coe_mul]
  change ‖D x - D y‖ ≤ ((c + 1) * (H : ℝ)) * r ^ (α : ℝ)
  simpa only [mul_assoc] using hcomp.trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
      (mul_nonneg H.coe_nonneg (Real.rpow_nonneg hr.le _)))
end ClockBarrier.Analysis
