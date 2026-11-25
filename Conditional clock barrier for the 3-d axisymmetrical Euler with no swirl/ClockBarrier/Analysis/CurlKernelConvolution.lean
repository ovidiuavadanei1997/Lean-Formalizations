/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.CurlKernelMoment
public import ClockBarrier.Geometry.CurlLinear
import ClockBarrier.Analysis.DirectionalStrainKernel
import ClockBarrier.Analysis.DirectionalFarField
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
/-! # Cancelled far-kernel convolution estimates

Absolute integrability precedes cancellation, and skew matrix entries are
controlled by the actual Cartesian curl.
-/

public section
namespace ClockBarrier.Analysis
open Set Metric MeasureTheory Geometry
open scoped Topology InnerProductSpace NNReal ContDiff
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Cancellation permits subtracting a constant only after the difference
kernel and its weighted moment have been shown to be integrable. -/
theorem integrable_abs_integral_mul_le_of_cancelled_moment
    {k v : E₃ → ℝ} {α H B c : ℝ} (hH : 0 ≤ H)
    (hk : Integrable k volume) (hcancel : (∫ x, k x) = 0)
    (hm : Integrable (fun x => |k x| * ‖x‖ ^ α) volume)
    (hB : (∫ x, |k x| * ‖x‖ ^ α) ≤ B) (hv : Measurable v)
    (hinc : ∀ x, |v x - c| ≤ H * ‖x‖ ^ α) :
    Integrable (fun x => k x * v x) volume ∧ |∫ x, k x * v x| ≤ H * B := by
  have hpoint (x : E₃) : ‖k x * (v x - c)‖ ≤ H * (|k x| * ‖x‖ ^ α) := by
    simpa only [Real.norm_eq_abs, abs_mul, mul_left_comm H] using
      mul_le_mul_of_nonneg_left (hinc x) (abs_nonneg (k x))
  have hi : Integrable (fun x => k x * (v x - c)) volume :=
    (hm.const_mul H).mono' (hk.aestronglyMeasurable.mul
      ((hv.sub measurable_const).aestronglyMeasurable)) (Filter.Eventually.of_forall hpoint)
  have heq : (fun x => k x * v x) =
      (fun x => k x * (v x - c)) + (fun x => k x * c) := by
    ext x; simp only [Pi.add_apply]; ring
  refine ⟨heq ▸ hi.add (hk.mul_const c), ?_⟩
  simp only [heq, Pi.add_def, integral_add hi (hk.mul_const c), integral_mul_const, hcancel, zero_mul, add_zero]
  exact (norm_integral_le_of_norm_le (hm.const_mul H)
    (Filter.Eventually.of_forall hpoint)).trans (by
      simpa only [integral_const_mul] using mul_le_mul_of_nonneg_left hB hH)
/-- The smooth far coefficient acts on a Hölder increment with a uniform
bound, after cancellation of its translation difference. -/
theorem exists_axis_far_difference_convolution_constant
    {χ : E₃ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : χ =ᶠ[𝓝 (0 : E₃)] 0)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1)
    (hradial : ∀ x y, ‖x‖ = ‖y‖ → χ x = χ y)
    {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1) (i j : Fin 3) :
    let k := fun x : E₃ => χ x * (x i * x j / ‖x‖ ^ 5)
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (b : E₃), ‖b‖ ≤ 1 → ∀ (v : E₃ → ℝ) (H c : ℝ),
      0 ≤ H → Measurable v → (∀ x, |v x - c| ≤ H * ‖x‖ ^ α) →
      Integrable (fun x => (k (x - b) - k x) * v x) volume ∧
        |∫ x, (k (x - b) - k x) * v x| ≤ H * B := by
  obtain ⟨B, hB, hm⟩ := exists_axis_far_translation_holder_moment_bound
    hχ hzero houter hα₀ hα₁ i j
  refine ⟨B, hB, fun b hb v H c hH hv hinc => ?_⟩
  obtain ⟨hk, hz⟩ := integrable_axis_far_translate_sub_and_integral_eq_zero
    hχ hzero houter hradial i j b hb
  exact integrable_abs_integral_mul_le_of_cancelled_moment hH hk hz (hm b hb).1 (hm b hb).2 hv hinc

/-- The directional kernel is a contraction of the skew entries of a linear map. -/
theorem directional_far_linear_expansion (χ : E₃ → ℝ) (A : E₃ →L[ℝ] E₃)
    (x e : E₃) :
    let w := curlLinearMap A
    χ x * (⟪e, x⟫_ℝ *
      ⟪e, (!₂[x 1 * w 2 - x 2 * w 1, x 2 * w 0 - x 0 * w 2,
        x 0 * w 1 - x 1 * w 0] : E₃)⟫_ℝ / ‖x‖ ^ 5) =
      ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3, e j * e k *
        (χ x * (x i * x j / ‖x‖ ^ 5) *
          (A (EuclideanSpace.single k 1) i - A (EuclideanSpace.single i 1) k)) := by
  simpa only [A.fderiv, ← mul_sub] using directional_far_curl_expansion χ A x e

/-- Each skew matrix entry is one signed Cartesian curl component. -/
theorem abs_skew_entry_le_norm_curl (A : E₃ →L[ℝ] E₃) (i k : Fin 3) :
    |A (EuclideanSpace.single k 1) i - A (EuclideanSpace.single i 1) k| ≤
      ‖curlLinearMap A‖ := by
  have h (l : Fin 3) := abs_euclidean_coordinate_le_norm (curlLinearMap A) l
  have hs : ∀ l : Fin 3, (EuclideanSpace.single l 1 : E₃) =
      !₂[if l = 0 then 1 else 0, if l = 1 then 1 else 0, if l = 2 then 1 else 0] := by
    intro l; ext j; fin_cases l <;> fin_cases j <;> simp
  fin_cases i <;> fin_cases k <;>
    simp only [hs, Fin.isValue] <;>
    first | simp only [sub_self, abs_zero]; exact norm_nonneg _
          | simpa [curlLinearMap_apply, abs_sub_comm] using h 0
          | simpa [curlLinearMap_apply, abs_sub_comm] using h 1
          | simpa [curlLinearMap_apply, abs_sub_comm] using h 2

end ClockBarrier.Analysis
