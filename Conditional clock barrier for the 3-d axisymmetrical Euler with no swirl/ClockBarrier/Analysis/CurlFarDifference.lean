/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.CurlKernelConvolution
import Mathlib.Tactic.Positivity
/-! # Hölder control of the complete far-field difference

The constant depends only on the exponent and fixed cutoff. Every component
uses the actual curl increment and an absolutely integrable cancelled kernel.
-/

public section
namespace ClockBarrier.Analysis
open Set Metric MeasureTheory Geometry
open scoped Topology InnerProductSpace NNReal ContDiff
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Hölder continuity of the curl bounds every skew-entry increment. -/
theorem abs_skew_entry_increment_le {D : E₃ → E₃ →L[ℝ] E₃} {H α : ℝ≥0}
    (hw : HolderWith H α (fun x => curlLinearMap (D x))) (x : E₃) (i k : Fin 3) :
    |(D x (EuclideanSpace.single k 1) i - D x (EuclideanSpace.single i 1) k) -
      (D 0 (EuclideanSpace.single k 1) i - D 0 (EuclideanSpace.single i 1) k)| ≤
        H * ‖x‖ ^ (α : ℝ) := by
  have hb := abs_skew_entry_le_norm_curl (D x - D 0) i k
  have hd : ‖curlLinearMap (D x) - curlLinearMap (D 0)‖ ≤ H * ‖x‖ ^ (α : ℝ) := by
    simpa only [dist_eq_norm, sub_zero] using hw.dist_le x 0
  simpa only [sub_apply, PiLp.sub_apply,
    sub_sub_sub_comm] using hb.trans (by simpa only [map_sub] using hd)

/-- The difference of complete far fields is bounded by the curl Hölder
constant, uniformly in unit strain directions and unit translations. -/
theorem exists_directional_far_difference_constant
    {χ : E₃ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : χ =ᶠ[𝓝 (0 : E₃)] 0)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1)
    (hradial : ∀ x y, ‖x‖ = ‖y‖ → χ x = χ y)
    {α : ℝ≥0} (hα₁ : α < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (D : E₃ → E₃ →L[ℝ] E₃), Continuous D →
      ∀ (H : ℝ≥0), HolderWith H α (fun x => curlLinearMap (D x)) →
      ∀ (b e : E₃), ‖b‖ ≤ 1 → ‖e‖ = 1 →
      let F := fun (a x : E₃) =>
        let y := x - a
        let w := curlLinearMap (D x)
        χ y * (⟪e, y⟫_ℝ *
          ⟪e, (!₂[y 1 * w 2 - y 2 * w 1, y 2 * w 0 - y 0 * w 2,
            y 0 * w 1 - y 1 * w 0] : E₃)⟫_ℝ / ‖y‖ ^ 5)
      Integrable (fun x => F b x - F 0 x) volume ∧
        |∫ x, F b x - F 0 x| ≤ B * H := by
  have hc (i j : Fin 3) := exists_axis_far_difference_convolution_constant
    hχ hzero houter hradial α.coe_nonneg (show (α : ℝ) < 1 from hα₁) i j
  choose B hB hconv using hc
  refine ⟨∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3, B i j,
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => hB _ _))), ?_⟩
  intro D hD H hw b e hb he F
  let v (i k : Fin 3) (x : E₃) :=
    D x (EuclideanSpace.single k 1) i - D x (EuclideanSpace.single i 1) k
  let g (i j k : Fin 3) (x : E₃) :=
    (χ (x - b) * ((x - b) i * (x - b) j / ‖x - b‖ ^ 5) -
      χ x * (x i * x j / ‖x‖ ^ 5)) * v i k x
  have hg (i j k : Fin 3) : Integrable (g i j k) volume ∧
      |∫ x, g i j k x| ≤ H * B i j :=
    hconv i j b hb (v i k) H (v i k 0) H.coe_nonneg
      (by dsimp [v]; fun_prop) (fun x => abs_skew_entry_increment_le hw x i k)
  have hf (x : E₃) : F b x - F 0 x =
      ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3, e j * e k * g i j k x := by
    simp only [F, directional_far_linear_expansion, sub_zero,
      Finset.sum_sub_distrib, g, v, mul_sub, sub_mul]
    ring
  have hit (i j k : Fin 3) : Integrable
      (fun x => e j * e k * g i j k x) volume :=
    (hg i j k).1.const_mul (e j * e k)
  refine ⟨by simpa only [hf] using integrable_finsetSum Finset.univ (fun j _ =>
    integrable_finsetSum Finset.univ (fun k _ =>
      integrable_finsetSum Finset.univ (fun i _ => hit i j k))), ?_⟩
  have hsplit : (∫ x, F b x - F 0 x) =
      ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3, e j * e k * ∫ x, g i j k x := by
    simp only [hf, integral_finsetSum _ (fun j _ => integrable_finsetSum _
      (fun k _ => integrable_finsetSum _ (fun i _ => hit i j k))),
      integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun i _ => hit i _ k)),
      integral_finsetSum _ (fun i _ => hit i _ _), integral_const_mul]
  have heprod (j k : Fin 3) : |e j * e k| ≤ 1 := by
    simpa only [abs_mul, he, one_mul] using mul_le_mul
      (abs_euclidean_coordinate_le_norm e j) (abs_euclidean_coordinate_le_norm e k)
      (abs_nonneg (e k)) (norm_nonneg e)
  have ht (i j k : Fin 3) : |e j * e k * ∫ x, g i j k x| ≤ B i j * H := by
    simpa only [abs_mul, one_mul, mul_comm (H : ℝ)] using
      mul_le_mul (heprod j k) (hg i j k).2 (abs_nonneg _) zero_le_one
  simpa only [hsplit, Finset.sum_mul] using
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ =>
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ =>
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ht i j k)))
end ClockBarrier.Analysis
