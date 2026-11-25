/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.CurlLinear
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Radial cancellation of the directional strain kernel

Reflection about the strain direction preserves its longitudinal factor and
reverses its transverse factor. This proves the cancellation without a choice
of Cartesian direction. Integrability is a separate obligation when applying
the identity to a signed integral decomposition.
-/

public section
namespace ClockBarrier.Analysis
open MeasureTheory
open scoped InnerProductSpace
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The constant-vector directional curl kernel has zero Bochner integral
against any radial scalar weight. This identity does not assert integrability. -/
theorem integral_radial_directional_curl_eq_zero
    {ψ : E₃ → ℝ} (hψ : ∀ x y, ‖x‖ = ‖y‖ → ψ x = ψ y)
    (w e : E₃) (he : ‖e‖ = 1) :
    (∫ x : E₃, ψ x * ⟪e, x⟫_ℝ *
      ⟪e, (!₂[x 1 * w 2 - x 2 * w 1, x 2 * w 0 - x 0 * w 2,
        x 0 * w 1 - x 1 * w 0] : E₃)⟫_ℝ) = 0 := by
  let R : E₃ ≃ₗᵢ[ℝ] E₃ := (ℝ ∙ e).reflection
  let f (x : E₃) : ℝ := ψ x * ⟪e, x⟫_ℝ *
    ⟪e, (!₂[x 1 * w 2 - x 2 * w 1, x 2 * w 0 - x 0 * w 2,
      x 0 * w 1 - x 1 * w 0] : E₃)⟫_ℝ
  have hR (x : E₃) : R x = (2 * ⟪e, x⟫_ℝ) • e - x := by
    simp [R, Submodule.reflection_singleton_apply, he, two_smul, add_smul, two_mul]
  have hlong (x : E₃) : ⟪e, R x⟫_ℝ = ⟪e, x⟫_ℝ := by
    rw [hR, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, he]
    ring
  have hcross (x : E₃) :
      ⟪e, (!₂[(R x) 1 * w 2 - (R x) 2 * w 1,
        (R x) 2 * w 0 - (R x) 0 * w 2,
        (R x) 0 * w 1 - (R x) 1 * w 0] : E₃)⟫_ℝ =
      -⟪e, (!₂[x 1 * w 2 - x 2 * w 1, x 2 * w 0 - x 0 * w 2,
        x 0 * w 1 - x 1 * w 0] : E₃)⟫_ℝ := by
    rw [hR]
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
    ring
  have hodd (x : E₃) : f (R x) = -f x := by
    simp only [f, hψ (R x) x (R.norm_map x), hlong, hcross, mul_neg]
  have hint := R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding f
  have hn : (∫ x, f (R x)) = -(∫ x, f x) := by
    simp only [hodd, integral_neg]
  change (∫ x, f x) = 0
  linarith

end ClockBarrier.Analysis
