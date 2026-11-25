/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.DirectionalBudget
import Mathlib.Tactic.Ring
/-! # Algebraic splitting and assembly of the signed directional integrals -/

public section
namespace ClockBarrier.Analysis
open Set MeasureTheory
open scoped ENNReal InnerProductSpace
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem directional_strain_kernel_add (e x v w : E₃) :
    ⟪e, x⟫_ℝ * ⟪e, (!₂[x 1 * (v + w) 2 - x 2 * (v + w) 1,
      x 2 * (v + w) 0 - x 0 * (v + w) 2, x 0 * (v + w) 1 - x 1 * (v + w) 0] : E₃)⟫_ℝ / ‖x‖ ^ 5 =
    (⟪e, x⟫_ℝ * ⟪e, (!₂[x 1 * v 2 - x 2 * v 1,
      x 2 * v 0 - x 0 * v 2, x 0 * v 1 - x 1 * v 0] : E₃)⟫_ℝ / ‖x‖ ^ 5) +
    (⟪e, x⟫_ℝ * ⟪e, (!₂[x 1 * w 2 - x 2 * w 1,
      x 2 * w 0 - x 0 * w 2, x 0 * w 1 - x 1 * w 0] : E₃)⟫_ℝ / ‖x‖ ^ 5) := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  ring

theorem integral_abs_add_le_of_bounds {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {s : Set X} {f g : X → ℝ} {B C : ℝ}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ)
    (hB : (∫ x in s, |f x| ∂μ) ≤ B) (hC : (∫ x in s, |g x| ∂μ) ≤ C) :
    IntegrableOn (fun x => f x + g x) s μ ∧
      (∫ x in s, |f x + g x| ∂μ) ≤ B + C := by
  refine ⟨hf.add hg, ?_⟩
  calc
    _ ≤ ∫ x in s, |f x| + |g x| ∂μ := integral_mono (hf.add hg).abs
      (hf.abs.add hg.abs) (fun x => abs_add_le _ _)
    _ = (∫ x in s, |f x| ∂μ) + ∫ x in s, |g x| ∂μ := integral_add hf.abs hg.abs
    _ ≤ _ := add_le_add hB hC

/-- A cutoff-weighted signed piece obeys the inverse-cube majorant. -/
theorem abs_directional_cutoff_apply_le (d v e : E₃) (he : ‖e‖ = 1)
    (A : E₃ →L[ℝ] E₃) {C χ : ℝ} (hA : ‖A‖ ≤ C) (hχ₀ : 0 ≤ χ) (hχ₁ : χ ≤ 1) :
    |χ * (⟪e, d⟫_ℝ * ⟪e, (!₂[d 1 * (A v) 2 - d 2 * (A v) 1,
      d 2 * (A v) 0 - d 0 * (A v) 2,
      d 0 * (A v) 1 - d 1 * (A v) 0] : E₃)⟫_ℝ / ‖d‖ ^ 5)| ≤ C * ‖v‖ / ‖d‖ ^ 3 := by
  rw [abs_mul, abs_of_nonneg hχ₀]
  refine (mul_le_mul_of_nonneg_right hχ₁ (abs_nonneg _)).trans ?_
  simp only [one_mul]
  exact (abs_directional_strain_kernel_le d (A v) e he).trans
    (div_le_div_of_nonneg_right ((A.le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg _))) (pow_nonneg (norm_nonneg _) 3))
end ClockBarrier.Analysis
