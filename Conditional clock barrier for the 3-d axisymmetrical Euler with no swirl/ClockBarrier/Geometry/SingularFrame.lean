/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Norms and scales in an actual singular frame -/

public section
namespace ClockBarrier.Geometry
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- An orthogonal singular-frame identity determines the exact squared norm. -/
theorem norm_sq_apply_of_singular_frame {F : E₃ →L[ℝ] E₃}
    {U V : E₃ ≃ₗᵢ[ℝ] E₃} {σ : Fin 3 → ℝ}
    (hF : ∀ η : E₃, F (V η) = U !₂[σ 0 * η 0, σ 1 * η 1, σ 2 * η 2])
    (x : E₃) :
    ‖F x‖ ^ 2 = ∑ i : Fin 3, (σ i * V.symm x i) ^ 2 := by
  rw [← V.apply_symm_apply x, hF, U.norm_map, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_three, V.symm_apply_apply]
  rfl

/-- The largest singular stretch bounds the operator norm, directly from the frame. -/
theorem norm_le_of_singular_frame {F : E₃ →L[ℝ] E₃}
    {U V : E₃ ≃ₗᵢ[ℝ] E₃} {σ : Fin 3 → ℝ}
    (hF : ∀ η : E₃, F (V η) = U !₂[σ 0 * η 0, σ 1 * η 1, σ 2 * η 2])
    (hσ : ∀ i, 0 ≤ σ i) (hmax : ∀ i, σ i ≤ σ 0) : ‖F‖ ≤ σ 0 := by
  apply F.opNorm_le_bound (hσ 0)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (hσ 0) (norm_nonneg _))).mp
  rw [norm_sq_apply_of_singular_frame hF, mul_pow, ← V.symm.norm_map x,
    EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hσ i) (hmax i) 2) (sq_nonneg _))

/-- Determinant one forces the product of the three actual singular values to one. -/
theorem prod_singularValues_eq_one {F : E₃ →L[ℝ] E₃}
    (hdet : F.toLinearMap.det = 1) :
    F.toLinearMap.singularValues 0 * F.toLinearMap.singularValues 1 *
      F.toLinearMap.singularValues 2 = 1 := by
  have h := F.toLinearMap.normDet_eq_prod_singularValues
  rw [F.toLinearMap.normDet_eq_abs_det, hdet, abs_one] at h
  simpa only [finrank_euclideanSpace, Fintype.card_fin, Finset.prod_range_succ,
    Finset.prod_range_zero, one_mul] using h.symm

/-- Coordinate shell bounds give two-sided Euclidean norm bounds with factor two. -/
theorem norm_bounds_of_singular_frame_shell {F : E₃ →L[ℝ] E₃}
    {U V : E₃ ≃ₗᵢ[ℝ] E₃} {σ : Fin 3 → ℝ} {γ x : E₃}
    (hF : ∀ η : E₃, F (V η) = U !₂[σ 0 * η 0, σ 1 * η 1, σ 2 * η 2])
    (hσ : ∀ i, 0 ≤ σ i) (hγ : ∀ i, 0 ≤ γ i)
    (hcoord : ∀ i, γ i ≤ σ i * |V.symm x i| ∧ σ i * |V.symm x i| ≤ 2 * γ i) :
    ‖γ‖ ≤ ‖F x‖ ∧ ‖F x‖ ≤ 2 * ‖γ‖ := by
  constructor
  · apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, norm_sq_apply_of_singular_frame hF]
    exact Finset.sum_le_sum (fun i _ => by
      simpa only [mul_pow, sq_abs] using pow_le_pow_left₀ (hγ i) (hcoord i).1 2)
  · apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [norm_sq_apply_of_singular_frame hF, mul_pow, EuclideanSpace.real_norm_sq_eq,
      Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => by
      simpa only [mul_pow, sq_abs] using
        pow_le_pow_left₀ (mul_nonneg (hσ i) (abs_nonneg _)) (hcoord i).2 2)

/-- For the actual singular values, their ordering supplies the operator bound. -/
theorem norm_le_largest_singularValue_of_frame {F : E₃ →L[ℝ] E₃}
    {U V : E₃ ≃ₗᵢ[ℝ] E₃}
    (hF : ∀ η : E₃, F (V η) = U !₂[F.toLinearMap.singularValues 0 * η 0,
      F.toLinearMap.singularValues 1 * η 1, F.toLinearMap.singularValues 2 * η 2]) :
    ‖F‖ ≤ F.toLinearMap.singularValues 0 := by
  exact norm_le_of_singular_frame hF
    (fun i => F.toLinearMap.singularValues_nonneg i)
    (fun i => F.toLinearMap.singularValues_antitone (Nat.zero_le i))

end ClockBarrier.Geometry
