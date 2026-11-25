/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-! # Geometric bounds near the identity

Operator perturbation bounds control all singular values, including repeated
ones, and imply global distance comparisons for differentiable maps.
-/

public section
namespace ClockBarrier.Geometry
open Set
open scoped InnerProductSpace

section Normed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A perturbation bound gives two-sided bounds on every vector. -/
theorem norm_bounds_of_norm_sub_id_le {F : E →L[ℝ] E} {ε : ℝ}
    (hF : ‖F - ContinuousLinearMap.id ℝ E‖ ≤ ε) (x : E) :
    (1 - ε) * ‖x‖ ≤ ‖F x‖ ∧ ‖F x‖ ≤ (1 + ε) * ‖x‖ := by
  have hd : ‖F x - x‖ ≤ ε * ‖x‖ :=
    ((F - ContinuousLinearMap.id ℝ E).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hF (norm_nonneg x))
  constructor <;> nlinarith [abs_le.mp ((abs_norm_sub_norm_le (F x) x).trans hd)]

/-- Uniform derivative closeness to the identity gives global distance bounds. -/
theorem norm_sub_bounds_of_norm_fderiv_sub_id_le {f : E → E} {ε : ℝ}
    (hdiff : Differentiable ℝ f)
    (hF : ∀ x, ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ ≤ ε) (a b : E) :
    (1 - ε) * ‖a - b‖ ≤ ‖f a - f b‖ ∧
      ‖f a - f b‖ ≤ (1 + ε) * ‖a - b‖ := by
  have hd : ‖(f a - a) - (f b - b)‖ ≤ ε * ‖a - b‖ :=
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x _ => ((hdiff x).hasFDerivAt.sub (hasFDerivAt_id x)).hasFDerivWithinAt)
      (fun x _ => hF x) convex_univ (mem_univ b) (mem_univ a)
  rw [show (f a - a) - (f b - b) = (f a - f b) - (a - b) by abel] at hd
  constructor <;>
    nlinarith [abs_le.mp ((abs_norm_sub_norm_le (f a - f b) (a - b)).trans hd)]

/-- The nonlinear displacement is comparable to its linearization at the
base label, with uniform explicit positive constants when `ε < 1`. -/
theorem norm_sub_comparison_of_norm_fderiv_sub_id_le {f : E → E} {ε : ℝ}
    (hdiff : Differentiable ℝ f)
    (hF : ∀ x, ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ ≤ ε)
    (hε : ε < 1) (a b : E) :
    (1 - ε) / (1 + ε) * ‖(fderiv ℝ f b) (a - b)‖ ≤ ‖f a - f b‖ ∧
      ‖f a - f b‖ ≤ (1 + ε) / (1 - ε) * ‖(fderiv ℝ f b) (a - b)‖ := by
  have hpos : 0 < 1 + ε :=
    add_pos_of_pos_of_nonneg zero_lt_one ((norm_nonneg _).trans (hF b))
  obtain ⟨hl, hu⟩ := norm_sub_bounds_of_norm_fderiv_sub_id_le hdiff hF a b
  obtain ⟨hFl, hFu⟩ := norm_bounds_of_norm_sub_id_le (hF b) (a - b)
  constructor
  · rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    nlinarith [mul_le_mul_of_nonneg_left hFu (sub_pos.mpr hε).le,
      mul_le_mul_of_nonneg_left hl hpos.le]
  · rw [div_mul_eq_mul_div, le_div_iff₀ (sub_pos.mpr hε)]
    nlinarith [mul_le_mul_of_nonneg_left hu (sub_pos.mpr hε).le,
      mul_le_mul_of_nonneg_left hFl hpos.le]

end Normed

section InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The stretch of each unit right Gram eigenvector is the corresponding
ordered singular value. Repeated eigenvalues require no additional premise. -/
theorem norm_apply_eigenvectorBasis_eq_singularValues (F : E →L[ℝ] E)
    {n : ℕ} (hn : Module.finrank ℝ E = n) (i : Fin n) :
    ‖F (F.toLinearMap.isSymmetric_adjoint_comp_self.eigenvectorBasis hn i)‖ =
      F.toLinearMap.singularValues i := by
  apply (sq_eq_sq₀ (norm_nonneg _) (F.toLinearMap.singularValues_nonneg i)).mp
  change ‖F.toLinearMap
    (F.toLinearMap.isSymmetric_adjoint_comp_self.eigenvectorBasis hn i)‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq, ← F.toLinearMap.adjoint_inner_right]
  change ⟪F.toLinearMap.isSymmetric_adjoint_comp_self.eigenvectorBasis hn i,
    (F.toLinearMap.adjoint ∘ₗ F.toLinearMap)
      (F.toLinearMap.isSymmetric_adjoint_comp_self.eigenvectorBasis hn i)⟫_ℝ = _
  rw [F.toLinearMap.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis,
    real_inner_smul_right, real_inner_self_eq_norm_sq,
    (F.toLinearMap.isSymmetric_adjoint_comp_self.eigenvectorBasis hn).norm_eq_one,
    one_pow, mul_one, F.toLinearMap.sq_singularValues_fin hn i]
  rfl

/-- Every actual singular value lies in the perturbation interval about one. -/
theorem singularValues_bounds_of_norm_sub_id_le {F : E →L[ℝ] E} {ε : ℝ}
    (hF : ‖F - ContinuousLinearMap.id ℝ E‖ ≤ ε)
    {n : ℕ} (hn : Module.finrank ℝ E = n) (i : Fin n) :
    1 - ε ≤ F.toLinearMap.singularValues i ∧
      F.toLinearMap.singularValues i ≤ 1 + ε := by
  simpa only [norm_apply_eigenvectorBasis_eq_singularValues F hn i,
    (F.toLinearMap.isSymmetric_adjoint_comp_self.eigenvectorBasis hn).norm_eq_one,
    mul_one] using norm_bounds_of_norm_sub_id_le hF
      (F.toLinearMap.isSymmetric_adjoint_comp_self.eigenvectorBasis hn i)

/-- Near identity, every ratio of actual singular values is uniformly bounded. -/
theorem singularValues_div_le_of_norm_sub_id_le {F : E →L[ℝ] E} {ε : ℝ}
    (hF : ‖F - ContinuousLinearMap.id ℝ E‖ ≤ ε) (hε : ε < 1)
    {n : ℕ} (hn : Module.finrank ℝ E = n) (i j : Fin n) :
    F.toLinearMap.singularValues i / F.toLinearMap.singularValues j ≤
      (1 + ε) / (1 - ε) := by
  exact div_le_div₀ (add_nonneg zero_le_one ((norm_nonneg _).trans hF))
    (singularValues_bounds_of_norm_sub_id_le hF hn i).2 (sub_pos.mpr hε)
    (singularValues_bounds_of_norm_sub_id_le hF hn j).1

end InnerProduct
end ClockBarrier.Geometry
