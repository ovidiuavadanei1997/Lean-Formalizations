/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.SpectralMinimum
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-! # Evolution of the smallest singular value

For a matrix path satisfying `F′ = L F`, the smallest positive singular value
has a right derivative equal to its value times the least strain quadratic
form on the entire left singular eigenspace. The proof follows the spectral-gap
decomposition and square completion, without eigenvalue simplicity
or a differentiable frame.
-/

public section
namespace ClockBarrier.Analysis
open Set Filter Metric
open scoped Topology InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The left Gram operator satisfies the differentiated product equation. -/
theorem hasDerivWithinAt_left_gram
    {F : ℝ → E →L[ℝ] E} {L : E →L[ℝ] E} {t₀ : ℝ}
    (hF : HasDerivWithinAt F (L.comp (F t₀)) (Ici t₀) t₀) :
    HasDerivWithinAt (fun t => (F t).comp (F t).adjoint)
      (L.comp ((F t₀).comp (F t₀).adjoint) +
        ((F t₀).comp (F t₀).adjoint).comp L.adjoint) (Ici t₀) t₀ := by
  have hd := hF.clm_comp hF.star
  simpa only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_assoc] using hd

/-- The skew-adjoint part contributes zero to a real quadratic form. -/
theorem inner_symmetric_part (L : E →L[ℝ] E) (x : E) :
    ⟪x, ((1 / 2 : ℝ) • (L + L.adjoint)) x⟫_ℝ = ⟪x, L x⟫_ℝ := by
  simp only [smul_apply, add_apply,
    real_inner_smul_right, inner_add_right, ContinuousLinearMap.adjoint_inner_right,
    real_inner_comm]
  ring

/-- On an eigenspace of the Gram operator, its quadratic-form derivative is
exactly twice the eigenvalue times the strain quadratic form. -/
theorem inner_gram_derivative_of_eigenvector
    (L C : E →L[ℝ] E) (hC : C.IsSymmetric) {x : E} {μ : ℝ}
    (hx : C x = μ • x) :
    ⟪x, (L.comp C + C.comp L.adjoint) x⟫_ℝ =
      (2 * μ) * ⟪x, ((1 / 2 : ℝ) • (L + L.adjoint)) x⟫_ℝ := by
  simp only [inner_symmetric_part, add_apply, ContinuousLinearMap.comp_apply,
    inner_add_right]
  have hsym : ⟪x, C (L.adjoint x)⟫_ℝ = ⟪C x, L.adjoint x⟫_ℝ := (hC x _).symm
  simp only [hsym, hx, map_smul, real_inner_smul_right,
    ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
  ring

/-- Right evolution of the genuine smallest singular value, with an attained
minimum over the entire left singular eigenspace. Multiplicity is unrestricted. -/
theorem exists_hasDerivWithinAt_smallest_singularValue [Nontrivial E]
    {n : ℕ} (hn : Module.finrank ℝ E = n + 1)
    {F : ℝ → E →L[ℝ] E} {L : E →L[ℝ] E} {t₀ : ℝ}
    (hF : HasDerivWithinAt F (L.comp (F t₀)) (Ici t₀) t₀)
    (hν : 0 < (F t₀).toLinearMap.singularValues n) :
    ∃ m, IsLeast {r : ℝ | ∃ e : E, ‖e‖ = 1 ∧
        (F t₀) ((F t₀).adjoint e) = ((F t₀).toLinearMap.singularValues n ^ 2) • e ∧
        r = ⟪e, ((1 / 2 : ℝ) • (L + L.adjoint)) e⟫_ℝ} m ∧
      HasDerivWithinAt (fun t => (F t).toLinearMap.singularValues n)
        ((F t₀).toLinearMap.singularValues n * m) (Ici t₀) t₀ := by
  let C : ℝ → E →L[ℝ] E := fun t => (F t).comp (F t).adjoint
  let D := L.comp (C t₀) + (C t₀).comp L.adjoint
  let q : ℝ → C(sphere (0 : E) 1, ℝ) := fun t =>
    ⟨fun x => ⟪(x : E), C t x⟫_ℝ, by fun_prop⟩
  let g : C(sphere (0 : E) 1, ℝ) := ⟨fun x => ⟪(x : E), D x⟫_ℝ, by fun_prop⟩
  haveI : Nonempty (sphere (0 : E) 1) :=
    ⟨Classical.choose (isLeast_unit_inner_sq_singularValues (F t₀) hn).1⟩
  obtain ⟨x, hmin, hgmin⟩ := exists_minimizer_minimizing (q t₀) g
  have hC : (C t₀).IsSymmetric := (IsSelfAdjoint.mul_star_self (F t₀)).isSymmetric
  have hder : HasDerivWithinAt (fun t => sInf (range (q t))) (g x) (Ici t₀) t₀ :=
    hasDerivWithinAt_sInf_unit_inner_of_minimizer
    (hasDerivWithinAt_left_gram hF) hC x hmin hgmin
  have hμ (t : ℝ) : sInf (range (q t)) = (F t).toLinearMap.singularValues n ^ 2 :=
    (isLeast_unit_inner_sq_singularValues (F t) hn).csInf_eq
  have hxval : q t₀ x = (F t₀).toLinearMap.singularValues n ^ 2 :=
    (show IsLeast (range (q t₀)) (q t₀ x) from
      ⟨mem_range_self x, fun _ ⟨y, hy⟩ => hy ▸ hmin y⟩).unique
      (isLeast_unit_inner_sq_singularValues (F t₀) hn)
  have heigen : C t₀ x = q t₀ x • (x : E) :=
    map_eq_smul_of_unit_minimizer hC (mem_sphere_zero_iff_norm.mp x.property)
      (fun y hy => hmin ⟨y, mem_sphere_zero_iff_norm.mpr hy⟩)
  rw [hxval] at heigen
  have hgx : g x = (2 * (F t₀).toLinearMap.singularValues n ^ 2) *
      ⟪(x : E), ((1 / 2 : ℝ) • (L + L.adjoint)) x⟫_ℝ :=
    inner_gram_derivative_of_eigenvector L (C t₀) hC heigen
  refine ⟨⟪(x : E), ((1 / 2 : ℝ) • (L + L.adjoint)) x⟫_ℝ,
    ⟨⟨x, mem_sphere_zero_iff_norm.mp x.property, heigen, rfl⟩, ?_⟩, ?_⟩
  · rintro r ⟨e, he, heig, rfl⟩
    have heval : q t₀ ⟨e, mem_sphere_zero_iff_norm.mpr he⟩ = q t₀ x := by
      simpa only [q, C, ContinuousMap.coe_mk, ContinuousLinearMap.comp_apply, heig,
        real_inner_smul_right, real_inner_self_eq_norm_sq, he, one_pow, mul_one] using hxval.symm
    have hge : g ⟨e, mem_sphere_zero_iff_norm.mpr he⟩ =
        (2 * (F t₀).toLinearMap.singularValues n ^ 2) *
          ⟪e, ((1 / 2 : ℝ) • (L + L.adjoint)) e⟫_ℝ :=
      inner_gram_derivative_of_eigenvector L (C t₀) hC heig
    exact (mul_le_mul_iff_right₀ (show 0 < 2 * (F t₀).toLinearMap.singularValues n ^ 2
      from mul_pos (by norm_num) (sq_pos_of_pos hν))).mp
        (by simpa only [hgx, hge] using hgmin _ heval)
  · have hne : sInf (range (q t₀)) ≠ 0 :=
      hμ t₀ ▸ (sq_pos_of_pos hν).ne'
    have hsqrt := hder.sqrt hne
    simp only [hμ, Real.sqrt_sq (LinearMap.singularValues_nonneg _ _), hgx] at hsqrt
    convert hsqrt using 1
    field_simp

end ClockBarrier.Analysis
