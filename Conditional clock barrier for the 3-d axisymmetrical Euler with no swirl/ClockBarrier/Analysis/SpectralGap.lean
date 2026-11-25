/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.RayleighMinimum
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # Eigenspace gaps and the square completion in Lemma 4.1 -/

public section
namespace ClockBarrier.Analysis
open Set Filter Metric
open scoped Topology InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem quadratic_lower_of_unit_lower (A : E →L[ℝ] E) (S : Submodule ℝ E) (c : ℝ)
    (h : ∀ x ∈ S, ‖x‖ = 1 → c ≤ ⟪x, A x⟫_ℝ) (x : E) (hx : x ∈ S) :
    c * ‖x‖ ^ 2 ≤ ⟪x, A x⟫_ℝ := by
  by_cases hz : x = 0
  · simp [hz]
  have hn : ‖‖x‖⁻¹ • x‖ = 1 := by simp [norm_smul, hz]
  have hb := h (‖x‖⁻¹ • x) (S.smul_mem _ hx) hn
  have hnz : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right] at hb
  field_simp at hb
  exact hb

/-- Positive spectral gap on the orthogonal complement of the least eigenspace. -/
theorem exists_least_eigenspace_gap [FiniteDimensional ℝ E] (A : E →L[ℝ] E) (hA : A.IsSymmetric)
    (μ : ℝ) (hμ : ∀ x : E, ‖x‖ = 1 → μ ≤ ⟪x, A x⟫_ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ (Module.End.eigenspace A.toLinearMap μ)ᗮ,
      (μ + δ) * ‖x‖ ^ 2 ≤ ⟪x, A x⟫_ℝ := by
  let K := Module.End.eigenspace A.toLinearMap μ
  let S := sphere (0 : E) 1 ∩ (Kᗮ : Set E)
  have hc : IsCompact S := (isCompact_sphere (0 : E) 1).inter_right Kᗮ.closed_of_finiteDimensional
  by_cases hs : S.Nonempty
  · obtain ⟨y, hy, hmin⟩ := hc.exists_isMinOn hs
      (show Continuous (fun x : E => ⟪x, A x⟫_ℝ) by fun_prop).continuousOn
    have hyn : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy.1
    have hpos : μ < ⟪y, A y⟫_ℝ := by
      apply lt_of_le_of_ne (hμ y hyn)
      intro he
      have heig := map_eq_smul_of_unit_minimizer hA hyn (fun x hx => he ▸ hμ x hx)
      have hyK : y ∈ K := Module.End.mem_eigenspace_iff.mpr (he ▸ heig)
      have hzero := Submodule.inner_right_of_mem_orthogonal hyK hy.2
      exact one_ne_zero (by simpa only [real_inner_self_eq_norm_sq, hyn, one_pow] using hzero)
    refine ⟨⟪y, A y⟫_ℝ - μ, sub_pos.mpr hpos, ?_⟩
    intro x hx
    apply quadratic_lower_of_unit_lower A Kᗮ _ _ x hx
    intro z hz hzn
    linarith only [show ⟪y, A y⟫_ℝ ≤ ⟪z, A z⟫_ℝ from
      hmin ⟨mem_sphere_zero_iff_norm.mpr hzn, hz⟩]
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    apply quadratic_lower_of_unit_lower A Kᗮ _ _ x hx
    intro z hz hzn
    exact (hs ⟨z, mem_sphere_zero_iff_norm.mpr hzn, hz⟩).elim

/-- The Rayleigh quotient split into the least eigenspace and its orthogonal complement. -/
theorem eigenspace_quadratic_decomposition (A : E →L[ℝ] E) (hA : A.IsSymmetric)
    {μ : ℝ} {p q : E} (hp : A p = μ • p) (hpq : ⟪p, q⟫_ℝ = 0) :
    ⟪p + q, A (p + q)⟫_ℝ = μ * ‖p‖ ^ 2 + ⟪q, A q⟫_ℝ := by
  have hcross : ⟪p, A q⟫_ℝ = 0 := by
    calc
      _ = ⟪A p, q⟫_ℝ := (hA p q).symm
      _ = 0 := by rw [hp, real_inner_smul_left, hpq, mul_zero]
  have hqp : ⟪q, p⟫_ℝ = 0 := (real_inner_comm p q).trans hpq
  simp only [map_add, inner_add_left, inner_add_right, hp, hcross,
    real_inner_smul_right, real_inner_self_eq_norm_sq, hqp, mul_zero, zero_add, add_zero]

/-- The derivative quadratic form loses at most four operator norms times the
orthogonal component, exactly the estimate preceding square completion. -/
theorem quadratic_derivative_lower_of_split (D : E →L[ℝ] E) {τ : ℝ}
    (hτ : |τ| ≤ ‖D‖) {p q : E} (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1)
    (hunit : ‖p‖ ^ 2 + ‖q‖ ^ 2 = 1)
    (hlower : τ * ‖p‖ ^ 2 ≤ ⟪p, D p⟫_ℝ) :
    τ - 4 * ‖D‖ * ‖q‖ ≤ ⟪p + q, D (p + q)⟫_ℝ := by
  have bound (x y : E) : |⟪x, D y⟫_ℝ| ≤ ‖D‖ * ‖x‖ * ‖y‖ := by
    calc
      _ ≤ ‖x‖ * ‖D y‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖D‖ * ‖y‖) := mul_le_mul_of_nonneg_left (D.le_opNorm y) (norm_nonneg x)
      _ = _ := by ring
  have hpp := (abs_le.mp (bound p q)).1
  have hqp := (abs_le.mp (bound q p)).1
  have hqq := (abs_le.mp (bound q q)).1
  have hsmall : ‖q‖ ^ 2 ≤ ‖q‖ := by nlinarith [norm_nonneg q]
  have hM := norm_nonneg D
  have hpq : ‖D‖ * ‖p‖ * ‖q‖ ≤ ‖D‖ * ‖q‖ := by
    nlinarith [mul_nonneg hM (norm_nonneg q)]
  have hqbound : ‖D‖ * ‖q‖ ^ 2 ≤ ‖D‖ * ‖q‖ := mul_le_mul_of_nonneg_left hsmall hM
  have htbound : τ * ‖q‖ ^ 2 ≤ ‖D‖ * ‖q‖ :=
    (mul_le_mul_of_nonneg_right (le_abs_self τ |>.trans hτ) (sq_nonneg _)).trans hqbound
  simp only [map_add, inner_add_left, inner_add_right]
  nlinarith only [hlower, hpp, hqp, hqq, hpq, htbound, hqbound,
    congrArg (τ * ·) hunit]

/-- Square completion: the error coefficient has no remaining
orthogonal-component factor. -/
theorem spectral_gap_square_completion {δ M h r : ℝ} (hδ : 0 < δ) :
    -(4 * M ^ 2 / δ) * h ^ 2 ≤ δ * r ^ 2 - 4 * M * h * r := by
  apply (mul_le_mul_iff_right₀ hδ).mp
  field_simp
  nlinarith only [sq_nonneg (δ * r - 2 * M * h)]

/-- Uniform affine perturbation estimate from the eigenspace decomposition and
the complementary spectral gap. -/
theorem unit_quadratic_affine_lower [FiniteDimensional ℝ E] (A D : E →L[ℝ] E) (hA : A.IsSymmetric)
    {μ τ δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ x ∈ (Module.End.eigenspace A.toLinearMap μ)ᗮ,
      (μ + δ) * ‖x‖ ^ 2 ≤ ⟪x, A x⟫_ℝ)
    (hτ : ∀ x ∈ Module.End.eigenspace A.toLinearMap μ,
      ‖x‖ = 1 → τ ≤ ⟪x, D x⟫_ℝ)
    (hτnorm : |τ| ≤ ‖D‖) {h : ℝ} (hh : 0 ≤ h) {v : E} (hv : ‖v‖ = 1) :
    μ + h * τ - (4 * ‖D‖ ^ 2 / δ) * h ^ 2 ≤ ⟪v, A v⟫_ℝ + h * ⟪v, D v⟫_ℝ := by
  let K := Module.End.eigenspace A.toLinearMap μ
  let p := K.starProjection v
  let q := v - p
  have hp : p ∈ K := K.starProjection_apply_mem v
  have hq : q ∈ Kᗮ := K.sub_starProjection_mem_orthogonal v
  have hpq : ⟪p, q⟫_ℝ = 0 := Submodule.inner_right_of_mem_orthogonal hp hq
  have hvsplit : p + q = v := add_sub_cancel _ _
  have hnorm : ‖p‖ ^ 2 + ‖q‖ ^ 2 = 1 := by
    simpa only [← sq, hvsplit, hv, one_pow] using
      (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p q hpq).symm
  have hpn : ‖p‖ ≤ 1 := by nlinarith [sq_nonneg ‖q‖, norm_nonneg p]
  have hqn : ‖q‖ ≤ 1 := by nlinarith [sq_nonneg ‖p‖, norm_nonneg q]
  have ha := eigenspace_quadratic_decomposition A hA
    (Module.End.mem_eigenspace_iff.mp hp) hpq
  have hlowA : μ + δ * ‖q‖ ^ 2 ≤ ⟪v, A v⟫_ℝ := by
    rw [hvsplit] at ha
    nlinarith only [ha, hgap q hq, congrArg (μ * ·) hnorm]
  have hlowD := quadratic_derivative_lower_of_split D hτnorm hpn hqn hnorm
    (quadratic_lower_of_unit_lower D K τ hτ p hp)
  rw [hvsplit] at hlowD
  have hmul := mul_le_mul_of_nonneg_left hlowD hh
  have hsq := spectral_gap_square_completion (M := ‖D‖) (h := h) (r := ‖q‖) hδ
  nlinarith only [hlowA, hmul, hsq]
end ClockBarrier.Analysis
