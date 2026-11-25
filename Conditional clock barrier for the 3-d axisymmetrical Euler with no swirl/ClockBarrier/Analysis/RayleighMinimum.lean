/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.CompactMinimum
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
/-! # Rayleigh minima and singular values

Unit-sphere minima of symmetric quadratic forms agree with the last ordered
eigenvalue. Applied to the left Gram operator, this characterizes Mathlib's
smallest singular value without any simplicity assumption.
-/

public section
namespace ClockBarrier.Analysis
open Set Filter Metric
open scoped Topology InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Every unit minimizer of a symmetric quadratic form is an eigenvector. -/
theorem map_eq_smul_of_unit_minimizer {A : E →L[ℝ] E} (hA : A.IsSymmetric)
    {x : E} (hx : ‖x‖ = 1)
    (hm : ∀ y : E, ‖y‖ = 1 → ⟪x, A x⟫_ℝ ≤ ⟪y, A y⟫_ℝ) :
    A x = ⟪x, A x⟫_ℝ • x := by
  have hex : IsMinOn A.reApplyInnerSelf (sphere (0 : E) ‖x‖) x := by
    intro y hy
    simpa only [mem_setOf_eq, ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real,
      real_inner_comm] using hm y ((mem_sphere_zero_iff_norm.mp hy).trans hx)
  simpa only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    RCLike.re_to_real, hx, one_pow, div_one, real_inner_comm] using
    hA.isSelfAdjoint.eq_smul_self_of_isLocalExtrOn_real (Or.inl hex.localize)

/-- The last ordered eigenvalue bounds every unit Rayleigh value from below. -/
theorem last_eigenvalue_le_unit_inner [Nontrivial E]
    {A : E →L[ℝ] E} (hA : A.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ E = n + 1) {x : E} (hx : ‖x‖ = 1) :
    hA.eigenvalues hn (Fin.last n) ≤ ⟪x, A x⟫_ℝ := by
  obtain ⟨i, hi⟩ := hA.exists_eigenvalues_eq hn hA.hasEigenvalue_iInf_of_finiteDimensional
  have hb : BddBelow (range (fun y : {y : E // y ≠ 0} => A.rayleighQuotient y)) :=
    ⟨-‖A‖, fun _ ⟨y, hy⟩ => hy ▸ (abs_le.mp (A.rayleighQuotient_le_norm y)).1⟩
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (hx ▸ one_ne_zero)
  have hi' : hA.eigenvalues hn i = ⨅ y : {y : E // y ≠ 0}, A.rayleighQuotient y := hi
  simpa only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    RCLike.re_to_real, hx, one_pow, div_one, real_inner_comm] using
    (hA.eigenvalues_antitone hn (Fin.le_last i)).trans
      (hi'.le.trans (ciInf_le hb (⟨x, hx0⟩ : {y : E // y ≠ 0})))

/-- The two Gram operators have the same ordered eigenvalues. -/
theorem eigenvalues_self_comp_adjoint_eq (F : E →ₗ[ℝ] E)
    {n : ℕ} (hn : Module.finrank ℝ E = n) :
    F.isSymmetric_self_comp_adjoint.eigenvalues hn =
      F.isSymmetric_adjoint_comp_self.eigenvalues hn := by
  apply (F.isSymmetric_self_comp_adjoint.eigenvalues_eq_eigenvalues_iff hn
    F.isSymmetric_adjoint_comp_self hn).mpr
  classical
  simpa only [LinearMap.charpoly_def,
    LinearMap.toMatrix_comp (Module.Free.chooseBasis ℝ E) (Module.Free.chooseBasis ℝ E)
      (Module.Free.chooseBasis ℝ E)] using
    Matrix.charpoly_mul_comm
      (LinearMap.toMatrix (Module.Free.chooseBasis ℝ E) (Module.Free.chooseBasis ℝ E) F)
      (LinearMap.toMatrix (Module.Free.chooseBasis ℝ E) (Module.Free.chooseBasis ℝ E) F.adjoint)

/-- The smallest eigenvalue is the attained minimum on the unit sphere. -/
theorem isLeast_unit_inner_last_eigenvalue [Nontrivial E]
    {A : E →L[ℝ] E} (hA : A.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ E = n + 1) :
    IsLeast (range (fun x : sphere (0 : E) 1 => ⟪(x : E), A x⟫_ℝ))
      (hA.eigenvalues hn (Fin.last n)) := by
  refine ⟨⟨⟨hA.eigenvectorBasis hn (Fin.last n),
    mem_sphere_zero_iff_norm.mpr ((hA.eigenvectorBasis hn).norm_eq_one _)⟩, ?_⟩,
    fun _ ⟨x, hx⟩ => hx ▸ last_eigenvalue_le_unit_inner hA hn
      (mem_sphere_zero_iff_norm.mp x.property)⟩
  change ⟪hA.eigenvectorBasis hn (Fin.last n),
    A.toLinearMap (hA.eigenvectorBasis hn (Fin.last n))⟫_ℝ = _
  simp [hA.apply_eigenvectorBasis, real_inner_smul_right,
    (hA.eigenvectorBasis hn).norm_eq_one]

/-- The squared smallest singular value is the attained left Gram minimum. -/
theorem isLeast_unit_inner_sq_singularValues [Nontrivial E]
    (F : E →L[ℝ] E) {n : ℕ} (hn : Module.finrank ℝ E = n + 1) :
    IsLeast (range (fun x : sphere (0 : E) 1 => ⟪(x : E), F (F.adjoint x)⟫_ℝ))
      (F.toLinearMap.singularValues n ^ 2) := by
  have hA : (F.comp F.adjoint).IsSymmetric := (IsSelfAdjoint.mul_star_self F).isSymmetric
  have he : hA.eigenvalues hn (Fin.last n) = F.toLinearMap.singularValues n ^ 2 := by
    rw [F.toLinearMap.sq_singularValues_of_lt hn (Nat.lt_succ_self n)]
    exact congrFun (eigenvalues_self_comp_adjoint_eq F.toLinearMap hn) (Fin.last n)
  exact he ▸ isLeast_unit_inner_last_eigenvalue hA hn

/-- Operator differentiation gives uniform differentiation of quadratic forms
on the compact unit sphere. -/
theorem hasDerivWithinAt_unit_inner
    {A : ℝ → E →L[ℝ] E} {B : E →L[ℝ] E} {t₀ : ℝ}
    (hA : HasDerivWithinAt A B (Ici t₀) t₀) :
    HasDerivWithinAt
      (fun t => (⟨fun x : sphere (0 : E) 1 => ⟪(x : E), A t x⟫_ℝ,
        by fun_prop⟩ : C(sphere (0 : E) 1, ℝ)))
      (⟨fun x : sphere (0 : E) 1 => ⟪(x : E), B x⟫_ℝ, by fun_prop⟩)
      (Ici t₀) t₀ := by
  let Q₀ : (E →L[ℝ] E) →ₗ[ℝ] C(sphere (0 : E) 1, ℝ) :=
    { toFun := fun M => ⟨fun x => ⟪(x : E), M x⟫_ℝ, by fun_prop⟩
      map_add' := fun M N => ContinuousMap.ext (fun x => inner_add_right _ _ _)
      map_smul' := fun c M => ContinuousMap.ext (fun x => inner_smul_right _ _ _) }
  have hQ : ∀ M, ‖Q₀ M‖ ≤ 1 * ‖M‖ := by
    intro M
    refine (ContinuousMap.norm_le _ (by positivity)).mpr (fun x => ?_)
    simpa only [Q₀, LinearMap.coe_mk, AddHom.coe_mk, ContinuousMap.coe_mk,
      mem_sphere_zero_iff_norm.mp x.property, mul_one] using
      (norm_inner_le_norm (x : E) (M x)).trans
        (mul_le_mul_of_nonneg_left (M.le_opNorm x) (norm_nonneg (x : E)))
  exact (Q₀.mkContinuous 1 hQ).hasFDerivAt.comp_hasDerivWithinAt t₀ hA

end ClockBarrier.Analysis
