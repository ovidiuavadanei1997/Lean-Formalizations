/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.NearIdentity
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Orthonormal singular frames, with arbitrary spectral multiplicities -/

public section
namespace ClockBarrier.Geometry
open scoped InnerProductSpace
open Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

/-- An ordered orthonormal eigenbasis identifies the actual ordered eigenvalues. -/
theorem eigenvalues_eq_of_ordered_basis {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hn : finrank ℝ E = n) (b : OrthonormalBasis (Fin n) ℝ E)
    {d : Fin n → ℝ} (hd : Antitone d) (he : ∀ i, T (b i) = d i • b i) :
    hT.eigenvalues hn = d := by
  classical
  have hmat : T.toMatrix b.toBasis b.toBasis = Matrix.diagonal d := by
    ext i j
    simp [LinearMap.toMatrix_apply, he, Matrix.diagonal_apply, eq_comm]
    split_ifs with hij <;> simp_all
  have hroots : T.charpoly.roots = Multiset.map d Finset.univ.val := by
    rw [← T.charpoly_toMatrix b.toBasis, hmat, Matrix.charpoly_diagonal,
      Polynomial.roots_prod _ _ (by simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
    simp
  apply List.ofFn_inj.mp (List.Perm.eq_of_sortedGE
    (hT.eigenvalues_antitone hn).sortedGE_ofFn hd.sortedGE_ofFn ?_)
  exact Multiset.coe_eq_coe.mp (by
    simpa only [RCLike.ofReal_real_eq_id, Function.id_comp, Fin.univ_val_map] using
      (hT.roots_charpoly_eq_eigenvalues hn).symm.trans hroots)

/-- Ordered stretches of a Gram eigenbasis are the actual singular values. -/
theorem norm_apply_eq_singularValues_of_gram_basis (F : E →L[ℝ] E)
    (hn : finrank ℝ E = n) (b : OrthonormalBasis (Fin n) ℝ E)
    (horder : Antitone (fun i => ‖F (b i)‖))
    (he : ∀ i, F.adjoint (F (b i)) = ‖F (b i)‖ ^ 2 • b i) (i : Fin n) :
    ‖F (b i)‖ = F.toLinearMap.singularValues i := by
  apply (sq_eq_sq₀ (norm_nonneg _) (F.toLinearMap.singularValues_nonneg i)).mp
  rw [F.toLinearMap.sq_singularValues_fin hn i,
    eigenvalues_eq_of_ordered_basis F.toLinearMap.isSymmetric_adjoint_comp_self hn b
      (fun j k hjk => pow_le_pow_left₀ (norm_nonneg _) (horder hjk) 2) he]

/-- A Gram eigenbasis for an injective operator has an orthonormal left singular basis. -/
theorem exists_left_basis_of_gram_basis (F : E →L[ℝ] E) (hF : Function.Injective F)
    (hn : finrank ℝ E = n) (b : OrthonormalBasis (Fin n) ℝ E)
    (he : ∀ i, F.adjoint (F (b i)) = ‖F (b i)‖ ^ 2 • b i) :
    ∃ c : OrthonormalBasis (Fin n) ℝ E, ∀ i, F (b i) = ‖F (b i)‖ • c i := by
  classical
  have hp : ∀ i, ‖F (b i)‖ ≠ 0 := fun i => norm_ne_zero_iff.mpr
    (fun hz => b.toBasis.ne_zero i (hF (hz.trans F.map_zero.symm)))
  have hi : ∀ i j, ⟪F (b i), F (b j)⟫_ℝ = ‖F (b j)‖ ^ 2 * (if i = j then 1 else 0) :=
    fun i j => by rw [← F.adjoint_inner_right, he, real_inner_smul_right, b.inner_eq_ite]
  have ho : Orthonormal ℝ (fun i => ‖F (b i)‖⁻¹ • F (b i)) :=
    orthonormal_iff_ite.mpr (fun i j => by
      simp only [real_inner_smul_left, real_inner_smul_right, hi]
      by_cases hij : i = j <;> simp [hij, pow_two, hp])
  refine ⟨OrthonormalBasis.mk ho
    (ho.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp [hn])).ge, ?_⟩
  simp [OrthonormalBasis.coe_mk, smul_smul, hp]

end ClockBarrier.Geometry
