/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.SingularFrameExistence
public import ClockBarrier.Analysis.CompactSelection

/-! # Measurable right singular frames

The compact space of orthonormal frames allows a Borel choice even where
singular values coincide. No continuous eigenvector choice is asserted.
-/

public section
namespace ClockBarrier.Geometry
open Set Metric Module
open scoped InnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

/-- Orthonormal frames form a compact set in the finite product of the ambient space. -/
theorem isCompact_setOf_orthonormal :
    IsCompact {v : Fin n → E | Orthonormal ℝ v} := by
  classical
  have hc : IsClosed {v : Fin n → E | Orthonormal ℝ v} := by
    simp_rw [orthonormal_iff_ite, setOf_forall]
    exact isClosed_iInter (fun i => isClosed_iInter (fun j =>
      isClosed_eq ((continuous_apply i).inner (continuous_apply j)) continuous_const))
  refine (isCompact_closedBall (0 : Fin n → E) 1).of_isClosed_subset hc ?_
  exact fun v hv => by
    simpa only [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one] using
      fun i => (hv.norm_eq_one i).le

/-- A continuous operator family admits a measurable ordered orthonormal Gram eigenbasis. -/
theorem exists_measurable_gram_basis {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace E] [BorelSpace E]
    (F : X → E →L[ℝ] E) (hF : Continuous F) (hn : finrank ℝ E = n) :
    ∃ b : X → OrthonormalBasis (Fin n) ℝ E,
      (∀ i, Measurable (fun x => b x i)) ∧
      (∀ x, Antitone (fun i => ‖F x (b x i)‖)) ∧
      ∀ x i, (F x).adjoint (F x (b x i)) = ‖F x (b x i)‖ ^ 2 • b x i := by
  classical
  let O := {v : Fin n → E // Orthonormal ℝ v}
  letI : CompactSpace O :=
    isCompact_iff_compactSpace.mp (isCompact_setOf_orthonormal (E := E) (n := n))
  letI : Nonempty O := ⟨⟨LinearMap.IsSymmetric.id.eigenvectorBasis hn,
    (LinearMap.IsSymmetric.id.eigenvectorBasis hn).orthonormal⟩⟩
  let R : Set (X × O) := {q | (∀ i, (F q.1).adjoint (F q.1 (q.2.val i)) =
    ‖F q.1 (q.2.val i)‖ ^ 2 • q.2.val i) ∧ Antitone (fun i => ‖F q.1 (q.2.val i)‖)}
  have hv : ∀ i, Continuous (fun q : X × O => q.2.val i) :=
    fun i => (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
  have hw : ∀ i, Continuous (fun q : X × O => F q.1 (q.2.val i)) :=
    fun i => (hF.comp continuous_fst).clm_apply (hv i)
  have hR : IsClosed R := by
    simp only [R, Antitone, setOf_and, setOf_forall]
    exact (isClosed_iInter (fun i => isClosed_eq
      ((ContinuousLinearMap.adjoint.continuous.comp (hF.comp continuous_fst)).clm_apply (hw i))
      (((hw i).norm.pow 2).smul (hv i)))).inter
        (isClosed_iInter (fun i => isClosed_iInter (fun j => isClosed_iInter
          (fun _ => isClosed_le (hw j).norm (hw i).norm))))
  have hne : ∀ x, ∃ v : O, (x, v) ∈ R := by
    intro x
    refine ⟨⟨(F x).toLinearMap.isSymmetric_adjoint_comp_self.eigenvectorBasis hn,
      ((F x).toLinearMap.isSymmetric_adjoint_comp_self.eigenvectorBasis hn).orthonormal⟩, ?_, ?_⟩
    · exact fun i => by
        rw [norm_apply_eigenvectorBasis_eq_singularValues (F x) hn i,
          (F x).toLinearMap.sq_singularValues_fin hn i]
        simpa only [RCLike.ofReal_real_eq_id, id_eq, ContinuousLinearMap.adjoint_toLinearMap,
          LinearMap.comp_apply, ContinuousLinearMap.coe_coe] using
          (F x).toLinearMap.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis hn i
    · exact fun i j hij => by
        simpa only [norm_apply_eigenvectorBasis_eq_singularValues] using
          (F x).toLinearMap.singularValues_antitone hij
  obtain ⟨v, hm, hvR⟩ := Analysis.exists_measurable_mem_closed_relation hR hne
  refine ⟨fun x => OrthonormalBasis.mk (v x).property
    ((v x).property.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp [hn])).ge, ?_⟩
  simpa only [OrthonormalBasis.coe_mk, Function.comp_def] using
    And.intro (fun i => (measurable_pi_apply i).comp (measurable_subtype_coe.comp hm))
      ⟨fun x => (hvR x).2, fun x => (hvR x).1⟩

/-- Continuous injective operator families admit measurable right singular frames for
all actual ordered singular values, without any simplicity assumption. -/
theorem exists_measurable_singular_frame {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace E] [BorelSpace E]
    (F : X → E →L[ℝ] E) (hF : Continuous F) (hinj : ∀ x, Function.Injective (F x))
    (hn : finrank ℝ E = n) :
    ∃ V : X → EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] E,
      (∀ i, Measurable (fun x => V x (EuclideanSpace.single i 1))) ∧
      ∀ x, ∃ U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] E,
        ∀ η, F x (V x η) = U (WithLp.toLp 2 (fun i => (F x).toLinearMap.singularValues i * η i)) := by
  obtain ⟨b, hm, ho, he⟩ := exists_measurable_gram_basis F hF hn
  refine ⟨fun x => (b x).repr.symm,
    by simpa only [OrthonormalBasis.repr_symm_single] using hm, ?_⟩
  intro x
  obtain ⟨c, hc⟩ := exists_left_basis_of_gram_basis (F x) (hinj x) hn (b x) (he x)
  refine ⟨c.repr.symm, fun η => ?_⟩
  have hci : ∀ i, F x (b x i) = (F x).toLinearMap.singularValues i • c i := by
    simpa only [norm_apply_eq_singularValues_of_gram_basis (F x) hn (b x) (ho x) (he x)] using hc
  simp only [← OrthonormalBasis.sum_repr_symm, map_sum, map_smul, hci,
    smul_smul, mul_comm]

end ClockBarrier.Geometry
