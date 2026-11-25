/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.RayleighMinimum

/-! # Continuity and initial normalization of the smallest singular value -/

public section
namespace ClockBarrier.Analysis
open Set Metric
open scoped Topology InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- The smallest singular value is continuous, including at multiplicities. -/
theorem continuous_smallest_singularValue {n : ℕ} (hn : Module.finrank ℝ E = n + 1) :
    Continuous (fun F : E →L[ℝ] E => F.toLinearMap.singularValues n) := by
  have hc := (isCompact_sphere (0 : E) 1).continuous_sInf
    (f := fun (F : E →L[ℝ] E) (x : E) => ⟪x, F (F.adjoint x)⟫_ℝ) (by fun_prop)
  have heq (F : E →L[ℝ] E) :
      Real.sqrt (sInf ((fun x : E => ⟪x, F (F.adjoint x)⟫_ℝ) '' sphere (0 : E) 1)) =
        F.toLinearMap.singularValues n := by
    rw [Set.image_eq_range, (isLeast_unit_inner_sq_singularValues F hn).csInf_eq,
      Real.sqrt_sq (F.toLinearMap.singularValues_nonneg n)]
  exact hc.sqrt.congr heq

/-- The identity has smallest singular value one. -/
theorem smallest_singularValue_id {n : ℕ} (hn : Module.finrank ℝ E = n + 1) :
    (ContinuousLinearMap.id ℝ E).toLinearMap.singularValues n = 1 := by
  obtain ⟨x, hx⟩ := (isLeast_unit_inner_sq_singularValues (ContinuousLinearMap.id ℝ E) hn).1
  have hs : 1 = (ContinuousLinearMap.id ℝ E).toLinearMap.singularValues n ^ 2 := by
    simpa only [ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply,
      real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp x.property, one_pow] using hx
  nlinarith [(ContinuousLinearMap.id ℝ E).toLinearMap.singularValues_nonneg n]

end ClockBarrier.Analysis
