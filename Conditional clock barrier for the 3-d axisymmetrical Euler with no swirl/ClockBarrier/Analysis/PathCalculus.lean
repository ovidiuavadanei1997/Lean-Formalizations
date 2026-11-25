/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Calculus on continuous paths

Pointwise application of a continuously differentiable spatial map defines a `C¹`
map on continuous paths over a compact parameter space. No derivative in the
parameter is required. This is the calculus needed for the Picard integral equation.
-/

@[expose] public section

namespace ClockBarrier.Analysis

open Filter Set Metric
open scoped Topology

variable {S E F : Type*} [TopologicalSpace S] [CompactSpace S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pointwise action of a continuous family of bounded linear maps on paths. -/
noncomputable def pathLinearMap (A : C(S, E →L[ℝ] F)) : C(S, E) →L[ℝ] C(S, F) :=
  LinearMap.mkContinuous
    { toFun := fun γ => ⟨fun s => A s (γ s), A.continuous.clm_apply γ.continuous⟩
      map_add' := fun γ δ => ContinuousMap.ext fun s => (A s).map_add (γ s) (δ s)
      map_smul' := fun c γ => ContinuousMap.ext fun s => (A s).map_smul c (γ s) }
    ‖A‖ (by
      intro γ
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg γ))).mpr
      intro s
      exact (A s).le_opNorm (γ s) |>.trans
        (mul_le_mul (A.norm_coe_le_norm s) (γ.norm_coe_le_norm s)
          (norm_nonneg _) (norm_nonneg _)))

/-- The pointwise operator has norm bounded by the supremum norm of its coefficients. -/
theorem norm_pathLinearMap_le (A : C(S, E →L[ℝ] F)) : ‖pathLinearMap A‖ ≤ ‖A‖ := by
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg A) _

/-- Continuous linear dependence of the pointwise operator on its coefficients. -/
noncomputable def pathLinearMapL :
    C(S, E →L[ℝ] F) →L[ℝ] (C(S, E) →L[ℝ] C(S, F)) := by
  let L : C(S, E →L[ℝ] F) →ₗ[ℝ] (C(S, E) →L[ℝ] C(S, F)) :=
    { toFun := pathLinearMap
      map_add' := fun A B => by ext γ s; rfl
      map_smul' := fun c A => by ext γ s; rfl }
  exact LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := C(S, E →L[ℝ] F)) (F := C(S, E) →L[ℝ] C(S, F)) L 1
    (fun A => by simpa only [L, LinearMap.coe_mk, AddHom.coe_mk, one_mul] using norm_pathLinearMap_le A)

/-- Apply a parameter-dependent spatial map to a continuous path. -/
def pathSuperposition (u : C(S × E, F)) (γ : C(S, E)) : C(S, F) :=
  ⟨fun s => u (s, γ s), u.continuous.comp (continuous_id.prodMk γ.continuous)⟩

omit [CompactSpace S] [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Joint continuity gives continuity of substitution in the compact-open topology. -/
theorem continuous_pathSuperposition [LocallyCompactSpace S] (u : C(S × E, F)) :
    Continuous (pathSuperposition u) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact u.continuous.comp (continuous_snd.prodMk continuous_eval)

/-- Spatial differentiation commutes with substitution into a continuous path.
Only joint continuity of the spatial derivative is required. -/
theorem hasFDerivAt_pathSuperposition [LocallyCompactSpace S]
    (u : C(S × E, F)) (D : C(S × E, E →L[ℝ] F))
    (hD : ∀ s x, HasFDerivAt (fun y => u (s, y)) (D (s, x)) x)
    (γ : C(S, E)) :
    HasFDerivAt (pathSuperposition u) (pathLinearMap (pathSuperposition D γ)) γ := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hshift : Continuous (fun v : E => pathSuperposition D (γ + ContinuousMap.const S v)) :=
    (continuous_pathSuperposition D).comp
      (continuous_const.add (ContinuousLinearMap.const ℝ S).continuous)
  obtain ⟨r, hr, hDr⟩ := Metric.continuousAt_iff.mp (hshift.continuousAt (x := 0)) ε hε
  have hnear (s : S) (x : E) (hx : x ∈ ball (γ s) r) :
      ‖D (s, x) - D (s, γ s)‖ ≤ ε := by
    have h := (ContinuousMap.dist_apply_le_dist s).trans_lt
      (hDr (x := x - γ s)
        (by simpa only [mem_ball, dist_zero_right, dist_eq_norm, sub_zero] using hx))
    simpa [pathSuperposition, dist_eq_norm, add_sub_cancel_left] using h.le
  refine Metric.eventually_nhds_iff_ball.mpr ⟨r, hr, fun η hη => ?_⟩
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro s
  have hm := (convex_ball (γ s) r).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun x _ => (hD s x).hasFDerivWithinAt) (hnear s)
    (mem_ball_self hr) ((ContinuousMap.dist_apply_le_dist s).trans_lt hη)
  exact hm.trans (mul_le_mul_of_nonneg_left ((η - γ).norm_coe_le_norm s) hε.le)

/-- A jointly continuous spatial derivative makes path substitution continuously
differentiable, without differentiating the parameter. -/
theorem contDiff_pathSuperposition [LocallyCompactSpace S]
    (u : C(S × E, F)) (D : C(S × E, E →L[ℝ] F))
    (hD : ∀ s x, HasFDerivAt (fun y => u (s, y)) (D (s, x)) x) :
    ContDiff ℝ 1 (pathSuperposition u) := by
  exact contDiff_one_iff_hasFDerivAt.mpr
    ⟨fun γ => pathLinearMap (pathSuperposition D γ),
      (pathLinearMapL (S := S) (E := E) (F := F)).continuous.comp
        (continuous_pathSuperposition D), hasFDerivAt_pathSuperposition u D hD⟩

/-- A bounded linear map into paths is a continuous path of operators when its
input space is finite dimensional. -/
noncomputable def linearMapPath [FiniteDimensional ℝ E]
    (B : E →L[ℝ] C(S, F)) : C(S, E →L[ℝ] F) :=
  ⟨fun s => (ContinuousMap.evalCLM ℝ s).comp B,
    continuous_clm_apply.mpr (fun v => (B v).continuous)⟩

/-- Passing from a linear map into paths to a path of linear maps does not increase norm. -/
theorem norm_linearMapPath_le [FiniteDimensional ℝ E] (B : E →L[ℝ] C(S, F)) :
    ‖linearMapPath B‖ ≤ ‖B‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg B)).mpr
  intro s
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
  intro v
  exact ((B v).norm_coe_le_norm s).trans (B.le_opNorm v)

/-- The operator-path interchange is itself a bounded linear map. -/
noncomputable def linearMapPathL [FiniteDimensional ℝ E] :
    (E →L[ℝ] C(S, F)) →L[ℝ] C(S, E →L[ℝ] F) := by
  let L : (E →L[ℝ] C(S, F)) →ₗ[ℝ] C(S, E →L[ℝ] F) :=
    { toFun := linearMapPath
      map_add' := fun A B => by ext s v; rfl
      map_smul' := fun c A => by ext s v; rfl }
  exact LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := E →L[ℝ] C(S, F)) (F := C(S, E →L[ℝ] F)) L 1
    (fun B => by simpa only [L, LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      using norm_linearMapPath_le B)

end ClockBarrier.Analysis
