/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Dynamics.FlowLifespan
public import ClockBarrier.Dynamics.MatrixLiouville
public import ClockBarrier.Geometry.EuclideanMatrix

/-!
# Unit Jacobian for incompressible trajectories

The spatial derivative and variational equation are derived from the velocity
and trajectory ODE. Zero divergence then implies determinant one.
-/

public section

namespace ClockBarrier.Dynamics

open ClockBarrier.Geometry Set
open scoped Topology NNReal

/-- Passing from the operator variational equation to its genuine Euclidean matrix. -/
theorem hasDerivWithinAt_euclideanMatrix_of_operator_ode
    {A : ℝ → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {M : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {s : Set ℝ} {t : ℝ} (hA : HasDerivWithinAt A (M.comp (A t)) s t) :
    HasDerivWithinAt (fun r => euclideanMatrix (A r))
      (euclideanMatrix M * euclideanMatrix (A t)) s t := by
  letI : NormedAddCommGroup (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (NormedAddCommGroup (Fin 3 → Fin 3 → ℝ))
  letI : NormedSpace ℝ (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (NormedSpace ℝ (Fin 3 → Fin 3 → ℝ))
  have h : HasFDerivAt (fun B : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) =>
      euclideanMatrix B) euclideanMatrix (A t) :=
    (euclideanMatrix (n := Fin 3)).hasFDerivAt
  convert! h.comp_hasDerivWithinAt t hA using 1
  exact (euclideanMatrix_comp M (A t)).symm

/-- A divergence-free velocity has unit flow Jacobian on each compact time interval. -/
theorem det_fderiv_flow_eq_one
    {T : ℝ} (hT : 0 ≤ T)
    {u Φ : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {K : ℝ≥0}
    (hu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hdiff : ∀ t ∈ Icc 0 T, Differentiable ℝ (u t))
    (hD : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => fderiv ℝ (u p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hbound : ∀ t ∈ Ico 0 T, ∀ x, ‖fderiv ℝ (u t) x‖₊ ≤ K)
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Icc 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x)
    (hdiv : ∀ t ∈ Ico 0 T, ∀ x,
      LinearMap.trace ℝ (EuclideanSpace ℝ (Fin 3)) (fderiv ℝ (u t) x).toLinearMap = 0)
    (x : EuclideanSpace ℝ (Fin 3)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (fderiv ℝ (Φ t) x).toLinearMap.det = 1 := by
  have hc : ContinuousOn (fun s => euclideanMatrix (fderiv ℝ (Φ s) x)) (Icc 0 T) := by
    apply continuousOn_iff_continuous_restrict.mpr
    exact euclideanMatrix.continuous.comp
      ((continuous_fderiv_flow hT hu hdiff hD hbound hcont hode hinit).comp
        (continuous_id.prodMk continuous_const))
  have heq := det_eq_of_matrix_ode_trace_zero hc
    (fun s hs => hasDerivWithinAt_euclideanMatrix_of_operator_ode
      (hasDerivWithinAt_fderiv_flow_right hT hu hdiff hD hbound hcont hode hinit x hs))
    (fun s hs => (trace_euclideanMatrix _).trans (hdiv s hs (Φ s x))) t ht
  simpa only [fderiv_flow_zero hinit, euclideanMatrix_id, Matrix.det_one,
    det_euclideanMatrix] using heq

/-- Unit Jacobian holds before the terminal time, with bounds local in time. -/
theorem det_fderiv_flow_eq_one_Ico
    {T : ℝ} {u Φ : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hu : ContinuousOn (Function.uncurry u) (Ico 0 T ×ˢ univ))
    (hdiff : ∀ t ∈ Ico 0 T, Differentiable ℝ (u t))
    (hD : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => fderiv ℝ (u p.1) p.2)
      (Ico 0 T ×ˢ univ))
    (hbound : ∀ b ∈ Ico 0 T, ∃ K : ℝ≥0,
      ∀ t ∈ Ico 0 b, ∀ x, ‖fderiv ℝ (u t) x‖₊ ≤ K)
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x)
    (hdiv : ∀ t ∈ Ico 0 T, ∀ x,
      LinearMap.trace ℝ (EuclideanSpace ℝ (Fin 3)) (fderiv ℝ (u t) x).toLinearMap = 0)
    (x : EuclideanSpace ℝ (Fin 3)) {t : ℝ} (ht : t ∈ Ico 0 T) :
    (fderiv ℝ (Φ t) x).toLinearMap.det = 1 := by
  obtain ⟨K, hK⟩ := hbound t ht
  have hsub : Icc 0 t ⊆ Ico 0 T := fun _ hs => ⟨hs.1, hs.2.trans_lt ht.2⟩
  exact det_fderiv_flow_eq_one ht.1 (hu.mono (prod_mono hsub subset_rfl))
    (fun s hs => hdiff s (hsub hs)) (hD.mono (prod_mono hsub subset_rfl)) hK
    (fun y => (hcont y).mono hsub)
    (fun y s hs => hode y s (hsub (Ico_subset_Icc_self hs))) hinit
    (fun s hs => hdiv s (hsub (Ico_subset_Icc_self hs))) x ⟨ht.1, le_rfl⟩

/-- Construct the incompressible flow, its spatial derivative equation, and its unit Jacobian
from velocity regularity and zero divergence. -/
theorem exists_incompressible_flow_Ico
    {T : ℝ} (hT : 0 < T) {u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hu : ContinuousOn (Function.uncurry u) (Ico 0 T ×ˢ univ))
    (hdiff : ∀ t ∈ Ico 0 T, Differentiable ℝ (u t))
    (hD : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => fderiv ℝ (u p.1) p.2)
      (Ico 0 T ×ˢ univ))
    (hbound : ∀ b ∈ Ico 0 T, ∃ K : ℝ≥0,
      ∀ t ∈ Ico 0 b, ∀ x, ‖fderiv ℝ (u t) x‖₊ ≤ K)
    (hdiv : ∀ t ∈ Ico 0 T, ∀ x,
      LinearMap.trace ℝ (EuclideanSpace ℝ (Fin 3)) (fderiv ℝ (u t) x).toLinearMap = 0) :
    ∃ Φ : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      (∀ x, Φ 0 x = x) ∧ (∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T)) ∧
      (∀ x, ∀ t ∈ Ico 0 T,
        HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t) ∧
      ∀ t ∈ Ico 0 T, ContDiff ℝ 1 (Φ t) ∧ ∀ x,
        HasDerivWithinAt (fun s => fderiv ℝ (Φ s) x)
          ((fderiv ℝ (u t) (Φ t x)).comp (fderiv ℝ (Φ t) x)) (Ici t) t ∧
        (fderiv ℝ (Φ t) x).toLinearMap.det = 1 := by
  obtain ⟨Φ, hinit, hcont, hode, hreg⟩ := exists_regular_flow_Ico hT hu hdiff hD hbound
  exact ⟨Φ, hinit, hcont, hode, fun t ht => ⟨(hreg t ht).1, fun x =>
    ⟨(hreg t ht).2 x, det_fderiv_flow_eq_one_Ico hu hdiff hD hbound hcont hode hinit hdiv x ht⟩⟩⟩

end ClockBarrier.Dynamics
