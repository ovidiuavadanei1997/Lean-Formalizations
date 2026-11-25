/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Dynamics.FlowDifferentiability
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# The variational equation

The spatial derivative is first obtained in continuous-path space. Differentiating
its linear integral equation in time uses the fundamental theorem of calculus,
without interchanging mixed derivatives or imposing second spatial derivatives.
-/

public section

namespace ClockBarrier.Dynamics

open ClockBarrier.Analysis Filter Set MeasureTheory intervalIntegral
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {T : ℝ}

/-- A linearized integral equation yields an operator-valued time derivative. -/
theorem hasDerivWithinAt_linearMapPath_of_integral_eq (hT : 0 ≤ T)
    (A : C(Icc 0 T, E →L[ℝ] E)) (B : E →L[ℝ] C(Icc 0 T, E))
    (hB : B = ContinuousLinearMap.const ℝ (Icc 0 T) + (pathVolterra hT A).comp B)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun s => linearMapPath B (projIcc 0 T hT s))
      ((A ⟨t, ht⟩).comp (linearMapPath B ⟨t, ht⟩)) (Icc 0 T) t := by
  let M : ℝ → E →L[ℝ] E := fun s =>
    (A (projIcc 0 T hT s)).comp (linearMapPath B (projIcc 0 T hT s))
  have hM : Continuous M :=
    (A.continuous.comp continuous_projIcc).clm_comp
      ((linearMapPath B).continuous.comp continuous_projIcc)
  have heq (s : Icc 0 T) : linearMapPath B s =
      ContinuousLinearMap.id ℝ E + ∫ r in 0..s.1, M r := by
    ext v
    have h := congrArg (fun L : E →L[ℝ] C(Icc 0 T, E) => L v s) hB
    rw [add_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.intervalIntegral_apply (hM.intervalIntegrable _ _)]
    exact h
  have hd := (intervalIntegral.integral_hasDerivAt_right (hM.intervalIntegrable 0 t)
    hM.aestronglyMeasurable.stronglyMeasurableAtFilter hM.continuousAt).const_add
      (ContinuousLinearMap.id ℝ E)
  have hd' := hd.hasDerivWithinAt.congr_of_mem
    (f₁ := fun s => linearMapPath B (projIcc 0 T hT s))
    (fun s hs => by simpa only [projIcc_of_mem hT hs] using heq ⟨s, hs⟩) ht
  simpa only [M, projIcc_of_mem hT ht] using hd'

/-- The actual spatial derivative of an existing flow satisfies the variational equation.
Spatial `C¹` regularity is derived from the velocity and trajectory hypotheses. -/
theorem hasDerivWithinAt_fderiv_flow (hT : 0 ≤ T)
    {u Φ : ℝ → E → E} {K : ℝ≥0}
    (hu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set E)))
    (hdiff : ∀ τ ∈ Icc 0 T, Differentiable ℝ (u τ))
    (hD : ContinuousOn (fun p : ℝ × E => fderiv ℝ (u p.1) p.2)
      (Icc 0 T ×ˢ (univ : Set E)))
    (hbound : ∀ τ ∈ Ico 0 T, ∀ x, ‖fderiv ℝ (u τ) x‖₊ ≤ K)
    (hcont : ∀ x, ContinuousOn (fun τ => Φ τ x) (Icc 0 T))
    (hode : ∀ x, ∀ τ ∈ Ico 0 T,
      HasDerivWithinAt (fun τ => Φ τ x) (u τ (Φ τ x)) (Ici τ) τ)
    (hinit : ∀ x, Φ 0 x = x)
    (x : E) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun s => fderiv ℝ (Φ s) x)
      ((fderiv ℝ (u t) (Φ t x)).comp (fderiv ℝ (Φ t) x)) (Icc 0 T) t := by
  let F : E → C(Icc 0 T, E) := fun y => ⟨fun s => Φ s.1 y, (hcont y).restrict⟩
  let U : C(Icc 0 T × E, E) :=
    ⟨fun p => u p.1.1 p.2, hu.comp_continuous (continuous_subtype_val.prodMap continuous_id)
      (fun p => ⟨p.1.2, mem_univ _⟩)⟩
  let D : C(Icc 0 T × E, E →L[ℝ] E) :=
    ⟨fun p => fderiv ℝ (u p.1.1) p.2,
      hD.comp_continuous (continuous_subtype_val.prodMap continuous_id)
        (fun p => ⟨p.1.2, mem_univ _⟩)⟩
  have hF : ContDiff ℝ 1 F := contDiff_flow_paths hT hu hdiff hD hbound hcont hode hinit
  have hfd (s : Icc 0 T) : fderiv ℝ (Φ s.1) x = linearMapPath (fderiv ℝ F x) s :=
    ((ContinuousMap.evalCLM ℝ (M := E) s).hasFDerivAt.comp x
      (hF.differentiable (by decide) x).hasFDerivAt).fderiv
  have hfix (y : E) : F y = ContinuousMap.const (Icc 0 T) y +
      pathIntegral hT (pathSuperposition U (F y)) := by
    ext s
    change Φ s.1 y = y + ∫ r in 0..s.1,
      u (projIcc 0 T hT r).1 (Φ (projIcc 0 T hT r).1 y)
    rw [eq_add_integral_of_trajectory hu (hcont y) (hode y) s.2, hinit]
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    simp only [projIcc_of_mem hT (uIcc_subset_Icc ⟨le_rfl, hT⟩ s.2 hr)]
  have hB := fderiv_path_integral_eq hT U D
    (fun s y => (hdiff s.1 s.2 y).hasFDerivAt)
    (hF.differentiable (by decide) x) (Filter.Eventually.of_forall hfix)
  have hd := hasDerivWithinAt_linearMapPath_of_integral_eq hT
    (pathSuperposition D (F x)) (fderiv ℝ F x) hB ht
  have hd' := hd.congr_of_mem (f₁ := fun s => fderiv ℝ (Φ s) x)
    (fun s hs => by simpa only [projIcc_of_mem hT hs] using hfd ⟨s, hs⟩) ht
  simpa only [← hfd ⟨t, ht⟩, pathSuperposition, D, F, ContinuousMap.coe_mk] using hd'

end ClockBarrier.Dynamics
