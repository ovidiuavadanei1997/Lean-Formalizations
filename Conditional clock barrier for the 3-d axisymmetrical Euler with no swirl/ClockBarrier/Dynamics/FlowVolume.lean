/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Dynamics.FlowJacobian
public import ClockBarrier.Dynamics.FlowUniqueness
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Preservation of volumes of transported measurable sets -/

public section

namespace ClockBarrier.Dynamics

open Set MeasureTheory
open scoped Topology NNReal ENNReal

/-- An injective differentiable map with determinant one preserves the volume of each
measurable set under its image. No surjectivity is required for this statement. -/
theorem volume_image_eq_of_det_fderiv_eq_one
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hdiff : Differentiable ℝ f) (hinj : Function.Injective f)
    (hdet : ∀ x, (fderiv ℝ f x).toLinearMap.det = 1)
    {s : Set (EuclideanSpace ℝ (Fin 3))} (hs : MeasurableSet s) :
    volume (f '' s) = volume s := by
  have h := lintegral_abs_det_fderiv_eq_addHaar_image volume hs
    (fun x _ => (hdiff x).hasFDerivAt.hasFDerivWithinAt) hinj.injOn
  simpa only [ContinuousLinearMap.det, hdet, abs_one, ENNReal.ofReal_one,
    MeasureTheory.lintegral_one, Measure.restrict_apply_univ] using h.symm

/-- Construct an incompressible flow with spatial regularity, its variational equation,
injectivity, unit Jacobian, and preservation of volumes of transported measurable sets. -/
theorem exists_flow_volume_image_eq_Ico
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
      ∀ t ∈ Ico 0 T, ContDiff ℝ 1 (Φ t) ∧ Function.Injective (Φ t) ∧
        (∀ x, HasDerivWithinAt (fun s => fderiv ℝ (Φ s) x)
          ((fderiv ℝ (u t) (Φ t x)).comp (fderiv ℝ (Φ t) x)) (Ici t) t ∧
          (fderiv ℝ (Φ t) x).toLinearMap.det = 1) ∧
        ∀ s : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet s → volume (Φ t '' s) = volume s := by
  obtain ⟨Φ, hinit, hcont, hode, hreg⟩ := exists_incompressible_flow_Ico hT hu hdiff hD hbound hdiv
  refine ⟨Φ, hinit, hcont, hode, fun t ht => ?_⟩
  have hi := injective_flow_Ico_of_fderiv_bound hu hdiff hbound hcont hode hinit ht
  exact ⟨(hreg t ht).1, hi, (hreg t ht).2, fun s hs =>
    volume_image_eq_of_det_fderiv_eq_one ((hreg t ht).1.differentiable (by decide)) hi
      (fun x => ((hreg t ht).2 x).2) hs⟩

end ClockBarrier.Dynamics
