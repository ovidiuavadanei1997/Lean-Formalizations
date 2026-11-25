/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Dynamics.FlowVolume
public import ClockBarrier.Dynamics.FlowSurjectivity

/-! # Global measure preservation of incompressible flows

Surjectivity upgrades preservation of image volumes to preservation of the
whole-space measure under pullback.
-/

public section

namespace ClockBarrier.Dynamics

open Set MeasureTheory
open scoped Topology NNReal

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- A differentiable bijection with determinant one preserves Euclidean volume. -/
theorem measurePreserving_of_bijective_det_fderiv_eq_one
    {f : E₃ → E₃} (hdiff : Differentiable ℝ f) (hbij : Function.Bijective f)
    (hdet : ∀ x, (fderiv ℝ f x).toLinearMap.det = 1) :
    MeasurePreserving f volume volume := by
  refine ⟨hdiff.continuous.measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hdiff.continuous.measurable hs]
  have hv := volume_image_eq_of_det_fderiv_eq_one hdiff hbij.1 hdet
    (hs.preimage hdiff.continuous.measurable)
  rw [image_preimage_eq s hbij.2] at hv
  exact hv.symm

end ClockBarrier.Dynamics
