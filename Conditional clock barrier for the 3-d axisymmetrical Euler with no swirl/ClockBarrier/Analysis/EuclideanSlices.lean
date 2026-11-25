/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.SliceAverage
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic.FinCases

/-! # Rotated Cartesian slices in three-dimensional Euclidean volume -/

public section
namespace ClockBarrier.Analysis
open Set MeasureTheory
open scoped ENNReal
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

/-- Separating height from the Euclidean transverse plane preserves volume. -/
theorem measurePreserving_height_plane :
    MeasurePreserving (fun q : ℝ × E₂ => (!₂[q.2 0, q.2 1, q.1] : E₃)) := by
  have h := (PiLp.volume_preserving_toLp (Fin 3)).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm.comp
      ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_ofLp (Fin 2))))
  convert! h using 1
  ext q i
  fin_cases i <;> rfl

/-- Rotation and translation preserve the same slice-volume normalization. -/
theorem measurePreserving_affine_height_plane (aStar : E₃) (V : E₃ ≃ₗᵢ[ℝ] E₃) :
    MeasurePreserving (fun q : ℝ × E₂ => aStar + V !₂[q.2 0, q.2 1, q.1]) := by
  exact (measurePreserving_add_left (volume : Measure E₃) aStar).comp
    (V.measurePreserving.comp measurePreserving_height_plane)

/-- The affine slice coordinates are a measurable embedding. -/
theorem measurableEmbedding_affine_height_plane (aStar : E₃) (V : E₃ ≃ₗᵢ[ℝ] E₃) :
    MeasurableEmbedding (fun q : ℝ × E₂ => aStar + V !₂[q.2 0, q.2 1, q.1]) := by
  apply (show Continuous (fun q : ℝ × E₂ => aStar + V !₂[q.2 0, q.2 1, q.1])
    by fun_prop).measurableEmbedding
  intro x y hxy
  have hv := V.injective (add_left_cancel hxy)
  refine Prod.ext (congrArg (fun v : E₃ => v 2) hv) ?_
  ext i
  fin_cases i
  · exact congrArg (fun v : E₃ => v 0) hv
  · exact congrArg (fun v : E₃ => v 1) hv

/-- Almost every label in a measurable block belongs to a positive-area slice
in any fixed orthogonal frame, even when exceptional fibers are nonempty. -/
theorem ae_affine_slice_measure_ne_zero (aStar : E₃) (V : E₃ ≃ₗᵢ[ℝ] E₃)
    {S : Set E₃} (hS : MeasurableSet S) :
    ∀ᵐ a ∂volume.restrict S,
      volume {q : E₂ | aStar + V !₂[q 0, q 1, V.symm (a - aStar) 2] ∈ S} ≠ 0 := by
  have hp := measurePreserving_affine_height_plane aStar V
  have he := measurableEmbedding_affine_height_plane aStar V
  rw [← (hp.restrict_preimage_emb he S).map_eq, he.ae_map_iff]
  simpa [Measure.volume_eq_prod, preimage] using
    (ae_fiber_measure_ne_zero (μ := (volume : Measure ℝ)) (ν := (volume : Measure E₂))
      (hS.preimage hp.measurable))

end ClockBarrier.Analysis
