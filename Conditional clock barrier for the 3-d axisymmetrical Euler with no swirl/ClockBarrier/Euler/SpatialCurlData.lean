/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.VorticityRegularity
/-! # Spatial data supplied by the classical Euler interface

This module exposes the bounded derivative, its qualitative Hölder regularity,
finite energy, divergence constraint, and the actual curl. It assumes
no Calderón–Zygmund or logarithmic estimate.
-/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped NNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Every time slice supplies exactly the spatial hypotheses of the Hölder
and logarithmic curl estimates, including time zero. -/
theorem classical_euler_on.exists_spatial_curl_data
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) :
    ∃ D : ℝ → E₃ →ᵇ (E₃ →L[ℝ] E₃), ContinuousOn D (Ico 0 T) ∧
      ∀ t (ht : t ∈ Ico 0 T),
        (∀ x, HasFDerivAt (u t : E₃ → E₃) (D t x) x) ∧
        (∃ K : ℝ≥0, HolderWith K α (D t : E₃ → E₃ →L[ℝ] E₃)) ∧
        MemLp (u t : E₃ → E₃) 2 volume ∧
        (∀ x, LinearMap.trace ℝ E₃ (D t x).toLinearMap = 0) ∧
        (∀ x, Geometry.curlLinearMap.compLeftContinuousBounded E₃ (D t) x =
          vorticity (u t) (h.cartesian_partials t ht) x) := by
  obtain ⟨D, hD, hd, hHolder⟩ := h.2.2.2.2.1
  refine ⟨D, hD, fun t ht => ⟨hd t ht, ?_, h.2.2.2.2.2.1 t ht, ?_, ?_⟩⟩
  · exact (hHolder t ht).imp (fun K hK => hK t ⟨ht.1, le_rfl⟩)
  · exact fun x => by
      simpa only [(hd t ht x).fderiv] using h.2.2.2.2.2.2.2.2.2.2 t ht x
  · exact fun x => by
      simpa only [(hd t ht x).fderiv, ContinuousLinearMap.compLeftContinuousBounded_apply]
        using (h.vorticity_eq_curlLinearMap t ht x).symm
end ClockBarrier.Euler
