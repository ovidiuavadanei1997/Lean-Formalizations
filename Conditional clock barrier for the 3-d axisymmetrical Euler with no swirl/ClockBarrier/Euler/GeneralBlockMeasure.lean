/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.SingularShells
public import ClockBarrier.Euler.AxisBlockMeasure

/-! # Null exceptional planes for the general singular-coordinate blocks -/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Translation and orthogonal coordinates preserve the nullity of a coordinate plane. -/
theorem volume_singular_coordinate_plane (aStar : E₃) (V : E₃ ≃ₗᵢ[ℝ] E₃) (i : Fin 3) :
    volume {a : E₃ | V.symm (a - aStar) i = 0} = 0 := by
  have hm := V.symm.measurePreserving.comp (measurePreserving_add_right volume (-aStar))
  have hp := hm.measure_preimage (s := {a : E₃ | a i = 0})
    (isClosed_eq (EuclideanSpace.proj i).continuous continuous_const).measurableSet.nullMeasurableSet
  simpa only [Function.comp_apply, Set.preimage_setOf_eq, sub_eq_add_neg,
    volume_coordinate_plane i 0] using hp

/-- Almost every label avoids all three rotated affine coordinate planes. -/
theorem ae_singular_coordinates_ne_zero (aStar : E₃) (V : E₃ ≃ₗᵢ[ℝ] E₃) :
    ∀ᵐ a : E₃, ∀ i : Fin 3, V.symm (a - aStar) i ≠ 0 := by
  exact ae_all_iff.mpr (fun i =>
    measure_eq_zero_iff_ae_notMem.mp (volume_singular_coordinate_plane aStar V i))

/-- The literal general shells cover every measurable region up to null planes. -/
theorem iUnion_singular_shell_inter_ae_eq (aStar : E₃) (V : E₃ ≃ₗᵢ[ℝ] E₃)
    {σ : Fin 3 → ℝ} (hσ : ∀ i, 0 < σ i) (s : Set E₃) :
    let E := fun k : Fin 3 → ℤ => {a : E₃ | let η := V.symm (a - aStar)
      (2 : ℝ) ^ (k 2) ≤ |η 2| ∧ |η 2| < 2 * (2 : ℝ) ^ (k 2) ∧
      (2 : ℝ) ^ (k 0) * σ 2 * (2 : ℝ) ^ (k 2) / σ 0 ≤ |η 0| ∧
      |η 0| < 2 * ((2 : ℝ) ^ (k 0) * σ 2 * (2 : ℝ) ^ (k 2) / σ 0) ∧
      (2 : ℝ) ^ (k 1) * σ 2 * (2 : ℝ) ^ (k 2) / σ 1 ≤ |η 1| ∧
      |η 1| < 2 * ((2 : ℝ) ^ (k 1) * σ 2 * (2 : ℝ) ^ (k 2) / σ 1)}
    (⋃ k, E k ∩ s) =ᵐ[volume] s := by
  intro E
  filter_upwards [ae_singular_coordinates_ne_zero aStar V] with a ha
  obtain ⟨k, hk, _⟩ := Geometry.existsUnique_singular_shell hσ ha
  exact propext ⟨fun h => (mem_iUnion.mp h).choose_spec.2,
    fun hs => mem_iUnion.mpr ⟨k, hk, hs⟩⟩

end ClockBarrier.Euler
