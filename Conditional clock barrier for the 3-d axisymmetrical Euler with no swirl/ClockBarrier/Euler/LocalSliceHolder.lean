/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.ClockSliceAverage
public import ClockBarrier.Geometry.LocalShellGeometry

/-! # Hölder estimates for clock-slice averages -/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

/-- The dyadic coordinate bounds control the longitudinal average by a Hölder
increment at the actual label distance, almost everywhere in the block. -/
theorem ae_norm_clock_average_sub_center_le
    {α H : ℝ≥0} (aStar : E₃) (V : E₃ ≃ₗᵢ[ℝ] E₃) (W : E₃ →ᵇ E₃)
    (hW : HolderWith H α W) {S : Set E₃} (hS : MeasurableSet S) {ℓ : ℝ}
    (hclock : ∀ a ∈ S, ‖a - aStar‖ < ℓ) {r : Fin 3 → ℝ}
    (hshell : ∀ a ∈ S, ∀ i, r i ≤ |V.symm (a - aStar) i| ∧
      |V.symm (a - aStar) i| ≤ 2 * r i) :
    let A := fun s : ℝ => {q : E₂ | aStar + V !₂[q 0, q 1, s] ∈ S}
    let avg := fun s : ℝ => if volume (A s) = 0 then (0 : E₃) else
      (volume (A s)).toReal⁻¹ • ∫ q in A s, W (aStar + V !₂[q 0, q 1, s])
    ∀ᵐ a ∂volume.restrict S, ‖avg (V.symm (a - aStar) 2) - W aStar‖ ≤
      ((H : ℝ) * (2 : ℝ) ^ (α : ℝ)) * ‖a - aStar‖ ^ (α : ℝ) := by
  apply ae_norm_clock_slice_average_sub_le aStar V W hS hclock
  intro a ha q hq
  have hb := Geometry.norm_le_two_mul_of_shell_bounds
    (fun i => (hshell _ hq i).2) (fun i => (hshell a ha i).1)
  simpa only [dist_eq_norm, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
    (norm_nonneg (a - aStar)), mul_assoc] using hW.dist_le_of_le
      (show dist (aStar + V !₂[q 0, q 1, V.symm (a - aStar) 2]) aStar ≤
        2 * ‖a - aStar‖ by simpa only [dist_eq_norm, V.symm.norm_map] using hb)

/-- Hölder continuity and the transverse slice diameter give the integrated-cusp
pointwise majorant on almost every label, including arbitrary orthogonal frames. -/
theorem ae_norm_clock_average_sub_value_le
    {α H : ℝ≥0} (aStar : E₃) (V : E₃ ≃ₗᵢ[ℝ] E₃) (W : E₃ →ᵇ E₃)
    (hW : HolderWith H α W) {S : Set E₃} (hS : MeasurableSet S) {ℓ : ℝ}
    (hclock : ∀ a ∈ S, ‖a - aStar‖ < ℓ) {r l₀ l₁ : ℝ}
    (hr : 0 ≤ r) (hl₀ : 0 ≤ l₀) (hl₁ : 0 ≤ l₁)
    (hbox : ∀ a ∈ S, |V.symm (a - aStar) 0| ≤ 2 * (l₀ * r) ∧
      |V.symm (a - aStar) 1| ≤ 2 * (l₁ * r)) :
    let A := fun s : ℝ => {q : E₂ | aStar + V !₂[q 0, q 1, s] ∈ S}
    let avg := fun s : ℝ => if volume (A s) = 0 then (0 : E₃) else
      (volume (A s)).toReal⁻¹ • ∫ q in A s, W (aStar + V !₂[q 0, q 1, s])
    ∀ᵐ a ∂volume.restrict S, ‖avg (V.symm (a - aStar) 2) - W a‖ ≤
      ((H : ℝ) * (4 : ℝ) ^ (α : ℝ)) *
        (r * Real.sqrt (l₀ ^ 2 + l₁ ^ 2)) ^ (α : ℝ) := by
  apply ae_norm_clock_slice_average_sub_le aStar V W hS hclock
  intro a ha q hq
  have hb := Geometry.norm_sub_le_transverse_shell_diameter hr hl₀ hl₁
    (x := V.symm (aStar + V !₂[q 0, q 1, V.symm (a - aStar) 2] - aStar))
    (y := V.symm (a - aStar)) (by simp)
    (hbox _ hq).1 (hbox _ hq).2 (hbox a ha).1 (hbox a ha).2
  simpa only [dist_eq_norm, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4)
    (mul_nonneg hr (Real.sqrt_nonneg _)), mul_assoc] using hW.dist_le_of_le
      (show dist (aStar + V !₂[q 0, q 1, V.symm (a - aStar) 2]) a ≤
        4 * (r * Real.sqrt (l₀ ^ 2 + l₁ ^ 2)) by
          simpa only [← map_sub, sub_sub_sub_cancel_right, V.symm.norm_map, dist_eq_norm] using hb)

end ClockBarrier.Euler
