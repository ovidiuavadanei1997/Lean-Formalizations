/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.SingularFrame

/-! # Deformation bounds from a smallest singular value barrier -/

public section
namespace ClockBarrier.Geometry
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- A lower bound on the smallest singular value and product one bound the
operator norm by the inverse square of the same lower bound. -/
theorem norm_le_inv_sq_of_singular_frame {F : E₃ →L[ℝ] E₃}
    {U V : E₃ ≃ₗᵢ[ℝ] E₃} {c : ℝ}
    (hframe : ∀ η : E₃, F (V η) = U !₂[F.toLinearMap.singularValues 0 * η 0,
      F.toLinearMap.singularValues 1 * η 1, F.toLinearMap.singularValues 2 * η 2])
    (hprod : F.toLinearMap.singularValues 0 * F.toLinearMap.singularValues 1 *
      F.toLinearMap.singularValues 2 = 1)
    (hc : 0 < c) (hmin : c ≤ F.toLinearMap.singularValues 2) :
    ‖F‖ ≤ (c ^ 2)⁻¹ := by
  apply (norm_le_largest_singularValue_of_frame hframe).trans
  have hmid : c ≤ F.toLinearMap.singularValues 1 :=
    hmin.trans (F.toLinearMap.singularValues_antitone (by decide : 1 ≤ 2))
  have hpair : c ^ 2 ≤ F.toLinearMap.singularValues 1 * F.toLinearMap.singularValues 2 :=
    (sq c).trans_le (mul_le_mul hmid hmin hc.le
      (F.toLinearMap.singularValues_nonneg 1))
  have hmul : F.toLinearMap.singularValues 0 * c ^ 2 ≤ 1 := by
    calc
      F.toLinearMap.singularValues 0 * c ^ 2 ≤
          F.toLinearMap.singularValues 0 *
            (F.toLinearMap.singularValues 1 * F.toLinearMap.singularValues 2) :=
        mul_le_mul_of_nonneg_left hpair (F.toLinearMap.singularValues_nonneg 0)
      _ = 1 := by rw [← mul_assoc, hprod]
  simpa only [one_div] using (le_div_iff₀ (sq_pos_of_pos hc)).mpr hmul

end ClockBarrier.Geometry
