/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisClockBlock
public import ClockBarrier.Geometry.AxisDeformation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Deriving dyadic block comparisons from near-field axis coherence

The conclusions are supplied to the analytic kernel estimate. The source's
near-field comparisons remain hypotheses; their propagation is not asserted.
-/

public section

namespace ClockBarrier.Euler

open ClockBarrier.Geometry

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The shells and the actual axis derivative yield the two block scales.
The upper radial comparison pays precisely the shell factor two. -/
theorem axisDyadicBlock_comparisons_of_hasFDerivAt
    {Φ : E₃ → E₃} {A : E₃ →L[ℝ] E₃} (J : {j : ℝ // 0 < j}) {z : ℝ}
    (hD : HasFDerivAt Φ A !₂[0, 0, z])
    (hA : euclideanMatrix A = Matrix.diagonal ![J.val⁻¹, J.val⁻¹, J.val ^ 2])
    {Cr cd : ℝ} (hCr : 0 ≤ Cr) (hcd : 0 ≤ cd) {k n : ℤ} {a : E₃}
    (ha : a ∈ axisDyadicBlock J z k n)
    (hr : Real.sqrt ((Φ a 0)^2 + (Φ a 1)^2) ≤ Cr * (Real.sqrt ((a 0)^2 + (a 1)^2) / J.val))
    (hd : cd * ‖(fderiv ℝ Φ !₂[0, 0, z]) (a - !₂[0, 0, z])‖ ≤ ‖Φ a - Φ !₂[0, 0, z]‖) :
    Real.sqrt ((Φ a 0)^2 + (Φ a 1)^2) ≤
        (2 * Cr) * (2 : ℝ) ^ k * J.val ^ 2 * (2 : ℝ) ^ n ∧
      cd * J.val ^ 2 * (2 : ℝ) ^ n * Real.sqrt (1 + ((2 : ℝ) ^ k)^2) ≤
        ‖Φ a - Φ !₂[0, 0, z]‖ := by
  constructor
  · calc
      _ ≤ Cr * (Real.sqrt ((a 0)^2 + (a 1)^2) / J.val) := hr
      _ ≤ Cr * ((2 * ((2 : ℝ) ^ k * J.val ^ 3 * (2 : ℝ) ^ n)) / J.val) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ha.2.2.2.le J.property.le) hCr
      _ = _ := by
        have hJ : J.val ≠ 0 := ne_of_gt J.property
        field_simp
  · have hnorm := clock_scale_le_norm_of_axis_diagonal
      (η := a - !₂[0, 0, z]) J.property
      (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) k))
      (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) n)) hA
      (by simpa using ha.2.2.1) (by simpa using ha.1)
    rw [hD.fderiv] at hd
    simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left hnorm hcd).trans hd

/-- Source near-field comparisons imply both block comparisons on every strict
clock-block interior, with constants fixed before the block indices and points. -/
theorem axisClockBlock_comparisons_of_coherence
    {Φ : E₃ → E₃} {A : E₃ →L[ℝ] E₃} (J : {j : ℝ // 0 < j}) (z : ℝ)
    (L ℓ : {r : ℝ // 0 < r}) (hD : HasFDerivAt Φ A !₂[0, 0, z])
    (hA : euclideanMatrix A = Matrix.diagonal ![J.val⁻¹, J.val⁻¹, J.val ^ 2])
    {Cr cd : ℝ} (hCr : 0 ≤ Cr) (hcd : 0 ≤ cd)
    (hr : ∀ a : E₃, ‖Φ a - Φ !₂[0, 0, z]‖ ≤ L.val → ‖a - !₂[0, 0, z]‖ < ℓ.val →
      Real.sqrt ((Φ a 0)^2 + (Φ a 1)^2) ≤ Cr * (Real.sqrt ((a 0)^2 + (a 1)^2) / J.val))
    (hd : ∀ a : E₃, ‖Φ a - Φ !₂[0, 0, z]‖ ≤ L.val → ‖a - !₂[0, 0, z]‖ < ℓ.val →
      cd * ‖(fderiv ℝ Φ !₂[0, 0, z]) (a - !₂[0, 0, z])‖ ≤ ‖Φ a - Φ !₂[0, 0, z]‖) :
    ∀ p : ℤ × ℤ, ∀ a ∈ axisClockBlock Φ J z L ℓ p.1 p.2,
      ‖a - !₂[0, 0, z]‖ < ℓ.val →
        Real.sqrt ((Φ a 0)^2 + (Φ a 1)^2) ≤
            (2 * Cr) * (2 : ℝ) ^ p.1 * J.val ^ 2 * (2 : ℝ) ^ p.2 ∧
          cd * J.val ^ 2 * (2 : ℝ) ^ p.2 * Real.sqrt (1 + ((2 : ℝ) ^ p.1)^2) ≤
            ‖Φ a - Φ !₂[0, 0, z]‖ := by
  intro p a ha hstrict
  exact axisDyadicBlock_comparisons_of_hasFDerivAt J hD hA hCr hcd ha.1.1
    (hr a ha.2 hstrict) (hd a ha.2 hstrict)

end ClockBarrier.Euler
