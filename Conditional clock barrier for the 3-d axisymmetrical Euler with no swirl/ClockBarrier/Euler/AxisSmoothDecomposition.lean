/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisBiotSavart
public import ClockBarrier.Analysis.WeightedDecomposition
import Mathlib.Tactic.Ring

/-! # The exact smooth near/far decomposition of the axis driver

The near integral has weight `1 - χ`; the far integral is over the whole
space. This retains the transition annulus required by integration by parts.
-/

public section

namespace ClockBarrier.Euler

open Set MeasureTheory
open scoped NNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- A smooth far cutoff and its complementary near weight give an exact driver
decomposition, without discarding the transition annulus. -/
theorem classical_euler_on.deriv_axis_eq_smooth_near_add_far
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (t : ℝ) (ht : t ∈ Ico 0 T)
    (haxis : axisymmetric_no_swirl (u t)) (z : ℝ)
    {χ : E₃ → ℝ} (hχ : Continuous χ) (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1) {L : ℝ} (hL : 0 < L) :
    let K := fun y : E₃ => (z - y 2) *
      (y 0 * vorticity (u t) (h.cartesian_partials t ht) y 1 -
        y 1 * vorticity (u t) (h.cartesian_partials t ht) y 0) / ‖y - !₂[0, 0, z]‖ ^ 5
    let η := fun y : E₃ => χ (L⁻¹ • (y - !₂[0, 0, z]))
    deriv (fun s : ℝ => u t !₂[0, 0, s] 2) z =
      -(3 / (4 * Real.pi)) * (∫ y in {y : E₃ | ‖y - !₂[0, 0, z]‖ ≤ L}, (1 - η y) * K y) +
      -(3 / (4 * Real.pi)) * ∫ y : E₃, η y * K y := by
  dsimp only
  have hc : Continuous (fun y : E₃ => χ (L⁻¹ • (y - !₂[0, 0, z]))) :=
    hχ.comp (by fun_prop)
  have hout : ∀ y : E₃, y ∉ {y : E₃ | ‖y - !₂[0, 0, z]‖ ≤ L} →
      χ (L⁻¹ • (y - !₂[0, 0, z])) = 1 := fun y hy => houter _ (by
    simpa only [norm_smul, norm_inv, Real.norm_of_nonneg hL.le, div_eq_mul_inv, mul_comm]
      using (one_le_div hL).mpr (le_of_lt (lt_of_not_ge hy)))
  have heq := Analysis.integral_eq_weighted_near_add_far
    (h.integrable_axis_strain_vorticity t ht haxis z) hc.aestronglyMeasurable
    (fun y => hχ₀ _) (fun y => hχ₁ _) hout
  rw [h.deriv_axis_eq_biot_savart t ht haxis z, heq, mul_add]

/-- The exact correction to the sharp far field is the full transition annulus. -/
theorem classical_euler_on.axis_smooth_far_eq_sharp_add_annulus
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (t : ℝ) (ht : t ∈ Ico 0 T)
    (haxis : axisymmetric_no_swirl (u t)) (z : ℝ)
    {χ : E₃ → ℝ} (hχ : Continuous χ) (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (hinner : ∀ x, ‖x‖ ≤ 1 / 2 → χ x = 0)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1) {L : ℝ} (hL : 0 < L) :
    let K := fun y : E₃ => (z - y 2) *
      (y 0 * vorticity (u t) (h.cartesian_partials t ht) y 1 -
        y 1 * vorticity (u t) (h.cartesian_partials t ht) y 0) / ‖y - !₂[0, 0, z]‖ ^ 5
    let η := fun y : E₃ => χ (L⁻¹ • (y - !₂[0, 0, z]))
    (∫ y : E₃, η y * K y) = (∫ y in {y : E₃ | L < ‖y - !₂[0, 0, z]‖}, K y) +
      ∫ y in {y : E₃ | L / 2 < ‖y - !₂[0, 0, z]‖ ∧ ‖y - !₂[0, 0, z]‖ ≤ L}, η y * K y := by
  dsimp only
  have hc : Continuous (fun y : E₃ => χ (L⁻¹ • (y - !₂[0, 0, z]))) := hχ.comp (by fun_prop)
  refine Analysis.integral_cutoff_eq_far_add_annulus
    (h.integrable_axis_strain_vorticity t ht haxis z) hc.aestronglyMeasurable
    (fun y => hχ₀ _) (fun y => hχ₁ _) (by fun_prop) (L / 2) L ?_ ?_
  · exact fun y hy => hinner _ (by
      simpa only [norm_smul, norm_inv, Real.norm_of_nonneg hL.le, div_eq_mul_inv, mul_comm]
        using (div_le_iff₀ hL).mpr
          (by simpa only [div_eq_mul_inv, mul_comm, one_mul] using hy :
            ‖y - !₂[0, 0, z]‖ ≤ (1 / 2) * L))
  · exact fun y hy => houter _ (by
      simpa only [norm_smul, norm_inv, Real.norm_of_nonneg hL.le, div_eq_mul_inv, mul_comm]
        using (one_le_div hL).mpr hy.le)

end ClockBarrier.Euler
