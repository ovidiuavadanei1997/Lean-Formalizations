/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.AxisFarTranslation
public import ClockBarrier.Euler.VorticityRegularity
import Mathlib.Tactic.Ring

/-! # The smooth far-field estimate for the Euler interface

The right side uses the energy at the current time. Energy conservation is
a separate obligation. The integral contains the entire transition annulus.
-/

public section

namespace ClockBarrier.Euler

open Set MeasureTheory Geometry
open scoped NNReal BoundedContinuousFunction Topology ContDiff

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The actual signed, normalized smooth far field has the energy
bound, uniformly in axis point and cutoff radius. -/
theorem exists_axis_smooth_far_energy_bound
    {χ : E₃ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : χ =ᶠ[𝓝 (0 : E₃)] 0)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ},
      ∀ h : classical_euler_on α T u p, ∀ t, ∀ ht : t ∈ Ico 0 T, ∀ z : ℝ, ∀ {L : ℝ}, 0 < L →
      Integrable (fun y : E₃ => χ (L⁻¹ • (y - !₂[0, 0, z])) * ((z - y 2) *
        (y 0 * vorticity (u t) (h.cartesian_partials t ht) y 1 -
          y 1 * vorticity (u t) (h.cartesian_partials t ht) y 0) / ‖y - !₂[0, 0, z]‖ ^ 5)) volume ∧
      |-(3 / (4 * Real.pi)) * ∫ y : E₃, χ (L⁻¹ • (y - !₂[0, 0, z])) * ((z - y 2) *
        (y 0 * vorticity (u t) (h.cartesian_partials t ht) y 1 -
          y 1 * vorticity (u t) (h.cartesian_partials t ht) y 0) / ‖y - !₂[0, 0, z]‖ ^ 5)| ≤
        C * L ^ (-(5 : ℝ) / 2) * Real.sqrt (∫ y : E₃, ‖u t y‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ :=
    Analysis.exists_translated_axis_far_energy_constant hχ hzero hχ₀ hχ₁ houter
  refine ⟨(3 / (4 * Real.pi)) * C, by positivity, ?_⟩
  intro α T u p h t ht z L hL
  obtain ⟨D, _, hd, hHolder⟩ := h.2.2.2.2.1
  obtain ⟨H, hH⟩ := hHolder t ht
  have hD : HolderWith H α (fderiv ℝ (u t)) := by
    simpa only [show fderiv ℝ (u t) = D t from funext (fun x => (hd t ht x).fderiv)]
      using hH t ⟨ht.1, le_rfl⟩
  have hL2 := h.2.2.2.2.2.1 t ht
  obtain ⟨hi, hb⟩ := hbound (fun x => (hd t ht x).differentiableAt) h.2.1 hD
    ((memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).mp hL2) !₂[0, 0, z] hL
  simp only [PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, sub_zero] at hi hb
  simp_rw [h.vorticity_eq_curlLinearMap t ht,
    show ∀ y : E₃, z - y 2 = -(y 2 - z) from fun y => (neg_sub (y 2) z).symm,
    neg_mul, neg_div, mul_neg]
  refine ⟨hi.neg, ?_⟩
  simp only [integral_neg, abs_neg, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ 3 / (4 * Real.pi))]
  simpa only [mul_assoc, neg_div, Matrix.head_cons, Matrix.tail_cons] using
    mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 3 / (4 * Real.pi))

end ClockBarrier.Euler
