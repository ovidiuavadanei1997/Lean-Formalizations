/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisVorticityStretching
public import ClockBarrier.Euler.AxisCoherentIntegral
import Mathlib.Tactic.NormNum

/-! # Clock-local integrability of actual transported Euler vorticity

The Euler interface supplies flow regularity, vorticity continuity, and Cauchy
transport. The remaining inputs are the geometric near-field comparisons and
the cusp/tail bounds. The integral is a label-space absolute majorant; its
identification with the physical axis strain is a separate obligation.
-/

public section

namespace ClockBarrier.Euler

open Set MeasureTheory Geometry
open scoped Topology NNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The clock-local kernel times the actual transported vorticity norm is
integrable with the cusp/tail bound. No transported-vorticity estimate,
measurability, spatial flow regularity, or initial-vorticity integrability is assumed. -/
theorem classical_euler_on.integrableOn_axisClockKernel_norm_vorticity
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x) (t : ℝ) (ht : t ∈ Ico 0 T)
    (J : {j : ℝ // 0 < j}) (z : ℝ) (L ℓ : {r : ℝ // 0 < r}) (hJ₁ : J.val ≤ 1)
    (hA : euclideanMatrix (fderiv ℝ (Φ t) !₂[0, 0, z]) =
      Matrix.diagonal ![J.val⁻¹, J.val⁻¹, J.val ^ 2])
    {Cr cd CF M B : ℝ} {b : ℤ → ℝ}
    (hCr : 0 ≤ Cr) (hcd : 0 < cd) (hCF : 0 ≤ CF) (hM : 0 ≤ M)
    (hr : ∀ a : E₃, ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L.val → ‖a - !₂[0, 0, z]‖ < ℓ.val →
      Real.sqrt ((Φ t a 0)^2 + (Φ t a 1)^2) ≤ Cr * (Real.sqrt ((a 0)^2 + (a 1)^2) / J.val))
    (hd : ∀ a : E₃, ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L.val → ‖a - !₂[0, 0, z]‖ < ℓ.val →
      cd * ‖(fderiv ℝ (Φ t) !₂[0, 0, z]) (a - !₂[0, 0, z])‖ ≤ ‖Φ t a - Φ t !₂[0, 0, z]‖)
    (hF : ∀ a : E₃, ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L.val → ‖a - !₂[0, 0, z]‖ < ℓ.val →
      ‖fderiv ℝ (Φ t) a‖ ≤ CF * ‖fderiv ℝ (Φ t) !₂[0, 0, z]‖)
    (hmass : ∀ q : ℤ × ℤ,
      (∫ a in axisClockBlock (Φ t) J z L ℓ q.1 q.2,
        ‖vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩) a‖) ≤
      (M * b q.2) * (((2 : ℝ) ^ q.1) ^ ((α : ℝ) + 2) * J.val ^ (3 * (α : ℝ) + 6) *
        ((2 : ℝ) ^ q.2) ^ ((α : ℝ) + 3)))
    (hb : ∀ n, 0 ≤ b n)
    (hB : ∀ q : Finset ℤ, (∀ n ∈ q, (2 : ℝ) ^ n ≤ ℓ.val) →
      ∑ n ∈ q, ((2 : ℝ) ^ n) ^ (α : ℝ) * b n ≤ B) :
    IntegrableOn (fun a =>
      (Real.sqrt ((Φ t a 0)^2 + (Φ t a 1)^2) * (Φ t a 2 - Φ t !₂[0, 0, z] 2) /
        ‖Φ t a - Φ t !₂[0, 0, z]‖ ^ 5) *
          ‖vorticity (u t) (h.cartesian_partials t ht) (Φ t a)‖)
      {a | ‖a - !₂[0, 0, z]‖ ≤ ℓ.val ∧ ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L.val} ∧
    (∫ a in {a | ‖a - !₂[0, 0, z]‖ ≤ ℓ.val ∧ ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L.val},
      |(Real.sqrt ((Φ t a 0)^2 + (Φ t a 1)^2) * (Φ t a 2 - Φ t !₂[0, 0, z] 2) /
        ‖Φ t a - Φ t !₂[0, 0, z]‖ ^ 5) *
          ‖vorticity (u t) (h.cartesian_partials t ht) (Φ t a)‖|) ≤
      (((2 * Cr) / cd ^ 4) * CF * M) *
        (∑' k : ℤ, ((2 : ℝ) ^ k) ^ ((α : ℝ) + 3) / (1 + ((2 : ℝ) ^ k)^2)^2) *
          B * J.val ^ (3 * (α : ℝ) - 1) := by
  have hΦ : ContDiff ℝ 1 (Φ t) := by
    obtain ⟨hu, hdiff, hD, hbound, _⟩ := h.velocity_regular
    exact (Dynamics.flow_spatial_regularity_Ico hu hdiff hD hbound hcont hode hinit t ht).1
  refine integrableOn_axisClockKernel_of_nearField hΦ.continuous
    (((h.continuous_vorticity t ht).comp hΦ.continuous).norm.measurable)
    (h.continuous_vorticity 0 ⟨le_rfl, h.1⟩) J z L ℓ
    ((hΦ.differentiable (by decide)) !₂[0, 0, z]).hasFDerivAt hA
    (lt_of_lt_of_le (by norm_num : (-3 : ℝ) < 0) α.coe_nonneg)
    (NNReal.coe_lt_one.mpr h.2.2.1) hCr hcd hCF hM hr hd ?_ hmass hb hB
  intro q a ha hstrict
  simpa only [abs_of_nonneg (norm_nonneg _), Function.comp_apply] using
    h.norm_vorticity_flow_le_of_axis_comparison hcont hode hinit t ht
      J.property hJ₁ hA a (hF a ha.2 hstrict)

end ClockBarrier.Euler
