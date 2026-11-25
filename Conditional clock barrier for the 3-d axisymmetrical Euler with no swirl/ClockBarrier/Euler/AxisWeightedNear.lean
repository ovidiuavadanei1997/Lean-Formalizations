/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisOffClock
public import ClockBarrier.Analysis.WeightedNear
import ClockBarrier.Analysis.AxisStrainMajorant
import Mathlib.Tactic.Positivity

/-! # Complementary near weights in the actual Lagrangian axis integral -/

public section

namespace ClockBarrier.Euler

open Set MeasureTheory Geometry
open scoped NNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Any measurable weight between zero and one preserves the clock-local
cusp bound plus the off-clock coherence bound, with the original normalization. -/
theorem classical_euler_on.abs_axis_near_cutoff_le
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x)
    (haxis : ∀ s ∈ Ico 0 T, axisymmetric_no_swirl (u s)) (t : ℝ) (ht : t ∈ Ico 0 T)
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
      ∑ n ∈ q, ((2 : ℝ) ^ n) ^ (α : ℝ) * b n ≤ B)
    {ψ : E₃ → ℝ} (hψ : AEStronglyMeasurable ψ volume)
    (hψ₀ : ∀ a, 0 ≤ ψ a) (hψ₁ : ∀ a, ψ a ≤ 1) {BR : ℝ}
    (hcoh : (∫ a in {a : E₃ | ℓ.val ≤ ‖a - !₂[0, 0, z]‖ ∧
        ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L.val},
      Real.sqrt ((Φ t a 0)^2 + (Φ t a 1)^2) * |Φ t a 2 - Φ t !₂[0, 0, z] 2| /
        ‖Φ t a - Φ t !₂[0, 0, z]‖ ^ 5 *
          ‖vorticity (u t) (h.cartesian_partials t ht) (Φ t a)‖) ≤ BR) :
    |-(3 / (4 * Real.pi)) *
      ∫ a in {a : E₃ | ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L.val}, ψ a *
        ((Φ t !₂[0, 0, z] 2 - Φ t a 2) *
          (Φ t a 0 * vorticity (u t) (h.cartesian_partials t ht) (Φ t a) 1 -
            Φ t a 1 * vorticity (u t) (h.cartesian_partials t ht) (Φ t a) 0) /
              ‖Φ t a - Φ t !₂[0, 0, z]‖ ^ 5)| ≤
      (3 / (4 * Real.pi)) *
        (((((2 * Cr) / cd ^ 4) * CF * M) *
          (∑' k : ℤ, ((2 : ℝ) ^ k) ^ ((α : ℝ) + 3) / (1 + ((2 : ℝ) ^ k)^2)^2) *
            B * J.val ^ (3 * (α : ℝ) - 1)) + BR) := by
  obtain ⟨_, hbound⟩ := h.integrableOn_axisClockKernel_norm_vorticity
    hcont hode hinit t ht J z L ℓ hJ₁ hA hCr hcd hCF hM hr hd hF hmass hb hB

  rw [abs_mul, abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ 3 / (4 * Real.pi) by positivity)]

  refine mul_le_mul_of_nonneg_left
    (Analysis.abs_integral_cutoff_mul_le_add_of_majorant
      (h.integrable_axis_strain_vorticity_flow hcont hode hinit haxis t ht z).integrableOn
      (h.integrableOn_axis_near_majorant_flow hcont hode hinit haxis t ht z L.val)
      (a := {a : E₃ | ‖a - !₂[0, 0, z]‖ ≤ ℓ.val})
      (measurableSet_le (by fun_prop) measurable_const)
      hψ.restrict hψ₀ hψ₁ ?_ ?_ ?_) (by positivity)

  · intro a
    have hk := Analysis.abs_signed_axis_kernel_le (Φ t a)
      (vorticity (u t) (h.cartesian_partials t ht) (Φ t a))
      (Φ t !₂[0, 0, z] 2) (‖Φ t a - Φ t !₂[0, 0, z]‖ ^ 5)

    simpa only [abs_mul, abs_div, abs_pow, abs_norm, abs_of_nonneg (Real.sqrt_nonneg _)] using hk

  · simpa only [setOf_and, inter_comm, abs_mul, abs_div, abs_pow, abs_norm,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hbound

  · exact (setIntegral_mono_set
      ((h.integrableOn_axis_near_majorant_flow hcont hode hinit haxis t ht z L.val).mono_set
        (fun _ ha => ha.2))
      (Filter.Eventually.of_forall (fun _ => by positivity))
      (Filter.Eventually.of_forall (fun _ ha => ⟨(lt_of_not_ge ha.2).le, ha.1⟩))).trans hcoh

end ClockBarrier.Euler
