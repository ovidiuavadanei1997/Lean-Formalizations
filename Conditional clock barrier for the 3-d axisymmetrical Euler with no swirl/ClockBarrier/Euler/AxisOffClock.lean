/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisClockBiotSavart
public import ClockBarrier.Analysis.AxisNearMajorant
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The off-clock near-field contribution to the actual axis strain

The source coherence hypothesis bounds a nonnegative Cartesian integral on
label distance at least ℓ. It controls the strict off-clock piece in the signed
decomposition, with the exact factor `3 / (4 * π)`. Convergence of the larger
majorant is derived from Euler regularity, axis vanishing and change of variables.
-/

public section

namespace ClockBarrier.Euler

open Set Metric MeasureTheory Geometry
open scoped NNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The actual norm-vorticity majorant is integrable on every closed near ball. -/
theorem classical_euler_on.integrableOn_axis_near_majorant
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (t : ℝ) (ht : t ∈ Ico 0 T)
    (haxis : axisymmetric_no_swirl (u t)) (z L : ℝ) :
    IntegrableOn (fun x => Real.sqrt ((x 0)^2 + (x 1)^2) * |x 2 - z| /
      ‖x - !₂[0, 0, z]‖ ^ 5 * ‖vorticity (u t) (h.cartesian_partials t ht) x‖)
      (closedBall !₂[0, 0, z] L) volume := by
  obtain ⟨H, hH⟩ := h.holderWith_vorticity t ht
  exact Analysis.integrableOn_axis_near_majorant_closedBall h.2.1
    (hH t ⟨ht.1, le_rfl⟩) z (h.vorticity_axis_eq_zero t ht haxis z) L

variable {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
  (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
  (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
  (hode : ∀ x, ∀ t ∈ Ico 0 T,
    HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
  (hinit : ∀ x, Φ 0 x = x)
  (haxis : ∀ s ∈ Ico 0 T, axisymmetric_no_swirl (u s))

include h hcont hode hinit haxis

/-- The actual Euler flow pulls back the locally integrable majorant to the
closed physical near region in label space, without coherence assumptions. -/
theorem classical_euler_on.integrableOn_axis_near_majorant_flow
    (t : ℝ) (ht : t ∈ Ico 0 T) (z L : ℝ) :
    IntegrableOn (fun a =>
      Real.sqrt ((Φ t a 0)^2 + (Φ t a 1)^2) * |Φ t a 2 - Φ t !₂[0, 0, z] 2| /
        ‖Φ t a - Φ t !₂[0, 0, z]‖ ^ 5 *
          ‖vorticity (u t) (h.cartesian_partials t ht) (Φ t a)‖)
      {a | ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L} volume := by
  have hi := (h.integrableOn_comp_flow_preimage hcont hode hinit ht).mpr
    (h.integrableOn_axis_near_majorant t ht (haxis t ht) (Φ t !₂[0, 0, z] 2) L)
  simpa only [← h.flow_axis_eq hcont hode hinit haxis t ht z,
    Metric.closedBall, dist_eq_norm, preimage_setOf_eq] using hi

/-- The source's closed off-clock coherence condition bounds the strict
off-clock contribution in the signed Biot–Savart decomposition. -/
theorem classical_euler_on.abs_axisOffClock_biot_savart_le
    (t : ℝ) (ht : t ∈ Ico 0 T) (z L ℓ B : ℝ)
    (hcoh : (∫ a in {a : E₃ | ℓ ≤ ‖a - !₂[0, 0, z]‖ ∧
        ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L},
      Real.sqrt ((Φ t a 0)^2 + (Φ t a 1)^2) * |Φ t a 2 - Φ t !₂[0, 0, z] 2| /
        ‖Φ t a - Φ t !₂[0, 0, z]‖ ^ 5 *
          ‖vorticity (u t) (h.cartesian_partials t ht) (Φ t a)‖) ≤ B) :
    |-(3 / (4 * Real.pi)) *
      ∫ a in {a : E₃ | ℓ < ‖a - !₂[0, 0, z]‖ ∧
          ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L},
        (Φ t !₂[0, 0, z] 2 - Φ t a 2) *
          (Φ t a 0 * vorticity (u t) (h.cartesian_partials t ht) (Φ t a) 1 -
            Φ t a 1 * vorticity (u t) (h.cartesian_partials t ht) (Φ t a) 0) /
              ‖Φ t a - Φ t !₂[0, 0, z]‖ ^ 5| ≤ (3 / (4 * Real.pi)) * B := by
  let G : E₃ → ℝ := fun a =>
    Real.sqrt ((Φ t a 0)^2 + (Φ t a 1)^2) * |Φ t a 2 - Φ t !₂[0, 0, z] 2| /
      ‖Φ t a - Φ t !₂[0, 0, z]‖ ^ 5 *
        ‖vorticity (u t) (h.cartesian_partials t ht) (Φ t a)‖
  have hi : IntegrableOn G
      {a | ℓ ≤ ‖a - !₂[0, 0, z]‖ ∧ ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L} :=
    (h.integrableOn_axis_near_majorant_flow hcont hode hinit haxis t ht z L).mono_set
      (fun _ ha => ha.2)
  have hn : ∀ a, 0 ≤ G a := fun a => by positivity
  have hs : {a : E₃ | ℓ < ‖a - !₂[0, 0, z]‖ ∧ ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L} ⊆
      {a | ℓ ≤ ‖a - !₂[0, 0, z]‖ ∧ ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L} :=
    fun _ ha => ⟨ha.1.le, ha.2⟩
  have hbound : (∫ a in {a : E₃ | ℓ < ‖a - !₂[0, 0, z]‖ ∧
      ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L}, G a) ≤ B :=
    (setIntegral_mono_set hi (Filter.Eventually.of_forall hn)
      (Filter.Eventually.of_forall hs)).trans hcoh
  rw [abs_mul, abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ 3 / (4 * Real.pi) by positivity)]
  refine mul_le_mul_of_nonneg_left
    ((abs_integral_le_integral_abs.trans ?_).trans hbound) (by positivity)
  apply integral_mono
    (h.integrable_axis_strain_vorticity_flow hcont hode hinit haxis t ht z).integrableOn.abs
    (hi.mono_set hs)
  intro a
  have hb := Analysis.abs_signed_axis_kernel_le (Φ t a)
    (vorticity (u t) (h.cartesian_partials t ht) (Φ t a))
    (Φ t !₂[0, 0, z] 2) (‖Φ t a - Φ t !₂[0, 0, z]‖ ^ 5)
  simpa only [G, abs_mul, abs_div, abs_pow, abs_norm, abs_of_nonneg (Real.sqrt_nonneg _)] using hb

/-- One source coherence envelope, independent of the axis label, gives one
integrable signed-contribution envelope throughout the lifespan. -/
theorem classical_euler_on.axisOffClock_biot_savart_uniform
    (L ℓ : ℝ) (B : ℝ → ℝ) (hB : IntegrableOn B (Ico 0 T) volume)
    (hcoh : ∀ t, ∀ ht : t ∈ Ico 0 T, ∀ z : ℝ, (∫ a in {a : E₃ | ℓ ≤ ‖a - !₂[0, 0, z]‖ ∧
        ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L},
      Real.sqrt ((Φ t a 0)^2 + (Φ t a 1)^2) * |Φ t a 2 - Φ t !₂[0, 0, z] 2| /
        ‖Φ t a - Φ t !₂[0, 0, z]‖ ^ 5 *
          ‖vorticity (u t) (h.cartesian_partials t ht) (Φ t a)‖) ≤ B t) :
    IntegrableOn (fun t => (3 / (4 * Real.pi)) * B t) (Ico 0 T) volume ∧
      (∀ t ∈ Ico 0 T, 0 ≤ (3 / (4 * Real.pi)) * B t) ∧
      ∀ t, ∀ ht : t ∈ Ico 0 T, ∀ z : ℝ,
        |-(3 / (4 * Real.pi)) *
          ∫ a in {a : E₃ | ℓ < ‖a - !₂[0, 0, z]‖ ∧
              ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L},
            (Φ t !₂[0, 0, z] 2 - Φ t a 2) *
              (Φ t a 0 * vorticity (u t) (h.cartesian_partials t ht) (Φ t a) 1 -
                Φ t a 1 * vorticity (u t) (h.cartesian_partials t ht) (Φ t a) 0) /
                  ‖Φ t a - Φ t !₂[0, 0, z]‖ ^ 5| ≤ (3 / (4 * Real.pi)) * B t := by
  exact ⟨hB.const_mul _, fun t ht => (abs_nonneg _).trans
    (h.abs_axisOffClock_biot_savart_le hcont hode hinit haxis t ht 0 L ℓ (B t) (hcoh t ht 0)),
    fun t ht z =>
    h.abs_axisOffClock_biot_savart_le hcont hode hinit haxis t ht z L ℓ (B t) (hcoh t ht z)⟩

/-- Removing the clock-local and far contributions from the actual axis strain
leaves a remainder bounded by the source off-clock coherence envelope. -/
theorem classical_euler_on.abs_axis_strain_offClock_remainder_le
    (t : ℝ) (ht : t ∈ Ico 0 T) (z L ℓ B : ℝ)
    (hcoh : (∫ a in {a : E₃ | ℓ ≤ ‖a - !₂[0, 0, z]‖ ∧
        ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L},
      Real.sqrt ((Φ t a 0)^2 + (Φ t a 1)^2) * |Φ t a 2 - Φ t !₂[0, 0, z] 2| /
        ‖Φ t a - Φ t !₂[0, 0, z]‖ ^ 5 *
          ‖vorticity (u t) (h.cartesian_partials t ht) (Φ t a)‖) ≤ B) :
    let K : E₃ → ℝ := fun a => (Φ t !₂[0, 0, z] 2 - Φ t a 2) *
      (Φ t a 0 * vorticity (u t) (h.cartesian_partials t ht) (Φ t a) 1 -
        Φ t a 1 * vorticity (u t) (h.cartesian_partials t ht) (Φ t a) 0) /
          ‖Φ t a - Φ t !₂[0, 0, z]‖ ^ 5
    |deriv (fun s : ℝ => u t !₂[0, 0, s] 2) (Φ t !₂[0, 0, z] 2) +
      (3 / (4 * Real.pi)) *
        ((∫ a in {a | ‖a - !₂[0, 0, z]‖ ≤ ℓ ∧ ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L}, K a) +
         (∫ a in {a | L < ‖Φ t a - Φ t !₂[0, 0, z]‖}, K a))| ≤
      (3 / (4 * Real.pi)) * B := by
  intro K
  calc
    _ = |-(3 / (4 * Real.pi)) * ∫ a in {a : E₃ |
        ℓ < ‖a - !₂[0, 0, z]‖ ∧ ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L}, K a| := by
      congr 1
      rw [h.deriv_axis_eq_clock_add_offClock_add_far hcont hode hinit haxis t ht z L ℓ]
      ring
    _ ≤ _ := h.abs_axisOffClock_biot_savart_le hcont hode hinit haxis t ht z L ℓ B hcoh

end ClockBarrier.Euler
