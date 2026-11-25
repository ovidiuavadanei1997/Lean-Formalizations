/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisDriverBound
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # A uniform driver bound for the actual meridional axis clocks

The initialized Euler trajectories determine the clock by their meridional
Jacobian. Positivity and the diagonal axis derivative are proved internally.
Only the source geometric, cusp/tail and off-clock coherence estimates are inputs.
-/

public section

namespace ClockBarrier.Euler

open Set MeasureTheory Geometry
open scoped NNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

/-- Common source coherence constants yield one nonnegative integrable driver
and one clock coefficient, before all times and axis labels. The clock is the
actual meridional derivative determinant; no matrix-shape or positivity premise
is added. The positive block parameter is identified with that actual clock. -/
theorem classical_euler_on.exists_uniform_axis_driver_bound
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x)
    (haxis : ∀ s ∈ Ico 0 T, axisymmetric_no_swirl (u s))
    (L ℓ : {r : ℝ // 0 < r}) {Cr cd CF M Tail : ℝ}
    (hCr : 0 ≤ Cr) (hcd : 0 < cd) (hCF : 0 ≤ CF) (hM : 0 ≤ M)
    (b : ℝ → ℝ → ℤ → ℝ) (BR : ℝ → ℝ) (hBR : IntegrableOn BR (Ico 0 T) volume) :
    let J : ℝ → ℝ → ℝ := fun z t =>
      (fderiv ℝ (fun q : E₂ =>
        (!₂[Φ t !₂[q 0, 0, q 1] 0, Φ t !₂[q 0, 0, q 1] 2] : E₂)) !₂[0, z]).toLinearMap.det
    (∀ t ∈ Ico 0 T, ∀ z : ℝ, ∀ a : E₃,
      ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L.val → ‖a - !₂[0, 0, z]‖ < ℓ.val →
      Real.sqrt ((Φ t a 0)^2 + (Φ t a 1)^2) ≤
        Cr * (Real.sqrt ((a 0)^2 + (a 1)^2) / J z t)) →
    (∀ t ∈ Ico 0 T, ∀ z : ℝ, ∀ a : E₃,
      ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L.val → ‖a - !₂[0, 0, z]‖ < ℓ.val →
      cd * ‖(fderiv ℝ (Φ t) !₂[0, 0, z]) (a - !₂[0, 0, z])‖ ≤
        ‖Φ t a - Φ t !₂[0, 0, z]‖) →
    (∀ t ∈ Ico 0 T, ∀ z : ℝ, ∀ a : E₃,
      ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L.val → ‖a - !₂[0, 0, z]‖ < ℓ.val →
      ‖fderiv ℝ (Φ t) a‖ ≤ CF * ‖fderiv ℝ (Φ t) !₂[0, 0, z]‖) →
    (∀ t ∈ Ico 0 T, ∀ z : ℝ, ∀ j : {r : ℝ // 0 < r}, j.val = J z t → ∀ q : ℤ × ℤ,
      (∫ a in axisClockBlock (Φ t) j z L ℓ q.1 q.2,
        ‖vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩) a‖) ≤
      (M * b t z q.2) * (((2 : ℝ) ^ q.1) ^ ((α : ℝ) + 2) * j.val ^ (3 * (α : ℝ) + 6) *
        ((2 : ℝ) ^ q.2) ^ ((α : ℝ) + 3))) →
    (∀ t ∈ Ico 0 T, ∀ z : ℝ, ∀ n : ℤ, 0 ≤ b t z n) →
    (∀ t ∈ Ico 0 T, ∀ z : ℝ, ∀ q : Finset ℤ, (∀ n ∈ q, (2 : ℝ) ^ n ≤ ℓ.val) →
      ∑ n ∈ q, ((2 : ℝ) ^ n) ^ (α : ℝ) * b t z n ≤ Tail) →
    (∀ t, ∀ ht : t ∈ Ico 0 T, ∀ z : ℝ,
      (∫ a in {a : E₃ | ℓ.val ≤ ‖a - !₂[0, 0, z]‖ ∧ ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L.val},
        Real.sqrt ((Φ t a 0)^2 + (Φ t a 1)^2) * |Φ t a 2 - Φ t !₂[0, 0, z] 2| /
          ‖Φ t a - Φ t !₂[0, 0, z]‖ ^ 5 *
            ‖vorticity (u t) (h.cartesian_partials t ht) (Φ t a)‖) ≤ BR t) →
    ∃ B : ℝ → ℝ, ∃ C : ℝ, 0 ≤ C ∧ IntegrableOn B (Ico 0 T) volume ∧
      (∀ t ∈ Ico 0 T, 0 ≤ B t) ∧
      ∀ t ∈ Ico 0 T, ∀ z : ℝ, J z t ≤ 1 →
        |deriv (fun s : ℝ => u t !₂[0, 0, s] 2) (Φ t !₂[0, 0, z] 2)| ≤
          B t + C * (J z t) ^ (3 * (α : ℝ) - 1) := by
  intro J hr hd hF hmass hb htail hcoh

  obtain ⟨χ, hχ, hzero, hχ₀, hχ₁, _, houter⟩ := Analysis.exists_axis_far_cutoff

  obtain ⟨Cfar, hCfar, hdriver⟩ := exists_axis_driver_bound_of_cutoff hχ hzero hχ₀ hχ₁ houter

  let A : ℝ := (3 / (4 * Real.pi)) * ((((2 * Cr) / cd ^ 4) * CF * M) *
    (∑' k : ℤ, ((2 : ℝ) ^ k) ^ ((α : ℝ) + 3) / (1 + ((2 : ℝ) ^ k)^2)^2) * Tail)

  let F0 : ℝ := Cfar * L.val ^ (-(5 : ℝ) / 2) * Real.sqrt (∫ y : E₃, ‖u 0 y‖ ^ 2)

  have hTail : 0 ≤ Tail := by
    simpa only [Finset.sum_empty] using htail 0 ⟨le_rfl, h.1⟩ 0 ∅ (fun _ hn => False.elim (Finset.notMem_empty _ hn))

  have hA : 0 ≤ A := mul_nonneg (by positivity)
    (mul_nonneg (mul_nonneg (by positivity) (tsum_nonneg (fun _ => by positivity))) hTail)

  have hF0 : 0 ≤ F0 := mul_nonneg
    (mul_nonneg hCfar (Real.rpow_nonneg L.property.le _)) (Real.sqrt_nonneg _)

  refine ⟨fun t => (3 / (4 * Real.pi)) * BR t + F0, A, hA,
    (hBR.const_mul _).add (integrableOn_const
      ((measure_mono Ico_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top).ne), ?_, ?_⟩

  · exact fun t ht => add_nonneg (mul_nonneg (by positivity)
      ((integral_nonneg (fun _ => by positivity)).trans (hcoh t ht 0))) hF0

  · intro t ht z hJ₁

    obtain ⟨hu, hdiff, hD, hbound, hdiv⟩ := h.velocity_regular

    have hclock := (Dynamics.axis_clock_of_cylindrical_velocity (u := fun s x => u s x)
      hu hdiff hD hbound haxis
      hcont hode hinit hdiv h.1 z).2 t ht

    have he := hdriver h hcont hode hinit haxis t ht ⟨J z t, hclock.2.1⟩ z L ℓ hJ₁
      hclock.2.2.1 hCr hcd hCF hM (hr t ht z) (hd t ht z) (hF t ht z)
      (hmass t ht z _ rfl) (hb t ht z) (htail t ht z) (hcoh t ht z)

    refine he.trans_eq ?_

    dsimp only [A, F0]

    ring

end ClockBarrier.Euler
