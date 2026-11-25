/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisUniformDriver
public import ClockBarrier.Analysis.ClockDriver

/-! # Uniform noncollapse of the actual physical axis clocks

Common source coherence supplies the driver. The initialized Euler flow supplies
normalization, positivity, the physical Jacobian limit and the exact clock ODE.
The scalar barrier then gives one positive lower bound before all axis labels.
-/

public section

namespace ClockBarrier.Euler

open Set Filter MeasureTheory Geometry
open scoped Topology NNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

/-- The actual meridional clocks stay uniformly positive under the source
coherence hypotheses. Their physical-radius Jacobians converge from positive
radius to these clocks. The driver, normalization and evolution are proved
internally, including the factor one-half in the clock equation. -/
theorem classical_euler_on.exists_uniform_axis_clock_barrier
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (hα : (1 / 3 : ℝ) ≤ (α : ℝ))
    {Φ : ℝ → E₃ → E₃}
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
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℝ, ∀ t ∈ Ico 0 T,
      c ≤ J z t ∧
      Tendsto (fun r : ℝ =>
        (fderiv ℝ (fun q : E₂ =>
          (!₂[Real.sqrt ((Φ t !₂[q 0, 0, q 1] 0)^2 + (Φ t !₂[q 0, 0, q 1] 1)^2),
            Φ t !₂[q 0, 0, q 1] 2] : E₂)) !₂[r, z]).toLinearMap.det)
        (𝓝[>] 0) (𝓝 (J z t)) := by
  intro J hr hd hF hmass hb htail hcoh

  obtain ⟨B, C, hC, hB, hB₀, hdriver⟩ := h.exists_uniform_axis_driver_bound
    hcont hode hinit haxis L ℓ hCr hcd hCF hM b BR hBR hr hd hF hmass hb htail hcoh

  obtain ⟨c, hc, hbarrier⟩ := Analysis.exists_pos_lower_bound_of_axis_driver hC hα hB hB₀

  obtain ⟨hu, hdiff, hD, hbound, hdiv⟩ := h.velocity_regular

  refine ⟨c, hc, fun z => ?_⟩

  have hclock := Dynamics.axis_clock_of_cylindrical_velocity (u := fun s x => u s x)
    hu hdiff hD hbound haxis hcont hode hinit hdiv h.1 z

  have hlower := hbarrier (J z)
    (fun t => deriv (fun s : ℝ => u t !₂[0, 0, s] 2) (Φ t !₂[0, 0, z] 2))
    hclock.1 (fun t ht => (hclock.2 t ht).2.1)
    (fun t ht => (hclock.2 t ht).2.2.2.2)
    (fun t ht hsmall => hdriver t ⟨ht.1.le, ht.2⟩ z hsmall)

  exact fun t ht => ⟨hlower t ht, (hclock.2 t ht).2.2.2.1⟩

end ClockBarrier.Euler
