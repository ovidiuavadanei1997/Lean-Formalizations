/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisBarrier

/-! # Constructing an Euler flow with the conditional physical axis barrier

The flow is constructed before any coherence parameters are chosen. Its actual
physical axis clocks share a positive lower bound whenever the source coherence
conditions hold with common constants and an integrable off-clock envelope.
-/

public section

namespace ClockBarrier.Euler

open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

/-- The Euler interface constructs a measure-preserving spatially C¹
bijective flow and supplies its uniform physical axis barrier under the explicit
source coherence assumptions. No flow, strain estimate or clock ODE is assumed. -/
theorem classical_euler_on.exists_flow_with_axis_clock_barrier
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (hα : (1 / 3 : ℝ) ≤ (α : ℝ))
    (haxis : ∀ s ∈ Ico 0 T, axisymmetric_no_swirl (u s)) :
    ∃ Φ : ℝ → E₃ → E₃,
      (∀ x, Φ 0 x = x) ∧
      (∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T)) ∧
      (∀ x, ∀ t ∈ Ico 0 T,
        HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t) ∧
      (∀ t ∈ Ico 0 T, ContDiff ℝ 1 (Φ t) ∧ Function.Bijective (Φ t) ∧
        MeasurePreserving (Φ t) volume volume) ∧ ∀
    (L ℓ : {r : ℝ // 0 < r}) {Cr cd CF M Tail : ℝ}
    (_ : 0 ≤ Cr) (_ : 0 < cd) (_ : 0 ≤ CF) (_ : 0 ≤ M)
    (b : ℝ → ℝ → ℤ → ℝ) (BR : ℝ → ℝ) (_ : IntegrableOn BR (Ico 0 T) volume),
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
  obtain ⟨Φ, hi, hc, ho, hreg⟩ := h.exists_measurePreserving_flow

  refine ⟨Φ, hi, hc, ho, hreg, ?_⟩

  intro L ℓ Cr cd CF M Tail hCr hcd hCF hM b BR hBR

  exact h.exists_uniform_axis_clock_barrier hα hc ho hi haxis L ℓ hCr hcd hCF hM b BR hBR

end ClockBarrier.Euler
