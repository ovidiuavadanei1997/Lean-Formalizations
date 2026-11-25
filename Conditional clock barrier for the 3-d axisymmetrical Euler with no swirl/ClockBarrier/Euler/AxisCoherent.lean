/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisClockBlock
public import ClockBarrier.Euler.VorticityRegularity
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! # Uniformly finite axis coherence

Source: Section 2, axis labels, of arXiv:2605.31587v3.
See docs/ERRATA-AND-DEVIATIONS.md for the conventions.
-/

@[expose] public section

namespace ClockBarrier.Euler

open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

/-- The axis coherent Euler class with constants uniform on the whole lifespan.
All three geometric comparisons are two-sided. The truncated dyadic tail is
summable with a strict uniform bound. No clock estimate is assumed. -/
def axis_coherent_on (α : ℝ≥0) (T : ℝ) (u : ℝ → E₃ →ᵇ E₃) : Prop :=
  ∃ p : ℝ → E₃ → ℝ, ∃ h : classical_euler_on α T u p,
    (∀ t ∈ Ico 0 T, axisymmetric_no_swirl (u t)) ∧
    ∃ Φ : ℝ → E₃ → E₃,
      (∀ x, Φ 0 x = x) ∧
      (∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T)) ∧
      (∀ x, ∀ t ∈ Ico 0 T,
        HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t) ∧
      let J : ℝ → ℝ → ℝ := fun z t =>
        (fderiv ℝ (fun q : E₂ =>
          (!₂[Φ t !₂[q 0, 0, q 1] 0, Φ t !₂[q 0, 0, q 1] 2] : E₂))
          !₂[0, z]).toLinearMap.det
      ∃ L ℓ cr Cr cd Cd cF CF M Tail : {r : ℝ // 0 < r},
      ∃ b : ℝ → ℝ → ℤ → ℝ, ∃ BR : ℝ → ℝ,
        IntegrableOn BR (Ico 0 T) volume ∧
        (∀ t ∈ Ico 0 T, ∀ z : ℝ, ∀ a : E₃,
          ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L.val → ‖a - !₂[0, 0, z]‖ < ℓ.val →
          cd.val * ‖(fderiv ℝ (Φ t) !₂[0, 0, z]) (a - !₂[0, 0, z])‖ ≤
            ‖Φ t a - Φ t !₂[0, 0, z]‖ ∧
          ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤
            Cd.val * ‖(fderiv ℝ (Φ t) !₂[0, 0, z]) (a - !₂[0, 0, z])‖ ∧
          cr.val * (Real.sqrt ((a 0)^2 + (a 1)^2) / J z t) ≤
            Real.sqrt ((Φ t a 0)^2 + (Φ t a 1)^2) ∧
          Real.sqrt ((Φ t a 0)^2 + (Φ t a 1)^2) ≤
            Cr.val * (Real.sqrt ((a 0)^2 + (a 1)^2) / J z t) ∧
          cF.val * ‖fderiv ℝ (Φ t) !₂[0, 0, z]‖ ≤ ‖fderiv ℝ (Φ t) a‖ ∧
          ‖fderiv ℝ (Φ t) a‖ ≤ CF.val * ‖fderiv ℝ (Φ t) !₂[0, 0, z]‖) ∧
        (∀ t ∈ Ico 0 T, ∀ z : ℝ, ∀ j : {r : ℝ // 0 < r}, j.val = J z t →
          ∀ q : ℤ × ℤ,
          (∫ a in axisClockBlock (Φ t) j z L ℓ q.1 q.2,
            ‖vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩) a‖) ≤
          (M.val * b t z q.2) *
            (((2 : ℝ) ^ q.1) ^ ((α : ℝ) + 2) * j.val ^ (3 * (α : ℝ) + 6) *
              ((2 : ℝ) ^ q.2) ^ ((α : ℝ) + 3))) ∧
        (∀ t ∈ Ico 0 T, ∀ z : ℝ, ∀ n : ℤ, 0 ≤ b t z n) ∧
        (∀ t ∈ Ico 0 T,
          (∀ z : ℝ, Summable (fun n : ℤ =>
            if (2 : ℝ) ^ n ≤ ℓ.val then ((2 : ℝ) ^ n) ^ (α : ℝ) * b t z n else 0)) ∧
          BddAbove (Set.range (fun z : ℝ => ∑' n : ℤ,
            if (2 : ℝ) ^ n ≤ ℓ.val then ((2 : ℝ) ^ n) ^ (α : ℝ) * b t z n else 0)) ∧
          sSup (Set.range (fun z : ℝ => ∑' n : ℤ,
            if (2 : ℝ) ^ n ≤ ℓ.val then
              ((2 : ℝ) ^ n) ^ (α : ℝ) * b t z n else 0)) < Tail.val) ∧
        ∀ t, ∀ ht : t ∈ Ico 0 T, ∀ z : ℝ,
          (∫ a in {a : E₃ | ℓ.val ≤ ‖a - !₂[0, 0, z]‖ ∧
              ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L.val},
            Real.sqrt ((Φ t a 0)^2 + (Φ t a 1)^2) *
                |Φ t a 2 - Φ t !₂[0, 0, z] 2| / ‖Φ t a - Φ t !₂[0, 0, z]‖ ^ 5 *
              ‖vorticity (u t) (h.cartesian_partials t ht) (Φ t a)‖) ≤ BR t

end ClockBarrier.Euler
