/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.GeneralCoherenceWellDefined
public import ClockBarrier.Analysis.EuclideanSlices

/-! # Almost-everywhere estimates for the literal clock-slice average -/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

/-- Pointwise bounds on each positive-area slice give the corresponding
almost-everywhere bound for the source's zero-on-null-slices average. -/
theorem ae_norm_clock_slice_average_sub_le
    (aStar : E₃) (V : E₃ ≃ₗᵢ[ℝ] E₃) (W : E₃ →ᵇ E₃)
    {S : Set E₃} (hS : MeasurableSet S) {ℓ : ℝ}
    (hclock : ∀ a ∈ S, ‖a - aStar‖ < ℓ) (c : E₃ → E₃) (C : E₃ → ℝ)
    (hbound : ∀ a ∈ S, ∀ q : E₂,
      aStar + V !₂[q 0, q 1, V.symm (a - aStar) 2] ∈ S →
      ‖W (aStar + V !₂[q 0, q 1, V.symm (a - aStar) 2]) - c a‖ ≤ C a) :
    let A := fun s : ℝ => {q : E₂ | aStar + V !₂[q 0, q 1, s] ∈ S}
    let avg := fun s : ℝ => if volume (A s) = 0 then (0 : E₃) else
      (volume (A s)).toReal⁻¹ • ∫ q in A s, W (aStar + V !₂[q 0, q 1, s])
    ∀ᵐ a ∂volume.restrict S, ‖avg (V.symm (a - aStar) 2) - c a‖ ≤ C a := by
  intro A avg
  filter_upwards [Analysis.ae_affine_slice_measure_ne_zero aStar V hS, ae_restrict_mem hS]
    with a ha0 ha
  rw [show avg (V.symm (a - aStar) 2) =
      (volume (A (V.symm (a - aStar) 2))).toReal⁻¹ •
        ∫ q in A (V.symm (a - aStar) 2),
          W (aStar + V !₂[q 0, q 1, V.symm (a - aStar) 2]) from if_neg ha0]
  exact Analysis.norm_normalized_integral_sub_le ha0
    (clock_slice_measure_lt_top aStar V hclock _).ne
    (integrableOn_clock_slice aStar V hclock W _)
    ((ae_restrict_mem (hS.preimage (by fun_prop))).mono
      (fun q hq => hbound a ha q hq))

end ClockBarrier.Euler
