/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisBlockComparison
public import ClockBarrier.Euler.AxisClockIntegral
import Mathlib.Tactic.Positivity

/-! # Supplying block geometry to the clock-local integral estimate

Near-field geometric coherence and the actual axis derivative produce the block
comparisons. The transported-vorticity bound remains an explicit input.
-/

public section

namespace ClockBarrier.Euler

open Set MeasureTheory ClockBarrier.Geometry

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The source near-field comparisons supply all dyadic geometry in the clock-local
cusp estimate. The radial shell enlargement contributes the explicit factor two. -/
theorem integrableOn_axisClockKernel_of_nearField
    {Φ : E₃ → E₃} (hΦ : Continuous Φ) {v : E₃ → ℝ} (hvm : Measurable v)
    {ω₀ : E₃ → E₃} (hω : Continuous ω₀)
    (J : {j : ℝ // 0 < j}) (z : ℝ) (L ℓ : {r : ℝ // 0 < r})
    {A : E₃ →L[ℝ] E₃} (hD : HasFDerivAt Φ A !₂[0, 0, z])
    (hA : euclideanMatrix A = Matrix.diagonal ![J.val⁻¹, J.val⁻¹, J.val ^ 2])
    {α Cr cd CV M B : ℝ} {b : ℤ → ℝ}
    (hα₀ : -3 < α) (hα₁ : α < 1) (hCr : 0 ≤ Cr) (hcd : 0 < cd)
    (hCV : 0 ≤ CV) (hM : 0 ≤ M)
    (hr : ∀ a : E₃, ‖Φ a - Φ !₂[0, 0, z]‖ ≤ L.val → ‖a - !₂[0, 0, z]‖ < ℓ.val →
      Real.sqrt ((Φ a 0)^2 + (Φ a 1)^2) ≤ Cr * (Real.sqrt ((a 0)^2 + (a 1)^2) / J.val))
    (hd : ∀ a : E₃, ‖Φ a - Φ !₂[0, 0, z]‖ ≤ L.val → ‖a - !₂[0, 0, z]‖ < ℓ.val →
      cd * ‖(fderiv ℝ Φ !₂[0, 0, z]) (a - !₂[0, 0, z])‖ ≤ ‖Φ a - Φ !₂[0, 0, z]‖)
    (hv : ∀ p : ℤ × ℤ, ∀ a ∈ axisClockBlock Φ J z L ℓ p.1 p.2,
      ‖a - !₂[0, 0, z]‖ < ℓ.val → |v a| ≤ CV * J.val⁻¹ * ‖ω₀ a‖)
    (hmass : ∀ p : ℤ × ℤ, (∫ a in axisClockBlock Φ J z L ℓ p.1 p.2, ‖ω₀ a‖) ≤
      (M * b p.2) * (((2 : ℝ) ^ p.1) ^ (α + 2) * J.val ^ (3 * α + 6) *
        ((2 : ℝ) ^ p.2) ^ (α + 3)))
    (hb : ∀ n, 0 ≤ b n)
    (hB : ∀ q : Finset ℤ, (∀ n ∈ q, (2 : ℝ) ^ n ≤ ℓ.val) →
      ∑ n ∈ q, ((2 : ℝ) ^ n) ^ α * b n ≤ B) :
    IntegrableOn (fun a =>
      (Real.sqrt ((Φ a 0)^2 + (Φ a 1)^2) * (Φ a 2 - Φ !₂[0, 0, z] 2) /
        ‖Φ a - Φ !₂[0, 0, z]‖ ^ 5) * v a)
      {a | ‖a - !₂[0, 0, z]‖ ≤ ℓ.val ∧ ‖Φ a - Φ !₂[0, 0, z]‖ ≤ L.val} ∧
    (∫ a in {a | ‖a - !₂[0, 0, z]‖ ≤ ℓ.val ∧ ‖Φ a - Φ !₂[0, 0, z]‖ ≤ L.val},
      |(Real.sqrt ((Φ a 0)^2 + (Φ a 1)^2) * (Φ a 2 - Φ !₂[0, 0, z] 2) /
        ‖Φ a - Φ !₂[0, 0, z]‖ ^ 5) * v a|) ≤
      (((2 * Cr) / cd ^ 4) * CV * M) *
        (∑' k : ℤ, ((2 : ℝ) ^ k) ^ (α + 3) / (1 + ((2 : ℝ) ^ k)^2)^2) *
          B * J.val ^ (3 * α - 1) := by
  have hcomp := axisClockBlock_comparisons_of_coherence J z L ℓ hD hA hCr hcd.le hr hd
  exact integrableOn_axisClockKernel_of_cusp hΦ hvm hω J z L ℓ hα₀ hα₁
    (by positivity) hcd hCV hM
    (fun p a ha hstrict => (hcomp p a ha hstrict).1)
    (fun p a ha hstrict => (hcomp p a ha hstrict).2) hv hmass hb hB

end ClockBarrier.Euler
