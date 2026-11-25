/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisWeightedNear

/-! # The complementary smooth near-field estimate in physical coordinates -/

public section

namespace ClockBarrier.Euler

open Set MeasureTheory Geometry
open scoped NNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The actual physical near contribution with complementary smooth weight is
bounded by the clock cusp estimate and the source off-clock envelope. -/
theorem classical_euler_on.abs_axis_smooth_near_le
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
    {χ : E₃ → ℝ} (hχ : Continuous χ)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1) {BR : ℝ}
    (hcoh : (∫ a in {a : E₃ | ℓ.val ≤ ‖a - !₂[0, 0, z]‖ ∧
        ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L.val},
      Real.sqrt ((Φ t a 0)^2 + (Φ t a 1)^2) * |Φ t a 2 - Φ t !₂[0, 0, z] 2| /
        ‖Φ t a - Φ t !₂[0, 0, z]‖ ^ 5 *
          ‖vorticity (u t) (h.cartesian_partials t ht) (Φ t a)‖) ≤ BR) :
    |-(3 / (4 * Real.pi)) *
      ∫ y in {y : E₃ | ‖y - !₂[0, 0, Φ t !₂[0, 0, z] 2]‖ ≤ L.val},
        (1 - χ (L.val⁻¹ • (y - !₂[0, 0, Φ t !₂[0, 0, z] 2]))) *
          ((Φ t !₂[0, 0, z] 2 - y 2) *
            (y 0 * vorticity (u t) (h.cartesian_partials t ht) y 1 -
              y 1 * vorticity (u t) (h.cartesian_partials t ht) y 0) /
                ‖y - !₂[0, 0, Φ t !₂[0, 0, z] 2]‖ ^ 5)| ≤
      (3 / (4 * Real.pi)) *
        (((((2 * Cr) / cd ^ 4) * CF * M) *
          (∑' k : ℤ, ((2 : ℝ) ^ k) ^ ((α : ℝ) + 3) / (1 + ((2 : ℝ) ^ k)^2)^2) *
            B * J.val ^ (3 * (α : ℝ) - 1)) + BR) := by
  have hΦ := (h.contDiff_bijective_measurePreserving_flow hcont hode hinit ht).1.continuous

  have hψ : Continuous (fun a : E₃ => 1 - χ (L.val⁻¹ • (Φ t a - Φ t !₂[0, 0, z]))) :=
    by fun_prop

  have hbnd := h.abs_axis_near_cutoff_le hcont hode hinit haxis t ht J z L ℓ hJ₁ hA
    hCr hcd hCF hM hr hd hF hmass hb hB hψ.aestronglyMeasurable
    (fun a => sub_nonneg.mpr (hχ₁ _)) (fun a => sub_le_self _ (hχ₀ _)) hcoh

  have he := h.setIntegral_flow_preimage hcont hode hinit ht
    (fun y : E₃ => (1 - χ (L.val⁻¹ • (y - Φ t !₂[0, 0, z]))) *
      ((Φ t !₂[0, 0, z] 2 - y 2) *
        (y 0 * vorticity (u t) (h.cartesian_partials t ht) y 1 -
          y 1 * vorticity (u t) (h.cartesian_partials t ht) y 0) /
            ‖y - Φ t !₂[0, 0, z]‖ ^ 5))
    {y : E₃ | ‖y - Φ t !₂[0, 0, z]‖ ≤ L.val}

  rw [← h.flow_axis_eq hcont hode hinit haxis t ht z, ← he]

  exact hbnd

end ClockBarrier.Euler
