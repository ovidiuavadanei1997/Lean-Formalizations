/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisSmoothNear
public import ClockBarrier.Euler.AxisInitialEnergyFarBound
public import ClockBarrier.Euler.AxisCylindricalAssembly

/-! # The full on-axis driver from weighted near and initial-energy far bounds -/

public section

namespace ClockBarrier.Euler

open Set MeasureTheory Geometry
open scoped NNReal BoundedContinuousFunction Topology ContDiff

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- One cutoff-dependent far constant precedes all Euler solutions and all
geometric and coherence parameters in the actual on-axis strain bound. -/
theorem exists_axis_driver_bound_of_cutoff
    {χ : E₃ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : χ =ᶠ[𝓝 (0 : E₃)] 0)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1) :
    ∃ Cfar : ℝ, 0 ≤ Cfar ∧ ∀
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (_ : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (_ : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (_ : ∀ x, Φ 0 x = x)
    (_ : ∀ s ∈ Ico 0 T, axisymmetric_no_swirl (u s)) (t : ℝ) (ht : t ∈ Ico 0 T)
    (J : {j : ℝ // 0 < j}) (z : ℝ) (L ℓ : {r : ℝ // 0 < r}) (_ : J.val ≤ 1)
    (_ : euclideanMatrix (fderiv ℝ (Φ t) !₂[0, 0, z]) =
      Matrix.diagonal ![J.val⁻¹, J.val⁻¹, J.val ^ 2])
    {Cr cd CF M B : ℝ} {b : ℤ → ℝ}
    (_ : 0 ≤ Cr) (_ : 0 < cd) (_ : 0 ≤ CF) (_ : 0 ≤ M)
    (_ : ∀ a : E₃, ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L.val → ‖a - !₂[0, 0, z]‖ < ℓ.val →
      Real.sqrt ((Φ t a 0)^2 + (Φ t a 1)^2) ≤ Cr * (Real.sqrt ((a 0)^2 + (a 1)^2) / J.val))
    (_ : ∀ a : E₃, ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L.val → ‖a - !₂[0, 0, z]‖ < ℓ.val →
      cd * ‖(fderiv ℝ (Φ t) !₂[0, 0, z]) (a - !₂[0, 0, z])‖ ≤ ‖Φ t a - Φ t !₂[0, 0, z]‖)
    (_ : ∀ a : E₃, ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L.val → ‖a - !₂[0, 0, z]‖ < ℓ.val →
      ‖fderiv ℝ (Φ t) a‖ ≤ CF * ‖fderiv ℝ (Φ t) !₂[0, 0, z]‖)
    (_ : ∀ q : ℤ × ℤ,
      (∫ a in axisClockBlock (Φ t) J z L ℓ q.1 q.2,
        ‖vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩) a‖) ≤
      (M * b q.2) * (((2 : ℝ) ^ q.1) ^ ((α : ℝ) + 2) * J.val ^ (3 * (α : ℝ) + 6) *
        ((2 : ℝ) ^ q.2) ^ ((α : ℝ) + 3)))
    (_ : ∀ n, 0 ≤ b n)
    (_ : ∀ q : Finset ℤ, (∀ n ∈ q, (2 : ℝ) ^ n ≤ ℓ.val) →
      ∑ n ∈ q, ((2 : ℝ) ^ n) ^ (α : ℝ) * b n ≤ B)
    {BR : ℝ}
    (_ : (∫ a in {a : E₃ | ℓ.val ≤ ‖a - !₂[0, 0, z]‖ ∧
        ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L.val},
      Real.sqrt ((Φ t a 0)^2 + (Φ t a 1)^2) * |Φ t a 2 - Φ t !₂[0, 0, z] 2| /
        ‖Φ t a - Φ t !₂[0, 0, z]‖ ^ 5 *
          ‖vorticity (u t) (h.cartesian_partials t ht) (Φ t a)‖) ≤ BR),
    |deriv (fun s : ℝ => u t !₂[0, 0, s] 2) (Φ t !₂[0, 0, z] 2)| ≤
      (3 / (4 * Real.pi)) *
        (((((2 * Cr) / cd ^ 4) * CF * M) *
          (∑' k : ℤ, ((2 : ℝ) ^ k) ^ ((α : ℝ) + 3) / (1 + ((2 : ℝ) ^ k)^2)^2) *
            B * J.val ^ (3 * (α : ℝ) - 1)) + BR) +
      Cfar * L.val ^ (-(5 : ℝ) / 2) * Real.sqrt (∫ y : E₃, ‖u 0 y‖ ^ 2) := by
  obtain ⟨Cfar, hCfar, hfar⟩ :=
    exists_axis_smooth_far_initial_energy_bound hχ hzero hχ₀ hχ₁ houter

  refine ⟨Cfar, hCfar, ?_⟩

  intro α T u p h Φ hcont hode hinit haxis t ht J z L ℓ hJ₁ hA
    Cr cd CF M B b hCr hcd hCF hM hr hd hF hmass hb hB BR hcoh

  have hnear := h.abs_axis_smooth_near_le hcont hode hinit haxis t ht J z L ℓ hJ₁ hA
    hCr hcd hCF hM hr hd hF hmass hb hB hχ.continuous hχ₀ hχ₁ hcoh

  rw [h.deriv_axis_eq_smooth_near_add_far_of_cylindrical hcont hode hinit haxis t ht z
    hχ.continuous hχ₀ hχ₁ houter L.property]

  exact (abs_add_le _ _).trans
    (add_le_add hnear (hfar h t ht (Φ t !₂[0, 0, z] 2) L.property).2)

end ClockBarrier.Euler
