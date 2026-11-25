/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisLagrangianBiotSavart
public import ClockBarrier.Euler.AxisVorticityIntegral
import ClockBarrier.Analysis.AxisStrainMajorant
import Mathlib.Tactic.Positivity

/-! # The signed clock-local contribution to the actual axis strain

The cusp mass convention is Cartesian volume. Its Biot–Savart prefactor remains
`3 / (4 * π)`; angular reduction must transform the masses as well as the kernel.
The off-clock and far-field contributions remain separate estimates.
-/

public section

namespace ClockBarrier.Euler

open Set MeasureTheory Geometry
open scoped NNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The signed clock-local part of the Lagrangian Biot–Savart formula obeys the
proved cusp bound. The Euler interface supplies convergence and Cauchy transport. -/
theorem classical_euler_on.abs_axisClock_biot_savart_le
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
      ∑ n ∈ q, ((2 : ℝ) ^ n) ^ (α : ℝ) * b n ≤ B) :
    |-(3 / (4 * Real.pi)) *
      ∫ a in {a : E₃ | ‖a - !₂[0, 0, z]‖ ≤ ℓ.val ∧
          ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L.val},
        (Φ t !₂[0, 0, z] 2 - Φ t a 2) *
          (Φ t a 0 * vorticity (u t) (h.cartesian_partials t ht) (Φ t a) 1 -
            Φ t a 1 * vorticity (u t) (h.cartesian_partials t ht) (Φ t a) 0) /
              ‖Φ t a - Φ t !₂[0, 0, z]‖ ^ 5| ≤
      (3 / (4 * Real.pi)) *
        ((((2 * Cr) / cd ^ 4) * CF * M) *
          (∑' k : ℤ, ((2 : ℝ) ^ k) ^ ((α : ℝ) + 3) / (1 + ((2 : ℝ) ^ k)^2)^2) *
            B * J.val ^ (3 * (α : ℝ) - 1)) := by
  obtain ⟨hmajor, hbound⟩ := h.integrableOn_axisClockKernel_norm_vorticity
    hcont hode hinit t ht J z L ℓ hJ₁ hA hCr hcd hCF hM hr hd hF hmass hb hB
  rw [abs_mul, abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ 3 / (4 * Real.pi) by positivity)]
  refine mul_le_mul_of_nonneg_left
    ((abs_integral_le_integral_abs.trans ?_).trans hbound) (by positivity)
  exact integral_mono
    (h.integrable_axis_strain_vorticity_flow hcont hode hinit haxis t ht z).integrableOn.abs
    hmajor.abs (fun a => Analysis.abs_signed_axis_kernel_le (Φ t a)
      (vorticity (u t) (h.cartesian_partials t ht) (Φ t a))
      (Φ t !₂[0, 0, z] 2) (‖Φ t a - Φ t !₂[0, 0, z]‖ ^ 5))

/-- The actual axis strain splits exactly into the clock-local, off-clock near,
and physical far contributions. All three are restrictions of an absolutely
integrable signed kernel; the boundary belongs to the closed near regions. -/
theorem classical_euler_on.deriv_axis_eq_clock_add_offClock_add_far
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x)
    (haxis : ∀ s ∈ Ico 0 T, axisymmetric_no_swirl (u s))
    (t : ℝ) (ht : t ∈ Ico 0 T) (z L ℓ : ℝ) :
    let K : E₃ → ℝ := fun a => (Φ t !₂[0, 0, z] 2 - Φ t a 2) *
      (Φ t a 0 * vorticity (u t) (h.cartesian_partials t ht) (Φ t a) 1 -
        Φ t a 1 * vorticity (u t) (h.cartesian_partials t ht) (Φ t a) 0) /
          ‖Φ t a - Φ t !₂[0, 0, z]‖ ^ 5
    deriv (fun s : ℝ => u t !₂[0, 0, s] 2) (Φ t !₂[0, 0, z] 2) =
      -(3 / (4 * Real.pi)) *
        ((∫ a in {a | ‖a - !₂[0, 0, z]‖ ≤ ℓ ∧ ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L}, K a) +
         (∫ a in {a | ℓ < ‖a - !₂[0, 0, z]‖ ∧ ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L}, K a) +
         (∫ a in {a | L < ‖Φ t a - Φ t !₂[0, 0, z]‖}, K a)) := by
  intro K
  have hΦ := (h.contDiff_bijective_measurePreserving_flow hcont hode hinit ht).1.continuous
  have hP : MeasurableSet {a : E₃ | ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L} :=
    measurableSet_le (by fun_prop) measurable_const
  have hA : MeasurableSet {a : E₃ | ‖a - !₂[0, 0, z]‖ ≤ ℓ} :=
    measurableSet_le (by fun_prop) measurable_const
  have hi : Integrable K := h.integrable_axis_strain_vorticity_flow hcont hode hinit haxis t ht z
  have he := integral_add_compl hP hi
  rw [← integral_inter_add_sdiff hA
    (hi.integrableOn (s := {a | ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L}))] at he
  refine (h.deriv_axis_eq_biot_savart_flow hcont hode hinit haxis t ht z).trans ?_
  simpa only [setOf_and, Set.sdiff_eq, compl_setOf, not_le, inter_comm]
    using congrArg (fun v : ℝ => -(3 / (4 * Real.pi)) * v) he.symm

end ClockBarrier.Euler

