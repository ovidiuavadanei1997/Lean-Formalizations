/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Scalar-component pairings controlled by kinetic energy -/

public section

namespace ClockBarrier.Analysis

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- Cauchy--Schwarz in a form using square roots of energy integrals. -/
theorem integral_mul_norm_le_sqrt_energy {f : X → E} {g : X → F}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, ‖f x‖ * ‖g x‖ ∂μ) ≤
      Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  have hh := integral_mul_norm_le_Lp_mul_Lq (μ := μ)
    Real.HolderConjugate.two_two
    (by simpa only [ENNReal.ofReal_ofNat] using hf.norm)
    (by simpa only [ENNReal.ofReal_ofNat] using hg.norm)
  simpa only [norm_norm, Real.rpow_ofNat, Real.sqrt_eq_rpow] using hh

/-- Pairing a scalar kernel with one velocity component is bounded by the
kernel's `L²` norm and the full kinetic energy. -/
theorem abs_integral_mul_coordinate_le_sqrt_energy
    {f : X → ℝ} {u : X → EuclideanSpace ℝ (Fin 3)}
    (hf : MemLp f 2 μ) (hu : MemLp u 2 μ) (k : Fin 3) :
    |∫ x, f x * u x k ∂μ| ≤
      Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂μ) := by
  refine abs_integral_le_integral_abs.trans (le_trans ?_ (integral_mul_norm_le_sqrt_energy hf hu))
  apply integral_mono (hf.integrable_mul ((EuclideanSpace.proj (𝕜 := ℝ) k).comp_memLp' hu)).abs
    (hf.norm.integrable_mul hu.norm)
  intro x
  change |f x * u x k| ≤ ‖f x‖ * ‖u x‖
  simpa only [abs_mul, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_left (PiLp.norm_apply_le (u x) k) (norm_nonneg (f x))

end ClockBarrier.Analysis
