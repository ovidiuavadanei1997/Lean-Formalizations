/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! # Normalization of the regularized three-dimensional Newtonian kernel -/

public section

namespace ClockBarrier.Analysis

open Set Filter MeasureTheory
open scoped Topology

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- A radial primitive for the unit-scale regularized Newtonian mass. -/
theorem hasDerivAt_newtonian_radial_primitive (r : ℝ) :
    HasDerivAt (fun s : ℝ => s ^ 3 * (1 + s ^ 2) ^ (-(3 : ℝ) / 2))
      (3 * r ^ 2 * (1 + r ^ 2) ^ (-(5 : ℝ) / 2)) r := by
  have hq : 0 < 1 + r ^ 2 := by positivity
  convert! ((hasDerivAt_id r).pow 3).mul
    (((hasDerivAt_id r).pow 2).const_add 1 |>.rpow_const
      (p := -(3 : ℝ) / 2) (Or.inl hq.ne')) using 1
  norm_num
  rw [show -(3 / 2 : ℝ) = -(5 / 2) + 1 by norm_num, Real.rpow_add hq, Real.rpow_one]
  ring

/-- The radial primitive tends to unit mass at infinity. -/
theorem tendsto_newtonian_radial_primitive :
    Tendsto (fun r : ℝ => r ^ 3 * (1 + r ^ 2) ^ (-(3 : ℝ) / 2)) atTop (𝓝 1) := by
  have hq : Tendsto (fun r : ℝ => 1 + r ^ 2) atTop atTop :=
    tendsto_atTop_mono (fun _ => le_add_of_nonneg_left zero_le_one)
      (tendsto_pow_atTop (by decide : 2 ≠ 0))
  have hi : Tendsto (fun r : ℝ => 1 - (1 + r ^ 2)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hq.inv_tendsto_atTop
  have hp : Tendsto (fun r : ℝ => (1 - (1 + r ^ 2)⁻¹) ^ ((3 : ℝ) / 2))
      atTop (𝓝 1) := by
    simpa using hi.rpow_const (p := (3 : ℝ) / 2) (Or.inl (by norm_num))
  apply hp.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  have heq : 1 - (1 + r ^ 2)⁻¹ = r ^ 2 / (1 + r ^ 2) := by
    field_simp
    ring
  rw [heq, Real.div_rpow (sq_nonneg r) (by positivity)]
  rw [show (-3 : ℝ) / 2 = -(3 / 2) by ring, Real.rpow_neg (by positivity),
    div_eq_mul_inv]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
  norm_num

/-- The radial density has an ordinary convergent integral. -/
theorem integrableOn_newtonian_radial_density :
    IntegrableOn (fun r : ℝ => 3 * r ^ 2 * (1 + r ^ 2) ^ (-(5 : ℝ) / 2))
      (Ioi 0) volume := by
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun r _ => hasDerivAt_newtonian_radial_primitive r)
    (fun r _ => by positivity) tendsto_newtonian_radial_primitive

/-- The radial density has total mass one. -/
theorem integral_newtonian_radial_density :
    (∫ r in Ioi (0 : ℝ), 3 * r ^ 2 * (1 + r ^ 2) ^ (-(5 : ℝ) / 2)) = 1 := by
  simpa using integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0)
    (fun r _ => hasDerivAt_newtonian_radial_primitive r)
    (fun r _ => by positivity) tendsto_newtonian_radial_primitive

/-- The regularized Newtonian mass density is integrable on Euclidean three-space. -/
theorem integrable_newtonian_density :
    Integrable (fun x : E₃ => (3 / (4 * Real.pi)) *
      (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)) volume := by
  rw [integrable_fun_norm_addHaar volume
    (f := fun r : ℝ => (3 / (4 * Real.pi)) * (1 + r ^ 2) ^ (-(5 : ℝ) / 2))]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
  exact (integrableOn_newtonian_radial_density.const_mul (1 / (4 * Real.pi))).congr
    (ae_of_all _ fun r => by ring)

/-- The factor `3 / (4π)` gives exactly unit mass in three dimensions. -/
theorem integral_newtonian_density :
    (∫ x : E₃, (3 / (4 * Real.pi)) *
      (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)) = 1 := by
  have hrad : (∫ r in Ioi (0 : ℝ), r ^ 2 *
      ((3 / (4 * Real.pi)) * (1 + r ^ 2) ^ (-(5 : ℝ) / 2))) = 1 / (4 * Real.pi) := by
    calc
      _ = (1 / (4 * Real.pi)) * ∫ r in Ioi (0 : ℝ),
          3 * r ^ 2 * (1 + r ^ 2) ^ (-(5 : ℝ) / 2) := by
        rw [← integral_const_mul]
        congr 1
        ext r
        ring
      _ = _ := by rw [integral_newtonian_radial_density, mul_one]
  rw [integral_fun_norm_addHaar volume
    (fun r : ℝ => (3 / (4 * Real.pi)) * (1 + r ^ 2) ^ (-(5 : ℝ) / 2))]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
  rw [hrad]
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_three,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  simp only [nsmul_eq_mul]
  field_simp
  ring

end ClockBarrier.Analysis
