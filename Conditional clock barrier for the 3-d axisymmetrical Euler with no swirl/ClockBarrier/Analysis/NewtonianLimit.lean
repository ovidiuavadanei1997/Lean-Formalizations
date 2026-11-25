/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.NewtonianNormalization
public import ClockBarrier.Analysis.NewtonianDerivatives
public import ClockBarrier.Analysis.AxisStrainKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Removing the Newtonian regularization by dominated convergence -/

public section

namespace ClockBarrier.Analysis

open Set Filter MeasureTheory
open scoped Topology

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The normalized regularized Newtonian density is an approximate identity. -/
theorem tendsto_integral_newtonian_density_smul
    {g : E₃ → ℝ} (hg : Continuous g) {B : ℝ} (hB : ∀ x, |g x| ≤ B) :
    Tendsto (fun ε : ℝ => ∫ x : E₃,
      (3 / (4 * Real.pi)) * (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) * g (ε • x))
      (𝓝 0) (𝓝 (g 0)) := by
  have hc := (contDiff_newtonian_power (-(5 : ℝ) / 2)).continuous
  have hlim : Tendsto (fun ε : ℝ => ∫ x : E₃,
      (3 / (4 * Real.pi)) * (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) * g (ε • x))
      (𝓝 0) (𝓝 (∫ x : E₃,
        (3 / (4 * Real.pi)) * (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) * g 0)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun x : E₃ => ((3 / (4 * Real.pi)) * (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)) * B)
    · exact Eventually.of_forall fun ε => (Continuous.aestronglyMeasurable (by fun_prop))
    · exact Eventually.of_forall fun ε => ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity :
          0 ≤ (3 / (4 * Real.pi)) * (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2))]
        exact mul_le_mul_of_nonneg_left (hB _) (by positivity)
    · exact integrable_newtonian_density.mul_const B
    · exact ae_of_all _ fun x => by
        have hpoint : ContinuousAt (fun ε : ℝ => g (ε • x)) 0 := by fun_prop
        simpa only [zero_smul] using
          hpoint.tendsto.const_mul
            ((3 / (4 * Real.pi)) * (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2))
  simpa only [integral_mul_const, integral_newtonian_density, one_mul] using hlim

/-- Conversion of the limiting radial power to the inverse fifth power. -/
theorem norm_sq_rpow_neg_five_halves (x : E₃) :
    (‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) = 1 / ‖x‖ ^ 5 := by
  rw [← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_mul (norm_nonneg x)]
  norm_num [Real.rpow_neg (norm_nonneg x)]

/-- Absolute convergence of the singular integral permits removal of the
regularization under the integral sign. -/
theorem tendsto_integral_regularized_axis_kernel
    {ω : E₃ → E₃} (hω : Continuous ω)
    (hi : Integrable (fun x => x 2 * (x 0 * ω x 1 - x 1 * ω x 0) / ‖x‖ ^ 5) volume) :
    Tendsto (fun ε : ℝ => ∫ x : E₃,
      3 * x 2 * (x 0 * ω x 1 - x 1 * ω x 0) *
        (ε ^ 2 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)) (𝓝 0)
      (𝓝 (3 * ∫ x : E₃, x 2 * (x 0 * ω x 1 - x 1 * ω x 0) / ‖x‖ ^ 5)) := by
  rw [← integral_const_mul]
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => 3 * |x 2 * (x 0 * ω x 1 - x 1 * ω x 0) / ‖x‖ ^ 5|)
  · exact Eventually.of_forall fun ε => Measurable.aestronglyMeasurable (by fun_prop)
  · refine Eventually.of_forall fun ε => ae_of_all _ fun x => ?_
    by_cases hx : x = 0
    · subst x
      simp
    have hp : (ε ^ 2 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) ≤ 1 / ‖x‖ ^ 5 := by
      rw [← norm_sq_rpow_neg_five_halves]
      exact Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos (norm_pos_iff.mpr hx))
        (le_add_of_nonneg_left (sq_nonneg ε)) (by norm_num)
    simp only [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_norm,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
      abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ ε ^ 2 + ‖x‖ ^ 2) (-(5 : ℝ) / 2))]
    calc
      _ ≤ 3 * |x 2| * |x 0 * ω x 1 - x 1 * ω x 0| * (1 / ‖x‖ ^ 5) := by gcongr
      _ = _ := by ring
  · exact hi.norm.const_mul 3
  · refine ae_of_all _ fun x => ?_
    by_cases hx : x = 0
    · subst x
      simp
    have hp : ContinuousAt (fun ε : ℝ => (ε ^ 2 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)) 0 := by
      apply ContinuousAt.rpow_const (by fun_prop)
      left
      simpa using (sq_pos_of_pos (norm_pos_iff.mpr hx)).ne'
    have ht := hp.tendsto.const_mul (3 * x 2 * (x 0 * ω x 1 - x 1 * ω x 0))
    simp only [zero_pow (by decide : 2 ≠ 0), zero_add, norm_sq_rpow_neg_five_halves] at ht
    simpa only [div_eq_mul_inv, one_mul, mul_assoc] using ht

end ClockBarrier.Analysis
