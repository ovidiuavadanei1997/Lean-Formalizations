/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.NewtonianLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Dominated convergence for a general regularized strain numerator -/

public section
namespace ClockBarrier.Analysis
open Filter MeasureTheory
open scoped Topology
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Regularization decreases the absolute inverse-fifth-power kernel. -/
theorem abs_regularized_radial_numerator_le {f : E₃ → ℝ} (hf0 : f 0 = 0)
    (ε : ℝ) (x : E₃) :
    |f x * (ε ^ 2 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)| ≤ |f x / ‖x‖ ^ 5| := by
  by_cases hx : x = 0
  · simp [hx, hf0]
  have hp : (ε ^ 2 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) ≤ 1 / ‖x‖ ^ 5 := by
    rw [← norm_sq_rpow_neg_five_halves]
    exact Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos (norm_pos_iff.mpr hx))
      (le_add_of_nonneg_left (sq_nonneg ε)) (by norm_num)
  simp only [abs_mul, abs_div, abs_pow, abs_norm,
    abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ ε ^ 2 + ‖x‖ ^ 2) (-(5 : ℝ) / 2))]
  simpa only [one_div, div_eq_mul_inv, one_mul] using
    mul_le_mul_of_nonneg_left hp (abs_nonneg (f x))

/-- Absolute convergence of a singular numerator implies convergence of each
of its regularizations. -/
theorem integrable_regularized_radial_numerator {f : E₃ → ℝ} (hf : Measurable f)
    (hf0 : f 0 = 0) (hi : Integrable (fun x => f x / ‖x‖ ^ 5) volume) (ε : ℝ) :
    Integrable (fun x => f x * (ε ^ 2 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)) volume := by
  refine hi.abs.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  exact ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs] using abs_regularized_radial_numerator_le hf0 ε x

/-- An absolutely integrable singular numerator permits removal of the
regularization under the integral, with no extra continuity requirement. -/
theorem tendsto_integral_regularized_radial_numerator
    {f : E₃ → ℝ} (hf : Measurable f) (hf0 : f 0 = 0)
    (hi : Integrable (fun x => f x / ‖x‖ ^ 5) volume) :
    Tendsto (fun ε : ℝ => ∫ x : E₃,
      f x * (ε ^ 2 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)) (𝓝 0)
      (𝓝 (∫ x : E₃, f x / ‖x‖ ^ 5)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x => |f x / ‖x‖ ^ 5|)
  · exact Eventually.of_forall fun ε => Measurable.aestronglyMeasurable (by fun_prop)
  · exact Eventually.of_forall fun ε => ae_of_all _ fun x => by
      simpa only [Real.norm_eq_abs] using abs_regularized_radial_numerator_le hf0 ε x
  · exact hi.abs
  · refine ae_of_all _ fun x => ?_
    by_cases hx : x = 0
    · simp [hx, hf0]
    have hp : ContinuousAt (fun ε : ℝ => (ε ^ 2 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)) 0 := by
      apply ContinuousAt.rpow_const (by fun_prop)
      left
      simpa using (sq_pos_of_pos (norm_pos_iff.mpr hx)).ne'
    have ht := hp.tendsto.const_mul (f x)
    simp only [zero_pow (by decide : 2 ≠ 0), zero_add, norm_sq_rpow_neg_five_halves] at ht
    simpa only [one_div, div_eq_mul_inv, one_mul] using ht

end ClockBarrier.Analysis
