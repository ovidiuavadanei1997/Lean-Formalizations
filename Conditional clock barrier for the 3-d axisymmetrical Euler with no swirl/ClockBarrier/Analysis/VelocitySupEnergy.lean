/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
/-! # Full velocity supremum control from Lipschitz regularity and energy -/

public section
namespace ClockBarrier.Analysis
open Set Metric MeasureTheory
open scoped NNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
/-- A fixed unit-ball average controls the full supremum norm by Lipschitz size and energy. -/
theorem norm_le_lipschitz_add_energy {F : Type*} [NormedAddCommGroup F]
    (u : E₃ →ᵇ F) {K : ℝ≥0} (hLip : LipschitzWith K (u : E₃ → F))
    (hE : Integrable (fun x => ‖u x‖ ^ 2) volume) :
    ‖u‖ ≤ (K : ℝ) + 1 + (∫ x, ‖u x‖ ^ 2) / (Real.pi * 4 / 3) := by
  have hv (x : E₃) : volume.real (closedBall x 1) = Real.pi * 4 / 3 := by
    rw [Measure.real, EuclideanSpace.volume_closedBall_fin_three]
    norm_num [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  have he0 : 0 ≤ ∫ x, ‖u x‖ ^ 2 := integral_nonneg (fun x => sq_nonneg _)
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  have hpoint (y : E₃) (hy : y ∈ closedBall x 1) : ‖u x‖ ≤ (K : ℝ) + 1 + ‖u y‖ ^ 2 := by
    have hdist : dist x y ≤ 1 := by simpa only [mem_closedBall, dist_comm] using hy
    have hdiff := (hLip.dist_le_mul x y).trans (mul_le_mul_of_nonneg_left hdist K.coe_nonneg)
    have htriangle := norm_sub_norm_le (u x) (u y)
    simp only [dist_eq_norm, mul_one] at hdiff
    nlinarith only [hdiff, htriangle, sq_nonneg (‖u y‖ - 1 / 2)]
  have hconst (r : ℝ) : IntegrableOn (fun _ : E₃ => r) (closedBall x 1) volume :=
    integrableOn_const (isCompact_closedBall x 1).measure_lt_top.ne
  have hint := setIntegral_mono_on (hconst ‖u x‖) ((hconst ((K : ℝ) + 1)).add hE.integrableOn)
    isClosed_closedBall.measurableSet hpoint
  simp only [Pi.add_apply, integral_add (hconst ((K : ℝ) + 1)) hE.integrableOn,
    setIntegral_const, smul_eq_mul, hv] at hint
  have hsub := setIntegral_le_integral (s := closedBall x 1) hE
    (Filter.Eventually.of_forall (fun y => sq_nonneg ‖u y‖))
  have hnorm : (‖u x‖ - ((K : ℝ) + 1)) * (Real.pi * 4 / 3) ≤ ∫ y, ‖u y‖ ^ 2 := by
    nlinarith only [hint, hsub]
  have hdiv := (le_div_iff₀ (by positivity : 0 < Real.pi * 4 / 3)).mpr hnorm
  linarith only [hdiv]
end ClockBarrier.Analysis
