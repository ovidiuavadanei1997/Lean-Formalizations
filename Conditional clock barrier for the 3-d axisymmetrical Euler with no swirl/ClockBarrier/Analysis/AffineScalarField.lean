/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.NewtonianGradientScaling
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Scalar fields under translations and positive spatial dilations -/
public section
namespace ClockBarrier.Analysis
open MeasureTheory
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem fderiv_scalar_affine_apply {f : Space → ℝ} (hf : Differentiable ℝ f)
    (r : ℝ) (a x v : Space) :
    fderiv ℝ (fun y => f (r • y + a)) x v = r * fderiv ℝ f (r • x + a) v := by
  have hd := ((hf (r • x + a)).hasFDerivAt).comp x
    (((hasFDerivAt_id x).const_smul r).add_const a)
  convert! congrArg (fun L : Space →L[ℝ] ℝ => L v) hd.fderiv using 1
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    map_smul, smul_eq_mul]

theorem memLp_two_affine {V : Type*} [NormedAddCommGroup V]
    {f : Space → V} (hc : Continuous f) (hf : MemLp f 2 volume)
    {r : ℝ} (hr : r ≠ 0) (a : Space) :
    MemLp (fun x => f (r • x + a)) 2 volume := by
  have hc' : Continuous (fun x : Space => f (x + a)) := by fun_prop
  have hf' : MemLp (fun x : Space => f (x + a)) 2 volume := by
    convert! hf.comp_measurePreserving (measurePreserving_add_right volume a) using 1
  exact memLp_two_comp_smul hc' hf' hr

theorem sqrt_inv_cube {r : ℝ} (hr : 0 < r) :
    Real.sqrt ((r ^ 3)⁻¹) = r ^ (-(3 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_natCast r 3,
    ← Real.rpow_mul hr.le, ← Real.rpow_mul hr.le]
  norm_num

theorem sqrt_energy_affine {V : Type*} [NormedAddCommGroup V]
    (f : Space → V) {r : ℝ} (hr : 0 < r) (a : Space) :
    Real.sqrt (∫ x : Space, ‖f (r • x + a)‖ ^ 2) =
      r ^ (-(3 : ℝ) / 2) * Real.sqrt (∫ x : Space, ‖f x‖ ^ 2) := by
  have hi := Measure.integral_comp_smul_of_nonneg volume
    (fun x : Space => ‖f (x + a)‖ ^ 2) r (hR := hr.le)
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at hi
  rw [hi, Real.sqrt_mul (by positivity), sqrt_inv_cube hr]
  rw [integral_add_right_eq_self (fun x : Space => ‖f x‖ ^ 2) a]

end ClockBarrier.Analysis
