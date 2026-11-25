/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.PathCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Integration on continuous paths

The Volterra integral operator and its linearization act on actual continuous
paths on a closed interval. The extension outside the interval is only the
canonical endpoint projection used to write ordinary interval integrals.
-/

@[expose] public section

namespace ClockBarrier.Analysis

open Set MeasureTheory intervalIntegral
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {T : ℝ}

/-- Integrate a continuous path from zero, as a bounded linear operator on paths. -/
noncomputable def pathIntegral (hT : 0 ≤ T) : C(Icc 0 T, E) →L[ℝ] C(Icc 0 T, E) := by
  let L : C(Icc 0 T, E) →ₗ[ℝ] C(Icc 0 T, E) :=
    { toFun := fun γ =>
        ⟨fun t => ∫ s in 0..t.1, γ (projIcc 0 T hT s),
          (differentiable_integral_of_continuous
            (γ.continuous.comp continuous_projIcc)).continuous.comp continuous_subtype_val⟩
      map_add' := by
        intro γ δ
        exact ContinuousMap.ext fun t => intervalIntegral.integral_add
          ((γ.continuous.comp continuous_projIcc).intervalIntegrable _ _)
          ((δ.continuous.comp continuous_projIcc).intervalIntegrable _ _)
      map_smul' := by
        intro c γ
        exact ContinuousMap.ext fun t => intervalIntegral.integral_smul c _ }
  exact L.mkContinuous T (by
    intro γ
    apply (ContinuousMap.norm_le _ (mul_nonneg hT (norm_nonneg γ))).mpr
    intro t
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := t.1) (fun s _ => γ.norm_coe_le_norm (projIcc 0 T hT s))
    exact h.trans (by
      rw [sub_zero, abs_of_nonneg t.2.1, mul_comm]
      exact mul_le_mul_of_nonneg_right t.2.2 (norm_nonneg γ)))

@[simp] theorem pathIntegral_apply (hT : 0 ≤ T) (γ : C(Icc 0 T, E)) (t : Icc 0 T) :
    pathIntegral hT γ t = ∫ s in 0..t.1, γ (projIcc 0 T hT s) := rfl

/-- Integrate a continuous time-dependent linear coefficient against a path. -/
noncomputable def pathVolterra (hT : 0 ≤ T) (A : C(Icc 0 T, E →L[ℝ] E)) :
    C(Icc 0 T, E) →L[ℝ] C(Icc 0 T, E) :=
  (pathIntegral hT).comp (pathLinearMap A)

@[simp] theorem pathVolterra_apply (hT : 0 ≤ T) (A : C(Icc 0 T, E →L[ℝ] E))
    (γ : C(Icc 0 T, E)) (t : Icc 0 T) :
    pathVolterra hT A γ t =
      ∫ s in 0..t.1, A (projIcc 0 T hT s) (γ (projIcc 0 T hT s)) := rfl

/-- Iterated time integration gives factorial decay, even on a long interval. -/
theorem norm_pathVolterra_pow_apply_le (hT : 0 ≤ T)
    (A : C(Icc 0 T, E →L[ℝ] E)) (γ : C(Icc 0 T, E)) (n : ℕ) (t : Icc 0 T) :
    ‖((pathVolterra hT A) ^ n) γ t‖ ≤ ‖A‖ ^ n * t.1 ^ n / n.factorial * ‖γ‖ := by
  induction n generalizing t with
  | zero => simpa using γ.norm_coe_le_norm t
  | succ n hn =>
    rw [pow_succ', mul_apply_eq_comp, pathVolterra_apply]
    have hbound : ∀ s ∈ Ioc 0 t.1,
        ‖A (projIcc 0 T hT s) (((pathVolterra hT A) ^ n) γ (projIcc 0 T hT s))‖ ≤
          ‖A‖ ^ (n + 1) * s ^ n / n.factorial * ‖γ‖ := by
      intro s hs
      rw [projIcc_of_mem hT (show s ∈ Icc 0 T from ⟨hs.1.le, hs.2.trans t.2.2⟩)]
      calc
        _ ≤ ‖A‖ * ‖((pathVolterra hT A) ^ n) γ ⟨s, ⟨hs.1.le, hs.2.trans t.2.2⟩⟩‖ :=
          (A _).le_opNorm _ |>.trans
            (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm _) (norm_nonneg _))
        _ ≤ ‖A‖ * (‖A‖ ^ n * s ^ n / n.factorial * ‖γ‖) :=
          mul_le_mul_of_nonneg_left (hn _) (norm_nonneg A)
        _ = _ := by ring
    have hi := intervalIntegral.norm_integral_le_of_norm_le t.2.1
      (Filter.Eventually.of_forall hbound)
      (show IntervalIntegrable (fun s : ℝ => ‖A‖ ^ (n + 1) * s ^ n / n.factorial * ‖γ‖)
        volume 0 t.1 from (by fun_prop : Continuous _).intervalIntegrable _ _)
    convert hi using 1
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul, integral_pow]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      pow_succ, mul_zero, sub_zero, div_mul_eq_div_div]
    ring

/-- The operator norms of Volterra powers satisfy the same factorial estimate. -/
theorem norm_pathVolterra_pow_le (hT : 0 ≤ T) (A : C(Icc 0 T, E →L[ℝ] E)) (n : ℕ) :
    ‖pathVolterra hT A ^ n‖ ≤ (‖A‖ * T) ^ n / n.factorial := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro γ
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  refine (norm_pathVolterra_pow_apply_le hT A γ n t).trans ?_
  rw [mul_pow]
  gcongr
  · exact t.2.1
  · exact t.2.2

/-- The Neumann series of a Volterra operator converges on every compact time interval. -/
theorem summable_pathVolterra_pow (hT : 0 ≤ T) (A : C(Icc 0 T, E →L[ℝ] E)) :
    Summable (fun n : ℕ => pathVolterra hT A ^ n) := by
  letI : NormedRing (C(Icc 0 T, E) →L[ℝ] C(Icc 0 T, E)) := ContinuousLinearMap.toNormedRing
  exact Summable.of_norm_bounded (Real.summable_pow_div_factorial (‖A‖ * T))
    (norm_pathVolterra_pow_le hT A)

/-- The linearized path equation is invertible without a short-time restriction. -/
theorem isInvertible_id_sub_pathVolterra (hT : 0 ≤ T) (A : C(Icc 0 T, E →L[ℝ] E)) :
    (ContinuousLinearMap.id ℝ C(Icc 0 T, E) - pathVolterra hT A).IsInvertible := by
  letI : NormedRing (C(Icc 0 T, E) →L[ℝ] C(Icc 0 T, E)) := ContinuousLinearMap.toNormedRing
  have h := summable_pathVolterra_pow hT A
  exact ContinuousLinearMap.IsInvertible.of_inverse h.one_sub_mul_tsum_pow h.tsum_pow_mul_one_sub

end ClockBarrier.Analysis
