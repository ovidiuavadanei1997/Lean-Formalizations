/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.SmoothPressureDivergence
public import ClockBarrier.Analysis.SmoothBoundedCauchy
public import ClockBarrier.Analysis.InterpolationCauchy

/-! # Uniform convergence of pressure gradients from strong L² convergence -/
public section
namespace ClockBarrier.Euler.Smooth
open MeasureTheory Filter ClockBarrier.Analysis Sobolev Solenoidal SmoothL2Field
open scoped Topology BoundedContinuousFunction
local notation "Space" => EuclideanSpace ℝ (Fin 3)
variable {K : Type*} [TopologicalSpace K]

theorem continuous_jetLp_pressureForce (A : K → SmoothL2Field Space)
    (hA : ∀ m, Continuous (fun t => (A t).jetLp m)) (m : ℕ) :
    Continuous (fun t => (pressureForce (A t)).jetLp m) := by
  exact continuous_smooth_iff.mp (continuous_pressureForce.comp
    (continuous_smooth_iff.mpr hA)) m

theorem pressure_bounded_cauchy [CompactSpace K] (U : ℕ → K → SmoothL2Field Space)
    (hUc : ∀ k m, Continuous (fun t => (U k t).jetLp m))
    (hsol : ∀ k t, (U k t).toLp ∈ solenoidalSpace) (R : ℝ)
    (hR : ∀ k t, ‖finiteField (U k t).derivative‖ ≤ R)
    (hLp : CauchySeq (fun k => fieldPath (fun t => pressureForce (U k t))
      (continuous_jetLp_pressureForce _ (hUc k)))) :
    CauchySeq (fun k => boundedFieldPath (fun t => pressureForce (U k t))
      (continuous_jetLp_pressureForce _ (hUc k))) := by
  obtain ⟨C, hC, hb⟩ := exists_pressureForce_difference_constant
  let P (k : ℕ) : C(K, Space →ᵇ Space) := boundedFieldPath (fun t => pressureForce (U k t))
    (continuous_jetLp_pressureForce _ (hUc k))
  let Q (k : ℕ) : C(K, L2) := fieldPath (fun t => pressureForce (U k t))
    (continuous_jetLp_pressureForce _ (hUc k))
  change CauchySeq P
  refine cauchySeq_of_scale_bound P Q (B := C * (6 * R ^ 2)) (by positivity)
    (fun r => C * r ^ (-(3 : ℝ) / 2)) (fun r hr => by positivity) ?_ hLp
  intro r hr n m
  have he : dist (P n) (P m) = ‖P n - P m‖ := by
    convert! dist_eq_norm (P n) (P m) using 1
  rw [he, dist_eq_norm]
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  change ‖finiteField (pressureForce (U n t)) - finiteField (pressureForce (U m t))‖ ≤ _
  have hq : ‖(pressureForce (U n t)).toLp - (pressureForce (U m t)).toLp‖ ≤
      ‖Q n - Q m‖ := (Q n - Q m).norm_coe_le_norm t
  calc
    _ ≤ C * (r * (6 * R ^ 2) + r ^ (-(3 : ℝ) / 2) *
        ‖(pressureForce (U n t)).toLp - (pressureForce (U m t)).toLp‖) :=
      hb _ _ (hsol n t) (hsol m t) R (hR n t) (hR m t) r hr
    _ ≤ C * (r * (6 * R ^ 2) + r ^ (-(3 : ℝ) / 2) * ‖Q n - Q m‖) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg hr.le _))) hC.le
    _ = _ := by ring

end ClockBarrier.Euler.Smooth
