/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.ExactPressureLimit
public import ClockBarrier.Analysis.ContinuousApplyPath

/-! # The pointwise Euler time equation for the rough-data limit -/
public section
namespace ClockBarrier.Euler.Smooth
open Set Filter MeasureTheory ContinuousLinearMap ClockBarrier.Analysis
  Sobolev Solenoidal SmoothL2Field ContinuousTimeIntegral
open scoped Topology BoundedContinuousFunction
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem exact_classical_time_limit {T : ℝ} (hT : 0 ≤ T)
    (U : ℕ → ℝ → SmoothL2Field Space)
    (hUc : ∀ k m, Continuous (fun t => (U k t).jetLp m))
    (hUd : ∀ k m, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => (U k s).jetLp m)
      ((rhs (U k t)).jetLp m) (Icc 0 T) t)
    (v P : C(Icc (0 : ℝ) T, Space →ᵇ Space))
    (D : C(Icc (0 : ℝ) T, Space →ᵇ (Space →L[ℝ] Space)))
    (hv : Tendsto (fun k => boundedFieldPath (fun t : Icc (0 : ℝ) T => U k t)
      (fun m => (hUc k m).comp continuous_subtype_val)) atTop (𝓝 v))
    (hD : Tendsto (fun k => boundedFieldPath (fun t : Icc (0 : ℝ) T => (U k t).derivative)
      (continuous_jetLp_derivative _ (fun m => (hUc k m).comp continuous_subtype_val)))
      atTop (𝓝 D))
    (hP : Tendsto (fun k => boundedFieldPath (fun t : Icc (0 : ℝ) T => pressureForce (U k t))
      (continuous_jetLp_pressureForce _ (fun m => (hUc k m).comp continuous_subtype_val)))
      atTop (𝓝 P)) (t : Icc (0 : ℝ) T) (x : Space) :
    HasDerivWithinAt (fun s => extendPath T hT v s x)
      (-(D t x) (v t x) - P t x) (Icc 0 T) t := by
  let A (k : ℕ) := boundedFieldPath (fun t : Icc (0 : ℝ) T => U k t)
    (fun m => (hUc k m).comp continuous_subtype_val)
  let B (k : ℕ) := boundedFieldPath (fun t : Icc (0 : ℝ) T => (U k t).derivative)
    (continuous_jetLp_derivative _ (fun m => (hUc k m).comp continuous_subtype_val))
  let G (k : ℕ) := boundedFieldPath (fun t : Icc (0 : ℝ) T => pressureForce (U k t))
    (continuous_jetLp_pressureForce _ (fun m => (hUc k m).comp continuous_subtype_val))
  let E : C(Icc (0 : ℝ) T, Space →ᵇ Space) →L[ℝ] C(Icc (0 : ℝ) T, Space) :=
    (BoundedContinuousFunction.evalCLM ℝ x).compLeftContinuous ℝ (Icc (0 : ℝ) T)
  let J : C(Icc (0 : ℝ) T, Space →ᵇ (Space →L[ℝ] Space)) →L[ℝ]
      C(Icc (0 : ℝ) T, Space →L[ℝ] Space) :=
    (BoundedContinuousFunction.evalCLM ℝ x).compLeftContinuous ℝ (Icc (0 : ℝ) T)
  have hvx := (E.continuous.tendsto v).comp hv
  have hDx := (J.continuous.tendsto D).comp hD
  have hPx := (E.continuous.tendsto P).comp hP
  have hN := (continuous_clmApplyPath.tendsto (J D, E v)).comp (hDx.prodMk_nhds hvx)
  have hQ := hN.neg.sub hPx
  have hd (k : ℕ) (s : Icc (0 : ℝ) T) :
      HasDerivWithinAt (extendPath T hT (E (A k)))
        ((-clmApplyPath (J (B k)) (E (A k)) - E (G k)) s) (Icc 0 T) s := by
    have hh := field_hasDerivWithinAt (U k) (rhs (U k s)) (Icc 0 T) s
      (fun m => hUd k m s s.property) x
    have he : (rhs (U k s)).field x =
        ((-clmApplyPath (J (B k)) (E (A k)) - E (G k)) s) := by
      change (rhs (U k s)).field x =
        -(finiteField (U k s).derivative x) (finiteField (U k s) x) -
          finiteField (pressureForce (U k s)) x
      simp only [finiteField_apply]
      change (rhs (U k s)).field x =
        -(fderiv ℝ (U k s).field x) ((U k s).field x) - (pressureForce (U k s)).field x
      have heq := equation (U k s) x
      rw [pressure_gradient] at heq
      have hh := eq_neg_of_add_eq_zero_left (by simpa only [add_assoc] using heq)
      exact hh.trans (by abel)
    rw [he] at hh
    apply hh.congr_of_mem _ s.property
    intro r hr
    change finiteField (U k (projIcc 0 T hT r)) x = (U k r).field x
    rw [projIcc_of_mem hT hr, finiteField_apply]
  have hm := hasDerivWithinAt_of_path_limits T hT (fun k => E (A k))
    (fun k => -clmApplyPath (J (B k)) (E (A k)) - E (G k)) (E v)
    (-clmApplyPath (J D) (E v) - E P) hvx hQ hd t
  convert! hm using 1

end ClockBarrier.Euler.Smooth
