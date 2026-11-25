/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.ExactSpatialLimit
public import ClockBarrier.Analysis.RoughAdvection
public import ClockBarrier.Analysis.ContinuousOdeLimit

/-! # The exact projected Euler equation for the rough-data limit

This passes the time equation in L². Recovering a jointly continuous pressure
gradient remains a separate spatial regularity assertion.
-/
@[expose] public noncomputable section
namespace ClockBarrier.Euler.Smooth
open Set Filter MeasureTheory ContinuousLinearMap ClockBarrier.Analysis
  Solenoidal SmoothL2Field Sobolev ContinuousTimeIntegral
open scoped Topology BoundedContinuousFunction
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem boundedApplyL2_smooth (A : SmoothL2Field Space) :
    boundedApplyL2 (finiteField A.derivative) A.toLp = (advectionField A A).toLp := by
  apply Lp.ext
  filter_upwards [boundedApplyL2_ae (finiteField A.derivative) A.toLp,
    A.toLp_ae, (advectionField A A).toLp_ae] with x hx ha hb
  rw [hx, hb, ha, finiteField_apply, advectionField_field]
  rfl

theorem exact_projected_limit {T : ℝ} (hT : 0 ≤ T)
    (U : ℕ → ℝ → SmoothL2Field Space)
    (hUc : ∀ k m, Continuous (fun t => (U k t).jetLp m))
    (hUd : ∀ k m, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => (U k s).jetLp m)
      ((rhs (U k t)).jetLp m) (Icc 0 T) t)
    (V : C(Icc (0 : ℝ) T, L2))
    (D : C(Icc (0 : ℝ) T, Space →ᵇ (Space →L[ℝ] Space)))
    (hV : Tendsto (fun k => fieldPath (fun t : Icc (0 : ℝ) T => U k t)
      (fun m => (hUc k m).comp continuous_subtype_val)) atTop (𝓝 V))
    (hD : Tendsto (fun k => boundedFieldPath (fun t : Icc (0 : ℝ) T => (U k t).derivative)
      (continuous_jetLp_derivative _ (fun m => (hUc k m).comp continuous_subtype_val)))
      atTop (𝓝 D)) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT V)
      (-solenoidalProjection (boundedApplyL2 (D t) (V t))) (Icc 0 T) t := by
  let A (k : ℕ) := fieldPath (fun t : Icc (0 : ℝ) T => U k t)
    (fun m => (hUc k m).comp continuous_subtype_val)
  let B (k : ℕ) := boundedFieldPath (fun t : Icc (0 : ℝ) T => (U k t).derivative)
    (continuous_jetLp_derivative _ (fun m => (hUc k m).comp continuous_subtype_val))
  let P : C(Icc (0 : ℝ) T, L2) →L[ℝ] C(Icc (0 : ℝ) T, L2) :=
    (-solenoidalProjection).compLeftContinuous ℝ (Icc (0 : ℝ) T)
  have hN := tendsto_advectionPath hD hV
  have hQ := (P.continuous.tendsto (advectionPath D V)).comp hN
  have hd (k : ℕ) (s : Icc (0 : ℝ) T) :
      HasDerivWithinAt (extendPath T hT (A k)) (P (advectionPath (B k) (A k)) s)
        (Icc 0 T) s := by
    have hh := word_hasDerivWithinAt (Fin.elim0 : Fin 0 → Fin 3) (hUd k 0 s s.property)
    simp only [wordField_zero] at hh
    have he : P (advectionPath (B k) (A k)) s = (rhs (U k s)).toLp := by
      change -solenoidalProjection
        (boundedApplyL2 (finiteField (U k s).derivative) (U k s).toLp) = _
      rw [boundedApplyL2_smooth, rhs_toLp]
    rw [he]
    apply hh.congr_of_mem _ s.property
    intro r hr
    change (U k (projIcc 0 T hT r)).toLp = (U k r).toLp
    rw [projIcc_of_mem hT hr]
  exact hasDerivWithinAt_of_path_limits T hT A
    (fun k => P (advectionPath (B k) (A k))) V (P (advectionPath D V)) hV hQ hd t

end ClockBarrier.Euler.Smooth
