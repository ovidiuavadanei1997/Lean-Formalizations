/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.ExactL2Stability
public import ClockBarrier.Euler.SmoothEnergyTime
public import ClockBarrier.Analysis.RoughSpatialLimit
public import ClockBarrier.Analysis.SmoothBoundedCauchy

/-! # The spatial C¹ and strong L² limit of exact Euler approximations -/
@[expose] public noncomputable section
namespace ClockBarrier.Euler.Smooth
open Set Filter MeasureTheory ContinuousLinearMap ClockBarrier.Analysis
  Solenoidal SmoothL2Field Sobolev
open scoped Topology NNReal BoundedContinuousFunction
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem exact_spatial_limit {T : ℝ} (U : ℕ → ℝ → SmoothL2Field Space)
    (hUc : ∀ k m, Continuous (fun t => (U k t).jetLp m))
    (hUd : ∀ k m, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => (U k s).jetLp m)
      ((rhs (U k t)).jetLp m) (Icc 0 T) t)
    (hUs : ∀ k, ∀ t ∈ Icc 0 T, (U k t).toLp ∈ solenoidalSpace)
    (R α : ℝ≥0) (hα : 0 < α)
    (hgrad : ∀ k, ∀ t ∈ Icc 0 T, ‖finiteField (U k t).derivative‖ ≤ (R : ℝ))
    (hholder : ∀ k, ∀ t ∈ Icc 0 T,
      HolderWith R α (finiteField (U k t).derivative : Space → Space →L[ℝ] Space))
    (hinit : CauchySeq (fun k => (U k 0).toLp)) :
    ∃ V : C(Icc (0 : ℝ) T, L2), ∃ v : C(Icc (0 : ℝ) T, Space →ᵇ Space),
    ∃ D : C(Icc (0 : ℝ) T, Space →ᵇ (Space →L[ℝ] Space)),
      Tendsto (fun k => fieldPath (fun t : Icc (0 : ℝ) T => U k t)
        (fun m => (hUc k m).comp continuous_subtype_val)) atTop (𝓝 V) ∧
      Tendsto (fun k => boundedFieldPath (fun t : Icc (0 : ℝ) T => U k t)
        (fun m => (hUc k m).comp continuous_subtype_val)) atTop (𝓝 v) ∧
      Tendsto (fun k => boundedFieldPath (fun t : Icc (0 : ℝ) T => (U k t).derivative)
        (continuous_jetLp_derivative _ (fun m => (hUc k m).comp continuous_subtype_val)))
        atTop (𝓝 D) ∧
      ∀ t, V t =ᵐ[volume] (v t : Space → Space) ∧
        MemLp (v t : Space → Space) 2 volume ∧
        (∀ x, HasFDerivAt (v t : Space → Space) (D t x) x) ∧
        ‖D t‖ ≤ (R : ℝ) ∧ HolderWith R α (D t : Space → Space →L[ℝ] Space) := by
  have hd (k : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (fun s => (U k s).toLp) (rhs (U k t)).toLp (Icc 0 T) t := by
    simpa only [wordField_zero] using
      word_hasDerivWithinAt (Fin.elim0 : Fin 0 → Fin 3) (hUd k 0 t ht)
  have hg (k : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) (x : Space) :
      ‖fderiv ℝ (U k t).field x‖ ≤ (R : ℝ) := by
    convert! ((finiteField (U k t).derivative).norm_coe_le_norm x).trans (hgrad k t ht) using 1
    rw [finiteField_apply]
    rfl
  have hc := exact_l2_cauchy hUc hd hUs R R.coe_nonneg hg hinit
  refine exists_bounded_c1_l2_limit _ _ _ hc ?_ ?_ R α hα ?_ ?_
  · intro k t
    filter_upwards [(U k t).toLp_ae] with x hx
    exact hx.trans (finiteField_apply (U k t) x).symm
  · intro k t x
    change HasFDerivAt (finiteField (U k t) : Space → Space)
      (finiteField (U k t).derivative x) x
    have he : (finiteField (U k t) : Space → Space) = (U k t).field :=
      funext (finiteField_apply _)
    rw [he, finiteField_apply]
    exact ((U k t).smooth.differentiable (by simp) x).hasFDerivAt
  · exact fun k t => hgrad k t t.property
  · exact fun k t => hholder k t t.property

end ClockBarrier.Euler.Smooth
