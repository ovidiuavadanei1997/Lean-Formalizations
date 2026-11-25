/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd.
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: focused imports, namespaces, module interface and pinned Mathlib compatibility.
-/
module
public import ClockBarrier.Analysis.SmoothSobolev
public import ClockBarrier.Analysis.L2Mollifier
import Mathlib.Tactic.FunProp
/-! # L2SpatialCutoff
Selective port of ordinary-space L² calculus from NavierStokesAndEuler.
-/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.L2Translation
open MeasureTheory Filter
open Solenoidal (cutoffScale cutoffScale_pos cutoffScale_tendsto)
open scoped ContDiff Topology
local notation "Space" => EuclideanSpace ℝ (Fin 3)
theorem cutoffScale_le_one (n : ℕ) : cutoffScale n ≤ 1 := by
  exact inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg n))

def cutoff (n : ℕ) (x : Space) : ℝ := SmoothSobolev.unitBump (cutoffScale n • x)

theorem cutoff_smooth (n : ℕ) : ContDiff ℝ ∞ (cutoff n) :=
  SmoothSobolev.unitBump.contDiff.comp (contDiff_id.const_smul (cutoffScale n))

theorem cutoff_compact (n : ℕ) : HasCompactSupport (cutoff n) :=
  SmoothSobolev.unitBump.hasCompactSupport.comp_smul (cutoffScale_pos n).ne'

theorem cutoff_bounds (n : ℕ) (x : Space) : 0 ≤ cutoff n x ∧ cutoff n x ≤ 1 :=
  ⟨SmoothSobolev.unitBump.nonneg, SmoothSobolev.unitBump.le_one⟩

theorem cutoff_sub_one_norm (n : ℕ) (x : Space) : ‖cutoff n x - 1‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [cutoff_bounds n x]

theorem cutoff_tendsto (x : Space) : Tendsto (fun n => cutoff n x) atTop (𝓝 1) := by
  have h := SmoothSobolev.unitBump.continuous.continuousAt.tendsto.comp (cutoffScale_tendsto.smul_const x)
  have hb : SmoothSobolev.unitBump (0 : Space) = 1 := SmoothSobolev.unitBump.one_of_mem_closedBall (by simp [SmoothSobolev.unitBump])
  simpa only [cutoff, zero_smul, hb, Function.comp_def] using h

theorem cutoff_derivative_bound : ∃ M : ℝ, 0 ≤ M ∧
    ∀ n x, ‖fderiv ℝ (cutoff n) x‖ ≤ M * cutoffScale n := by
  have hs : ContDiff ℝ ∞ (SmoothSobolev.unitBump : Space → ℝ) := SmoothSobolev.unitBump.contDiff
  obtain ⟨M, hM⟩ := (SmoothSobolev.unitBump.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hs.fderiv_right (m := ∞) (by simp)).continuous
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine ⟨M, hM0, ?_⟩
  intro n x
  have hder := ((hs.differentiable (by simp)) (cutoffScale n • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul (cutoffScale n))
  change HasFDerivAt (cutoff n)
    ((fderiv ℝ (SmoothSobolev.unitBump : Space → ℝ) (cutoffScale n • x)).comp
      (cutoffScale n • ContinuousLinearMap.id ℝ Space)) x at hder
  rw [hder.fderiv]
  calc
    _ ≤ ‖fderiv ℝ (SmoothSobolev.unitBump : Space → ℝ) (cutoffScale n • x)‖ *
        ‖cutoffScale n • ContinuousLinearMap.id ℝ Space‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖fderiv ℝ (SmoothSobolev.unitBump : Space → ℝ) (cutoffScale n • x)‖ * cutoffScale n := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (cutoffScale_pos n), ContinuousLinearMap.norm_id, mul_one]
    _ ≤ M * cutoffScale n := mul_le_mul_of_nonneg_right (hM _) (cutoffScale_pos n).le

theorem cutoff_derivative_tendsto (x : Space) :
    Tendsto (fun n => fderiv ℝ (cutoff n) x) atTop (𝓝 0) := by
  obtain ⟨M, _, hM⟩ := cutoff_derivative_bound
  apply squeeze_zero_norm (fun n => hM n x)
  simpa only [mul_zero] using cutoffScale_tendsto.const_mul M

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def cutoffField (f : Space → V) (n : ℕ) (x : Space) : V := cutoff n x • f x

theorem cutoffField_smooth (f : Space → V) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (cutoffField f n) := (cutoff_smooth n).smul hf

theorem cutoffField_compact (f : Space → V) (n : ℕ) : HasCompactSupport (cutoffField f n) :=
  (cutoff_compact n).smul_right

theorem cutoffField_fderiv (f : Space → V) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : Space) :
    fderiv ℝ (cutoffField f n) x = cutoff n x • fderiv ℝ f x +
      (fderiv ℝ (cutoff n) x).smulRight (f x) :=
  fderiv_fun_smul ((cutoff_smooth n).differentiable (by simp) x) (hf.differentiable (by simp) x)

theorem cutoffField_tendsto (f : Space → V) (x : Space) :
    Tendsto (fun n => cutoffField f n x) atTop (𝓝 (f x)) := by
  simpa only [one_smul, cutoffField] using (cutoff_tendsto x).smul_const (f x)

theorem cutoffField_fderiv_tendsto (f : Space → V) (hf : ContDiff ℝ ∞ f) (x : Space) :
    Tendsto (fun n => fderiv ℝ (cutoffField f n) x) atTop (𝓝 (fderiv ℝ f x)) := by
  have hright : Tendsto (fun n => (fderiv ℝ (cutoff n) x).smulRight (f x)) atTop (𝓝 0) := by
    have hc : Continuous (fun L : Space →L[ℝ] ℝ => L.smulRight (f x)) := by fun_prop
    simpa only [ContinuousLinearMap.zero_smulRight, Function.comp_def] using hc.continuousAt.tendsto.comp
      (cutoff_derivative_tendsto x)
  simp_rw [cutoffField_fderiv f hf]
  simpa only [one_smul, add_zero] using ((cutoff_tendsto x).smul_const (fderiv ℝ f x)).add hright

end ClockBarrier.Analysis.L2Translation
