/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.SmoothJetField
public import ClockBarrier.Analysis.SmoothBoundedField
public import ClockBarrier.Analysis.L2PointwiseLimit
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! # Reconstructing one genuine smooth field from limits of its actual jets -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Sobolev
open MeasureTheory ContinuousLinearMap SmoothL2Field Filter
open scoped Topology ContDiff BoundedContinuousFunction
local notation "Space" => EuclideanSpace ℝ (Fin 3)
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem smooth_field_of_jet_limits (A : ℕ → SmoothL2Field V)
    (G : ∀ n : ℕ, Space →ᵇ (Space [×n]→L[ℝ] V))
    (hG : ∀ n, Tendsto (fun k => finiteField (jetField n (A k))) atTop (𝓝 (G n)))
    (J : ∀ n : ℕ, Lp (Space [×n]→L[ℝ] V) 2 (volume : Measure Space))
    (hJ : ∀ n, Tendsto (fun k => (A k).jetLp n) atTop (𝓝 (J n))) :
    ∃ F : SmoothL2Field V, ∀ n, F.jetLp n = J n ∧ finiteField (jetField n F) = G n := by
  have hu (n : ℕ) : TendstoUniformly (fun k => iteratedFDeriv ℝ n (A k).field) (G n) atTop := by
    have h := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp (hG n)
    change TendstoUniformly (fun k x => finiteField (jetField n (A k)) x) (G n) atTop at h
    simpa only [finiteField_apply, jetField_field] using h
  have hd (n : ℕ) (x : Space) : HasFDerivAt (G n : Space → Space [×n]→L[ℝ] V)
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => Space) V) (G (n+1) x)) x := by
    let L : (Space [×(n+1)]→L[ℝ] V) →L[ℝ] (Space →L[ℝ] Space [×n]→L[ℝ] V) :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => Space) V).toContinuousLinearEquiv.toContinuousLinearMap
    apply hasFDerivAt_of_tendstoUniformly (L.uniformContinuous.comp_tendstoUniformly (hu (n+1)))
      _ (fun y => (hu n).tendsto_at y) x
    intro k y
    have h := ((A k).smooth.differentiable_iteratedFDeriv
      (show (n : ℕ∞ω) < (∞ : ℕ∞ω) by exact_mod_cast ENat.coe_lt_top n) y).hasFDerivAt
    convert! (by simpa only [fderiv_iteratedFDeriv, Function.comp_def, L] using h) using 1
  let f : Space → V := fun x => (continuousMultilinearCurryFin0 ℝ Space V) (G 0 x)
  have hj (n : ℕ) : iteratedFDeriv ℝ n f = (G n : Space → Space [×n]→L[ℝ] V) := by
    induction n with
    | zero =>
      funext x
      rw [iteratedFDeriv_zero_eq_comp]
      exact (continuousMultilinearCurryFin0 ℝ Space V).symm_apply_apply (G 0 x)
    | succ n ih =>
      funext x
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih, (hd n x).fderiv]
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => Space) V).symm_apply_apply _
  have hs : ContDiff ℝ ∞ f := by
    apply contDiff_of_differentiable_iteratedFDeriv
    intro n _
    rw [hj n]
    exact fun x => (hd n x).differentiableAt
  have hae (n : ℕ) : J n =ᵐ[volume] (G n : Space → Space [×n]→L[ℝ] V) :=
    l2_ae_eq_pointwise_limit (fun k => (A k).jetLp n) (fun k => iteratedFDeriv ℝ n (A k).field)
      (fun k => (A k).jetLp_ae n) (hJ n) (fun x => (hu n).tendsto_at x)
  have hm (n : ℕ) : MemLp (iteratedFDeriv ℝ n f) 2 volume := by
    rw [hj n]
    exact (Lp.memLp (J n)).ae_eq (hae n)
  let F : SmoothL2Field V := ⟨f, hs, hm⟩
  refine ⟨F, fun n => ⟨?_, ?_⟩⟩
  · apply Lp.ext
    filter_upwards [F.jetLp_ae n, hae n] with x hx hy
    exact hx.trans ((congrFun (hj n) x).trans hy.symm)
  · apply BoundedContinuousFunction.ext
    intro x
    simpa only [finiteField_apply, jetField_field] using congrFun (hj n) x

end ClockBarrier.Analysis.Sobolev
