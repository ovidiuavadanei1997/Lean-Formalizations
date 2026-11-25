/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.SmoothPressurePotential
public import ClockBarrier.Analysis.SmoothBoundedField
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # C¹ potentials of uniform limits of smooth gradients -/
public section
namespace ClockBarrier.Analysis.SmoothPressure
open MeasureTheory Filter Set InnerProductSpace Sobolev SmoothL2Field Solenoidal
open scoped Topology ContDiff BoundedContinuousFunction
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem tendsto_radialPotential (G : ℕ → Space →ᵇ Space) (F : Space →ᵇ Space)
    (hG : Tendsto G atTop (𝓝 F)) (x : Space) :
    Tendsto (fun n => radialPotential (G n) x) atTop (𝓝 (radialPotential F x)) := by
  have hu := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hG).comp
    (fun s : ℝ => s • x)
  have hh := (toDual ℝ Space x).uniformContinuous.comp_tendstoUniformly hu
  have hi : TendstoUniformly (fun (n : ℕ) (s : ℝ) => ⟪G n (s • x), x⟫_ℝ)
      (fun s : ℝ => ⟪F (s • x), x⟫_ℝ) atTop := by
    simpa only [Function.comp_def, toDual_apply_apply, real_inner_comm] using hh
  exact hi.tendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
    (Eventually.of_forall (fun n => (by fun_prop : Continuous
      (fun s : ℝ => ⟪G n (s • x), x⟫_ℝ)).continuousOn))

theorem hasFDerivAt_radialPotential_limit (A : ℕ → SmoothL2Field Space)
    (hA : ∀ n, (A n).toLp ∈ gradientSpace) (F : Space →ᵇ Space)
    (hF : Tendsto (fun n => finiteField (A n)) atTop (𝓝 F)) (x : Space) :
    HasFDerivAt (radialPotential F) (toDual ℝ Space (F x)) x := by
  have hu := (toDual ℝ Space).isometry.uniformContinuous.comp_tendstoUniformly
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hF)
  have hD : TendstoUniformly (fun n y => toDual ℝ Space ((A n).field y))
      (fun y => toDual ℝ Space (F y)) atTop := by
    simpa only [Function.comp_def, finiteField_apply] using hu
  have hd (n : ℕ) (y : Space) : HasFDerivAt (radialPotential (A n).field)
      (toDual ℝ Space ((A n).field y)) y := by
    have hp := gradientSpace_radial_potential (A n).toLp (hA n) (A n).field
      (A n).toLp_ae (A n).smooth
    rw [← hp.2.2 y, toDual_gradient]
    exact (hp.1.differentiable (by simp) y).hasFDerivAt
  exact hasFDerivAt_of_tendstoUniformly hD hd (fun y => by
    simpa only [radialPotential, finiteField_apply] using
      tendsto_radialPotential (fun n => finiteField (A n)) F hF y) x

theorem gradient_radialPotential_limit (A : ℕ → SmoothL2Field Space)
    (hA : ∀ n, (A n).toLp ∈ gradientSpace) (F : Space →ᵇ Space)
    (hF : Tendsto (fun n => finiteField (A n)) atTop (𝓝 F)) (x : Space) :
    gradient (radialPotential F) x = F x := by
  rw [gradient, (hasFDerivAt_radialPotential_limit A hA F hF x).fderiv]
  exact (toDual ℝ Space).symm_apply_apply (F x)

end ClockBarrier.Analysis.SmoothPressure
