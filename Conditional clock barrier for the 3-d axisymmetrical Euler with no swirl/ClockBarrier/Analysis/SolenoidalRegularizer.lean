/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd,
Euler/OrdinaryRegularizer.lean. See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: focused imports, module interface, project namespace and carrier.
-/
module

public import ClockBarrier.Analysis.L2Mollifier

/-! # Concrete solenoidal regularization

`regularizerMap n = P ∘ Jₙ ∘ P`, with canonical Helmholtz projection `P`
and the normalized compact convolution `Jₙ` constructed in `L2Mollifier`.
-/

@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Solenoidal
open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap
open scoped ContDiff Topology
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem projection_inner (u v : L2) :
    ⟪solenoidalProjection u,v⟫_ℝ=⟪u,solenoidalProjection v⟫_ℝ :=
  solenoidalSpace.inner_starProjection_left_eq_right u v

theorem projection_idempotent (u : L2) :
    solenoidalProjection (solenoidalProjection u)=solenoidalProjection u :=
  solenoidalSpace.starProjection_eq_self_iff.mpr (solenoidalProjection_mem u)

def regularizerMap (n : ℕ) : L2 →L[ℝ] L2 :=
  solenoidalProjection.comp ((mollifier n).comp solenoidalProjection)

@[simp] theorem regularizerMap_apply (n : ℕ) (u : L2) :
    regularizerMap n u=solenoidalProjection (mollify n (solenoidalProjection u)) := rfl

theorem regularizerMap_translation (n : ℕ) (a : E₃) (u : L2) :
    translation a (regularizerMap n u)=
      regularizerMap n (translation a u) := by
  simp only [regularizerMap_apply,solenoidalProjection_translation,mollify_translation]

theorem regularizerMap_smooth (n : ℕ) (u : L2) : ContDiff ℝ ∞ (fun a => translation a (regularizerMap n u)) := by
  have h := solenoidalProjection.contDiff.comp (mollify_smooth n (solenoidalProjection u))
  simpa only [Function.comp_def,← solenoidalProjection_translation,← regularizerMap_apply] using h

theorem regularizerMap_symmetric (n : ℕ) (u v : L2) :
    ⟪regularizerMap n u,v⟫_ℝ=⟪u,regularizerMap n v⟫_ℝ := by
  simp only [regularizerMap_apply,projection_inner,mollify_symmetric]

theorem regularizerMap_contract (n : ℕ) (u : L2) : ‖regularizerMap n u‖ ≤ ‖u‖ :=
  (solenoidalProjection_apply_norm_le _).trans
    ((mollify_norm_le n _).trans (solenoidalProjection_apply_norm_le u))

theorem regularizerMap_tendsto (u : L2) :
    Tendsto (fun n => regularizerMap n u) atTop (𝓝 (solenoidalProjection u)) := by
  change Tendsto (fun n => solenoidalProjection (mollify n (solenoidalProjection u)))
    atTop (𝓝 (solenoidalProjection u))
  have h := solenoidalProjection.continuous.tendsto (solenoidalProjection u)
  simpa only [Function.comp_def,projection_idempotent] using
    h.comp (mollify_tendsto (solenoidalProjection u))

theorem regularizerMap_mem (n : ℕ) (u : L2) :
    regularizerMap n u ∈ solenoidalSpace := solenoidalProjection_mem _

end ClockBarrier.Analysis.Solenoidal
