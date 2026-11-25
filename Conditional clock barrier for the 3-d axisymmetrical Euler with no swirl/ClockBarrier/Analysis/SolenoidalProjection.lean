/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd,
Euler/MeanSolenoidalSpace.lean. See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: focused imports, module interface, project namespace and carrier.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # The closed solenoidal subspace and its canonical Helmholtz projection

The subspace is the orthogonal complement of the closure of compactly supported
smooth gradients. No projection, solution, or estimate is supplied as an input.
-/

@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Solenoidal
open MeasureTheory InnerProductSpace
open scoped ContDiff ENNReal NNReal
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

abbrev L2 := MeasureTheory.Lp E₃ 2 (volume : Measure E₃)

theorem contDiff_gradient {φ : E₃ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (gradient φ) := by
  exact (toDual ℝ E₃).symm.toContinuousLinearEquiv.contDiff.comp
    (hφ.fderiv_right (m := ∞) (by simp))

theorem compactSupport_gradient {φ : E₃ → ℝ} (hφ : HasCompactSupport φ) :
    HasCompactSupport (gradient φ) := by
  exact (hφ.fderiv (𝕜 := ℝ)).comp_left (map_zero (toDual ℝ E₃).symm)

theorem gradient_memLp {φ : E₃ → ℝ}
    (hc : HasCompactSupport φ) (hs : ContDiff ℝ ∞ φ) :
    MemLp (gradient φ) 2 (volume : Measure E₃) :=
  (contDiff_gradient hs).continuous.memLp_of_hasCompactSupport (compactSupport_gradient hc)

def testGradient (φ : E₃ → ℝ) (hc : HasCompactSupport φ)
    (hs : ContDiff ℝ ∞ φ) : L2 :=
  (gradient_memLp hc hs).toLp (gradient φ)

theorem testGradient_ae (φ : E₃ → ℝ) (hc : HasCompactSupport φ)
    (hs : ContDiff ℝ ∞ φ) : testGradient φ hc hs =ᵐ[volume] gradient φ :=
  (gradient_memLp hc hs).coeFn_toLp

def gradientGenerators : Set L2 :=
  {g | ∃ φ : E₃ → ℝ, HasCompactSupport φ ∧ ContDiff ℝ ∞ φ ∧
    g =ᵐ[volume] gradient φ}

def gradientSpace : Submodule ℝ L2 :=
  (Submodule.span ℝ gradientGenerators).topologicalClosure

theorem gradientSpace_closed : IsClosed (gradientSpace : Set L2) :=
  (Submodule.span ℝ gradientGenerators).isClosed_topologicalClosure

instance : CompleteSpace gradientSpace := gradientSpace_closed.completeSpace_coe

def solenoidalSpace : Submodule ℝ L2 := gradientSpace.orthogonal

instance : CompleteSpace solenoidalSpace :=
  gradientSpace.isClosed_orthogonal.completeSpace_coe

theorem testGradient_mem (φ : E₃ → ℝ) (hc : HasCompactSupport φ)
    (hs : ContDiff ℝ ∞ φ) : testGradient φ hc hs ∈ gradientSpace :=
  (Submodule.span ℝ gradientGenerators).le_topologicalClosure
    (Submodule.subset_span ⟨φ, hc, hs, testGradient_ae φ hc hs⟩)

theorem weak_divergence_test {u : L2} (hu : u ∈ solenoidalSpace)
    (φ : E₃ → ℝ) (hc : HasCompactSupport φ) (hs : ContDiff ℝ ∞ φ) :
    ∫ x, ⟪gradient φ x, u x⟫_ℝ = 0 := by
  have h := hu (testGradient φ hc hs) (testGradient_mem φ hc hs)
  rw [MeasureTheory.L2.inner_def] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [testGradient_ae φ hc hs] with x hx
  rw [hx]

/-- Orthogonality is equivalent to the ordinary distributional divergence test. -/
theorem mem_solenoidal_iff (u : L2) : u ∈ solenoidalSpace ↔
    ∀ φ : E₃ → ℝ, HasCompactSupport φ → ContDiff ℝ ∞ φ →
      ∫ x, ⟪gradient φ x, u x⟫_ℝ = 0 := by
  constructor
  · exact fun hu => weak_divergence_test hu
  · intro hu
    let K := (innerSL ℝ u).ker
    have hg : Submodule.span ℝ gradientGenerators ≤ K := by
      apply Submodule.span_le.2
      rintro g ⟨φ, hc, hs, hg⟩
      change ⟪u, g⟫_ℝ = 0
      rw [real_inner_comm, MeasureTheory.L2.inner_def]
      calc
        (∫ x, ⟪g x, u x⟫_ℝ) = ∫ x, ⟪gradient φ x, u x⟫_ℝ := by
          apply integral_congr_ae
          filter_upwards [hg] with x hx
          rw [hx]
        _ = 0 := hu φ hc hs
    have hclosure : gradientSpace ≤ K :=
      (Submodule.span ℝ gradientGenerators).topologicalClosure_minimal hg
        (innerSL ℝ u).isClosed_ker
    intro g hg
    rw [real_inner_comm]
    exact hclosure hg

def solenoidalProjection : L2 →L[ℝ] L2 := solenoidalSpace.starProjection

theorem solenoidalProjection_mem (u : L2) :
    solenoidalProjection u ∈ solenoidalSpace := solenoidalSpace.starProjection_apply_mem u

theorem solenoidalProjection_norm_le : ‖solenoidalProjection‖ ≤ 1 :=
  solenoidalSpace.starProjection_norm_le

theorem solenoidalProjection_apply_norm_le (u : L2) : ‖solenoidalProjection u‖ ≤ ‖u‖ :=
  solenoidalSpace.norm_starProjection_apply_le u

theorem solenoidal_orthogonal : solenoidalSpace.orthogonal = gradientSpace :=
  gradientSpace.orthogonal_orthogonal

/-- The pressure component of the ordinary Helmholtz decomposition. -/
theorem sub_solenoidalProjection_mem_gradient (u : L2) :
    u - solenoidalProjection u ∈ gradientSpace := by
  rw [← solenoidal_orthogonal]
  exact solenoidalSpace.sub_starProjection_mem_orthogonal u

theorem solenoidalProjection_eq_zero_iff (u : L2) :
    solenoidalProjection u = 0 ↔ u ∈ gradientSpace := by
  change u ∈ solenoidalSpace.starProjection.ker ↔ u ∈ gradientSpace
  rw [Submodule.ker_starProjection, solenoidal_orthogonal]

theorem pressure_pairing_zero {p u : L2} (hp : p ∈ gradientSpace)
    (hu : u ∈ solenoidalSpace) : ⟪p, u⟫_ℝ = 0 := hu p hp

end ClockBarrier.Analysis.Solenoidal
