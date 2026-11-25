/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.RegularizedEquation
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.Calculus.MeanValue

/-! # Actual solenoidal regularized Euler trajectories and their uniform energy bound

The energy estimate is uniform in the smoothing index on every finite time
interval. Spatial operator bounds in this module retain their index dependence.
-/

public section
namespace ClockBarrier.Euler.Regularized
open Set Filter MeasureTheory ClockBarrier.Analysis.Solenoidal
open scoped Topology BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem quadratic_mem (n : ℕ) (u v : L2) : quadratic n u v ∈ solenoidalSpace :=
  solenoidalSpace.neg_mem (regularizerMap_mem n (advection n u v))

theorem projection_quadratic (n : ℕ) (u v : L2) :
    solenoidalProjection (quadratic n u v) = quadratic n u v :=
  solenoidalSpace.starProjection_eq_self_iff.mpr (quadratic_mem n u v)

theorem solution_solenoidal {n : ℕ} {T : ℝ} {u : ℝ → L2}
    (hcont : ContinuousOn u (Icc 0 T))
    (hode : ∀ t ∈ Ico 0 T,
      HasDerivWithinAt u (quadratic n (u t) (u t)) (Ici t) t)
    (hzero : u 0 ∈ solenoidalSpace) (t : ℝ) (ht : t ∈ Icc 0 T) :
    u t ∈ solenoidalSpace := by
  have hd (s : ℝ) (hs : s ∈ Ico 0 T) :
      HasDerivWithinAt (fun r => u r - solenoidalProjection (u r)) 0 (Ici s) s := by
    convert! (hode s hs).sub
      (solenoidalProjection.hasFDerivAt.comp_hasDerivWithinAt s (hode s hs)) using 1
    simp only [projection_quadratic, sub_self]
  have he := constant_of_has_deriv_right_zero
    (hcont.sub (solenoidalProjection.continuous.comp_continuousOn hcont)) hd t ht
  have hz : u t - solenoidalProjection (u t) = 0 := by
    simpa only [Pi.sub_apply, Function.comp_def, show solenoidalProjection (u 0) = u 0 from
      solenoidalSpace.starProjection_eq_self_iff.mpr hzero, sub_self] using he
  exact solenoidalSpace.starProjection_eq_self_iff.mp (sub_eq_zero.mp hz).symm

/-- Concrete regularized solutions with smoothed initial data, on a common
arbitrary finite interval. Their L² bound is independent of the smoothing index. -/
theorem exists_family_Icc (u₀ : L2) {T : ℝ} (hT : 0 ≤ T) :
    ∃ U : ℕ → ℝ → L2, ∀ n,
      U n 0 = regularizerMap n u₀ ∧
      ContinuousOn (U n) (Icc 0 T) ∧
      (∀ t ∈ Ico 0 T,
        HasDerivWithinAt (U n) (quadratic n (U n t) (U n t)) (Ici t) t) ∧
      ∀ t ∈ Icc 0 T, U n t ∈ solenoidalSpace ∧
        ‖U n t‖ = ‖regularizerMap n u₀‖ ∧ ‖U n t‖ ≤ ‖u₀‖ := by
  choose U hinit hcont hode hnorm using
    (fun n => exists_solution_Icc n (regularizerMap n u₀) hT)
  refine ⟨U, fun n => ⟨hinit n, hcont n, hode n, fun t ht => ⟨?_, hnorm n t ht, ?_⟩⟩⟩
  · exact solution_solenoidal (hcont n) (hode n)
      ((hinit n).symm ▸ regularizerMap_mem n u₀) t ht
  · exact (hnorm n t ht).le.trans (regularizerMap_contract n u₀)

/-- The initial regularizations recover each solenoidal datum strongly in L². -/
theorem initial_tendsto (u₀ : L2) (h₀ : u₀ ∈ solenoidalSpace) :
    Tendsto (fun n => regularizerMap n u₀) atTop (𝓝 u₀) := by
  simpa only [show solenoidalProjection u₀ = u₀ from
    solenoidalSpace.starProjection_eq_self_iff.mpr h₀] using regularizerMap_tendsto u₀

/-- Along a constructed L² trajectory the smoothed velocity is continuous in
the supremum norm and has its actual strong time derivative in that norm. -/
theorem velocity_time {n : ℕ} {T : ℝ} {u : ℝ → L2}
    (hcont : ContinuousOn u (Icc 0 T))
    (hode : ∀ t ∈ Ico 0 T,
      HasDerivWithinAt u (quadratic n (u t) (u t)) (Ici t) t) :
    ContinuousOn (fun t => regularizedField n (u t)) (Icc 0 T) ∧
      ContinuousOn (fun t => regularizedDerivative n (u t)) (Icc 0 T) ∧
      ∀ t ∈ Ico 0 T,
        HasDerivWithinAt (fun s => regularizedField n (u s))
          (regularizedField n (quadratic n (u t) (u t))) (Ici t) t := by
  refine ⟨(regularizedField n).continuous.comp_continuousOn hcont,
    (regularizedDerivative n).continuous.comp_continuousOn hcont, ?_⟩
  exact fun t ht => (regularizedField n).hasFDerivAt.comp_hasDerivWithinAt t (hode t ht)

/-- The actual smooth velocity representative has the same index-independent
L² contraction bound as the canonical regularizer. -/
theorem velocity_energy_le (n : ℕ) (u : L2) :
    (eLpNorm (regularizedField n u : E₃ → E₃) 2 volume).toReal ≤ ‖u‖ := by
  rw [← eLpNorm_congr_ae (regularizerMap_ae_field n u), ← Lp.norm_def]
  exact regularizerMap_contract n u

/-- Initial-data compatibility with the classical interface: a bounded
continuous derivative and trace zero suffice; no smoothness of the datum is assumed. -/
theorem initial_tendsto_of_hasFDerivAt
    (u₀ : E₃ →ᵇ E₃) (D₀ : E₃ →ᵇ (E₃ →L[ℝ] E₃))
    (hD : ∀ x, HasFDerivAt (u₀ : E₃ → E₃) (D₀ x) x)
    (hLp : MemLp (u₀ : E₃ → E₃) 2 volume)
    (htr : ∀ x, LinearMap.trace ℝ E₃ (D₀ x).toLinearMap = 0) :
    Tendsto (fun n => regularizerMap n (hLp.toLp u₀)) atTop (𝓝 (hLp.toLp u₀)) := by
  have hC : ContDiff ℝ 1 (u₀ : E₃ → E₃) :=
    contDiff_one_iff_hasFDerivAt.mpr ⟨D₀, D₀.continuous, hD⟩
  have hdiv (x : E₃) :
      ∑ i : Fin 3, fderiv ℝ (u₀ : E₃ → E₃) x (EuclideanSpace.single i 1) i = 0 := by
    simpa [(hD x).fderiv, LinearMap.trace_eq_matrix_trace ℝ (PiLp.basisFun 2 ℝ (Fin 3)),
      Matrix.trace, LinearMap.toMatrix_apply] using htr x
  exact initial_tendsto (hLp.toLp u₀) (c1_mem_solenoidal u₀ hC hLp hdiv)

end ClockBarrier.Euler.Regularized
