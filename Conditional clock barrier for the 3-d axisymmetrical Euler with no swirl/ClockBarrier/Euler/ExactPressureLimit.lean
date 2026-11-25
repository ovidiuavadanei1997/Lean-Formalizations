/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.PressurePathCauchy
public import ClockBarrier.Euler.ExactProjectedLimit
public import ClockBarrier.Analysis.UniformGradientPotential

/-! # Pressure-gradient limits for the exact smooth approximation family -/
public section
namespace ClockBarrier.Euler.Smooth
open MeasureTheory Filter ContinuousLinearMap ClockBarrier.Analysis Sobolev Solenoidal SmoothL2Field
open scoped Topology BoundedContinuousFunction
local notation "Space" => EuclideanSpace ℝ (Fin 3)
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [LocallyCompactSpace K]

omit [CompactSpace K] in
theorem pressure_L2_cauchy (U : ℕ → K → SmoothL2Field Space)
    (hUc : ∀ k m, Continuous (fun t => (U k t).jetLp m))
    (V : C(K, L2)) (D : C(K, Space →ᵇ (Space →L[ℝ] Space)))
    (hV : Tendsto (fun k => fieldPath (U k) (hUc k)) atTop (𝓝 V))
    (hD : Tendsto (fun k => boundedFieldPath (fun t => (U k t).derivative)
      (continuous_jetLp_derivative _ (hUc k))) atTop (𝓝 D)) :
    CauchySeq (fun k => fieldPath (fun t => pressureForce (U k t))
      (continuous_jetLp_pressureForce _ (hUc k))) := by
  let P : C(K, L2) →L[ℝ] C(K, L2) :=
    (solenoidalProjection - ContinuousLinearMap.id ℝ L2).compLeftContinuous ℝ K
  have hN := tendsto_advectionPath hD hV
  have hQ := (P.continuous.tendsto (advectionPath D V)).comp hN
  have he (k : ℕ) : fieldPath (fun t => pressureForce (U k t))
      (continuous_jetLp_pressureForce _ (hUc k)) =
      P (advectionPath (boundedFieldPath (fun t => (U k t).derivative)
        (continuous_jetLp_derivative _ (hUc k))) (fieldPath (U k) (hUc k))) := by
    apply ContinuousMap.ext
    intro t
    change (pressureForce (U k t)).toLp =
      solenoidalProjection (boundedApplyL2 (finiteField (U k t).derivative) (U k t).toLp) -
        boundedApplyL2 (finiteField (U k t).derivative) (U k t).toLp
    rw [boundedApplyL2_smooth, pressureForce, toLp_fieldSub, solenoidalField_toLp]
  convert! hQ.cauchySeq using 1
  exact funext he

theorem exact_pressure_limit (U : ℕ → K → SmoothL2Field Space)
    (hUc : ∀ k m, Continuous (fun t => (U k t).jetLp m))
    (hsol : ∀ k t, (U k t).toLp ∈ solenoidalSpace) (R : ℝ)
    (hR : ∀ k t, ‖finiteField (U k t).derivative‖ ≤ R)
    (V : C(K, L2)) (D : C(K, Space →ᵇ (Space →L[ℝ] Space)))
    (hV : Tendsto (fun k => fieldPath (U k) (hUc k)) atTop (𝓝 V))
    (hD : Tendsto (fun k => boundedFieldPath (fun t => (U k t).derivative)
      (continuous_jetLp_derivative _ (hUc k))) atTop (𝓝 D)) :
    ∃ P : C(K, Space →ᵇ Space),
      Tendsto (fun k => boundedFieldPath (fun t => pressureForce (U k t))
        (continuous_jetLp_pressureForce _ (hUc k))) atTop (𝓝 P) ∧
      ∀ t, Differentiable ℝ (SmoothPressure.radialPotential (P t)) ∧
        ∀ x, gradient (SmoothPressure.radialPotential (P t)) x = P t x := by
  obtain ⟨P, hP⟩ := cauchySeq_tendsto_of_complete (pressure_bounded_cauchy U hUc hsol R hR
    (pressure_L2_cauchy U hUc V D hV hD))
  refine ⟨P, hP, fun t => ?_⟩
  have ht : Tendsto (fun k => finiteField (pressureForce (U k t))) atTop (𝓝 (P t)) := by
    have h := ((ContinuousMap.evalCLM ℝ t).continuous.tendsto P).comp hP
    convert! h using 1
  exact ⟨fun x => (SmoothPressure.hasFDerivAt_radialPotential_limit
      (fun k => pressureForce (U k t)) (fun k => pressureForce_gradient (U k t)) (P t) ht x).differentiableAt,
    SmoothPressure.gradient_radialPotential_limit (fun k => pressureForce (U k t))
      (fun k => pressureForce_gradient (U k t)) (P t) ht⟩

end ClockBarrier.Euler.Smooth
