/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd,
Euler/MeanSolenoidalSpace.lean and Euler/EulerProof.lean (coordinate calculus).
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: explicit coordinate divergence, focused imports and modules.
-/
module

public import ClockBarrier.Analysis.SolenoidalProjection
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Tactic.Linarith

/-! # Smooth representatives of weakly solenoidal L² fields -/

@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Solenoidal
open MeasureTheory InnerProductSpace
open scoped ContDiff
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private def partialDerivative (f : E₃ → ℝ) (i : Fin 3) (x : E₃) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

private theorem contDiff_partialDerivative (f : E₃ → ℝ) (hf : ContDiff ℝ ∞ f)
    (i : Fin 3) : ContDiff ℝ ∞ (partialDerivative f i) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem fderiv_coordinate (f : E₃ → E₃) (x : E₃)
    (hf : DifferentiableAt ℝ f x) (i : Fin 3) (v : E₃) :
    fderiv ℝ (fun y => f y i) x v = (fderiv ℝ f x v) i := by
  have he : HasFDerivAt (fun y => f y i)
      ((EuclideanSpace.proj i).comp (fderiv ℝ f x)) x :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (f x) i).comp x hf.hasFDerivAt
  rw [he.fderiv]
  rfl

/-- Classical integration by parts against a compact smooth test, on R³. -/
theorem gradient_test_integration_by_parts (u : E₃ → E₃)
    (hu : ContDiff ℝ 1 u) (φ : E₃ → ℝ)
    (hc : HasCompactSupport φ) (hs : ContDiff ℝ ∞ φ) :
    (∫ x, ⟪gradient φ x, u x⟫_ℝ) = -∫ x, φ x * (∑ i : Fin 3, fderiv ℝ u x (EuclideanSpace.single i 1) i) := by
  let ui (i : Fin 3) (x : E₃) := u x i
  have hui (i : Fin 3) : ContDiff ℝ 1 (ui i) :=
    (EuclideanSpace.proj i : E₃ →L[ℝ] ℝ).contDiff.comp hu
  have hi₁ (i : Fin 3) : Integrable (fun x => partialDerivative φ i x * ui i x) :=
    ((contDiff_partialDerivative φ hs i).continuous.mul (hui i).continuous).integrable_of_hasCompactSupport
        ((hc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)).mul_right)
  have hi₂ (i : Fin 3) : Integrable (fun x => φ x * partialDerivative (ui i) i x) :=
    (hs.continuous.mul
      (((hui i).continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport
      hc.mul_right
  have hibp (i : Fin 3) : (∫ x, partialDerivative φ i x * ui i x) =
      -∫ x, φ x * partialDerivative (ui i) i x := by
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure E₃)) (v := EuclideanSpace.single i 1)
      (hi₁ i) (hi₂ i)
      ((hs.continuous.mul (hui i).continuous).integrable_of_hasCompactSupport hc.mul_right)
      (fun x _ => (hs.differentiable (by simp)).differentiableAt)
      (fun x _ => ((hui i).differentiable (by simp)).differentiableAt)
    change (∫ x, φ x * partialDerivative (ui i) i x) =
      -∫ x, partialDerivative φ i x * ui i x at h
    linarith
  have hinner (x : E₃) : ⟪gradient φ x, u x⟫_ℝ =
      ∑ i : Fin 3, partialDerivative φ i x * ui i x := by
    rw [inner_gradient_left]
    have hre : ∑ i : Fin 3, u x i • (EuclideanSpace.single i 1 : E₃) = u x := by
      simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
        (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (u x)
    calc
      fderiv ℝ φ x (u x) =
          fderiv ℝ φ x (∑ i : Fin 3, u x i • EuclideanSpace.single i 1) :=
        congrArg (fderiv ℝ φ x) hre.symm
      _ = ∑ i : Fin 3, partialDerivative φ i x * ui i x := by
        simp only [map_sum, map_smul, smul_eq_mul, partialDerivative, ui, mul_comm]
  have hdiv (x : E₃) : φ x * (∑ i : Fin 3, fderiv ℝ u x (EuclideanSpace.single i 1) i) =
      ∑ i : Fin 3, φ x * partialDerivative (ui i) i x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact (fderiv_coordinate u x ((hu.differentiable (by simp)).differentiableAt)
      i (EuclideanSpace.single i 1)).symm
  simp_rw [hinner, hdiv]
  rw [integral_finsetSum _ (fun i _ => hi₁ i),
    integral_finsetSum _ (fun i _ => hi₂ i)]
  simp only [hibp, Finset.sum_neg_distrib]

theorem solenoidal_representative_divergence (u : L2) (hu : u ∈ solenoidalSpace)
    (f : E₃ → E₃) (hf : ContDiff ℝ ∞ f) (hrep : u =ᵐ[volume] f) :
    ∀ x, (∑ i : Fin 3, fderiv ℝ f x (EuclideanSpace.single i 1) i) = 0 := by
  let d : E₃ → ℝ := fun x => ∑ i : Fin 3, fderiv ℝ f x (EuclideanSpace.single i 1) i
  have hc : Continuous d := continuous_finsetSum _ (fun i _ =>
    (EuclideanSpace.proj i).continuous.comp
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_const))
  have hz : d =ᵐ[volume] 0 :=
    ae_eq_zero_of_integral_contDiff_smul_eq_zero hc.locallyIntegrable (fun φ hφ hcφ => by
      have hw := weak_divergence_test hu φ hcφ hφ
      have hi := gradient_test_integration_by_parts f (hf.of_le (by simp)) φ hcφ hφ
      have heq : (∫ x, ⟪gradient φ x, u x⟫_ℝ) = ∫ x, ⟪gradient φ x, f x⟫_ℝ := by
        apply integral_congr_ae
        filter_upwards [hrep] with x hx
        rw [hx]
      change (∫ x, φ x * (∑ i : Fin 3, fderiv ℝ f x (EuclideanSpace.single i 1) i)) = 0
      rw [heq, hi] at hw
      exact neg_eq_zero.mp hw)
  intro x
  exact congrFun (Measure.eq_of_ae_eq hz hc continuous_const) x

/-- A classical divergence-free L² field lies in the actual closed mean space. -/
theorem c1_mem_solenoidal (u : E₃ → E₃) (hu : ContDiff ℝ 1 u)
    (hLp : MemLp u 2 (volume : Measure E₃))
    (hdiv : ∀ x, (∑ i : Fin 3, fderiv ℝ u x (EuclideanSpace.single i 1) i) = 0) : hLp.toLp u ∈ solenoidalSpace := by
  apply (mem_solenoidal_iff _).2
  intro φ hc hs
  calc
    (∫ x, ⟪gradient φ x, hLp.toLp u x⟫_ℝ) = ∫ x, ⟪gradient φ x, u x⟫_ℝ := by
      apply integral_congr_ae
      filter_upwards [hLp.coeFn_toLp] with x hx
      rw [hx]
    _ = -∫ x, φ x * (∑ i : Fin 3, fderiv ℝ u x (EuclideanSpace.single i 1) i) := gradient_test_integration_by_parts u hu φ hc hs
    _ = 0 := by simp only [hdiv, mul_zero, integral_zero, neg_zero]

end ClockBarrier.Analysis.Solenoidal
