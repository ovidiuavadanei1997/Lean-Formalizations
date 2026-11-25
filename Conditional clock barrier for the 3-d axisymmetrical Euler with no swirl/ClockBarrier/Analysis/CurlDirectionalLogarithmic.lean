/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.CurlLocalIntegralEstimates
import ClockBarrier.Analysis.DirectionalBiotSavartTranslation
import ClockBarrier.Analysis.DirectionalFarTranslation
import ClockBarrier.Analysis.RadialFarCutoff
public import Mathlib.LinearAlgebra.Trace
public import ClockBarrier.Geometry.CurlLinear

/-! # The logarithmic directional strain estimate

The signed Biot–Savart formula combines the optimized near integral with the
complete finite-energy far integral, uniformly in center and unit direction.
-/

public section
open Set Metric MeasureTheory ClockBarrier.Geometry
open scoped NNReal ENNReal Topology InnerProductSpace BoundedContinuousFunction

namespace ClockBarrier.Analysis
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Translation makes the optimized near estimate uniform in its center. -/
theorem directional_smooth_near_logarithmic_bound_sub
    (ω : E₃ →ᵇ E₃) {H α : ℝ≥0} (hα : 0 < α)
    (hω : HolderWith H α (ω : E₃ → E₃))
    {χ : E₃ → ℝ} (hχ : Measurable χ)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1) (a e : E₃) (he : ‖e‖ = 1) :
    let f := fun x : E₃ =>
      let y := x - a
      let w := ω x - ω a
      (1 - χ y) * (⟪e, y⟫_ℝ *
        ⟪e, (!₂[y 1 * w 2 - y 2 * w 1, y 2 * w 0 - y 0 * w 2,
          y 0 * w 1 - y 1 * w 0] : E₃)⟫_ℝ / ‖y‖ ^ 5)
    Integrable f volume ∧ |∫ x, f x| ≤
      (3 * volume.real (ball (0 : E₃) 1) / (α : ℝ)) *
        (1 + (2 * ‖ω‖) * Real.log (Real.exp 1 + (H : ℝ))) := by
  let τ : C(E₃, E₃) := ⟨fun x => x + a, by fun_prop⟩
  let ωa := ω.compContinuous τ
  have hωa : HolderWith H α (ωa : E₃ → E₃) := fun x y => by
    simpa only [ωa, BoundedContinuousFunction.compContinuous_apply, τ,
      ContinuousMap.coe_mk, edist_add_right] using hω (x + a) (y + a)
  obtain ⟨hi, hb⟩ := directional_smooth_near_logarithmic_bound
    ωa hα hωa hχ hχ₀ hχ₁ houter e he
  intro f
  refine ⟨?_, ?_⟩
  · simpa only [ωa, BoundedContinuousFunction.compContinuous_apply, τ, ContinuousMap.coe_mk,
      zero_add, ← sub_eq_add_neg, sub_add_cancel] using hi.comp_add_right (-a)
  · rw [← integral_add_right_eq_self f a]
    have hb' : |∫ x, f (x + a)| ≤
        (3 * volume.real (ball (0 : E₃) 1) / (α : ℝ)) *
          (1 + (2 * ‖ωa‖) * Real.log (Real.exp 1 + (H : ℝ))) := by
      simpa only [f, add_sub_cancel_right, ωa, BoundedContinuousFunction.compContinuous_apply,
        τ, ContinuousMap.coe_mk, zero_add] using hb
    have hlog : 0 ≤ Real.log (Real.exp 1 + (H : ℝ)) := Real.log_nonneg
      ((Real.one_lt_exp_iff.mpr zero_lt_one).le.trans (le_add_of_nonneg_right H.coe_nonneg))
    exact hb'.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (ω.norm_compContinuous_le τ) (by norm_num)) hlog)) (by positivity))

/-- A constant chosen before the field controls its actual directional strain.
Only a positive Hölder exponent is needed for this supremum estimate. -/
theorem exists_directional_logarithmic_constant {α : ℝ≥0} (hα : 0 < α) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : E₃ →ᵇ E₃) (D : E₃ →ᵇ (E₃ →L[ℝ] E₃)),
        (∀ x, HasFDerivAt (u : E₃ → E₃) (D x) x) →
        (∃ K : ℝ≥0, HolderWith K α (D : E₃ → E₃ →L[ℝ] E₃)) →
        MemLp (u : E₃ → E₃) 2 volume →
        (∀ x, LinearMap.trace ℝ E₃ (D x).toLinearMap = 0) →
        let ω : E₃ →ᵇ E₃ := curlLinearMap.compLeftContinuousBounded E₃ D
        ∀ H : ℝ≥0, HolderWith H α (ω : E₃ → E₃) → ∀ a e : E₃, ‖e‖ = 1 →
          |⟪e, D a e⟫_ℝ| ≤ C *
            (1 + Real.sqrt (∫ x, ‖u x‖ ^ 2) + ‖ω‖ * Real.log (Real.exp 1 + (H : ℝ))) := by
  obtain ⟨χ, hχ, hzero, hχ₀, hχ₁, _, houter, hradial⟩ := exists_radial_far_cutoff
  obtain ⟨F, hF, hfar⟩ := exists_translated_directional_far_energy_constant hχ hzero hχ₀ hχ₁ houter
  let A : ℝ := 3 * volume.real (ball (0 : E₃) 1) / (α : ℝ)
  refine ⟨(3 / (4 * Real.pi)) * (2 * A + F), by dsimp [A]; positivity, ?_⟩
  rintro u D hd ⟨K, hK⟩ hL2 hdiv ω H hω a e he
  have hdf : fderiv ℝ (u : E₃ → E₃) = (D : E₃ → E₃ →L[ℝ] E₃) := funext (fun x => (hd x).fderiv)
  have hdiv' (x : E₃) : ∑ i : Fin 3, fderiv ℝ (u : E₃ → E₃) x (EuclideanSpace.single i 1) i = 0 := by
    simpa [hdf, LinearMap.trace_eq_matrix_trace ℝ (PiLp.basisFun 2 ℝ (Fin 3)),
      Matrix.trace, LinearMap.toMatrix_apply] using hdiv x
  have henergy := (memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).mp hL2
  obtain ⟨_, _, hrep⟩ := directional_strain_eq_smooth_near_add_far_sub
    (fun x => (hd x).differentiableAt) hα (by simpa only [hdf] using hK) henergy
    (fun x => u.norm_coe_le_norm x) (fun x => by rw [hdf]; exact D.norm_coe_le_norm x)
    hdiv' hχ hzero hχ₀ hχ₁ houter hradial zero_lt_one a e he
  have hn := (directional_smooth_near_logarithmic_bound_sub ω hα hω
    hχ.continuous.measurable hχ₀ hχ₁ houter a e he).2
  have hωx (x : E₃) : ω x = curlLinearMap (D x) :=
    ContinuousLinearMap.compLeftContinuousBounded_apply E₃ curlLinearMap D x
  simp only [hωx] at hn
  have hf := (hfar (fun x => (hd x).differentiableAt) hα
    (by simpa only [hdf] using hK) henergy a zero_lt_one e he).2
  simp only [hdf, inv_one, one_smul, Real.one_rpow, mul_one] at hrep hf
  rw [hrep, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (3 : ℝ) / (4 * Real.pi))]
  refine (mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hn hf))
    (by positivity : 0 ≤ (3 : ℝ) / (4 * Real.pi))).trans ?_
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hV : 0 ≤ ‖ω‖ * Real.log (Real.exp 1 + (H : ℝ)) := mul_nonneg (norm_nonneg _)
    (Real.log_nonneg ((Real.one_lt_exp_iff.mpr zero_lt_one).le.trans (le_add_of_nonneg_right H.coe_nonneg)))
  rw [mul_assoc (3 / (4 * Real.pi)) (2 * A + F)]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (3 : ℝ) / (4 * Real.pi))
  change A * (1 + 2 * ‖ω‖ * Real.log (Real.exp 1 + (H : ℝ))) +
      F * Real.sqrt (∫ x, ‖u x‖ ^ 2) ≤ _
  nlinarith only [hA, hF, mul_nonneg hA (Real.sqrt_nonneg (∫ x, ‖u x‖ ^ 2)),
    mul_nonneg hF hV]

/-- For an actual `L²` field, the square root of energy is the real `L²` norm. -/
theorem sqrt_integral_sq_norm_eq_eLpNorm_toReal {u : E₃ → E₃}
    (hu : MemLp u 2 volume) :
    Real.sqrt (∫ x, ‖u x‖ ^ 2) = (eLpNorm u 2 volume).toReal := by
  rw [hu.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat, ← one_div, ← Real.sqrt_eq_rpow,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

end ClockBarrier.Analysis
