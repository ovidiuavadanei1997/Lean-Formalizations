/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Cylindrical integration in three-dimensional Euclidean space

The radius is positive, the height is unrestricted, and the angular integral
contributes exactly `2 * π`. The axis and polar branch cut have zero volume.
-/

public section

namespace ClockBarrier.Analysis

open Set MeasureTheory

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Separating height from the two transverse Cartesian coordinates preserves
the standard Euclidean volume, with no normalization factor. -/
theorem measurePreserving_height_transverse :
    MeasurePreserving (fun q : ℝ × (ℝ × ℝ) => (!₂[q.2.1, q.2.2, q.1] : E₃)) := by
  have h := (PiLp.volume_preserving_toLp (Fin 3)).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm.comp
      ((MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ).symm))
  convert! h using 1
  ext q i
  fin_cases i <;> rfl

/-- The coordinate separation is a measurable embedding, so it also transports
integrability rather than only totalized integrals. -/
theorem measurableEmbedding_height_transverse :
    MeasurableEmbedding (fun q : ℝ × (ℝ × ℝ) => (!₂[q.2.1, q.2.2, q.1] : E₃)) := by
  apply (show Continuous (fun q : ℝ × (ℝ × ℝ) =>
    (!₂[q.2.1, q.2.2, q.1] : E₃)) by fun_prop).measurableEmbedding
  exact fun _ _ he => Prod.ext (congrArg (fun x : E₃ => x 2) he)
    (Prod.ext (congrArg (fun x : E₃ => x 0) he) (congrArg (fun x : E₃ => x 1) he))

/-- The polar Jacobian transports absolute integrability on the whole plane. -/
theorem integrableOn_polar_pullback {f : ℝ × ℝ → ℝ} (hf : Integrable f) :
    IntegrableOn (fun q : ℝ × ℝ => q.1 * f (q.1 * Real.cos q.2, q.1 * Real.sin q.2))
      (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) := by
  have h := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    polarCoord.open_target.measurableSet
    (fun q _ => (hasFDerivAt_polarCoord_symm q).hasFDerivWithinAt)
    polarCoord.symm.injOn f).mp
    (polarCoord.symm_image_target_eq_source.symm ▸ hf.integrableOn)
  refine h.congr_fun (fun q hq => ?_) polarCoord.open_target.measurableSet
  simp only [det_fderivPolarCoordSymm, abs_of_pos (show 0 < q.1 from hq.1),
    smul_eq_mul, polarCoord_symm_apply]

/-- Integrating an angularly invariant scalar over the plane contributes exactly
`2 * π`; its remaining one-dimensional measure is `r dr`. -/
theorem integral_eq_two_pi_mul_radial {f : ℝ × ℝ → ℝ}
    (hrot : ∀ r : ℝ, 0 < r → ∀ θ : ℝ,
      f (r * Real.cos θ, r * Real.sin θ) = f (r, 0)) :
    ∫ q : ℝ × ℝ, f q = (2 * Real.pi) * ∫ r in Ioi (0 : ℝ), r * f (r, 0) := by
  rw [← integral_comp_polarCoord_symm f]
  have he : (∫ q in polarCoord.target, q.1 • f (polarCoord.symm q)) =
      ∫ q in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, q.1 * f (q.1, 0) :=
    setIntegral_congr_fun polarCoord.open_target.measurableSet
      (fun q hq => congrArg (fun v : ℝ => q.1 * v) (hrot q.1 hq.1 q.2))
  rw [he]
  change (∫ q : ℝ × ℝ, q.1 * f (q.1, 0)
    ∂(volume.prod volume).restrict (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi)) = _
  rw [← Measure.prod_restrict, integral_fun_fst (fun r : ℝ => r * f (r, 0))]
  simp [Measure.real, Real.volume_Ioo, sub_neg_eq_add, two_mul, Real.pi_pos.le]

/-- Absolute planar integrability gives absolute integrability with the radial
weight; the angular measure is finite and nonzero. -/
theorem integrableOn_radial_of_integrable {f : ℝ × ℝ → ℝ} (hf : Integrable f)
    (hrot : ∀ r : ℝ, 0 < r → ∀ θ : ℝ,
      f (r * Real.cos θ, r * Real.sin θ) = f (r, 0)) :
    IntegrableOn (fun r : ℝ => r * f (r, 0)) (Ioi (0 : ℝ)) := by
  have hp : IntegrableOn (fun q : ℝ × ℝ => q.1 * f (q.1, 0))
      (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) :=
    (integrableOn_polar_pullback hf).congr_fun
      (fun q hq => congrArg (fun v : ℝ => q.1 * v) (hrot q.1 hq.1 q.2))
      (measurableSet_Ioi.prod measurableSet_Ioo)
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hp
  refine hp.of_comp_fst ?_
  simp [ne_eq, Measure.restrict_eq_zero, Real.volume_Ioo, sub_neg_eq_add,
    Real.pi_pos]

/-- Cylindrical reduction of an integrable angularly invariant scalar. The order
of the remaining integrals is height, then positive radius. -/
theorem integral_eq_two_pi_mul_cylindrical {f : E₃ → ℝ} (hf : Integrable f)
    (hrot : ∀ r : ℝ, 0 < r → ∀ θ z : ℝ,
      f !₂[r * Real.cos θ, r * Real.sin θ, z] = f !₂[r, 0, z]) :
    ∫ x : E₃, f x = (2 * Real.pi) * ∫ z : ℝ, ∫ r in Ioi (0 : ℝ), r * f !₂[r, 0, z] := by
  rw [← measurePreserving_height_transverse.integral_comp
    measurableEmbedding_height_transverse f, Measure.volume_eq_prod,
    integral_prod (fun q : ℝ × (ℝ × ℝ) => f !₂[q.2.1, q.2.2, q.1])
      ((measurePreserving_height_transverse.integrable_comp_emb
      measurableEmbedding_height_transverse).mpr hf)]
  have he (z : ℝ) : (∫ q : ℝ × ℝ, f !₂[q.1, q.2, z]) =
      (2 * Real.pi) * ∫ r in Ioi (0 : ℝ), r * f !₂[r, 0, z] :=
    integral_eq_two_pi_mul_radial (fun r hr θ => hrot r hr θ z)
  simp only [he, integral_const_mul]

/-- Absolute cylindrical mass has the same angular normalization as signed mass. -/
theorem integral_norm_radial_eq_inv_two_pi_mul {f : ℝ × ℝ → ℝ}
    (hrot : ∀ r : ℝ, 0 < r → ∀ θ : ℝ,
      f (r * Real.cos θ, r * Real.sin θ) = f (r, 0)) :
    (∫ r in Ioi (0 : ℝ), ‖r * f (r, 0)‖) =
      (2 * Real.pi)⁻¹ * ∫ q : ℝ × ℝ, ‖f q‖ := by
  rw [integral_eq_two_pi_mul_radial (f := fun q => ‖f q‖)
    (fun r hr θ => congrArg norm (hrot r hr θ))]
  rw [← mul_assoc, inv_mul_cancel₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero), one_mul]
  exact setIntegral_congr_fun measurableSet_Ioi
    (fun r hr => by simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (show 0 < r from hr)])

/-- The weighted meridional integrand is jointly absolutely integrable. This
licenses either order of cylindrical integration. -/
theorem integrableOn_cylindrical_of_integrable {f : E₃ → ℝ}
    (hm : Measurable f) (hf : Integrable f)
    (hrot : ∀ r : ℝ, 0 < r → ∀ θ z : ℝ,
      f !₂[r * Real.cos θ, r * Real.sin θ, z] = f !₂[r, 0, z]) :
    IntegrableOn (fun q : ℝ × ℝ => q.2 * f !₂[q.2, 0, q.1])
      (univ ×ˢ Ioi (0 : ℝ)) := by
  have hs : Integrable (fun q : ℝ × (ℝ × ℝ) => f !₂[q.2.1, q.2.2, q.1])
      (volume.prod volume) :=
    (measurePreserving_height_transverse.integrable_comp_emb
      measurableEmbedding_height_transverse).mpr hf
  have hmc : Measurable (fun q : ℝ × ℝ => q.2 * f !₂[q.2, 0, q.1]) := by fun_prop
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  refine (integrable_prod_iff hmc.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  case refine_2 =>
    exact (hs.integral_norm_prod_left.const_mul (2 * Real.pi)⁻¹).congr
      (Filter.Eventually.of_forall (fun z =>
        (integral_norm_radial_eq_inv_two_pi_mul
          (f := fun q : ℝ × ℝ => f !₂[q.1, q.2, z])
          (fun r hr θ => hrot r hr θ z)).symm))
  exact hs.prod_right_ae.mono (fun z hz =>
    integrableOn_radial_of_integrable hz (fun r hr θ => hrot r hr θ z))

end ClockBarrier.Analysis
