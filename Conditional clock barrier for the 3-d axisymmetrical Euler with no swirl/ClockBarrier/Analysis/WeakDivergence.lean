/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.ComplexMixedIntegration
public import ClockBarrier.Analysis.SchwartzPairing

/-! # Weak divergence identities for bounded continuously differentiable fields -/

public section

namespace ClockBarrier.Analysis

open MeasureTheory SchwartzMap

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Moving a derivative between a Schwartz test and a bounded `C¹` function. -/
theorem integral_schwartz_fderiv_mul_eq_neg {q : E₃ → ℂ}
    (hq : Differentiable ℝ q) (hD : Continuous (fderiv ℝ q))
    {A B : ℝ} (hA : ∀ x, ‖q x‖ ≤ A) (hB : ∀ x, ‖fderiv ℝ q x‖ ≤ B)
    (φ : 𝓢(E₃, ℂ)) (v : E₃) :
    (∫ x : E₃, fderiv ℝ φ x v * q x) =
      -(∫ x : E₃, φ x * fderiv ℝ q x v) := by
  have hiq (ψ : 𝓢(E₃, ℂ)) :=
    integrable_schwartz_mul_of_bounded ψ hq.continuous.aestronglyMeasurable hA
  have hid : Integrable (fun x => φ x * fderiv ℝ q x v) volume :=
    integrable_schwartz_mul_of_bounded φ (hD.clm_apply continuous_const).aestronglyMeasurable
      (fun x => ((fderiv ℝ q x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hB x) (norm_nonneg v)))
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := (φ : E₃ → ℂ)) (g := q) (v := v)
    (by simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using hiq (LineDeriv.lineDerivOp v φ))
    hid (hiq φ) (fun x _ => φ.differentiableAt) (fun x _ => hq x)
  simpa only [neg_neg] using congrArg Neg.neg hi.symm

/-- Classical divergence zero yields the weak Schwartz-test identity. -/
theorem sum_integral_schwartz_fderiv_mul_eq_zero {g : E₃ → E₃}
    (hg : Differentiable ℝ g) (hD : Continuous (fderiv ℝ g))
    {A B : ℝ} (hA : ∀ x, ‖g x‖ ≤ A) (hB : ∀ x, ‖fderiv ℝ g x‖ ≤ B)
    (hdiv : ∀ x, ∑ i : Fin 3, fderiv ℝ g x (EuclideanSpace.single i 1) i = 0)
    (φ : 𝓢(E₃, ℂ)) :
    ∑ i : Fin 3, (∫ x : E₃, fderiv ℝ φ x (EuclideanSpace.single i 1) * (g x i : ℂ)) = 0 := by
  let L (i : Fin 3) := Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) i)
  have hd (i : Fin 3) (x : E₃) : fderiv ℝ (fun y => (g y i : ℂ)) x =
      (L i).comp (fderiv ℝ g x) :=
    ((L i).hasFDerivAt.comp x (hg x).hasFDerivAt).fderiv
  have hq (i : Fin 3) : Differentiable ℝ (fun x => (g x i : ℂ)) :=
    (L i).differentiable.comp hg
  have hDc (i : Fin 3) : Continuous (fderiv ℝ (fun x => (g x i : ℂ))) := by
    exact (continuous_const.clm_comp hD).congr (fun x => (hd i x).symm)
  have hBc (i : Fin 3) (x : E₃) : ‖fderiv ℝ (fun y => (g y i : ℂ)) x‖ ≤ ‖L i‖ * B := by
    rw [hd]
    exact ((L i).opNorm_comp_le (fderiv ℝ g x)).trans
      (mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _))
  have hAc (i : Fin 3) (x : E₃) : ‖(g x i : ℂ)‖ ≤ A := by
    simpa only [Complex.norm_real] using (PiLp.norm_apply_le (g x) i).trans (hA x)
  have hi (i : Fin 3) := integral_schwartz_fderiv_mul_eq_neg
    (hq i) (hDc i) (hAc i) (hBc i) φ (EuclideanSpace.single i 1)
  simp_rw [hi, Finset.sum_neg_distrib]
  have hid (i : Fin 3) : Integrable (fun x => φ x *
      fderiv ℝ (fun y => (g y i : ℂ)) x (EuclideanSpace.single i 1)) volume :=
    integrable_schwartz_mul_of_bounded φ
      ((hDc i).clm_apply continuous_const).aestronglyMeasurable
      (fun x => ((fderiv ℝ (fun y => (g y i : ℂ)) x).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hBc i x) (norm_nonneg _)))
  rw [← integral_finsetSum _ (fun i _ => hid i), neg_eq_zero]
  apply integral_eq_zero_of_ae
  filter_upwards [] with x
  simp only [hd, ContinuousLinearMap.comp_apply, L, Complex.ofRealCLM_apply,
    EuclideanSpace.coe_proj, ← Finset.mul_sum, ← Complex.ofReal_sum, hdiv, Complex.ofReal_zero,
    mul_zero, Pi.zero_apply]

end ClockBarrier.Analysis
