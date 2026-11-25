/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.ComplexMixedIntegration
public import ClockBarrier.Analysis.SchwartzPairing
import Mathlib.Analysis.Calculus.MeanValue

/-! # Weak curl identities for continuously differentiable potentials -/

public section

namespace ClockBarrier.Analysis

open Set MeasureTheory SchwartzMap

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- A continuously differentiable potential with bounded derivative has a
weakly curl-free gradient. Second derivatives fall only on the test function. -/
theorem integral_schwartz_fderiv_mul_swap {q : E₃ → ℂ}
    (hq : Differentiable ℝ q) (hD : Continuous (fderiv ℝ q))
    {C : ℝ} (hC : ∀ x, ‖fderiv ℝ q x‖ ≤ C) (φ : 𝓢(E₃, ℂ)) (v w : E₃) :
    (∫ x : E₃, fderiv ℝ φ x v * fderiv ℝ q x w) =
      ∫ x : E₃, fderiv ℝ φ x w * fderiv ℝ q x v := by
  have hgrowth (x : E₃) : ‖q x‖ ≤ ‖q 0‖ + C * ‖x‖ := by
    have hs := (convex_univ : Convex ℝ (univ : Set E₃)).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => hq y) (fun y _ => hC y) (mem_univ 0) (mem_univ x)
    simp only [sub_zero] at hs
    linarith [norm_le_norm_sub_add (q x) (q 0)]
  have hiq (ψ : 𝓢(E₃, ℂ)) : Integrable (fun x => ψ x * q x) volume :=
    integrable_schwartz_mul_of_linear_growth ψ hq.continuous.aestronglyMeasurable hgrowth
  have hid (ψ : 𝓢(E₃, ℂ)) (a : E₃) :
      Integrable (fun x => ψ x * fderiv ℝ q x a) volume := by
    apply integrable_schwartz_mul_of_linear_growth ψ
      (hD.clm_apply continuous_const).aestronglyMeasurable (A := C * ‖a‖) (B := 0)
    intro x
    simpa only [zero_mul, add_zero] using ((fderiv ℝ q x).le_opNorm a).trans
      (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg a))
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    ((φ.smooth 2).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have heval (x a b : E₃) :
      fderiv ℝ (fun y => fderiv ℝ φ y a) x b = fderiv ℝ (fderiv ℝ φ) x b a := by
    rw [fderiv_clm_apply (hd x) (differentiableAt_const a)]
    simp
  apply integral_complex_fderiv_mul_fderiv_swap (φ.smooth 2) hq v w
  · simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using hid (LineDeriv.lineDerivOp v φ) w
  · simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using hid (LineDeriv.lineDerivOp w φ) v
  · simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using hiq (LineDeriv.lineDerivOp v φ)
  · simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using hiq (LineDeriv.lineDerivOp w φ)
  · have he : ⇑(LineDeriv.lineDerivOp v φ) = fun x => fderiv ℝ φ x v :=
      funext (SchwartzMap.lineDerivOp_apply_eq_fderiv v φ)
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv, he, heval] using
      hiq (LineDeriv.lineDerivOp w (LineDeriv.lineDerivOp v φ))

end ClockBarrier.Analysis
