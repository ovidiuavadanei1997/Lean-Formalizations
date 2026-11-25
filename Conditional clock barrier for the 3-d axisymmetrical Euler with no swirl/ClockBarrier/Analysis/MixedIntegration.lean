/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! # Transferring mixed spatial derivatives to a smooth kernel -/

public section

namespace ClockBarrier.Analysis

open MeasureTheory

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Mixed integration by parts uses second derivatives only of the smooth kernel
`f`; the function `g` needs just one spatial derivative. -/
theorem integral_fderiv_mul_fderiv_swap
    {f g : E₃ → ℝ} (hf : ContDiff ℝ 2 f) (hg : Differentiable ℝ g) (v w : E₃)
    (hvw : Integrable (fun x => fderiv ℝ f x v * fderiv ℝ g x w) volume)
    (hwv : Integrable (fun x => fderiv ℝ f x w * fderiv ℝ g x v) volume)
    (hv : Integrable (fun x => fderiv ℝ f x v * g x) volume)
    (hw : Integrable (fun x => fderiv ℝ f x w * g x) volume)
    (hsecond : Integrable (fun x => fderiv ℝ (fderiv ℝ f) x w v * g x) volume) :
    (∫ x, fderiv ℝ f x v * fderiv ℝ g x w) =
      ∫ x, fderiv ℝ f x w * fderiv ℝ g x v := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have heval (x a b : E₃) :
      fderiv ℝ (fun y => fderiv ℝ f y a) x b = fderiv ℝ (fderiv ℝ f) x b a := by
    rw [fderiv_clm_apply (hd x) (differentiableAt_const a)]
    simp
  have hsym (x : E₃) := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by norm_num) v w
  have hleft := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun x => fderiv ℝ f x v) (g := g) (v := w)
    (by simpa only [heval] using hsecond) hvw hv
    (fun x _ => (hd x).clm_apply (differentiableAt_const v)) (fun x _ => hg x)
  have hright := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun x => fderiv ℝ f x w) (g := g) (v := v)
    (by simpa only [heval, hsym] using hsecond) hwv hw
    (fun x _ => (hd x).clm_apply (differentiableAt_const w)) (fun x _ => hg x)
  simp only [heval, hsym] at hleft hright
  exact hleft.trans hright.symm

end ClockBarrier.Analysis
