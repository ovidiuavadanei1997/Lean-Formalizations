/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.BilinearZero
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-! # Recovering the curl two-form from a C¹ Weber potential

Subtracting constant covectors makes the potentially rough factor multiply a
vanishing factor. The corrected potential has a second derivative at the one
point under consideration; the flow itself needs no second derivative.
-/

public section

namespace ClockBarrier.Geometry

open scoped Topology InnerProductSpace

/-- An exact difference of pulled-back velocity covectors preserves their
antisymmetric derivatives, even when the change of variables is only C¹. -/
theorem skew_deriv_eq_of_weber_potential
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f g Φ : E → E} {G : E → ℝ} {a : E}
    (hΦ : ContDiff ℝ 1 Φ) (hf : DifferentiableAt ℝ f a)
    (hg : DifferentiableAt ℝ g (Φ a))
    (hG : ∀ b, HasFDerivAt G
      ((innerSL ℝ (g (Φ b))).comp (fderiv ℝ Φ b) - innerSL ℝ (f b)) b)
    (v w : E) :
    ⟪fderiv ℝ g (Φ a) (fderiv ℝ Φ a v), fderiv ℝ Φ a w⟫_ℝ -
        ⟪fderiv ℝ g (Φ a) (fderiv ℝ Φ a w), fderiv ℝ Φ a v⟫_ℝ =
      ⟪fderiv ℝ f a v, w⟫_ℝ - ⟪fderiv ℝ f a w, v⟫_ℝ := by
  let A := fderiv ℝ Φ a
  let U := (fderiv ℝ g (Φ a)).comp A
  let q : E → ℝ := fun b => G b - ⟪g (Φ a), Φ b⟫_ℝ + ⟪f a, b⟫_ℝ
  let q' : E → E →L[ℝ] ℝ := fun b =>
    (innerSL ℝ (g (Φ b) - g (Φ a))).comp (fderiv ℝ Φ b) - innerSL ℝ (f b - f a)
  have hq (b : E) : HasFDerivAt q (q' b) b := by
    have hh : HasFDerivAt q
        (((innerSL ℝ (g (Φ b))).comp (fderiv ℝ Φ b) - innerSL ℝ (f b)) -
          (innerSL ℝ (g (Φ a))).comp (fderiv ℝ Φ b) + innerSL ℝ (f a)) b :=
      ((hG b).sub ((innerSL ℝ (g (Φ a))).hasFDerivAt.comp b
        ((hΦ.differentiable (by decide)) b).hasFDerivAt)).add
        (innerSL ℝ (f a)).hasFDerivAt
    apply hh.congr_fderiv
    ext z
    simp only [q', sub_apply, add_apply, ContinuousLinearMap.comp_apply, map_sub]
    module
  have hsmall : HasFDerivAt (fun b => innerSL ℝ (g (Φ b) - g (Φ a)))
      ((innerSL ℝ).comp U) a :=
    (innerSL ℝ).hasFDerivAt.comp a
      ((hg.hasFDerivAt.comp a ((hΦ.differentiable (by decide)) a).hasFDerivAt).sub_const _)
  have hprod := Analysis.hasFDerivAt_bilinear_of_zero
    (ContinuousLinearMap.compL ℝ E E ℝ) hsmall
    (by simp only [sub_self, map_zero])
    ((hΦ.continuous_fderiv (by decide)).continuousAt (x := a))
  have hsub := (innerSL ℝ).hasFDerivAt.comp a (hf.hasFDerivAt.sub_const (f a))
  have hsymm := second_derivative_symmetric hq (hprod.sub hsub) v w
  simp only [sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    A, U] at hsymm
  change ⟪fderiv ℝ g (Φ a) (fderiv ℝ Φ a v), fderiv ℝ Φ a w⟫_ℝ -
      ⟪fderiv ℝ f a v, w⟫_ℝ =
    ⟪fderiv ℝ g (Φ a) (fderiv ℝ Φ a w), fderiv ℝ Φ a v⟫_ℝ -
      ⟪fderiv ℝ f a w, v⟫_ℝ at hsymm
  linarith only [hsymm]

end ClockBarrier.Geometry
