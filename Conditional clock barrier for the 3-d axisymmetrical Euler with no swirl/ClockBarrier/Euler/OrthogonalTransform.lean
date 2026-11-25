/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.Classical
public import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! # Orthogonal covariance of the classical Euler interface -/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Orthogonal changes of coordinates preserve the full classical interface,
including finite energy and both temporal norm conventions. -/
theorem classical_euler_on.exists_orthogonal_transform
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (R : E₃ ≃ₗᵢ[ℝ] E₃) :
    ∃ v : ℝ → E₃ →ᵇ E₃, (∀ t x, v t x = R (u t (R.symm x))) ∧
      classical_euler_on α T v (fun t x => p t (R.symm x)) := by
  obtain ⟨hT, hα, hα1, hu, ⟨D, hD, hd, hH⟩, hL, hLt, hp, hgp, hut, hdiv⟩ := h
  let c : C(E₃, E₃) := ⟨R.symm, R.symm.continuous⟩
  let v (t : ℝ) := R.toContinuousLinearMap.compLeftContinuousBounded E₃
    ((u t).compContinuous c)
  let C : (E₃ →L[ℝ] E₃) →L[ℝ] (E₃ →L[ℝ] E₃) :=
    ((ContinuousLinearMap.compL ℝ E₃ E₃ E₃).flip R.symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.compL ℝ E₃ E₃ E₃ R.toContinuousLinearMap)
  let d (t : ℝ) := C.compLeftContinuousBounded E₃ ((D t).compContinuous c)
  have hv (t : ℝ) (x : E₃) : v t x = R (u t (R.symm x)) := rfl
  have hd' (t : ℝ) (ht : t ∈ Ico 0 T) (x : E₃) : HasFDerivAt (v t) (d t x) x :=
    R.toContinuousLinearMap.hasFDerivAt.comp x
      ((hd t ht (R.symm x)).comp x R.symm.toContinuousLinearMap.hasFDerivAt)
  have hgrad (t : ℝ) (ht : t ∈ Ico 0 T) (x : E₃) :
      gradient (fun y => p t (R.symm y)) x = R (gradient (p t) (R.symm x)) := by
    have hh := ((hp t ht (R.symm x)).hasGradientAt.hasFDerivAt).comp x
      R.symm.toContinuousLinearMap.hasFDerivAt
    have he : HasFDerivAt (fun y => p t (R.symm y))
        (innerSL ℝ (R (gradient (p t) (R.symm x)))) x := by
      apply hh.congr_fderiv
      ext z
      change inner ℝ (gradient (p t) (R.symm x)) (R.symm z) =
        inner ℝ (R (gradient (p t) (R.symm x))) z
      exact (R.inner_map_eq_flip _ _).symm
    exact (hasGradientAt_iff_hasFDerivAt.mpr he).gradient
  refine ⟨v, hv, hT, hα, hα1, ?_, ⟨d, ?_, hd', ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact R.toContinuousLinearMap.compLeftContinuousBounded E₃ |>.continuous.comp_continuousOn
      ((BoundedContinuousFunction.continuous_compContinuous c).comp_continuousOn hu)
  · exact (C.compLeftContinuousBounded E₃).continuous.comp_continuousOn
      ((BoundedContinuousFunction.continuous_compContinuous c).comp_continuousOn hD)
  · intro b hb
    obtain ⟨H, hH'⟩ := hH b hb
    refine ⟨‖C‖₊ * H, ?_⟩
    intro t ht
    change HolderWith (‖C‖₊ * H) α (fun x => C (D t (R.symm x)))
    simpa only [NNReal.coe_one, NNReal.rpow_one, NNReal.one_rpow, one_mul, mul_one,
      Function.comp_def] using
      C.lipschitz.holderWith.comp ((hH' t ht).comp R.symm.isometry.lipschitz.holderWith)
  · intro t ht
    exact R.toContinuousLinearMap.comp_memLp' ((hL t ht).comp_measurePreserving R.symm.measurePreserving)
  · intro t ht
    have he (s : ℝ) : eLpNorm (fun x => v s x - v t x) 2 volume =
        eLpNorm (fun x => u s x - u t x) 2 volume := by
      calc
        _ = eLpNorm ((fun y => u s y - u t y) ∘ R.symm) 2 volume := by
          apply eLpNorm_congr_norm_ae
          exact Eventually.of_forall (fun x => by rw [hv, hv, ← map_sub, R.norm_map]; rfl)
        _ = _ := eLpNorm_comp_measurePreserving
          ((u s).continuous.sub (u t).continuous).aestronglyMeasurable R.symm.measurePreserving
    simpa only [he] using hLt t ht
  · intro t ht
    exact (hp t ht).comp R.symm.toContinuousLinearMap.differentiable
  · have hpull : ContinuousOn (fun q : ℝ × E₃ => gradient (p q.1) (R.symm q.2))
        (Ico 0 T ×ˢ univ) :=
      hgp.comp (continuousOn_fst.prodMk (R.symm.continuous.comp_continuousOn continuousOn_snd))
        (fun q hq => ⟨hq.1, mem_univ _⟩)
    exact (R.continuous.comp_continuousOn hpull).congr
      (fun q hq => hgrad q.1 hq.1 q.2)
  · intro t ht x
    have hh := R.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t (hut t ht (R.symm x))
    apply hh.congr_deriv
    rw [(hd' t ht x).fderiv, hgrad t ht x, (hd t ht (R.symm x)).fderiv]
    change R (-D t (R.symm x) (u t (R.symm x)) - gradient (p t) (R.symm x)) =
      -R (D t (R.symm x) (R.symm (R (u t (R.symm x))))) - R (gradient (p t) (R.symm x))
    rw [R.symm_apply_apply, map_sub, map_neg]
  · intro t ht x
    rw [(hd' t ht x).fderiv]
    change LinearMap.trace ℝ E₃ (R.toLinearEquiv.conj (D t (R.symm x)).toLinearMap) = 0
    rw [LinearMap.trace_conj', ← (hd t ht (R.symm x)).fderiv]
    exact hdiv t ht (R.symm x)

end ClockBarrier.Euler
