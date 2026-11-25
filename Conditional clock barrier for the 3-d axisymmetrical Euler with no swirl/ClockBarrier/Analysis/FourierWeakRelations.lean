/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Recovering almost-everywhere identities from tempered `L²` relations -/

public section

namespace ClockBarrier.Analysis

open MeasureTheory SchwartzMap
open scoped ContDiff

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Continuous scalar multiplication preserves local integrability of an `L²` function. -/
theorem locallyIntegrable_mul_lp (c : E₃ → ℂ) (hc : Continuous c)
    (f : Lp ℂ 2 (volume : Measure E₃)) :
    LocallyIntegrable (fun x => c x * f x) volume := by
  rw [← locallyIntegrableOn_univ]
  exact (locallyIntegrableOn_univ.mpr ((Lp.memLp f).locallyIntegrable (by norm_num))).continuousOn_mul
    hc.continuousOn isClosed_univ.isLocallyClosed

/-- A finite distributional multiplier identity for `L²` functions holds
almost everywhere. The multipliers need not be bounded. -/
theorem ae_sum_mul_lp_eq_zero {ι : Type*} [Fintype ι]
    (c : ι → E₃ → ℂ) (hc : ∀ i, (c i).HasTemperateGrowth)
    (f : ι → Lp ℂ 2 (volume : Measure E₃))
    (h : ∑ i, TemperedDistribution.smulLeftCLM ℂ (c i) (f i : 𝓢'(E₃, ℂ)) = 0) :
    ∀ᵐ x : E₃, ∑ i, c i x * f i x = 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
  · exact locallyIntegrable_finsetSum Finset.univ
      (fun i _ => locallyIntegrable_mul_lp (c i) (hc i).1.continuous (f i))
  intro g hg hs
  have hgc : HasCompactSupport (Complex.ofRealCLM ∘ g) := hs.comp_left rfl
  have hgd : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  have he := congrArg (fun D : 𝓢'(E₃, ℂ) => D (hgc.toSchwartzMap hgd)) h
  simp only [sum_apply, zero_apply, TemperedDistribution.smulLeftCLM_apply_apply,
    Lp.toTemperedDistribution_apply, SchwartzMap.smulLeftCLM_apply_apply (hc _)] at he
  have hi (i : ι) := (locallyIntegrable_mul_lp (c i) (hc i).1.continuous (f i)).integrable_smul_left_of_hasCompactSupport hg.continuous hs
  simp_rw [Finset.smul_sum]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simpa [smul_eq_mul, Complex.real_smul, mul_comm, mul_left_comm, mul_assoc] using he

/-- A vanishing distributional divergence becomes the corresponding
frequency-space identity almost everywhere. -/
theorem ae_sum_inner_fourier_eq_zero {ι : Type*} [Fintype ι]
    (m : ι → E₃) (f : ι → Lp ℂ 2 (volume : Measure E₃))
    (h : ∑ i, LineDeriv.lineDerivOp (m i) (f i : 𝓢'(E₃, ℂ)) = 0) :
    ∀ᵐ x : E₃, ∑ i, (inner ℝ x (m i) : ℂ) * (FourierTransform.fourier (f i)) x = 0 := by
  have he := congrArg (fun D : 𝓢'(E₃, ℂ) => FourierTransform.fourier D) h
  simp only [FourierTransform.fourier_sum, FourierTransform.fourier_zero,
    TemperedDistribution.fourier_lineDerivOp_eq, Lp.fourier_toTemperedDistribution_eq,
    ← Finset.smul_sum] at he
  have hz := (smul_eq_zero.mp he).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
  exact ae_sum_mul_lp_eq_zero (fun i x => (inner ℝ x (m i) : ℂ)) (by fun_prop)
    (fun i => FourierTransform.fourier (f i)) hz

/-- Equality of distributional cross derivatives gives the curl-free
frequency relation without differentiating either `L²` function. -/
theorem ae_inner_mul_fourier_eq (v w : E₃) (f g : Lp ℂ 2 (volume : Measure E₃))
    (h : LineDeriv.lineDerivOp v (f : 𝓢'(E₃, ℂ)) =
      LineDeriv.lineDerivOp w (g : 𝓢'(E₃, ℂ))) :
    ∀ᵐ x : E₃, (inner ℝ x v : ℂ) * (FourierTransform.fourier f) x =
      (inner ℝ x w : ℂ) * (FourierTransform.fourier g) x := by
  have hz : ∑ i : Fin 2, LineDeriv.lineDerivOp (![v, -w] i)
      (![f, g] i : 𝓢'(E₃, ℂ)) = 0 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      LineDeriv.lineDerivOp_left_neg, h, add_neg_cancel]
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    inner_neg_right, Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg, sub_eq_zero] using
    ae_sum_inner_fourier_eq_zero ![v, -w] ![f, g] hz

end ClockBarrier.Analysis
