/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.FourierOrthogonality

/-! # Weak derivative tests for real finite-energy vector fields -/

public section

namespace ClockBarrier.Analysis

open MeasureTheory SchwartzMap

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The weak derivative of an `L²` function is evaluated against a Schwartz
test by moving one derivative onto that test. -/
theorem lineDerivOp_toLp_apply {f : E₃ → ℂ} (hf : MemLp f 2 volume)
    (v : E₃) (φ : 𝓢(E₃, ℂ)) :
    LineDeriv.lineDerivOp v (hf.toLp f : 𝓢'(E₃, ℂ)) φ =
      -(∫ x : E₃, fderiv ℝ φ x v * f x) := by
  simp only [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
    neg_apply, smul_eq_mul, neg_mul, integral_neg,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  exact congrArg Neg.neg (integral_congr_ae (hf.coeFn_toLp.mono fun x hx => by simp only [hx]))

/-- Real `L²` vector fields with weak curl and divergence identities are
orthogonal. The tests are smooth; neither field needs second derivatives. -/
theorem integral_inner_eq_zero_of_weak_curl_div {f g : E₃ → E₃}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hc : ∀ (i j : Fin 3) (φ : 𝓢(E₃, ℂ)),
      (∫ x : E₃, fderiv ℝ φ x (EuclideanSpace.single i 1) * (f x j : ℂ)) =
        ∫ x : E₃, fderiv ℝ φ x (EuclideanSpace.single j 1) * (f x i : ℂ))
    (hd : ∀ φ : 𝓢(E₃, ℂ), ∑ i : Fin 3,
      (∫ x : E₃, fderiv ℝ φ x (EuclideanSpace.single i 1) * (g x i : ℂ)) = 0) :
    (∫ x : E₃, inner ℝ (f x) (g x)) = 0 := by
  have hfc (i : Fin 3) : MemLp (fun x => (f x i : ℂ)) 2 volume :=
    (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) i)).comp_memLp' hf
  have hgc (i : Fin 3) : MemLp (fun x => (g x i : ℂ)) 2 volume :=
    (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) i)).comp_memLp' hg
  let F (i : Fin 3) := (hfc i).toLp (fun x => (f x i : ℂ))
  let G (i : Fin 3) := (hgc i).toLp (fun x => (g x i : ℂ))
  have hcF : ∀ i j, LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) (F j : 𝓢'(E₃, ℂ)) =
      LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ)) (F i : 𝓢'(E₃, ℂ)) := by
    intro i j
    ext φ
    simpa only [F, lineDerivOp_toLp_apply] using congrArg Neg.neg (hc i j φ)
  have hdG : ∑ i : Fin 3, LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ))
      (G i : 𝓢'(E₃, ℂ)) = 0 := by
    ext φ
    simpa only [sum_apply, zero_apply, G, lineDerivOp_toLp_apply,
      Finset.sum_neg_distrib, neg_eq_zero] using hd φ
  have ho := sum_inner_lp_eq_zero_of_weak_curl_div F G hcF hdG
  simp_rw [L2.inner_def] at ho
  rw [← integral_finsetSum _ (fun i _ => L2.integrable_inner (𝕜 := ℂ) (F i) (G i))] at ho
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, Complex.ofReal_zero]
  rw [← ho]
  apply integral_congr_ae
  have hFa : ∀ᵐ x : E₃, ∀ i : Fin 3, F i x = (f x i : ℂ) :=
    ae_all_iff.mpr fun i => (hfc i).coeFn_toLp
  have hGa : ∀ᵐ x : E₃, ∀ i : Fin 3, G i x = (g x i : ℂ) :=
    ae_all_iff.mpr fun i => (hgc i).coeFn_toLp
  filter_upwards [hFa, hGa] with x hxF hxG
  simp only [PiLp.inner_apply, RCLike.inner_apply, Complex.ofReal_sum,
    Complex.ofReal_mul, conj_trivial, hxF, hxG, Complex.conj_ofReal]

end ClockBarrier.Analysis
