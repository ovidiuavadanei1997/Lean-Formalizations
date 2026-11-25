/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.FourierWeakRelations
import Mathlib.Tactic.Ring

/-! # Orthogonality of weak gradients and solenoidal fields in `L²` -/

public section

namespace ClockBarrier.Analysis

open MeasureTheory SchwartzMap FourierTransform
open scoped ComplexConjugate ComplexInnerProductSpace

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- At a nonzero real frequency, curl-free and divergence-free vectors are
orthogonal in the complex inner product. -/
theorem sum_conj_mul_eq_zero_of_curl_div (x : Fin 3 → ℝ) (a b : Fin 3 → ℂ)
    (hx : ∃ j, x j ≠ 0) (hc : ∀ i j, (x i : ℂ) * a j = (x j : ℂ) * a i)
    (hd : ∑ i, (x i : ℂ) * b i = 0) : ∑ i, conj (a i) * b i = 0 := by
  obtain ⟨j, hj⟩ := hx
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hj)
  have hm (i : Fin 3) : (x j : ℂ) * conj (a i) = conj (a j) * (x i : ℂ) := by
    simpa only [map_mul, Complex.conj_ofReal, mul_comm] using (congrArg conj (hc i j)).symm
  rw [mul_zero, Finset.mul_sum]
  simp_rw [← mul_assoc, hm, mul_assoc]
  rw [← Finset.mul_sum, hd, mul_zero]

/-- Weak curl-free and divergence-free `L²` vector fields are orthogonal.
No spatial differentiability of the curl-free field is assumed. -/
theorem sum_inner_lp_eq_zero_of_weak_curl_div
    (f g : Fin 3 → Lp ℂ 2 (volume : Measure E₃))
    (hc : ∀ i j, LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) (f j : 𝓢'(E₃, ℂ)) =
      LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ)) (f i : 𝓢'(E₃, ℂ)))
    (hd : ∑ i, LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) (g i : 𝓢'(E₃, ℂ)) = 0) :
    ∑ i, inner ℂ (f i) (g i) = 0 := by
  have hda := ae_sum_inner_fourier_eq_zero (fun i => EuclideanSpace.single i (1 : ℝ)) g hd
  have hca (i j : Fin 3) := ae_inner_mul_fourier_eq
    (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) (f j) (f i) (hc i j)
  simp only [EuclideanSpace.inner_single_right, conj_trivial, one_mul] at hda hca
  have hcall : ∀ᵐ x : E₃, ∀ i j : Fin 3,
      (x i : ℂ) * (𝓕 (f j)) x = (x j : ℂ) * (𝓕 (f i)) x :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr (hca i)
  have hzero : ∀ᵐ x : E₃, x ≠ 0 := volume.ae_ne 0
  simp_rw [← Lp.inner_fourier_eq (f _) (g _), L2.inner_def]
  rw [← integral_finsetSum _ (fun i _ => L2.integrable_inner (𝕜 := ℂ) (𝓕 (f i)) (𝓕 (g i)))]
  apply integral_eq_zero_of_ae
  filter_upwards [hda, hcall, hzero] with x hxdiv hxcurl hx
  have hnz : ∃ i : Fin 3, x i ≠ 0 := not_forall.mp (fun h0 => hx (PiLp.ext h0))
  simp only [RCLike.inner_apply, Pi.zero_apply]
  simp_rw [mul_comm]
  exact sum_conj_mul_eq_zero_of_curl_div (fun i => x i) (fun i => (𝓕 (f i)) x)
    (fun i => (𝓕 (g i)) x) hnz hxcurl hxdiv

end ClockBarrier.Analysis
