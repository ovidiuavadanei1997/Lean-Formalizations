/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.MixedIntegration
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Tactic.Linarith

/-! # A whole-space Newtonian identity for curl-free fields

The identity transfers two derivatives using genuine L² integrability of the
kernel, field and their first derivatives. It does not integrate the singular
Newtonian gradient against an arbitrary bounded source.
-/
public section
namespace ClockBarrier.Analysis
open MeasureTheory
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem integral_curl_free_kernel_coordinate (K F : Fin 3 → Space → ℝ)
    (hK : ∀ i, Differentiable ℝ (K i)) (hF : ∀ i, Differentiable ℝ (F i))
    (hK0 : ∀ i, MemLp (K i) 2 volume) (hF0 : ∀ i, MemLp (F i) 2 volume)
    (hK1 : ∀ i j, MemLp (fun x => fderiv ℝ (K i) x (EuclideanSpace.single j 1)) 2 volume)
    (hF1 : ∀ i j, MemLp (fun x => fderiv ℝ (F i) x (EuclideanSpace.single j 1)) 2 volume)
    (hKs : ∀ x i j, fderiv ℝ (K i) x (EuclideanSpace.single j 1) =
      fderiv ℝ (K j) x (EuclideanSpace.single i 1))
    (hFs : ∀ x i j, fderiv ℝ (F i) x (EuclideanSpace.single j 1) =
      fderiv ℝ (F j) x (EuclideanSpace.single i 1)) (i j : Fin 3) :
    (∫ x, fderiv ℝ (K i) x (EuclideanSpace.single i 1) * F j x) =
      -(∫ x, K j x * fderiv ℝ (F i) x (EuclideanSpace.single i 1)) := by
  have hibp (a b c : Fin 3) := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := K a) (g := F b) (v := (EuclideanSpace.single c 1 : Space))
    ((hK1 a c).integrable_mul (hF0 b)) ((hK0 a).integrable_mul (hF1 b c))
    ((hK0 a).integrable_mul (hF0 b)) (fun x _ => hK a x) (fun x _ => hF b x)
  calc
    _ = -(∫ x, K i x * fderiv ℝ (F j) x (EuclideanSpace.single i 1)) := by
      linarith [hibp i j i]
    _ = -(∫ x, K i x * fderiv ℝ (F i) x (EuclideanSpace.single j 1)) := by
      simp only [hFs _ j i]
    _ = ∫ x, fderiv ℝ (K i) x (EuclideanSpace.single j 1) * F i x := by
      linarith [hibp i i j]
    _ = ∫ x, fderiv ℝ (K j) x (EuclideanSpace.single i 1) * F i x := by
      simp only [hKs _ i j]
    _ = _ := by linarith [hibp j i i]

theorem integral_curl_free_kernel_divergence (K F : Fin 3 → Space → ℝ)
    (hK : ∀ i, Differentiable ℝ (K i)) (hF : ∀ i, Differentiable ℝ (F i))
    (hK0 : ∀ i, MemLp (K i) 2 volume) (hF0 : ∀ i, MemLp (F i) 2 volume)
    (hK1 : ∀ i j, MemLp (fun x => fderiv ℝ (K i) x (EuclideanSpace.single j 1)) 2 volume)
    (hF1 : ∀ i j, MemLp (fun x => fderiv ℝ (F i) x (EuclideanSpace.single j 1)) 2 volume)
    (hKs : ∀ x i j, fderiv ℝ (K i) x (EuclideanSpace.single j 1) =
      fderiv ℝ (K j) x (EuclideanSpace.single i 1))
    (hFs : ∀ x i j, fderiv ℝ (F i) x (EuclideanSpace.single j 1) =
      fderiv ℝ (F j) x (EuclideanSpace.single i 1)) (j : Fin 3) :
    (∫ x, (∑ i : Fin 3, fderiv ℝ (K i) x (EuclideanSpace.single i 1)) * F j x) =
      -(∫ x, K j x * ∑ i : Fin 3, fderiv ℝ (F i) x (EuclideanSpace.single i 1)) := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum (f := fun i x => fderiv ℝ (K i) x (EuclideanSpace.single i 1) * F j x)
      _ (fun i _ => (hK1 i i).integrable_mul (hF0 j)),
    integral_finsetSum (f := fun i x => K j x * fderiv ℝ (F i) x (EuclideanSpace.single i 1))
      _ (fun i _ => (hK0 j).integrable_mul (hF1 i i))]
  simp only [integral_curl_free_kernel_coordinate K F hK hF hK0 hF0 hK1 hF1 hKs hFs,
    Finset.sum_neg_distrib]

end ClockBarrier.Analysis
