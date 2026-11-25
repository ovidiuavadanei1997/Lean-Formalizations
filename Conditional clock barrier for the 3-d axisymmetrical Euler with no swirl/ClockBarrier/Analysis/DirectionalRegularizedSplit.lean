/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.DirectionalNearIntegrability
public import ClockBarrier.Analysis.DirectionalNewtonianLimit
public import ClockBarrier.Analysis.DirectionalCancellation
import Mathlib.Tactic.Ring

/-! # The integrable signed split before removing regularization

The near term retains its complementary cutoff. The full far term includes the
transition annulus. Every integral split below consumes actual integrability.
-/

public section
namespace ClockBarrier.Analysis
open Filter MeasureTheory
open scoped Topology InnerProductSpace
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Subtraction of the constant vorticity is justified at each positive
regularizing length before passage to the singular limit. -/
theorem integral_regularized_directional_eq_near_add_far
    {ω : E₃ → E₃} (hω : Continuous ω) {χ : E₃ → ℝ} (hχ : Continuous χ)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (hradial : ∀ x y, ‖x‖ = ‖y‖ → χ x = χ y)
    {r : ℝ} (houter : ∀ x, r ≤ ‖x‖ → χ x = 1) (e : E₃) (he : ‖e‖ = 1) :
    let N := fun (x w : E₃) => ⟪e, x⟫_ℝ *
      ⟪e, (!₂[x 1 * w 2 - x 2 * w 1, x 2 * w 0 - x 0 * w 2,
        x 0 * w 1 - x 1 * w 0] : E₃)⟫_ℝ
    Integrable (fun x => (1 - χ x) * (N x (ω x - ω 0) / ‖x‖ ^ 5)) volume →
    Integrable (fun x => χ x * (N x (ω x) / ‖x‖ ^ 5)) volume →
    ∀ {ε : ℝ}, 0 < ε →
      (∫ x, N x (ω x) * (ε ^ 2 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)) =
        (∫ x, (1 - χ x) * N x (ω x - ω 0) *
          (ε ^ 2 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)) +
        ∫ x, χ x * N x (ω x) * (ε ^ 2 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) := by
  intro N hnear hfar ε hε
  have hN (x v w : E₃) : N x (v - w) = N x v - N x w := by
    simp [N, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
    ring
  let R (x : E₃) := (ε ^ 2 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)
  have hin : Integrable (fun x => (1 - χ x) * N x (ω x - ω 0) * R x) volume :=
    integrable_regularized_radial_numerator (by dsimp [N]; fun_prop)
      (by simp [N]) (by simpa only [mul_div_assoc] using hnear) ε
  have hif : Integrable (fun x => χ x * N x (ω x) * R x) volume :=
    integrable_regularized_radial_numerator (by dsimp [N]; fun_prop)
      (by simp [N]) (by simpa only [mul_div_assoc] using hfar) ε
  have hic : Integrable (fun x => (1 - χ x) * (N x (ω 0) * R x)) volume :=
    integrable_near_regularized_numerator (by dsimp [N]; fun_prop)
      hχ hχ₀ hχ₁ houter hε
  have hz : (∫ x, (1 - χ x) * (N x (ω 0) * R x)) = 0 := by
    have hc := integral_radial_directional_curl_eq_zero (ψ := fun x => (1 - χ x) * R x)
      (fun x y hxy => by simp only [R, hxy, hradial x y hxy]) (ω 0) e he
    refine Eq.trans (integral_congr_ae (ae_of_all _ fun x => ?_)) hc
    dsimp only [N]
    ring
  calc
    _ = ∫ x, ((1 - χ x) * N x (ω x - ω 0) * R x + χ x * N x (ω x) * R x) +
        (1 - χ x) * (N x (ω 0) * R x) := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      change N x (ω x) * R x =
        ((1 - χ x) * N x (ω x - ω 0) * R x + χ x * N x (ω x) * R x) +
          (1 - χ x) * (N x (ω 0) * R x)
      rw [hN]
      ring
    _ = _ := by
      have hsum := integral_add (hin.add hif) hic
      simp only [Pi.add_apply] at hsum
      rw [hsum, integral_add hin hif, hz, add_zero]

end ClockBarrier.Analysis
