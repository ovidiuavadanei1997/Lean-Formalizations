/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.AxisFarL2Bound
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! # The complete far-field estimate in an arbitrary direction

Finite Cartesian contraction reuses the component integration-by-parts estimate.
The resulting constant is uniform in the unit direction, and includes the
derivative of the cutoff throughout its transition annulus.
-/

public section
namespace ClockBarrier.Analysis
open MeasureTheory Geometry
open scoped Topology ContDiff NNReal InnerProductSpace
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The directional curl kernel is a finite contraction of Cartesian derivatives. -/
theorem directional_far_curl_expansion (χ : E₃ → ℝ) (u : E₃ → E₃) (x e : E₃) :
    let w := curlLinearMap (fderiv ℝ u x)
    χ x * (⟪e, x⟫_ℝ *
      ⟪e, (!₂[x 1 * w 2 - x 2 * w 1, x 2 * w 0 - x 0 * w 2,
        x 0 * w 1 - x 1 * w 0] : E₃)⟫_ℝ / ‖x‖ ^ 5) =
      ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3, e j * e k *
        (χ x * (x i * x j / ‖x‖ ^ 5) * fderiv ℝ u x (EuclideanSpace.single k 1) i -
          χ x * (x i * x j / ‖x‖ ^ 5) * fderiv ℝ u x (EuclideanSpace.single i 1) k) := by
  intro w
  have h0 : (EuclideanSpace.single 0 1 : E₃) = !₂[1, 0, 0] := by
    ext i; fin_cases i <;> simp
  have h1 : (EuclideanSpace.single 1 1 : E₃) = !₂[0, 1, 0] := by
    ext i; fin_cases i <;> simp
  have h2 : (EuclideanSpace.single 2 1 : E₃) = !₂[0, 0, 1] := by
    ext i; fin_cases i <;> simp
  simp only [Fin.sum_univ_three, h0, h1, h2, w, curlLinearMap_apply]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  ring

/-- The complete far-field functional is bounded by energy, uniformly in the
unit strain direction. No vorticity cancellation at the origin is assumed. -/
theorem exists_directional_far_energy_constant
    {χ : E₃ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : χ =ᶠ[𝓝 (0 : E₃)] 0)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : E₃ → E₃} {H α : ℝ≥0},
      Differentiable ℝ u → 0 < α → HolderWith H α (fderiv ℝ u) →
      Integrable (fun x => ‖u x‖ ^ 2) volume → ∀ e : E₃, ‖e‖ = 1 →
      let f := fun x : E₃ =>
        let w := curlLinearMap (fderiv ℝ u x)
        χ x * (⟪e, x⟫_ℝ *
          ⟪e, (!₂[x 1 * w 2 - x 2 * w 1, x 2 * w 0 - x 0 * w 2,
            x 0 * w 1 - x 1 * w 0] : E₃)⟫_ℝ / ‖x‖ ^ 5)
      Integrable f volume ∧ |∫ x, f x| ≤ C * Real.sqrt (∫ x : E₃, ‖u x‖ ^ 2) := by
  let B (i j k : Fin 3) : ℝ := Real.sqrt (∫ x : E₃,
    ‖fderiv ℝ (fun y : E₃ => χ y * (y i * y j / ‖y‖ ^ 5)) x
      (EuclideanSpace.single k 1)‖ ^ 2)
  refine ⟨∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3, (B i j k + B i j i),
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))), ?_⟩
  intro u H α hu hα hD henergy e he f
  let g (i j k l : Fin 3) (x : E₃) : ℝ :=
    χ x * (x i * x j / ‖x‖ ^ 5) * fderiv ℝ u x (EuclideanSpace.single k 1) l
  have hi (i j k l : Fin 3) : Integrable (g i j k l) volume :=
    integrable_axis_far_mul_velocity_derivative hχ hzero hχ₀ hχ₁ hu hα hD henergy
      i j l (EuclideanSpace.single k 1) (by simp)
  have hb (i j k l : Fin 3) : |∫ x, g i j k l x| ≤
      B i j k * Real.sqrt (∫ x : E₃, ‖u x‖ ^ 2) :=
    abs_integral_axis_far_mul_velocity_derivative_le hχ hzero hχ₀ hχ₁ houter
      hu hα hD henergy i j l (EuclideanSpace.single k 1) (by simp)
  have hf (x : E₃) : f x = ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
      e j * e k * (g i j k i x - g i j i k x) :=
    directional_far_curl_expansion χ u x e
  have hit (i j k : Fin 3) : Integrable
      (fun x => e j * e k * (g i j k i x - g i j i k x)) volume :=
    ((hi i j k i).sub (hi i j i k)).const_mul (e j * e k)
  refine ⟨by
    change Integrable (fun x => f x) volume
    simpa only [hf] using integrable_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ (fun k _ =>
        integrable_finsetSum Finset.univ (fun i _ => hit i j k))), ?_⟩
  have hsplit : (∫ x, f x) = ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
      e j * e k * ((∫ x, g i j k i x) - ∫ x, g i j i k x) := by
    simp_rw [hf]
    rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ =>
      integrable_finsetSum _ (fun i _ => hit i j k)))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun i _ => hit i j k))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ (fun i _ => hit i j k)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_sub (hi i j k i) (hi i j i k)]
  have heprod (j k : Fin 3) : |e j * e k| ≤ 1 := by
    rw [abs_mul]
    have hj : |e j| ≤ 1 := he ▸ abs_euclidean_coordinate_le_norm e j
    have hk : |e k| ≤ 1 := he ▸ abs_euclidean_coordinate_le_norm e k
    simpa only [one_mul] using mul_le_mul hj hk (abs_nonneg _) zero_le_one
  have hterm (i j k : Fin 3) :
      |e j * e k * ((∫ x, g i j k i x) - ∫ x, g i j i k x)| ≤
        (B i j k + B i j i) * Real.sqrt (∫ x : E₃, ‖u x‖ ^ 2) := by
    rw [abs_mul]
    calc
      _ ≤ 1 * (|∫ x, g i j k i x| + |∫ x, g i j i k x|) :=
        mul_le_mul (heprod j k) (abs_sub _ _) (abs_nonneg _) zero_le_one
      _ ≤ _ := by simpa only [one_mul, add_mul] using add_le_add (hb i j k i) (hb i j i k)
  rw [hsplit]
  simp only [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hterm i j k)

end ClockBarrier.Analysis
