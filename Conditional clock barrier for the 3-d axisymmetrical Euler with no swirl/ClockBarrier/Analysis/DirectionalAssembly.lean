/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.DirectionalSplit

/-! # Combining deformation and initial-vorticity budgets in the signed kernel -/

public section
namespace ClockBarrier.Analysis
open Set MeasureTheory
open scoped ENNReal InnerProductSpace
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Two finite inverse-cube budgets control the signed near kernel of their
transported sum, with genuine integrability. -/
theorem integrableOn_directional_sum_of_budgets
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {s : Set X}
    {d z v : X → E₃} (hd : Measurable d) (hz : Measurable z) (hv : Measurable v)
    {χ : X → ℝ} (hχ : Measurable χ) (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    {A : E₃ →L[ℝ] E₃} {C BD BI : ℝ} (hC : 0 ≤ C) (hA : ‖A‖ ≤ C)
    (hBD : 0 ≤ BD) (hBI : 0 ≤ BI) (e : E₃) (he : ‖e‖ = 1)
    (hD : (∫⁻ x in s, ENNReal.ofReal (‖z x‖ / ‖d x‖ ^ 3) ∂μ) ≤ ENNReal.ofReal BD)
    (hI : (∫⁻ x in s, ENNReal.ofReal (C * ‖v x‖ / ‖d x‖ ^ 3) ∂μ) ≤ ENNReal.ofReal BI) :
    let Δ := fun x => z x + A (v x)
    let f := fun x => χ x * (⟪e, d x⟫_ℝ *
      ⟪e, (!₂[(d x) 1 * (Δ x) 2 - (d x) 2 * (Δ x) 1,
        (d x) 2 * (Δ x) 0 - (d x) 0 * (Δ x) 2,
        (d x) 0 * (Δ x) 1 - (d x) 1 * (Δ x) 0] : E₃)⟫_ℝ / ‖d x‖ ^ 5)
    IntegrableOn f s μ ∧ (∫ x in s, |f x| ∂μ) ≤ BD + BI := by
  intro Δ f
  let ker := fun (x w : E₃) => ⟪e, x⟫_ℝ *
    ⟪e, (!₂[x 1 * w 2 - x 2 * w 1, x 2 * w 0 - x 0 * w 2,
      x 0 * w 1 - x 1 * w 0] : E₃)⟫_ℝ / ‖x‖ ^ 5
  let fII := fun x => χ x * ker (d x) (z x)
  let fI := fun x => χ x * ker (d x) (A (v x))
  have hII := integrableOn_directional_cutoff_apply_of_budget
    (A := ContinuousLinearMap.id ℝ E₃) hd hz hχ hχ₀ hχ₁
    (by norm_num : (0 : ℝ) ≤ 1) ContinuousLinearMap.norm_id_le hBD e he
    (by simpa only [one_mul] using hD)
  have hI := integrableOn_directional_cutoff_apply_of_budget
    hd hv hχ hχ₀ hχ₁ hC hA hBI e he hI
  have hsplit : f = fun x => fII x + fI x := by
    funext x
    exact (congrArg (χ x * ·) (directional_strain_kernel_add e (d x) (z x) (A (v x)))).trans
      (mul_add _ _ _)
  rw [hsplit]
  exact integral_abs_add_le_of_bounds hII.1 hI.1 hII.2 hI.2

end ClockBarrier.Analysis
