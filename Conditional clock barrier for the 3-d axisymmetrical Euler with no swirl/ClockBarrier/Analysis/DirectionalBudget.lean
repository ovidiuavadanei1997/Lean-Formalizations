/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.CoherenceIntegral
public import ClockBarrier.Analysis.DirectionalStrainKernel

/-! # Directional contributions dominated by a literal coherence budget -/

public section
namespace ClockBarrier.Analysis
open Set MeasureTheory
open scoped ENNReal InnerProductSpace
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- A pointwise inverse-cube majorant and a finite coherence budget control the
absolute cutoff integral. Integrability is a conclusion, not an assumption. -/
theorem integrableOn_directional_cutoff_apply_of_budget
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {s : Set X}
    {d v : X → E₃} (hd : Measurable d) (hv : Measurable v)
    {χ : X → ℝ} (hχ : Measurable χ) (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    {A : E₃ →L[ℝ] E₃} {C B : ℝ} (hC : 0 ≤ C) (hA : ‖A‖ ≤ C) (hB : 0 ≤ B)
    (e : E₃) (he : ‖e‖ = 1)
    (hbudget : (∫⁻ x in s, ENNReal.ofReal (C * ‖v x‖ / ‖d x‖ ^ 3) ∂μ) ≤ ENNReal.ofReal B) :
    let f := fun x => χ x * (⟪e, d x⟫_ℝ *
      ⟪e, (!₂[(d x) 1 * (A (v x)) 2 - (d x) 2 * (A (v x)) 1,
        (d x) 2 * (A (v x)) 0 - (d x) 0 * (A (v x)) 2,
        (d x) 0 * (A (v x)) 1 - (d x) 1 * (A (v x)) 0] : E₃)⟫_ℝ / ‖d x‖ ^ 5)
    IntegrableOn f s μ ∧ (∫ x in s, |f x| ∂μ) ≤ B := by
  intro f
  have hg : Measurable (fun x => C * ‖v x‖ / ‖d x‖ ^ 3) :=
    (measurable_const.mul hv.norm).div (hd.norm.pow_const 3)
  obtain ⟨hgi, hgb⟩ := integrable_and_integral_le_of_lintegral_bound hg.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => div_nonneg (mul_nonneg hC (norm_nonneg _))
      (pow_nonneg (norm_nonneg _) 3))) hB hbudget
  have hf : Measurable f := by dsimp only [f]; fun_prop
  have hp (x : X) : |f x| ≤ C * ‖v x‖ / ‖d x‖ ^ 3 := by
    dsimp only [f]
    rw [abs_mul, abs_of_nonneg (hχ₀ x)]
    refine (mul_le_mul_of_nonneg_right (hχ₁ x) (abs_nonneg _)).trans ?_
    simp only [one_mul]
    exact (abs_directional_strain_kernel_le (d x) (A (v x)) e he).trans
      (div_le_div_of_nonneg_right ((A.le_opNorm (v x)).trans
        (mul_le_mul_of_nonneg_right hA (norm_nonneg _))) (pow_nonneg (norm_nonneg _) 3))
  have hfi : IntegrableOn f s μ := hgi.mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hp x))
  exact ⟨hfi, (integral_mono hfi.abs hgi hp).trans hgb⟩

end ClockBarrier.Analysis
