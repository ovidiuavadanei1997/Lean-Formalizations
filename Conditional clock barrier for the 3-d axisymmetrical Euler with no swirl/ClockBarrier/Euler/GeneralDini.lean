/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.GeneralBlockMeasure
public import ClockBarrier.Euler.GeneralCoherenceWellDefined
public import ClockBarrier.Analysis.CoherenceIntegral

/-! # The deformation contribution controlled by the summed Dini budget -/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The literal summed Dini condition controls the entire physical near region.
Spatial regularity and singular-value positivity are supplied by the actual Euler flow. -/
theorem classical_euler_on.integrableOn_deformation_of_dini
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x) {t : ℝ} (ht : t ∈ Ico 0 T)
    (aStar : E₃) (V : E₃ ≃ₗᵢ[ℝ] E₃) (L : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    let F := fderiv ℝ (Φ t)
    let σ := fun i : Fin 3 => (F aStar).toLinearMap.singularValues i
    let w₀ := vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩)
    let E := fun k : Fin 3 → ℤ => {a : E₃ | let η := V.symm (a - aStar)
      (2 : ℝ) ^ (k 2) ≤ |η 2| ∧ |η 2| < 2 * (2 : ℝ) ^ (k 2) ∧
      (2 : ℝ) ^ (k 0) * σ 2 * (2 : ℝ) ^ (k 2) / σ 0 ≤ |η 0| ∧
      |η 0| < 2 * ((2 : ℝ) ^ (k 0) * σ 2 * (2 : ℝ) ^ (k 2) / σ 0) ∧
      (2 : ℝ) ^ (k 1) * σ 2 * (2 : ℝ) ^ (k 2) / σ 1 ≤ |η 1| ∧
      |η 1| < 2 * ((2 : ℝ) ^ (k 1) * σ 2 * (2 : ℝ) ^ (k 2) / σ 1)}
    let s := {a : E₃ | ‖Φ t a - Φ t aStar‖ ≤ L}
    let f := fun a => ‖(F a - F aStar) (w₀ a)‖ / ‖Φ t a - Φ t aStar‖ ^ 3
    (∑' k, ∫⁻ a in E k ∩ s, ENNReal.ofReal (f a)) ≤ ENNReal.ofReal B →
      IntegrableOn f s volume ∧ (∫ a in s, f a) ≤ B := by
  intro F σ w₀ E s f hbudget
  have hreg := (h.contDiff_bijective_measurePreserving_flow hcont hode hinit ht).1
  have hF : Continuous F := hreg.continuous_fderiv (by decide)
  have hw : Continuous w₀ := h.continuous_vorticity 0 ⟨le_rfl, h.1⟩
  have hf : Measurable f := ((hF.sub continuous_const).clm_apply hw).norm.measurable.div
    ((hreg.continuous.sub continuous_const).norm.pow 3).measurable
  exact Analysis.integrableOn_and_integral_le_of_cover_budget
    (iUnion_singular_shell_inter_ae_eq aStar V
      (fun i => h.singularValues_fderiv_flow_pos hcont hode hinit ht aStar i) s)
    hf.aestronglyMeasurable (Filter.Eventually.of_forall (fun a =>
      div_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) 3))) hB hbudget

end ClockBarrier.Euler
