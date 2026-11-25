/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.SingularGeometry
public import ClockBarrier.Analysis.DirectionalBudget

/-! # The general off-clock directional contribution -/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped Topology NNReal ENNReal InnerProductSpace BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The literal off-clock budget controls the actual transported initial-vorticity
increment, retaining the complementary smooth cutoff in its integral. -/
theorem classical_euler_on.directional_offclock_bound
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x) {t : ℝ} (ht : t ∈ Ico 0 T)
    (aStar : E₃) (U V : E₃ ≃ₗᵢ[ℝ] E₃) (L ℓ : ℝ) {B : ℝ} (hB : 0 ≤ B)
    {χ : E₃ → ℝ} (hχ : Continuous χ) (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (e : E₃) (he : ‖e‖ = 1) :
    let F := fderiv ℝ (Φ t) aStar
    let σ := F.toLinearMap.singularValues
    let w₀ := vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩)
    let d := fun a => Φ t a - Φ t aStar
    let v := fun a => w₀ a - w₀ aStar
    let s := {a : E₃ | ℓ ≤ ‖a - aStar‖ ∧ ‖d a‖ ≤ L}
    (∀ η : E₃, F (V η) = U !₂[σ 0 * η 0, σ 1 * η 1, σ 2 * η 2]) →
    (∫⁻ a in s, ENNReal.ofReal (σ 0 * ‖v a‖ / ‖d a‖ ^ 3)) ≤ ENNReal.ofReal B →
    let f := fun a => (1 - χ (L⁻¹ • d a)) * (⟪e, d a⟫_ℝ *
      ⟪e, (!₂[(d a) 1 * (F (v a)) 2 - (d a) 2 * (F (v a)) 1,
        (d a) 2 * (F (v a)) 0 - (d a) 0 * (F (v a)) 2,
        (d a) 0 * (F (v a)) 1 - (d a) 1 * (F (v a)) 0] : E₃)⟫_ℝ / ‖d a‖ ^ 5)
    IntegrableOn f s volume ∧ (∫ a in s, |f a|) ≤ B := by
  intro F σ w₀ d v s hframe hbudget f
  have hd : Continuous d :=
    (h.contDiff_bijective_measurePreserving_flow hcont hode hinit ht).1.continuous.sub continuous_const
  have hv : Continuous v := (h.continuous_vorticity 0 ⟨le_rfl, h.1⟩).sub continuous_const
  exact Analysis.integrableOn_directional_cutoff_apply_of_budget hd.measurable hv.measurable
    ((continuous_const.sub (hχ.comp (hd.const_smul (L⁻¹)))).measurable)
    (fun a => sub_nonneg.mpr (hχ₁ _)) (fun a => sub_le_self _ (hχ₀ _))
    (F.toLinearMap.singularValues_nonneg 0) (Geometry.norm_le_largest_singularValue_of_frame hframe)
    hB e he hbudget

end ClockBarrier.Euler
