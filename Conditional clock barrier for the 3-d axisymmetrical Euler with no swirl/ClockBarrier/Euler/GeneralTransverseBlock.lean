/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.SingularGeometry
public import ClockBarrier.Analysis.GeneralCuspBlock
public import ClockBarrier.Analysis.DirectionalStrainKernel

/-! # The actual transverse contribution on a general clock block -/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped Topology NNReal ENNReal InnerProductSpace BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

/-- The actual flow geometry and slice-average cusp condition supply the transverse
block estimate. Determinant, positivity, measurability and integrability are derived. -/
theorem classical_euler_on.directional_transverse_block_bound
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x) {t : ℝ} (ht : t ∈ Ico 0 T)
    (aStar : E₃) (U V : E₃ ≃ₗᵢ[ℝ] E₃) (k : Fin 3 → ℤ) (L ℓ : ℝ)
    {c M b : ℝ} (hc : 0 < c) (hM : 0 ≤ M) (hb : 0 ≤ b)
    {χ : E₃ → ℝ} (hχ : Continuous χ) (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (e : E₃) (he : ‖e‖ = 1) :
    let F := fderiv ℝ (Φ t) aStar
    let σ := fun i : Fin 3 => F.toLinearMap.singularValues i
    let w₀ := vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩)
    let Λ := (2 : ℝ) ^ (k 2)
    let l₁ := (2 : ℝ) ^ (k 0)
    let l₂ := (2 : ℝ) ^ (k 1)
    let d := fun a => Φ t a - Φ t aStar
    let E := {a : E₃ | let η := V.symm (a - aStar)
      Λ ≤ |η 2| ∧ |η 2| < 2 * Λ ∧
      l₁ * σ 2 * Λ / σ 0 ≤ |η 0| ∧ |η 0| < 2 * (l₁ * σ 2 * Λ / σ 0) ∧
      l₂ * σ 2 * Λ / σ 1 ≤ |η 1| ∧ |η 1| < 2 * (l₂ * σ 2 * Λ / σ 1)} ∩
      {a | ‖a - aStar‖ < ℓ} ∩ {a | ‖d a‖ ≤ L}
    let A := fun z : ℝ => {q : E₂ | aStar + V !₂[q 0, q 1, z] ∈ E}
    let avg := fun z : ℝ => if volume (A z) = 0 then (0 : E₃) else
      (volume (A z)).toReal⁻¹ • ∫ q in A z, w₀ (aStar + V !₂[q 0, q 1, z])
    let v := fun a => w₀ a - avg (V.symm (a - aStar) 2)
    (∀ η : E₃, F (V η) = U !₂[σ 0 * η 0, σ 1 * η 1, σ 2 * η 2]) →
    (∀ a, ‖d a‖ ≤ L → c * ‖F (a - aStar)‖ ≤ ‖d a‖) →
    (∫⁻ a in E, ENNReal.ofReal (‖v a‖)) ≤ ENNReal.ofReal
      ((M * b) * (Real.sqrt (l₁ ^ 2 + l₂ ^ 2) * σ 2 * Λ / σ 1) ^ (α : ℝ) *
        (l₁ * l₂ * (σ 2) ^ 2 * Λ ^ 3 / (σ 0 * σ 1))) →
    let f := fun a => (1 - χ (L⁻¹ • d a)) * (⟪e, d a⟫_ℝ *
      ⟪e, (!₂[(d a) 1 * (F (v a)) 2 - (d a) 2 * (F (v a)) 1,
        (d a) 2 * (F (v a)) 0 - (d a) 0 * (F (v a)) 2,
        (d a) 0 * (F (v a)) 1 - (d a) 1 * (F (v a)) 0] : E₃)⟫_ℝ / ‖d a‖ ^ 5)
    IntegrableOn f E volume ∧ (∫ a in E, |f a|) ≤
      (M * b / c ^ 3) * Λ ^ (α : ℝ) * (σ 2) ^ ((3 * (α : ℝ) - 1) / 2) *
        (σ 0 / σ 1) ^ (((α : ℝ) + 1) / 2) *
        ((Real.sqrt (l₁ ^ 2 + l₂ ^ 2)) ^ (α : ℝ) * l₁ * l₂ /
          (Real.sqrt (1 + l₁ ^ 2 + l₂ ^ 2)) ^ 3) := by
  intro F σ w₀ Λ l₁ l₂ d E A avg v hframe hnear hmass f
  have hreg := (h.contDiff_bijective_measurePreserving_flow hcont hode hinit ht).1
  have hd : Continuous d := hreg.continuous.sub continuous_const
  have hE : MeasurableSet E := measurableSet_singular_clock_block hreg.continuous aStar V σ k ℓ L
  have hm : StronglyMeasurable avg :=
    (h.initial_vorticity_clock_slices aStar V hE (fun a ha => ha.1.2)).2
  have hz : Continuous (fun a : E₃ => V.symm (a - aStar) 2) := by fun_prop
  have hv : Measurable v := (h.continuous_vorticity 0 ⟨le_rfl, h.1⟩).measurable.sub
    (hm.measurable.comp hz.measurable)
  have hσ (i : Fin 3) : 0 < σ i :=
    h.singularValues_fderiv_flow_pos hcont hode hinit ht aStar i
  have hΛ : 0 < Λ := zpow_pos (by norm_num) _
  have hl₁ : 0 < l₁ := zpow_pos (by norm_num) _
  have hl₂ : 0 < l₂ := zpow_pos (by norm_num) _
  have hnorm : ‖F‖ ≤ σ 0 := Geometry.norm_le_largest_singularValue_of_frame hframe
  have hf : Measurable f := by dsimp only [f]; fun_prop
  refine Analysis.integrableOn_general_cusp_block (d := fun a => ‖d a‖)
    (hσ 0) (hσ 1) (hσ 2) hΛ hc (by positivity) (Real.sqrt_nonneg _)
    hl₁.le hl₂.le hM hb (h.prod_singularValues_fderiv_flow hcont hode hinit ht aStar)
    hE hf.aestronglyMeasurable hv.norm.aestronglyMeasurable (fun a => norm_nonneg (v a))
    ?_ ?_ hmass
  · intro a _
    dsimp only [f]
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hχ₁ _))]
    refine (mul_le_mul_of_nonneg_right (sub_le_self _ (hχ₀ _)) (abs_nonneg _)).trans ?_
    simp only [one_mul]
    exact (Analysis.abs_directional_strain_kernel_le (d a) (F (v a)) e he).trans
      (div_le_div_of_nonneg_right ((F.le_opNorm (v a)).trans
        (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))) (pow_nonneg (norm_nonneg _) 3))
  · intro a ha
    have hshell := ha.1.1
    have hscale := (Geometry.norm_bounds_of_singular_shell hframe hσ hl₁.le hl₂.le hΛ.le
      ⟨hshell.2.2.1, hshell.2.2.2.1⟩ hshell.2.2.2.2 ⟨hshell.1, hshell.2.1⟩).1
    calc
      c * σ 2 * Λ * Real.sqrt (1 + l₁ ^ 2 + l₂ ^ 2) =
          c * (σ 2 * Λ * Real.sqrt (1 + l₁ ^ 2 + l₂ ^ 2)) := by ring
      _ ≤ c * ‖F (a - aStar)‖ := mul_le_mul_of_nonneg_left hscale hc.le
      _ ≤ ‖d a‖ := hnear a ha.2


end ClockBarrier.Euler
