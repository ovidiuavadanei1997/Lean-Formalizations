/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.DirectionalRegularizedSplit
public import ClockBarrier.Analysis.DirectionalNewtonianScaling
public import ClockBarrier.Analysis.DirectionalFarScaling
import Mathlib.Tactic.Ring

/-! # The signed subtracted directional Biot–Savart representation

Both terms are absolutely integrable. The near term keeps its complementary
smooth cutoff and the far term is integrated over the whole space.
-/

public section
namespace ClockBarrier.Analysis
open Set Filter MeasureTheory Geometry
open scoped Topology ContDiff NNReal InnerProductSpace
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The normalized signed near/far representation at an arbitrary vorticity
value. Integrability is derived from first-derivative Hölder regularity and
finite energy, and the whole transition annulus is retained. -/
theorem directional_strain_eq_smooth_near_add_far
    {u : E₃ → E₃} {H α : ℝ≥0} (hu : Differentiable ℝ u)
    (hα : 0 < α) (hD : HolderWith H α (fderiv ℝ u))
    (henergy : Integrable (fun x => ‖u x‖ ^ 2) volume)
    {B C : ℝ} (hbound : ∀ x, ‖u x‖ ≤ B) (hDbound : ∀ x, ‖fderiv ℝ u x‖ ≤ C)
    (hdiv : ∀ x, ∑ i : Fin 3, fderiv ℝ u x (EuclideanSpace.single i 1) i = 0)
    {χ : E₃ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : χ =ᶠ[𝓝 (0 : E₃)] 0)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1)
    (hradial : ∀ x y, ‖x‖ = ‖y‖ → χ x = χ y) {L : ℝ} (hL : 0 < L)
    (e : E₃) (he : ‖e‖ = 1) :
    let w := fun x => curlLinearMap (fderiv ℝ u x)
    let N := fun (x w : E₃) => ⟪e, x⟫_ℝ *
      ⟪e, (!₂[x 1 * w 2 - x 2 * w 1, x 2 * w 0 - x 0 * w 2,
        x 0 * w 1 - x 1 * w 0] : E₃)⟫_ℝ
    let η := fun x => χ (L⁻¹ • x)
    Integrable (fun x => (1 - η x) * (N x (w x - w 0) / ‖x‖ ^ 5)) volume ∧
    Integrable (fun x => η x * (N x (w x) / ‖x‖ ^ 5)) volume ∧
      ⟪e, fderiv ℝ u 0 e⟫_ℝ = (3 / (4 * Real.pi)) *
        ((∫ x, (1 - η x) * (N x (w x - w 0) / ‖x‖ ^ 5)) +
          ∫ x, η x * (N x (w x) / ‖x‖ ^ 5)) := by
  intro w N η
  have hw := holderWith_curlLinearMap hD
  have hη : Continuous η := hχ.continuous.comp (by fun_prop)
  have hout : ∀ x, L ≤ ‖x‖ → η x = 1 := fun x hx => houter _ (by
    simpa only [norm_smul, norm_inv, Real.norm_of_nonneg hL.le, div_eq_mul_inv, mul_comm]
      using (one_le_div hL).mpr hx)
  have hrad : ∀ x y, ‖x‖ = ‖y‖ → η x = η y := fun x y hxy =>
    hradial _ _ (by simp only [norm_smul, hxy])
  have hn : Integrable (fun x => (1 - η x) * (N x (w x - w 0) / ‖x‖ ^ 5)) volume :=
    integrable_directional_near_increment hα hw hη (fun x => hχ₀ _) (fun x => hχ₁ _) hout e he
  obtain ⟨_, _, hfar⟩ := exists_scaled_directional_far_energy_constant hχ hzero hχ₀ hχ₁ houter
  have hf : Integrable (fun x => η x * (N x (w x) / ‖x‖ ^ 5)) volume :=
    (hfar hu hα hD henergy hL e he).1
  refine ⟨hn, hf, ?_⟩
  have hcw : Continuous w := hw.continuous hα
  have htn := tendsto_integral_regularized_radial_numerator
    (f := fun x => (1 - η x) * N x (w x - w 0))
    (by dsimp [N]; fun_prop) (by simp [N])
    (by simpa only [mul_div_assoc] using hn)
  have htf := tendsto_integral_regularized_radial_numerator
    (f := fun x => η x * N x (w x))
    (by dsimp [N]; fun_prop) (by simp [N])
    (by simpa only [mul_div_assoc] using hf)
  have hlim : Tendsto (fun ε : ℝ => ∫ x,
      N x (w x) * (ε ^ 2 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)) (𝓝[>] 0)
      (𝓝 ((∫ x, (1 - η x) * (N x (w x - w 0) / ‖x‖ ^ 5)) +
        ∫ x, η x * (N x (w x) / ‖x‖ ^ 5))) := by
    have ht := (htn.add htf).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simp only [mul_div_assoc] at ht
    exact ht.congr' (Eventually.mono
      (self_mem_nhdsWithin : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioi 0)
      (fun ε hε => (integral_regularized_directional_eq_near_add_far hcw hη
        (fun x => hχ₀ _) (fun x => hχ₁ _) hrad hout e he hn hf hε).symm))
  have hstrain : Tendsto (fun ε : ℝ => (3 / (4 * Real.pi)) *
      (∫ x, N x (w x) * (ε ^ 2 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)))
      (𝓝[>] 0) (𝓝 ⟪e, fderiv ℝ u 0 e⟫_ℝ) := by
    apply (tendsto_integral_regularized_directional_strain
      hu hα hD henergy hbound hDbound hdiv e he).congr'
    refine Eventually.of_forall fun ε => ?_
    dsimp only
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only [N, w]
    ring
  exact tendsto_nhds_unique hstrain (hlim.const_mul (3 / (4 * Real.pi)))

end ClockBarrier.Analysis
