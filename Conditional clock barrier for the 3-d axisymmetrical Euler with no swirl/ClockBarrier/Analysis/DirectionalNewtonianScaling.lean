/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.NewtonianScaling
public import ClockBarrier.Analysis.StrainComponents
public import ClockBarrier.Analysis.VelocityScaling
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Scaling and normalization of the directional regularized identity -/

public section
namespace ClockBarrier.Analysis
open Set Filter MeasureTheory Geometry
open scoped Topology NNReal InnerProductSpace
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Spatial dilation converts the unit regularization to any positive length. -/
theorem integral_regularized_directional_kernel_scaling (ω : E₃ → E₃) (e : E₃)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ x : E₃, 3 * ⟪e, x⟫_ℝ *
      ⟪e, (!₂[x 1 * ω (ε • x) 2 - x 2 * ω (ε • x) 1,
        x 2 * ω (ε • x) 0 - x 0 * ω (ε • x) 2,
        x 0 * ω (ε • x) 1 - x 1 * ω (ε • x) 0] : E₃)⟫_ℝ *
        (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)) =
      ∫ x : E₃, 3 * ⟪e, x⟫_ℝ *
        ⟪e, (!₂[x 1 * ω x 2 - x 2 * ω x 1, x 2 * ω x 0 - x 0 * ω x 2,
          x 0 * ω x 1 - x 1 * ω x 0] : E₃)⟫_ℝ *
          (ε ^ 2 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) := by
  let f (x : E₃) : ℝ := 3 * ⟪e, x⟫_ℝ *
    ⟪e, (!₂[x 1 * ω x 2 - x 2 * ω x 1, x 2 * ω x 0 - x 0 * ω x 2,
      x 0 * ω x 1 - x 1 * ω x 0] : E₃)⟫_ℝ *
      (ε ^ 2 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)
  have hscale (x : E₃) : f (ε • x) = (ε ^ 3)⁻¹ *
      (3 * ⟪e, x⟫_ℝ *
        ⟪e, (!₂[x 1 * ω (ε • x) 2 - x 2 * ω (ε • x) 1,
          x 2 * ω (ε • x) 0 - x 0 * ω (ε • x) 2,
          x 0 * ω (ε • x) 1 - x 1 * ω (ε • x) 0] : E₃)⟫_ℝ *
          (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)) := by
    simp only [f, newtonian_power_smul hε, PiLp.smul_apply, smul_eq_mul]
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
    field_simp
  apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 hε.ne'))
  calc
    _ = ∫ x : E₃, f (ε • x) := by simp_rw [hscale]; rw [integral_const_mul]
    _ = _ := by
      simpa only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] using
        Measure.integral_comp_smul_of_nonneg (volume : Measure E₃) f ε (hR := hε.le)

/-- The normalized regularized directional curl integral converges to the
actual directional derivative. No value of the vorticity is prescribed at zero. -/
theorem tendsto_integral_regularized_directional_strain
    {u : E₃ → E₃} {H α : ℝ≥0} (hu : Differentiable ℝ u)
    (hα : 0 < α) (hD : HolderWith H α (fderiv ℝ u))
    (henergy : Integrable (fun x => ‖u x‖ ^ 2) volume)
    {B C : ℝ} (hbound : ∀ x, ‖u x‖ ≤ B) (hDbound : ∀ x, ‖fderiv ℝ u x‖ ≤ C)
    (hdiv : ∀ x, ∑ i : Fin 3, fderiv ℝ u x (EuclideanSpace.single i 1) i = 0)
    (e : E₃) (he : ‖e‖ = 1) :
    Tendsto (fun ε : ℝ => (1 / (4 * Real.pi)) * (∫ x : E₃, 3 * ⟪e, x⟫_ℝ *
      ⟪e, (!₂[x 1 * curlLinearMap (fderiv ℝ u x) 2 -
          x 2 * curlLinearMap (fderiv ℝ u x) 1,
        x 2 * curlLinearMap (fderiv ℝ u x) 0 -
          x 0 * curlLinearMap (fderiv ℝ u x) 2,
        x 0 * curlLinearMap (fderiv ℝ u x) 1 -
          x 1 * curlLinearMap (fderiv ℝ u x) 0] : E₃)⟫_ℝ *
        (ε ^ 2 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2))) (𝓝[>] 0)
      (𝓝 ⟪e, fderiv ℝ u 0 e⟫_ℝ) := by
  have hid (ε : ℝ) (hε : 0 < ε) :
      (1 / (4 * Real.pi)) * (∫ x : E₃, 3 * ⟪e, x⟫_ℝ *
        ⟪e, (!₂[x 1 * curlLinearMap (fderiv ℝ u x) 2 -
            x 2 * curlLinearMap (fderiv ℝ u x) 1,
          x 2 * curlLinearMap (fderiv ℝ u x) 0 -
            x 0 * curlLinearMap (fderiv ℝ u x) 2,
          x 0 * curlLinearMap (fderiv ℝ u x) 1 -
            x 1 * curlLinearMap (fderiv ℝ u x) 0] : E₃)⟫_ℝ *
          (ε ^ 2 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2)) =
        ∫ x : E₃, (3 / (4 * Real.pi)) * (1 + ‖x‖ ^ 2) ^ (-(5 : ℝ) / 2) *
          ⟪e, fderiv ℝ u (ε • x) e⟫_ℝ := by
    have hv : Differentiable ℝ (fun x => ε⁻¹ • u (ε • x)) :=
      (hu.comp (differentiable_id.const_smul ε)).const_smul ε⁻¹
    obtain ⟨Hε, hHε⟩ := exists_holderWith_fderiv_rescaled_velocity hu hD hε.ne'
    have hvb (x : E₃) : ‖ε⁻¹ • u (ε • x)‖ ≤ ‖ε⁻¹‖ * B := by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)
    have hvdiv (x : E₃) : ∑ i : Fin 3,
        fderiv ℝ (fun y => ε⁻¹ • u (ε • y)) x (EuclideanSpace.single i 1) i = 0 := by
      rw [fderiv_rescaled_velocity hu hε.ne']
      exact hdiv _
    have heq := integral_regularized_directional_strain hv hα hHε
      (integrable_sq_norm_rescaled_velocity henergy hε.ne') hvb hvdiv e
    simp only [fderiv_rescaled_velocity hu hε.ne'] at heq
    rw [integral_regularized_directional_kernel_scaling
      (fun x => curlLinearMap (fderiv ℝ u x)) e hε] at heq
    rw [heq, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  have hc := hD.continuous hα
  have hg : Continuous (fun x => ⟪e, fderiv ℝ u x e⟫_ℝ) := by fun_prop
  have hgb (x : E₃) : |⟪e, fderiv ℝ u x e⟫_ℝ| ≤ C := by
    have hi := abs_real_inner_le_norm e (fderiv ℝ u x e)
    simp only [he, one_mul] at hi
    have hnorm := (fderiv ℝ u x).le_opNorm e
    simp only [he, mul_one] at hnorm
    exact hi.trans (hnorm.trans (hDbound x))
  have ht := (tendsto_integral_newtonian_density_smul hg hgb).mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  exact ht.congr' (Eventually.mono
    (self_mem_nhdsWithin : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioi 0)
    (fun ε hε => (hid ε hε).symm))

end ClockBarrier.Analysis
