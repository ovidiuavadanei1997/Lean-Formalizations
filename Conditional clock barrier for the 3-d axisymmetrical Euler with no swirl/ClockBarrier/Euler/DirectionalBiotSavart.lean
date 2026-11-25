/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.DirectionalBiotSavartTranslation
public import ClockBarrier.Euler.VorticityRegularity
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import ClockBarrier.Analysis.SingularValueEvolution
import ClockBarrier.Euler.AxisFlow

/-! # The signed directional strain representation for classical Euler

The interface supplies the actual derivative, global spatial Hölder
regularity, boundedness and finite energy. No flow or symmetry is assumed here.
-/

public section
namespace ClockBarrier.Euler
open Set Filter MeasureTheory Geometry
open scoped Topology ContDiff NNReal InnerProductSpace BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The actual symmetric velocity gradient has the signed near/far formula
at every center and unit direction, with both integrals absolutely convergent. -/
theorem classical_euler_on.strain_eq_smooth_near_add_far
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (t : ℝ) (ht : t ∈ Ico 0 T)
    {χ : E₃ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : χ =ᶠ[𝓝 (0 : E₃)] 0)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1)
    (hradial : ∀ x y, ‖x‖ = ‖y‖ → χ x = χ y) {L : ℝ} (hL : 0 < L)
    (a e : E₃) (he : ‖e‖ = 1) :
    let w := vorticity (u t) (h.cartesian_partials t ht)
    let N := fun (x v : E₃) => ⟪e, x⟫_ℝ *
      ⟪e, (!₂[x 1 * v 2 - x 2 * v 1, x 2 * v 0 - x 0 * v 2,
        x 0 * v 1 - x 1 * v 0] : E₃)⟫_ℝ
    let η := fun x => χ (L⁻¹ • (x - a))
    let D := fderiv ℝ (u t) a
    let S := (1 / 2 : ℝ) • (D + D.adjoint)
    Integrable (fun x => (1 - η x) * (N (x - a) (w x - w a) / ‖x - a‖ ^ 5)) volume ∧
    Integrable (fun x => η x * (N (x - a) (w x) / ‖x - a‖ ^ 5)) volume ∧
      ⟪e, S e⟫_ℝ = (3 / (4 * Real.pi)) *
        ((∫ x, (1 - η x) * (N (x - a) (w x - w a) / ‖x - a‖ ^ 5)) +
          ∫ x, η x * (N (x - a) (w x) / ‖x - a‖ ^ 5)) := by
  obtain ⟨D, _, hd, hHolder⟩ := h.2.2.2.2.1
  obtain ⟨H, hH⟩ := hHolder t ht
  have hD : HolderWith H α (fderiv ℝ (u t)) := by
    simpa only [show fderiv ℝ (u t) = D t from funext (fun x => (hd t ht x).fderiv)]
      using hH t ⟨ht.1, le_rfl⟩
  have hL2 := h.2.2.2.2.2.1 t ht
  have hdiv (x : E₃) : ∑ i : Fin 3,
      fderiv ℝ (u t) x (EuclideanSpace.single i 1) i = 0 := by
    have htr := h.velocity_regular.2.2.2.2 t ht x
    simpa [LinearMap.trace_eq_matrix_trace ℝ (PiLp.basisFun 2 ℝ (Fin 3)),
      Matrix.trace, LinearMap.toMatrix_apply] using htr
  simpa only [h.vorticity_eq_curlLinearMap t ht, Analysis.inner_symmetric_part] using
    Analysis.directional_strain_eq_smooth_near_add_far_sub
      (fun x => (hd t ht x).differentiableAt) h.2.1 hD
      ((memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).mp hL2)
      (fun x => (u t).norm_coe_le_norm x)
      (fun x => by rw [(hd t ht x).fderiv]; exact (D t).norm_coe_le_norm x)
      hdiv hχ hzero hχ₀ hχ₁ houter hradial hL a e he

end ClockBarrier.Euler
