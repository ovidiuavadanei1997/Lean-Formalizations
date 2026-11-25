/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.DirectionalTransport
public import ClockBarrier.Analysis.DirectionalStrainKernel

/-! # The three-term pointwise majorant for the directional near integrand -/

public section
namespace ClockBarrier.Euler
open Set
open scoped Topology NNReal InnerProductSpace BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The kernel bound and Cauchy transport produce the deformation, transverse
and longitudinal majorants. A slice average may be used for `m`; no regularity
or integrability of a family of such averages is silently assumed here. -/
theorem classical_euler_on.abs_directional_near_integrand_le
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x) (t : ℝ) (ht : t ∈ Ico 0 T)
    {χ : E₃ → ℝ} (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (L : ℝ) (aStar a m e : E₃) (he : ‖e‖ = 1) :
    let F := fderiv ℝ (Φ t)
    let w₀ := vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩)
    let w := vorticity (u t) (h.cartesian_partials t ht)
    let d := Φ t a - Φ t aStar
    let v := w (Φ t a) - w (Φ t aStar)
    |(1 - χ (L⁻¹ • d)) * (⟪e, d⟫_ℝ *
      ⟪e, (!₂[d 1 * v 2 - d 2 * v 1, d 2 * v 0 - d 0 * v 2,
        d 0 * v 1 - d 1 * v 0] : E₃)⟫_ℝ / ‖d‖ ^ 5)| ≤
      (‖(F a - F aStar) (w₀ a)‖ + ‖F aStar‖ * (‖w₀ a - m‖ + ‖m - w₀ aStar‖)) /
        ‖d‖ ^ 3 := by
  intro F w₀ w d v
  have hc₀ : 0 ≤ 1 - χ (L⁻¹ • d) := sub_nonneg.mpr (hχ₁ _)
  have hc₁ : 1 - χ (L⁻¹ • d) ≤ 1 := sub_le_self _ (hχ₀ _)
  rw [abs_mul, abs_of_nonneg hc₀]
  have hv : ‖v‖ ≤ ‖(F a - F aStar) (w₀ a)‖ +
      ‖F aStar‖ * (‖w₀ a - m‖ + ‖m - w₀ aStar‖) :=
    h.norm_vorticity_flow_sub_le_deformation_add_slice hcont hode hinit t ht aStar a m
  refine (mul_le_mul_of_nonneg_right hc₁ (abs_nonneg _)).trans ?_
  simp only [one_mul]
  exact (Analysis.abs_directional_strain_kernel_le d v e he).trans
    (div_le_div_of_nonneg_right hv (pow_nonneg (norm_nonneg d) 3))

end ClockBarrier.Euler
