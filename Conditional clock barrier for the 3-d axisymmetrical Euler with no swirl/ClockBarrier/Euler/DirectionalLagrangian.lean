/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.DirectionalBiotSavart
public import ClockBarrier.Euler.DirectionalTransport
public import ClockBarrier.Euler.FlowChangeOfVariables

/-! # The general strain driver in Lagrangian variables

The complementary near cutoff is retained in the exact formula. The vorticity
increment is supplied by Cauchy transport, and the actual flow supplies the
global change of variables. The far integral remains the complete smooth term.
-/

public section
namespace ClockBarrier.Euler
open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal InnerProductSpace BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The signed strain representation pulled back to labels, with the exact
deformation/initial-vorticity increment and genuine near-field integrability. -/
theorem classical_euler_on.strain_eq_lagrangian_near_add_far
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x) (t : ℝ) (ht : t ∈ Ico 0 T)
    {χ : E₃ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hzero : χ =ᶠ[𝓝 (0 : E₃)] 0)
    (hχ₀ : ∀ x, 0 ≤ χ x) (hχ₁ : ∀ x, χ x ≤ 1)
    (houter : ∀ x, 1 ≤ ‖x‖ → χ x = 1)
    (hradial : ∀ x y, ‖x‖ = ‖y‖ → χ x = χ y) {L : ℝ} (hL : 0 < L)
    (aStar e : E₃) (he : ‖e‖ = 1) :
    let F := fderiv ℝ (Φ t)
    let w₀ := vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩)
    let w := vorticity (u t) (h.cartesian_partials t ht)
    let d := fun a => Φ t a - Φ t aStar
    let Δ := fun a => (F a - F aStar) (w₀ a) + F aStar (w₀ a - w₀ aStar)
    let K := fun (x v : E₃) => (⟪e, x⟫_ℝ *
      ⟪e, (!₂[x 1 * v 2 - x 2 * v 1, x 2 * v 0 - x 0 * v 2,
        x 0 * v 1 - x 1 * v 0] : E₃)⟫_ℝ / ‖x‖ ^ 5)
    let η := fun a => χ (L⁻¹ • d a)
    let D := fderiv ℝ (u t) (Φ t aStar)
    let S := (1 / 2 : ℝ) • (D + D.adjoint)
    IntegrableOn (fun a => (1 - η a) * K (d a) (Δ a)) {a | ‖d a‖ ≤ L} volume ∧
    Integrable (fun x => χ (L⁻¹ • (x - Φ t aStar)) * K (x - Φ t aStar) (w x)) volume ∧
      ⟪e, S e⟫_ℝ = (3 / (4 * Real.pi)) *
        ((∫ a in {a | ‖d a‖ ≤ L}, (1 - η a) * K (d a) (Δ a)) +
          ∫ x, χ (L⁻¹ • (x - Φ t aStar)) * K (x - Φ t aStar) (w x)) := by
  intro F w₀ w d Δ K η D S
  have htransport (a : E₃) : w (Φ t a) - w (Φ t aStar) = Δ a :=
    h.vorticity_flow_sub_eq_deformation_add hcont hode hinit t ht aStar a
  obtain ⟨hn, hf, hrep⟩ := h.strain_eq_smooth_near_add_far t ht
    hχ hzero hχ₀ hχ₁ houter hradial hL (Φ t aStar) e he
  let g (x : E₃) := (1 - χ (L⁻¹ • (x - Φ t aStar))) *
    K (x - Φ t aStar) (w x - w (Φ t aStar))
  have hng : Integrable g volume := hn
  have hcomp (a : E₃) : g (Φ t a) = (1 - η a) * K (d a) (Δ a) :=
    congrArg (fun v => (1 - η a) * K (d a) v) (htransport a)
  have hnearlabel : Integrable (fun a => (1 - η a) * K (d a) (Δ a)) volume :=
    ((h.integrable_comp_flow_iff hcont hode hinit ht).mpr hng).congr
      (ae_of_all _ hcomp)
  have hchange : (∫ a, (1 - η a) * K (d a) (Δ a)) = ∫ x, g x :=
    (integral_congr_ae (ae_of_all _ fun a => (hcomp a).symm)).trans
      (h.integral_comp_flow hcont hode hinit ht g)
  have hlocal : (∫ a in {a | ‖d a‖ ≤ L}, (1 - η a) * K (d a) (Δ a)) =
      ∫ a, (1 - η a) * K (d a) (Δ a) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro a ha
    have hout : η a = 1 := houter _ (by
      simpa only [norm_smul, norm_inv, Real.norm_of_nonneg hL.le, div_eq_mul_inv, mul_comm]
        using (one_le_div hL).mpr (le_of_lt (lt_of_not_ge ha)))
    simp only [hout, sub_self, zero_mul]
  refine ⟨hnearlabel.integrableOn, hf, ?_⟩
  exact hrep.trans (congrArg (fun z => (3 / (4 * Real.pi)) *
    (z + ∫ x, χ (L⁻¹ • (x - Φ t aStar)) * K (x - Φ t aStar) (w x)))
      (hchange.symm.trans hlocal.symm))

end ClockBarrier.Euler
