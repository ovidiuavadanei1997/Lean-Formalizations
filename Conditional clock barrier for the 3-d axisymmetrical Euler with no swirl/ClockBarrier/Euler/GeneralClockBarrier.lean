/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Frozen.GeneralDriver
public import ClockBarrier.Frozen.SingularValueEvolution
import ClockBarrier.Analysis.Scalar
import ClockBarrier.Analysis.SingularValueContinuity
import ClockBarrier.Dynamics.FlowDerivativeWithin

/-! # The uniform general-label clock barrier

Section 4 of arXiv:2605.31587v3: the driver estimate and evolution
formula supply the already proved scalar barrier. All flow regularity inputs
are derived from the classical Euler interface.
-/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped Topology NNReal InnerProductSpace BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Uniform general coherence prevents collapse of the smallest singular value.
One positive constant works for every initialized flow, label and lifespan time. -/
theorem general_coherent_on.exists_uniform_smallest_singularValue_lower_bound
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃}
    (hα : (1 / 3 : ℝ) ≤ (α : ℝ)) (hcoh : general_coherent_on α T u) :
    ∃ c : ℝ, 0 < c ∧ ∀ Φ : ℝ → E₃ → E₃,
      (∀ x, Φ 0 x = x) →
      (∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T)) →
      (∀ x, ∀ t ∈ Ico 0 T,
        HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t) →
      ∀ a : E₃, ∀ t ∈ Ico 0 T,
        c ≤ (fderiv ℝ (Φ t) a).toLinearMap.singularValues 2 := by
  obtain ⟨B, C, hB, hBpos, hC, hdriver⟩ := general_driver_bound hα hcoh
  obtain ⟨p, h, _⟩ := hcoh
  have hp : 1 ≤ (3 * (α : ℝ) + 1) / 2 := by linarith only [hα]
  obtain ⟨c, hc, hlower⟩ := Analysis.exists_pos_lower_bound_of_power_deriv_ge hC.le hp hB
    (fun t ht => (hBpos t ht).le)
  refine ⟨c, hc, ?_⟩
  intro Φ hinit hcont hode a
  let F := fun t => fderiv ℝ (Φ t) a
  let ν := fun t => (F t).toLinearMap.singularValues 2
  let S := fun t => (1 / 2 : ℝ) •
    (fderiv ℝ (u t) (Φ t a) + (fderiv ℝ (u t) (Φ t a)).adjoint)
  let G := fun t => {r : ℝ | ∃ e : E₃, ‖e‖ = 1 ∧
    F t ((F t).adjoint e) = ν t ^ 2 • e ∧ r = ⟪e, S t e⟫_ℝ}
  let ν' := fun t => ν t * sInf (G t)
  obtain ⟨hu, hdiff, hD, hbound, _⟩ := h.velocity_regular
  have hFc : ContinuousOn F (Ico 0 T) := fun t ht =>
    (Dynamics.hasDerivWithinAt_fderiv_flow_Ico hu hdiff hD hbound hcont hode hinit a ht).continuousWithinAt
  have hνc : ContinuousOn ν (Ico 0 T) :=
    (Analysis.continuous_smallest_singularValue (E := E₃) (n := 2) (by simp)).comp_continuousOn hFc
  have hν0 : ν 0 = 1 := by
    dsimp only [ν, F]
    rw [Dynamics.fderiv_flow_zero hinit a]
    exact Analysis.smallest_singularValue_id (by simp)
  have hνpos (t : ℝ) (ht : t ∈ Ico 0 T) : 0 < ν t :=
    h.singularValues_fderiv_flow_pos hcont hode hinit ht a 2
  refine hlower ν ν' hνc hν0 hνpos ?_ ?_
  · intro t ht
    exact (smallest_singularValue_evolution h hcont hode hinit a ⟨ht.1.le, ht.2⟩).2.Ioi_of_Ici
  · intro t ht _
    obtain ⟨e, he, heigen, hmin⟩ :=
      (smallest_singularValue_evolution h hcont hode hinit a ⟨ht.1.le, ht.2⟩).1.1
    have hd := hdriver Φ hinit hcont hode a t ⟨ht.1.le, ht.2⟩ e he heigen
    have hminBound : -(B t + C * ν t ^ ((3 * (α : ℝ) - 1) / 2)) ≤ sInf (G t) := by
      rw [show sInf (G t) = ⟪e, S t e⟫_ℝ from hmin]
      exact (abs_le.mp hd).1
    have hpower : ν t ^ ((3 * (α : ℝ) + 1) / 2) =
        ν t ^ ((3 * (α : ℝ) - 1) / 2) * ν t := by
      rw [show (3 * (α : ℝ) + 1) / 2 = (3 * (α : ℝ) - 1) / 2 + 1 by ring]
      exact Real.rpow_add_one (hνpos t ⟨ht.1.le, ht.2⟩).ne' _
    calc
      -B t * ν t - C * ν t ^ ((3 * (α : ℝ) + 1) / 2) =
          ν t * -(B t + C * ν t ^ ((3 * (α : ℝ) - 1) / 2)) := by rw [hpower]; ring
      _ ≤ ν t * sInf (G t) :=
        mul_le_mul_of_nonneg_left hminBound (hνpos t ⟨ht.1.le, ht.2⟩).le

end ClockBarrier.Euler
