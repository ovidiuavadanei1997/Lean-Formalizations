/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.FlowHolder
public import ClockBarrier.Euler.LocalFlowGeometry
public import ClockBarrier.Euler.GeneralCoherenceWellDefined
import ClockBarrier.Analysis.LocalHolderIntegral
import ClockBarrier.Geometry.SingularShellDisjoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The local averaged Dini estimate for classical Euler flows

All Hölder, boundedness, and distance-comparison hypotheses are supplied by the
classical Euler interface. The constant precedes time, labels, and frames.
-/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- On one positive initial interval, the literal uncut-shell Dini sum has a
uniform constant bound, independently of the choice of orthogonal frames. -/
theorem classical_euler_on.exists_local_dini_bound
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x) (L : ℝ) :
    ∃ T₀ B : ℝ, 0 < T₀ ∧ T₀ < T ∧ 0 < B ∧
    ∀ t ∈ Icc 0 T₀, ∀ V : E₃ → E₃ ≃ₗᵢ[ℝ] E₃,
    let F := fderiv ℝ (Φ t)
    let w₀ := vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩)
    (⨆ aStar : E₃,
    let σ := fun i : Fin 3 => (F aStar).toLinearMap.singularValues i
    let E := fun k : Fin 3 → ℤ => {a : E₃ | let η := (V aStar).symm (a - aStar)
      (2 : ℝ) ^ (k 2) ≤ |η 2| ∧ |η 2| < 2 * (2 : ℝ) ^ (k 2) ∧
      (2 : ℝ) ^ (k 0) * σ 2 * (2 : ℝ) ^ (k 2) / σ 0 ≤ |η 0| ∧
      |η 0| < 2 * ((2 : ℝ) ^ (k 0) * σ 2 * (2 : ℝ) ^ (k 2) / σ 0) ∧
      (2 : ℝ) ^ (k 1) * σ 2 * (2 : ℝ) ^ (k 2) / σ 1 ≤ |η 1| ∧
      |η 1| < 2 * ((2 : ℝ) ^ (k 1) * σ 2 * (2 : ℝ) ^ (k 2) / σ 1)}
    ∑' k, ∫⁻ a in E k ∩ {a | ‖Φ t a - Φ t aStar‖ ≤ L},
      ENNReal.ofReal (‖(F a - F aStar) (w₀ a)‖ / ‖Φ t a - Φ t aStar‖ ^ 3)) ≤
      ENNReal.ofReal B := by
  obtain ⟨T₀, hT₀, hT₀T, hgeo⟩ := h.exists_initial_flow_geometry
  obtain ⟨H, hH⟩ := h.exists_uniform_holder_bound_fderiv_flow hcont hode hinit
    ⟨hT₀.le, hT₀T⟩
  obtain ⟨W, _, hW, _⟩ := h.exists_boundedContinuous_vorticity
  obtain ⟨B, hB, hb⟩ := Analysis.exists_uniform_disjoint_nearField_budget
    (I := Fin 3 → ℤ) (C := (H : ℝ) * ‖W 0‖) (by exact_mod_cast h.2.1)
    (mul_nonneg H.coe_nonneg (norm_nonneg _)) L
  refine ⟨T₀, B, hT₀, hT₀T, hB, fun t ht V => ?_⟩
  intro F w₀
  refine iSup_le (fun aStar => ?_)
  extract_lets σ E
  have hΦ := (h.contDiff_bijective_measurePreserving_flow hcont hode hinit
    ⟨ht.1, ht.2.trans_lt hT₀T⟩).1.continuous
  refine hb (Φ t) (fun a b => by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using (hgeo Φ hinit hcont hode t ht).2.1 a b |>.1)
    aStar _ (fun _ a => ‖(F a - F aStar) (w₀ a)‖) ?_ ?_
    (fun _ _ ha => ha.2) ?_
  · exact fun k => (Geometry.measurableSet_singular_shell aStar (V aStar) σ k).inter
      (isClosed_le ((hΦ.sub continuous_const).norm) continuous_const).measurableSet
  · exact Geometry.pairwise_disjoint_of_singular_shells
      (fun i => h.singularValues_fderiv_flow_pos hcont hode hinit
        ⟨ht.1, ht.2.trans_lt hT₀T⟩ aStar i) aStar (V aStar) _ (fun _ _ ha => ha.1)
  · refine fun _ => Filter.Eventually.of_forall (fun a => ?_)
    calc
      ‖(F a - F aStar) (w₀ a)‖ ≤ ‖F a - F aStar‖ * ‖w₀ a‖ :=
        (F a - F aStar).le_opNorm _
      _ ≤ ((H : ℝ) * ‖a - aStar‖ ^ (α : ℝ)) * ‖W 0‖ :=
        mul_le_mul (hH t ht a aStar)
          (by rw [show w₀ a = W 0 a from (hW 0 ⟨le_rfl, h.1⟩ a).symm]
              exact (W 0).norm_coe_le_norm a)
          (norm_nonneg _) (mul_nonneg H.coe_nonneg (Real.rpow_nonneg (norm_nonneg _) _))
      _ = _ := mul_right_comm _ _ _

end ClockBarrier.Euler
