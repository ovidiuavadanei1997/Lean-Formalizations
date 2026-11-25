/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.LocalFlowGeometry
public import ClockBarrier.Euler.GeneralCoherenceWellDefined
import ClockBarrier.Analysis.LocalHolderIntegral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The local off-clock estimate for classical Euler flows

All Hölder and distance-comparison hypotheses are supplied by the
classical Euler interface. The constant precedes time, labels, and frames.
-/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The off-clock integral has one uniform constant budget on a positive initial
interval. The same bound works for every label cutoff. -/
theorem classical_euler_on.exists_local_offClock_bound
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x) (L : ℝ) :
    ∃ T₀ B : ℝ, 0 < T₀ ∧ T₀ < T ∧ 0 < B ∧ ∀ t ∈ Icc 0 T₀, ∀ ℓ : ℝ,
    let w₀ := vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩)
    (⨆ aStar : E₃,
      ∫⁻ a in {a : E₃ | ℓ ≤ ‖a - aStar‖ ∧ ‖Φ t a - Φ t aStar‖ ≤ L},
        ENNReal.ofReal ((fderiv ℝ (Φ t) aStar).toLinearMap.singularValues 0 *
          ‖w₀ a - w₀ aStar‖ / ‖Φ t a - Φ t aStar‖ ^ 3)) ≤ ENNReal.ofReal B := by
  obtain ⟨T₀, hT₀, hT₀T, hgeo⟩ := h.exists_initial_flow_geometry
  obtain ⟨H, hH⟩ := h.holderWith_vorticity 0 ⟨le_rfl, h.1⟩
  obtain ⟨B, hB, hb⟩ := Analysis.exists_uniform_disjoint_nearField_budget
    (I := Unit) (C := (3 / 2 : ℝ) * H) (by exact_mod_cast h.2.1)
    (mul_nonneg (by norm_num) H.coe_nonneg) L
  refine ⟨T₀, B, hT₀, hT₀T, hB, fun t ht ℓ => ?_⟩
  intro w₀
  refine iSup_le (fun aStar => ?_)
  have hΦ := (h.contDiff_bijective_measurePreserving_flow hcont hode hinit
    ⟨ht.1, ht.2.trans_lt hT₀T⟩).1.continuous
  have hN (a : E₃) : (fderiv ℝ (Φ t) aStar).toLinearMap.singularValues 0 *
      ‖w₀ a - w₀ aStar‖ ≤ (3 / 2 : ℝ) * H * ‖a - aStar‖ ^ (α : ℝ) := by
    have hw : ‖w₀ a - w₀ aStar‖ ≤ (H : ℝ) * ‖a - aStar‖ ^ (α : ℝ) := by
      simpa only [dist_eq_norm] using (hH 0 ⟨le_rfl, le_rfl⟩).dist_le a aStar
    exact (mul_le_mul ((hgeo Φ hinit hcont hode t ht).1 aStar 0).2 hw
      (norm_nonneg _) (by norm_num)).trans_eq (mul_assoc _ _ _).symm
  simpa only [tsum_fintype, Fintype.sum_unique] using hb (Φ t) (fun a b => by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using
      ((hgeo Φ hinit hcont hode t ht).2.1 a b).1) aStar
    (fun _ : Unit => {a : E₃ | ℓ ≤ ‖a - aStar‖ ∧ ‖Φ t a - Φ t aStar‖ ≤ L})
    (fun _ a => (fderiv ℝ (Φ t) aStar).toLinearMap.singularValues 0 * ‖w₀ a - w₀ aStar‖)
    (fun _ => (isClosed_le continuous_const (show Continuous (fun a : E₃ => ‖a - aStar‖) by fun_prop)).measurableSet.inter
      (isClosed_le ((hΦ.sub continuous_const).norm) continuous_const).measurableSet)
    (fun _ _ hne => (hne (Subsingleton.elim _ _)).elim) (fun _ _ ha => ha.2) (fun _ => Filter.Eventually.of_forall hN)

end ClockBarrier.Euler
