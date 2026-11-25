/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisFlow
public import Mathlib.Analysis.InnerProductSpace.SingularValues
import ClockBarrier.Dynamics.FlowPerturbation
import ClockBarrier.Geometry.NearIdentity
import Mathlib.Tactic.NormNum

/-! # Short-time geometry of classical Euler flows

The first step of Proposition 3.1 uses only the classical solution
regularity. The time is uniform over all labels and every initialized flow.
-/

public section
namespace ClockBarrier.Euler
open Set
open scoped Topology NNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- On a sufficiently short interval, every initialized Euler flow has its
actual spatial derivative uniformly close to the identity. -/
theorem classical_euler_on.exists_uniform_fderiv_flow_sub_id_le
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ < T ∧ ∀ Φ : ℝ → E₃ → E₃,
      (∀ x, Φ 0 x = x) →
      (∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T)) →
      (∀ x, ∀ t ∈ Ico 0 T,
        HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t) →
      ∀ t ∈ Icc 0 T₀, ∀ a : E₃,
        ‖fderiv ℝ (Φ t) a - ContinuousLinearMap.id ℝ E₃‖ ≤ ε := by
  obtain ⟨hu, hdiff, hD, hbound, _⟩ := h.velocity_regular
  obtain ⟨b, hb0, hbT⟩ := exists_between h.1
  obtain ⟨K, hK⟩ := hbound b ⟨hb0.le, hbT⟩
  have hC : 0 < (K : ℝ) * Real.exp (K * b) + 1 :=
    add_pos_of_nonneg_of_pos (mul_nonneg K.coe_nonneg (Real.exp_pos _).le) zero_lt_one
  refine ⟨min b (ε / (K * Real.exp (K * b) + 1)),
    lt_min hb0 (div_pos hε hC), (min_le_left _ _).trans_lt hbT,
    fun Φ hi hc ho t ht a => ?_⟩
  have hsub : Icc 0 b ⊆ Ico 0 T := fun _ hs => ⟨hs.1, hs.2.trans_lt hbT⟩
  refine (Dynamics.norm_fderiv_flow_sub_id_le hb0.le
    (hu.mono (prod_mono hsub subset_rfl)) (fun s hs => hdiff s (hsub hs))
    (hD.mono (prod_mono hsub subset_rfl)) hK (fun x => (hc x).mono hsub)
    (fun x s hs => ho x s (hsub (Ico_subset_Icc_self hs))) hi
    ⟨ht.1, ht.2.trans (min_le_left _ _)⟩ a).trans ?_
  exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) ht.1).trans
    (by simpa only [mul_comm] using
      (le_div_iff₀ hC).mp (ht.2.trans (min_le_right _ _)))

/-- The first geometric steps of Proposition 3.1, with one common initial
interval and explicit constants for all labels and all initialized flows. -/
theorem classical_euler_on.exists_initial_flow_geometry
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ < T ∧ ∀ Φ : ℝ → E₃ → E₃,
      (∀ x, Φ 0 x = x) →
      (∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T)) →
      (∀ x, ∀ t ∈ Ico 0 T,
        HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t) →
      ∀ t ∈ Icc 0 T₀,
        (∀ a : E₃, ∀ i : Fin 3,
          (1 / 2 : ℝ) ≤ (fderiv ℝ (Φ t) a).toLinearMap.singularValues i ∧
          (fderiv ℝ (Φ t) a).toLinearMap.singularValues i ≤ 3 / 2) ∧
        (∀ a b : E₃,
          (1 / 2 : ℝ) * ‖a - b‖ ≤ ‖Φ t a - Φ t b‖ ∧
          ‖Φ t a - Φ t b‖ ≤ (3 / 2 : ℝ) * ‖a - b‖) ∧
        (∀ a b : E₃,
          (1 / 3 : ℝ) * ‖(fderiv ℝ (Φ t) b) (a - b)‖ ≤ ‖Φ t a - Φ t b‖ ∧
          ‖Φ t a - Φ t b‖ ≤ 3 * ‖(fderiv ℝ (Φ t) b) (a - b)‖) ∧
        ∀ a : E₃,
          (fderiv ℝ (Φ t) a).toLinearMap.singularValues 0 /
            (fderiv ℝ (Φ t) a).toLinearMap.singularValues 1 ≤ 3 := by
  obtain ⟨T₀, hT₀, hT₀T, hclose⟩ :=
    h.exists_uniform_fderiv_flow_sub_id_le (ε := 1 / 2) (by norm_num)
  refine ⟨T₀, hT₀, hT₀T, fun Φ hi hc ho t ht => ?_⟩
  obtain ⟨hu, hdiff, hD, hbound, _⟩ := h.velocity_regular
  have hd : Differentiable ℝ (Φ t) :=
    (Dynamics.flow_spatial_regularity_Ico hu hdiff hD hbound hc ho hi t
      ⟨ht.1, ht.2.trans_lt hT₀T⟩).1.differentiable (by decide)
  refine ⟨fun a i => ?_, fun a b => ?_, fun a b => ?_, fun a => ?_⟩
  · convert Geometry.singularValues_bounds_of_norm_sub_id_le
      (hclose Φ hi hc ho t ht a) (by simp) i using 1 <;> norm_num
  · convert Geometry.norm_sub_bounds_of_norm_fderiv_sub_id_le hd
      (hclose Φ hi hc ho t ht) a b using 1 <;> norm_num
  · convert Geometry.norm_sub_comparison_of_norm_fderiv_sub_id_le hd
      (hclose Φ hi hc ho t ht) (by norm_num) a b using 1 <;> norm_num
  · convert Geometry.singularValues_div_le_of_norm_sub_id_le
      (hclose Φ hi hc ho t ht a) (by norm_num) (by simp) (0 : Fin 3) (1 : Fin 3)
      using 1 <;> norm_num

end ClockBarrier.Euler
