/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.LocalAxisGeometry
public import ClockBarrier.Euler.AxisOffClock
import ClockBarrier.Analysis.LocalHolderIntegral
import ClockBarrier.Analysis.AxisLocalKernel
import Mathlib.Tactic.Linarith

/-! # A uniform local off-clock budget for axis labels -/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Cauchy transport and the local Hölder integral supply a constant axis budget. -/
theorem classical_euler_on.exists_local_axis_offClock_bound
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hc : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (ho : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hi : ∀ x, Φ 0 x = x)
    (haxis : ∀ t ∈ Ico 0 T, axisymmetric_no_swirl (u t)) (L : ℝ) :
    ∃ T₀ B : ℝ, 0 < T₀ ∧ T₀ < T ∧ 0 < B ∧ ∀ t, ∀ ht : t ∈ Ico 0 T, t ≤ T₀ →
      ∀ ℓ z : ℝ,
      (∫ a in {a : E₃ | ℓ ≤ ‖a - !₂[0, 0, z]‖ ∧
          ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L},
        Real.sqrt ((Φ t a 0)^2 + (Φ t a 1)^2) *
          |Φ t a 2 - Φ t !₂[0, 0, z] 2| / ‖Φ t a - Φ t !₂[0, 0, z]‖^5 *
          ‖vorticity (u t) (h.cartesian_partials t ht) (Φ t a)‖) ≤ B := by
  obtain ⟨T₀, hT₀, hT₀T, hclose⟩ :=
    h.exists_uniform_fderiv_flow_sub_id_le (ε := 1 / 2) (by norm_num)
  obtain ⟨H, hH⟩ := h.holderWith_vorticity 0 ⟨le_rfl, h.1⟩
  obtain ⟨B, hB, hb⟩ := Analysis.exists_uniform_disjoint_nearField_budget
    (I := Unit) (C := (3 / 2 : ℝ) * H) (by exact_mod_cast h.2.1)
    (by positivity) L
  refine ⟨T₀, B, hT₀, hT₀T, hB, fun t ht ht₀ ℓ z => ?_⟩
  have hdist (a b : E₃) : ‖a - b‖ / 2 ≤ ‖Φ t a - Φ t b‖ := by
    convert
      (Geometry.norm_sub_bounds_of_norm_fderiv_sub_id_le
        ((h.contDiff_bijective_measurePreserving_flow hc ho hi ht).1.differentiable (by decide))
        (hclose Φ hi hc ho t ⟨ht.1, ht₀⟩) a b).1 using 1
    ring
  have hN (a : E₃) : ‖vorticity (u t) (h.cartesian_partials t ht) (Φ t a)‖ ≤
      (3 / 2 : ℝ) * H * ‖a - !₂[0, 0, z]‖ ^ (α : ℝ) := by
    refine (h.norm_vorticity_flow_le hc ho hi t ht a).trans ?_
    have hw : ‖vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩) a‖ ≤
        (H : ℝ) * ‖a - !₂[0, 0, z]‖ ^ (α : ℝ) := by
      simpa only [h.vorticity_axis_eq_zero 0 ⟨le_rfl, h.1⟩
        (haxis 0 ⟨le_rfl, h.1⟩) z, dist_zero_right, dist_eq_norm, sub_zero] using
        (hH 0 ⟨le_rfl, le_rfl⟩).dist_le a !₂[0, 0, z]
    exact (mul_le_mul (Geometry.opNorm_bounds_of_half_perturbation
      (hclose Φ hi hc ho t ⟨ht.1, ht₀⟩ a)).2 hw (norm_nonneg _)
      (by norm_num)).trans_eq (mul_assoc _ _ _).symm
  have hbudget : (∫⁻ a in {a : E₃ | ℓ ≤ ‖a - !₂[0, 0, z]‖ ∧
        ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L},
      ENNReal.ofReal (‖vorticity (u t) (h.cartesian_partials t ht) (Φ t a)‖ /
        ‖Φ t a - Φ t !₂[0, 0, z]‖^3)) ≤ ENNReal.ofReal B := by
    simpa only [tsum_fintype, Fintype.sum_unique] using hb (Φ t) hdist !₂[0, 0, z]
      (fun _ : Unit => {a : E₃ | ℓ ≤ ‖a - !₂[0, 0, z]‖ ∧
        ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L})
      (fun _ a => ‖vorticity (u t) (h.cartesian_partials t ht) (Φ t a)‖)
      (fun _ => (isClosed_le continuous_const
        (show Continuous (fun a : E₃ => ‖a - !₂[0, 0, z]‖) by fun_prop)).measurableSet.inter
        (isClosed_le (((h.contDiff_bijective_measurePreserving_flow hc ho hi ht).1.continuous.sub
          continuous_const).norm) continuous_const).measurableSet)
      (fun _ _ hne => (hne (Subsingleton.elim _ _)).elim)
      (fun _ _ ha => ha.2) (fun _ => Filter.Eventually.of_forall hN)
  have hint := (h.integrableOn_axis_near_majorant_flow hc ho hi haxis t ht z L).mono_set
    (show {a : E₃ | ℓ ≤ ‖a - !₂[0, 0, z]‖ ∧ ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L} ⊆
      {a : E₃ | ‖Φ t a - Φ t !₂[0, 0, z]‖ ≤ L} from fun _ ha => ha.2)
  apply (ENNReal.ofReal_le_ofReal_iff hB.le).mp
  rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall (fun _ => by positivity))]
  refine (lintegral_mono (fun a => ENNReal.ofReal_le_ofReal ?_)).trans hbudget
  refine Analysis.axis_weight_mul_le_div_cube (abs_nonneg _) (norm_nonneg _)
    (norm_nonneg _) ?_ (Analysis.abs_euclidean_coordinate_le_norm
      (Φ t a - Φ t !₂[0, 0, z]) 2)
  have hx : Φ t !₂[0, 0, z] 0 = 0 :=
    congrArg (fun x : E₃ => x 0) (h.flow_axis_eq hc ho hi haxis t ht z)
  have hy : Φ t !₂[0, 0, z] 1 = 0 :=
    congrArg (fun x : E₃ => x 1) (h.flow_axis_eq hc ho hi haxis t ht z)
  simpa [hx, hy] using Analysis.radius_le_norm (Φ t a - Φ t !₂[0, 0, z])

end ClockBarrier.Euler
