/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.LocalSliceHolder
public import ClockBarrier.Euler.LocalFlowGeometry
public import ClockBarrier.Euler.GeneralCoherenceWellDefined
import ClockBarrier.Analysis.LocalHolderIntegral
import ClockBarrier.Geometry.SingularShellDisjoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The local longitudinal estimate for classical Euler flows

All Hölder and distance-comparison hypotheses are supplied by the
classical Euler interface. The constant precedes time, labels, and frames.
-/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

/-- The clock-local longitudinal sum has one positive constant bound on a
common initial interval, for all labels, clock cutoffs, and orthogonal frames. -/
theorem classical_euler_on.exists_local_longitudinal_bound
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x) (L : ℝ) :
    ∃ T₀ B : ℝ, 0 < T₀ ∧ T₀ < T ∧ 0 < B ∧
    ∀ t ∈ Icc 0 T₀, ∀ ℓ : ℝ, ∀ V : E₃ → E₃ ≃ₗᵢ[ℝ] E₃,
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
    let Ec := fun k => E k ∩ {a | ‖a - aStar‖ < ℓ} ∩ {a | ‖Φ t a - Φ t aStar‖ ≤ L}
    let A := fun k (z : ℝ) => {q : E₂ | aStar + V aStar !₂[q 0, q 1, z] ∈ Ec k}
    let avg := fun k z => if volume (A k z) = 0 then (0 : E₃) else
      (volume (A k z)).toReal⁻¹ • ∫ q in A k z, w₀ (aStar + V aStar !₂[q 0, q 1, z])
    ∑' k, ∫⁻ a in Ec k,
      ENNReal.ofReal (σ 0 * ‖avg k ((V aStar).symm (a - aStar) 2) - w₀ aStar‖ /
        ‖Φ t a - Φ t aStar‖ ^ 3)) ≤ ENNReal.ofReal B := by
  obtain ⟨T₀, hT₀, hT₀T, hgeo⟩ := h.exists_initial_flow_geometry
  obtain ⟨W, _, hW, hHolder⟩ := h.exists_boundedContinuous_vorticity
  obtain ⟨H, hH⟩ := hHolder 0 ⟨le_rfl, h.1⟩
  obtain ⟨B, hB, hb⟩ := Analysis.exists_uniform_disjoint_nearField_budget
    (I := Fin 3 → ℤ) (C := (3 / 2 : ℝ) * ((H : ℝ) * (2 : ℝ) ^ (α : ℝ)))
    (by exact_mod_cast h.2.1) (by positivity) L
  refine ⟨T₀, B, hT₀, hT₀T, hB, fun t ht ℓ V => ?_⟩
  intro F w₀
  have hw : w₀ = W 0 := (funext (hW 0 ⟨le_rfl, h.1⟩)).symm
  simp (config := { zeta := false }) only [hw]
  refine iSup_le (fun aStar => ?_)
  extract_lets σ E Ec A avg
  have hΦ := (h.contDiff_bijective_measurePreserving_flow hcont hode hinit
    ⟨ht.1, ht.2.trans_lt hT₀T⟩).1.continuous
  have hm (k : Fin 3 → ℤ) : MeasurableSet (Ec k) :=
    measurableSet_singular_clock_block hΦ aStar (V aStar) σ k ℓ L
  have havg (k : Fin 3 → ℤ) : ∀ᵐ a ∂volume.restrict (Ec k),
      ‖avg k ((V aStar).symm (a - aStar) 2) - W 0 aStar‖ ≤
        ((H : ℝ) * (2 : ℝ) ^ (α : ℝ)) * ‖a - aStar‖ ^ (α : ℝ) := by
    apply ae_norm_clock_average_sub_center_le aStar (V aStar) (W 0)
      (hH 0 ⟨le_rfl, le_rfl⟩) (hm k) (fun _ ha => ha.1.2)
      (r := ![(2 : ℝ) ^ (k 0) * σ 2 * (2 : ℝ) ^ (k 2) / σ 0,
        (2 : ℝ) ^ (k 1) * σ 2 * (2 : ℝ) ^ (k 2) / σ 1, (2 : ℝ) ^ (k 2)])
    intro a ha i
    have he := ha.1.1
    fin_cases i
    · exact ⟨he.2.2.1, he.2.2.2.1.le⟩
    · exact ⟨he.2.2.2.2.1, he.2.2.2.2.2.le⟩
    · exact ⟨he.1, he.2.1.le⟩
  refine hb (Φ t) (fun a b => by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using
      ((hgeo Φ hinit hcont hode t ht).2.1 a b).1) aStar Ec
    (fun k a => σ 0 * ‖avg k ((V aStar).symm (a - aStar) 2) - W 0 aStar‖) hm ?_
    (fun _ _ ha => ha.2) ?_
  · exact Geometry.pairwise_disjoint_of_singular_shells
      (fun i => h.singularValues_fderiv_flow_pos hcont hode hinit
        ⟨ht.1, ht.2.trans_lt hT₀T⟩ aStar i) aStar (V aStar) Ec (fun _ _ ha => ha.1.1)
  · intro k
    filter_upwards [havg k] with a ha
    exact (mul_le_mul ((hgeo Φ hinit hcont hode t ht).1 aStar 0).2 ha
      (norm_nonneg _) (by norm_num)).trans_eq (mul_assoc _ _ _).symm

end ClockBarrier.Euler
