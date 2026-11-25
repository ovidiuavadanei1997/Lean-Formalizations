/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.GeneralCoherent
public import ClockBarrier.Euler.ClassicalRestriction
public import ClockBarrier.Euler.LocalDini
public import ClockBarrier.Euler.LocalOffClock
public import ClockBarrier.Euler.LocalLongitudinal
public import ClockBarrier.Euler.LocalCusp
public import ClockBarrier.Euler.MeasurableSingularFrame
import ClockBarrier.Analysis.HolderDyadicTail
import ClockBarrier.Dynamics.FlowLifespan
import Mathlib.Tactic.NormNum

/-! # Assembly of the local general-coherence estimates

This ordinary conditional theorem constructs the actual flow, measurable frame,
and all coherence constants and budgets. Its explicit lifespan symmetry premise
is stronger than the initial symmetry premise of the public
Proposition 3.1; propagation of that symmetry is a separate obligation.
-/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Classical solutions that retain axisymmetry and no swirl have a positive
initial interval in the exact general coherence class. All analytic estimates,
flow properties and measurable frames are proved internally. This conditional
helper does not assert propagation of symmetry from time zero. -/
theorem classical_euler_on.exists_local_general_coherence_of_lifespan_axisymmetry
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p)
    (haxis : ∀ t ∈ Ico 0 T, axisymmetric_no_swirl (u t)) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ < T ∧ general_coherent_on α T₀ u := by
  obtain ⟨hu, hdiff, hD, hbound, _⟩ := h.velocity_regular
  obtain ⟨Φ, hi, hc, ho, _⟩ := Dynamics.exists_regular_flow_Ico
    (u := fun t x => u t x) h.1 hu hdiff hD hbound
  obtain ⟨V, hVm, hV⟩ := h.exists_measurable_singular_frame hc ho hi
  obtain ⟨TG, hTG, hTGT, hgeo⟩ := h.exists_initial_flow_geometry
  obtain ⟨TD, BD, hTD, hTDT, hBD, hdini⟩ := h.exists_local_dini_bound hc ho hi 1
  obtain ⟨TP, BP, hTP, hTPT, hBP, hlong⟩ := h.exists_local_longitudinal_bound hc ho hi 1
  obtain ⟨TR, BR, hTR, hTRT, hBR, hoff⟩ := h.exists_local_offClock_bound hc ho hi 1
  obtain ⟨M, hM, hcusp⟩ := h.exists_local_cusp_bound hc ho hi
  obtain ⟨Tail, hTail, htail⟩ := Analysis.exists_truncated_dyadic_holder_budget
    (by exact_mod_cast h.2.1)
  let T₀ := min TG (min TD (min TP TR))
  have hT₀ : 0 < T₀ := lt_min hTG (lt_min hTD (lt_min hTP hTR))
  have hT₀T : T₀ < T := (min_le_left _ _).trans_lt hTGT
  have htimes : T₀ ≤ TG ∧ T₀ ≤ TD ∧ T₀ ≤ TP ∧ T₀ ≤ TR := by
    exact ⟨min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hsub : Ico (0 : ℝ) T₀ ⊆ Ico 0 T := Ico_subset_Ico_right hT₀T.le
  refine ⟨T₀, hT₀, hT₀T, p, h.restrict_time hT₀ hT₀T.le,
    fun t ht => haxis t (hsub ht), Φ, hi, fun x => (hc x).mono hsub,
    fun x t ht => ho x t (hsub ht), ?_⟩
  intro F σ ω₀
  refine ⟨V, fun t ht => hVm t (hsub ht), fun t ht => hV t (hsub ht),
    ⟨1, by norm_num⟩, ⟨1, by norm_num⟩, ⟨1 / 3, by norm_num⟩, ⟨3, by norm_num⟩,
    ⟨M, hM⟩, ⟨Tail, hTail⟩, ⟨3, by norm_num⟩,
    (fun _ _ _ => 1), (fun _ => BD), (fun _ => BP), (fun _ => BR), ?_⟩
  intro E Ec A avg
  have hconst (B : ℝ) : IntegrableOn (fun _ : ℝ => B) (Ico 0 T₀) volume :=
    integrableOn_const
      ((measure_mono Ico_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top).ne
  refine ⟨hconst BD, hconst BP, hconst BR, fun _ _ => ⟨hBD.le, hBP.le, hBR.le⟩,
    fun t ht aStar a _ => (hgeo Φ hi hc ho t ⟨ht.1, ht.2.le.trans htimes.1⟩).2.2.1 a aStar,
    fun t ht => hdini t ⟨ht.1, ht.2.le.trans htimes.2.1⟩ (V t),
    ?_, fun _ _ _ _ => zero_le_one, ?_,
    fun t ht => hlong t ⟨ht.1, ht.2.le.trans htimes.2.2.1⟩ 1 (V t),
    fun t ht => hoff t ⟨ht.1, ht.2.le.trans htimes.2.2.2⟩ 1,
    fun t ht aStar => (hgeo Φ hi hc ho t ⟨ht.1, ht.2.le.trans htimes.1⟩).2.2.2 aStar⟩
  · intro t ht aStar k
    simpa only [mul_one] using hcusp t (hsub ht) aStar (V t aStar) k 1 1
  · intro t ht
    simpa only [one_mul, iSup_const, NNReal.toReal] using htail

end ClockBarrier.Euler
