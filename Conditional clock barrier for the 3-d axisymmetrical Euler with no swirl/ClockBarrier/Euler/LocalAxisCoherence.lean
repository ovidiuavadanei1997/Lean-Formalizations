/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisCoherent
public import ClockBarrier.Euler.Reflection
import ClockBarrier.Euler.ClassicalRestriction
import ClockBarrier.Euler.LocalAxisCusp
import ClockBarrier.Euler.LocalAxisOffClock
import ClockBarrier.Euler.SymmetryPreservation
import ClockBarrier.Euler.FlowCylindrical
import ClockBarrier.Geometry.HoopStretch
import ClockBarrier.Analysis.HolderDyadicTail

/-! # Local axis coherence from the classical Euler interface

The actual flow and every coherence witness are constructed on a common
initial interval, following the short-time, cusp, tail and off-clock source proof.
-/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped NNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The exact local axis-class conclusion, with only the initial symmetries. -/
theorem classical_euler_on.exists_local_axis_coherence
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (haxis : axisymmetric_no_swirl (u 0))
    (_hreflection : z_reflection_symmetric (u 0)) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ < T ∧ axis_coherent_on α T₀ u := by
  have ha : ∀ t ∈ Ico 0 T, Euler.axisymmetric_no_swirl (u t) :=
    fun _ ht => h.axisymmetric_no_swirl haxis ht
  obtain ⟨⟨Φ, hi, hc, ho, hreg, hJ⟩, ⟨TG, hTG, hTGT, hclose⟩, ⟨M, hM, hcusp⟩⟩ :=
    And.intro (h.exists_axis_flow ha)
      (And.intro (h.exists_uniform_fderiv_flow_sub_id_le (ε := 1 / 2) (by norm_num))
        (h.exists_local_axis_cusp_bound ha))
  obtain ⟨TR, B, hTR, hTRT, hB, hoff⟩ := h.exists_local_axis_offClock_bound hc ho hi ha 1
  have hsub : Ico (0 : ℝ) (min TG TR) ⊆ Ico 0 T :=
    Ico_subset_Ico_right ((min_le_left _ _).trans hTGT.le)
  refine ⟨min TG TR, lt_min hTG hTR, (min_le_left _ _).trans_lt hTGT,
    p, h.restrict_time (lt_min hTG hTR) ((min_le_left _ _).trans hTGT.le),
    fun t ht => ha t (hsub ht), Φ, hi, fun x => (hc x).mono hsub,
    fun x t ht => ho x t (hsub ht), ?_⟩
  intro J
  let Q : ℝ := ∑' n : ℤ, if (2 : ℝ)^n ≤ 1 then ((2 : ℝ)^n) ^ (α : ℝ) else 0
  refine ⟨⟨1, by norm_num⟩, ⟨1, by norm_num⟩,
    ⟨1 / 3, by norm_num⟩, ⟨3, by norm_num⟩,
    ⟨1 / 3, by norm_num⟩, ⟨3, by norm_num⟩,
    ⟨1 / 3, by norm_num⟩, ⟨3, by norm_num⟩,
    ⟨M, hM⟩, ⟨|Q| + 1, by positivity⟩, (fun _ _ _ => 1), (fun _ => B),
    integrableOn_const ((measure_mono Ico_subset_Icc_self).trans_lt
      isCompact_Icc.measure_lt_top).ne, ?_, ?_, fun _ _ _ _ => zero_le_one, ?_,
    fun t ht z => hoff t (hsub ht) (ht.2.le.trans (min_le_right _ _)) 1 z⟩
  · intro t ht z a _ _
    have hcl := hclose Φ hi hc ho t ⟨ht.1, ht.2.le.trans (min_le_left _ _)⟩
    have hd := (hreg t (hsub ht)).1.differentiable (by decide)
    obtain ⟨_, hjpos, hjdiag, _⟩ := (hJ z).2 t (hsub ht)
    have hjb : (2 / 3 : ℝ) ≤ J z t ∧ J z t ≤ 2 :=
      Geometry.axis_clock_bounds_of_half_perturbation hjpos hjdiag (hcl !₂[0, 0, z])
    have hnorm (b : E₃) := Geometry.opNorm_bounds_of_half_perturbation (hcl b)
    have hcmp := Geometry.norm_sub_comparison_of_norm_fderiv_sub_id_le
      hd hcl (by norm_num) a !₂[0, 0, z]
    norm_num only at hcmp
    have hr := Geometry.radius_bounds_of_hoop_stretch (hd a)
      (h.rotation_semiconj_flow hc ho hi ha t (hsub ht)) (hcl a)
    refine ⟨hcmp.1, hcmp.2, ?_, ?_,
      by change (1 / 3 : ℝ) * _ ≤ _; linarith [(hnorm a).1, (hnorm !₂[0, 0, z]).2],
      by change _ ≤ (3 : ℝ) * _; linarith [(hnorm a).2, (hnorm !₂[0, 0, z]).1]⟩
    · rw [← mul_div_assoc, div_le_iff₀ hjpos]
      nlinarith only [mul_le_mul hr.1 hjb.1 (by norm_num : (0 : ℝ) ≤ 2 / 3)
        (Real.sqrt_nonneg ((Φ t a 0)^2 + (Φ t a 1)^2))]
    · rw [← mul_div_assoc, le_div_iff₀ hjpos]
      nlinarith only [mul_le_mul hr.2 hjb.2 hjpos.le
        (show 0 ≤ (3 / 2 : ℝ) * Real.sqrt ((a 0)^2 + (a 1)^2) by positivity)]
  · exact fun t _ z j _ q => by
      simpa only [mul_one, mul_assoc] using
        (hcusp (Φ t) j z ⟨1, by norm_num⟩ ⟨1, by norm_num⟩ q.1 q.2).2
  · intro _ _
    simp only [mul_one]
    exact ⟨fun _ => Analysis.summable_truncated_dyadic_holder (by exact_mod_cast h.2.1),
      ⟨Q, fun _ ⟨_, he⟩ => he ▸ le_rfl⟩,
      by simpa only [range_const, csSup_singleton] using
        (lt_of_le_of_lt (le_abs_self Q) (lt_add_one |Q|))⟩

end ClockBarrier.Euler
