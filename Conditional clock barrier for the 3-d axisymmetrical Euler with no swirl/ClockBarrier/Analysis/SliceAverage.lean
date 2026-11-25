/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Bounds for finite slice averages and negligible zero-area fibers -/

public section
namespace ClockBarrier.Analysis
open Set MeasureTheory Metric
open scoped ENNReal

/-- A positive finite normalized average stays in every closed ball containing
its integrand almost everywhere. This is the literal normalization in coherence. -/
theorem norm_normalized_integral_sub_le
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {μ : Measure X} {S : Set X} {f : X → E} {c : E} {C : ℝ}
    (h0 : μ S ≠ 0) (hfin : μ S ≠ ∞) (hi : IntegrableOn f S μ)
    (hbound : ∀ᵐ q ∂μ.restrict S, ‖f q - c‖ ≤ C) :
    ‖(μ S).toReal⁻¹ • ∫ q in S, f q ∂μ - c‖ ≤ C := by
  have hm := (convex_closedBall c C).set_average_mem isClosed_closedBall h0 hfin
    (hbound.mono (fun _ hq => mem_closedBall.mpr (by simpa only [dist_eq_norm] using hq))) hi
  simpa only [mem_closedBall, dist_eq_norm, setAverage_eq, Measure.real] using hm

/-- A measurable set contains almost no points lying in a zero-measure fiber.
Nonempty null fibers are allowed; no pointwise positivity assertion is made. -/
theorem ae_fiber_measure_ne_zero
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite ν]
    {S : Set (X × Y)} (hS : MeasurableSet S) :
    ∀ᵐ p ∂(μ.prod ν).restrict S, ν (Prod.mk p.1 ⁻¹' S) ≠ 0 := by
  have hm := measurable_measure_prodMk_left (ν := ν) hS
  have hp : MeasurableSet {p : X × Y | p ∈ S → ν (Prod.mk p.1 ⁻¹' S) ≠ 0} := by
    simpa only [preimage, compl_def, union_def, mem_singleton_iff,
      Function.comp_apply, imp_iff_not_or, mem_setOf_eq] using
      hS.compl.union ((hm.comp measurable_fst) (measurableSet_singleton 0)).compl
  refine (ae_restrict_iff' hS).2 ((Measure.ae_prod_iff_ae_ae hp).2
    (Filter.Eventually.of_forall (fun x => ?_)))
  by_cases hz : ν (Prod.mk x ⁻¹' S) = 0
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with y hy
    exact fun hxy => (hy hxy).elim
  · exact Filter.Eventually.of_forall (fun _ _ => hz)

end ClockBarrier.Analysis
