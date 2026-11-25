/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Identification of a strong L² limit with a pointwise limit -/
public section
namespace ClockBarrier.Analysis
open MeasureTheory Filter
open scoped Topology
variable {X V : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup V]

theorem l2_ae_eq_pointwise_limit (U : ℕ → Lp V 2 μ) (f : ℕ → X → V)
    (hU : ∀ n, U n =ᵐ[μ] f n) {v : Lp V 2 μ} {g : X → V}
    (hv : Tendsto U atTop (𝓝 v)) (hg : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    v =ᵐ[μ] g := by
  obtain ⟨ns, hns, ha⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  have hall := ae_all_iff.mpr hU
  filter_upwards [ha, hall] with x hx he
  apply tendsto_nhds_unique hx
  simpa only [Function.comp_def, he] using (hg x).comp hns.tendsto_atTop

end ClockBarrier.Analysis
