/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import Mathlib.Topology.MetricSpace.HolderNorm
import ClockBarrier.Analysis.CurlHolder
public import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.Bochner.Set
/-! # Temporal measurability of finite Hölder seminorms

Pointwise continuity implies lower semicontinuity of the actual finite seminorm.
A compact-time Hölder bound then supplies integrability, without continuity in
the Hölder norm.
-/

public section
namespace ClockBarrier.Analysis
open Set Filter MeasureTheory
open scoped NNReal Topology

/-- Every Hölder difference quotient is bounded by the actual finite seminorm. -/
theorem holder_quotient_le_nnHolderNorm {X Y : Type*} [MetricSpace X] [MetricSpace Y] {α : ℝ≥0} {f : X → Y} (hf : MemHolder α f) (x y : X) :
    dist (f x) (f y) / dist x y ^ (α : ℝ) ≤ (nnHolderNorm α f : ℝ) := by
  by_cases hxy : x = y
  · simp only [hxy, dist_self, zero_div]; positivity
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (dist_pos.mpr hxy) _)).mpr
    (hf.holderWith.dist_le x y)

/-- A real bound on all difference quotients is exactly a bound on the finite
Hölder seminorm. Finiteness rules out the `toNNReal` fallback. -/
theorem nnHolderNorm_le_iff_quotient_le {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {α : ℝ≥0} {f : X → Y} (hf : MemHolder α f) {C : ℝ} (hC : 0 ≤ C) :
    (nnHolderNorm α f : ℝ) ≤ C ↔
      ∀ x y, dist (f x) (f y) / dist x y ^ (α : ℝ) ≤ C := by
  refine ⟨fun h x y => (holder_quotient_le_nnHolderNorm hf x y).trans h, fun h => ?_⟩
  have hb : HolderWith ⟨C, hC⟩ α f := by
    apply holderWith_of_dist_le_mul_rpow
    intro x y
    by_cases hxy : x = y
    · simp only [hxy, dist_self]; positivity
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (dist_pos.mpr hxy) _)).mp (h x y)
  exact NNReal.coe_le_coe.mpr hb.nnholderNorm_le

/-- The finite Hölder seminorm is lower semicontinuous in a parameter under
pointwise continuity; continuity in the Hölder norm is not required. -/
theorem lowerSemicontinuousOn_nnHolderNorm {Z X Y : Type*} [TopologicalSpace Z]
    [MetricSpace X] [MetricSpace Y] {s : Set Z} {f : Z → X → Y} {α : ℝ≥0}
    (hf : ∀ t ∈ s, MemHolder α (f t))
    (hc : ∀ x, ContinuousOn (fun t => f t x) s) :
    LowerSemicontinuousOn (fun t => (nnHolderNorm α (f t) : ℝ)) s := by
  intro t ht c hct
  by_cases hC : 0 ≤ c
  · have hex : ∃ x y, c < dist (f t x) (f t y) / dist x y ^ (α : ℝ) := by
      by_contra hn
      exact (not_le_of_gt hct) ((nnHolderNorm_le_iff_quotient_le (hf t ht) hC).mpr
        (fun x y => le_of_not_gt (fun hxy => hn ⟨x, y, hxy⟩)))
    obtain ⟨x, y, hxy⟩ := hex
    have hq : ContinuousOn (fun z => dist (f z x) (f z y) / dist x y ^ (α : ℝ)) s :=
      (continuous_dist.comp_continuousOn ((hc x).prodMk (hc y))).div_const _
    filter_upwards [(hq t ht).eventually (Ioi_mem_nhds hxy), self_mem_nhdsWithin]
      with z hz hzs using hz.trans_le (holder_quotient_le_nnHolderNorm (hf z hzs) x y)
  · exact Eventually.of_forall (fun z => (lt_of_not_ge hC).trans_le (nnHolderNorm α (f z)).coe_nonneg)

/-- A pointwise continuous family with a common Hölder constant has an
integrable actual seminorm on every measurable set of finite measure. -/
theorem integrableOn_nnHolderNorm_of_uniform_bound {Z X Y : Type*}
    [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    [MetricSpace X] [MetricSpace Y] {μ : Measure Z} {s : Set Z}
    {f : Z → X → Y} {H α : ℝ≥0} (hs : MeasurableSet s) (hμ : μ s ≠ ⊤)
    (hf : ∀ t ∈ s, HolderWith H α (f t))
    (hc : ∀ x, ContinuousOn (fun t => f t x) s) :
    IntegrableOn (fun t => (nnHolderNorm α (f t) : ℝ)) s μ := by
  have hl := lowerSemicontinuousOn_nnHolderNorm (fun t ht => (hf t ht).memHolder) hc
  have hm : AEStronglyMeasurable (fun t => (nnHolderNorm α (f t) : ℝ)) (μ.restrict s) :=
    (aemeasurable_restrict_of_measurable_subtype hs
      (lowerSemicontinuous_restrict_iff.mpr hl).measurable).aestronglyMeasurable
  exact (integrableOn_const (C := (H : ℝ)) hμ).mono' hm
    (ae_restrict_of_forall_mem hs (fun t ht => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (nnHolderNorm α (f t)).coe_nonneg] using
        NNReal.coe_le_coe.mpr (hf t ht).nnholderNorm_le))
end ClockBarrier.Analysis
