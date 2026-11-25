/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Measurable selection from a closed relation with compact fibers

Selections are obtained as limits of measurable approximations from a fixed
dense sequence. Uniqueness of the chosen point is not required.
-/

public section
namespace ClockBarrier.Analysis
open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
/-- Hitting a fixed closed ball is a closed condition on a compact closed relation. -/
theorem isClosed_exists_mem_relation_closedBall {R : Set (X × Y)} (hR : IsClosed R)
    (y : Y) (r : ℝ) :
    IsClosed {x | ∃ z, (x, z) ∈ R ∧ dist z y ≤ r} := by
  convert isClosedMap_fst_of_compactSpace
    (R ∩ Prod.snd ⁻¹' closedBall y r) (hR.inter (isClosed_closedBall.preimage continuous_snd))
    using 1
  ext x
  simp only [mem_setOf_eq, mem_image, Prod.exists, mem_inter_iff, mem_preimage,
    mem_closedBall, exists_and_right, exists_eq_right]

/-- Refine a measurable approximation to a nonempty closed fiber while controlling its jump. -/
theorem exists_measurable_relation_approximation [Nonempty Y]
    {R : Set (X × Y)} (hR : IsClosed R) {f : X → Y} (hf : Measurable f)
    {r s : ℝ} (hs : 0 < s)
    (hnear : ∀ x, ∃ z, (x, z) ∈ R ∧ dist z (f x) ≤ r) :
    ∃ g : X → Y, Measurable g ∧
      (∀ x, ∃ z, (x, z) ∈ R ∧ dist z (g x) ≤ s) ∧
      ∀ x, dist (f x) (g x) ≤ r + s := by
  classical
  let P : X → ℕ → Prop := fun x k =>
    (∃ z, (x, z) ∈ R ∧ dist z (denseSeq Y k) ≤ s) ∧
      dist (f x) (denseSeq Y k) ≤ r + s
  have hex : ∀ x, ∃ k, P x k := by
    intro x
    obtain ⟨z, hz, hzf⟩ := hnear x
    obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp (denseRange_denseSeq Y) z s hs
    exact ⟨k, ⟨z, hz, hk.le⟩, (dist_triangle_left _ _ _).trans (add_le_add hzf hk.le)⟩
  have hm : ∀ k, MeasurableSet {x | P x k} := fun k =>
    (isClosed_exists_mem_relation_closedBall hR (denseSeq Y k) s).measurableSet.inter
      (measurableSet_le (hf.dist measurable_const) measurable_const)
  exact ⟨fun x => denseSeq Y (Nat.find (hex x)),
    Measurable.find (fun _ => measurable_const) hm hex,
    fun x => (Nat.find_spec (hex x)).1, fun x => (Nat.find_spec (hex x)).2⟩

/-- A closed relation with nonempty fibers in a compact metric space has a Borel selector. -/
theorem exists_measurable_mem_closed_relation [Nonempty Y]
    {R : Set (X × Y)} (hR : IsClosed R) (hne : ∀ x, ∃ y, (x, y) ∈ R) :
    ∃ f : X → Y, Measurable f ∧ ∀ x, (x, f x) ∈ R := by
  classical
  let r : ℕ → ℝ := fun n => (diam (univ : Set Y) + 1) * (1 / 2 : ℝ) ^ n
  have hr : ∀ n, 0 < r n := fun n =>
    mul_pos (lt_add_of_le_of_pos diam_nonneg zero_lt_one) (pow_pos (by norm_num) n)
  let S : ℕ → Type _ := fun n =>
    {f : X → Y // Measurable f ∧ ∀ x, ∃ z, (x, z) ∈ R ∧ dist z (f x) ≤ r n}
  have hzero : ∀ x, ∃ z, (x, z) ∈ R ∧ dist z (Classical.ofNonempty : Y) ≤ r 0 :=
    fun x => (hne x).imp (fun z hz => ⟨hz,
      (dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ z) (mem_univ _)).trans
        (by simpa only [r, pow_zero, mul_one] using
          le_add_of_nonneg_right (a := diam (univ : Set Y)) zero_le_one)⟩)
  choose next hm hn hj using fun n (f : S n) =>
    exists_measurable_relation_approximation hR f.property.1 (hr (n + 1)) f.property.2
  let f : ∀ n, S n := Nat.rec ⟨fun _ => Classical.ofNonempty, measurable_const, hzero⟩
    (fun n f => ⟨next n f, hm n f, hn n f⟩)
  have hstep : ∀ n x, dist ((f n).val x) ((f (n + 1)).val x) ≤ r n + r (n + 1) :=
    fun n x => hj n (f n) x
  have hc : ∀ x, CauchySeq (fun n => (f n).val x) := fun x =>
    cauchySeq_of_le_geometric (1 / 2) ((3 / 2) * (diam (univ : Set Y) + 1)) (by norm_num)
      (fun n => (hstep n x).trans_eq (by dsimp [r]; rw [pow_succ]; ring))
  choose g hg using fun x => cauchySeq_tendsto_of_complete (hc x)
  refine ⟨g, measurable_of_tendsto_metrizable (fun n => (f n).property.1)
    (tendsto_pi_nhds.mpr hg), ?_⟩
  intro x
  choose z hz hd using fun n => (f n).property.2 x
  have hr0 : Tendsto r atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul
        (diam (univ : Set Y) + 1)
  have hzlim : Tendsto z atTop (𝓝 (g x)) := (hg x).congr_dist
    (squeeze_zero (fun _ => dist_nonneg) (fun n => (dist_comm _ _).trans_le (hd n)) hr0)
  exact hR.mem_of_tendsto (tendsto_const_nhds.prodMk_nhds hzlim) (Eventually.of_forall hz)

end ClockBarrier.Analysis
