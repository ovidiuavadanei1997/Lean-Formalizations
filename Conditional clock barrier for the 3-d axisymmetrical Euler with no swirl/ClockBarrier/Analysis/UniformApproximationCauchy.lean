/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic.Linarith

/-! # Cauchy convergence from uniformly accurate approximations -/
public section
namespace ClockBarrier.Analysis
open Filter
open scoped Topology
variable {E : Type*} [PseudoMetricSpace E]

/-- A uniformly accurate family of Cauchy approximations is Cauchy. The scale
is fixed before the two sequence indices are sent to infinity. -/
theorem cauchySeq_of_uniform_approximations (u : ℕ → E) (v : ℕ → ℕ → E)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (herr : ∀ k n, dist (u n) (v k n) ≤ e k)
    (hc : ∀ k, CauchySeq (v k)) : CauchySeq u := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := ((tendsto_order.mp he).2 (ε / 3) (by linarith)).exists
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hc k) (ε / 3) (by linarith)
  refine ⟨N, fun m hm n hn => ?_⟩
  calc
    dist (u m) (u n) ≤ dist (u m) (v k m) +
        dist (v k m) (v k n) + dist (v k n) (u n) := dist_triangle4 _ _ _ _
    _ ≤ e k + dist (v k m) (v k n) + e k := by
      exact add_le_add (add_le_add (herr k m) le_rfl) ((dist_comm _ _).trans_le (herr k n))
    _ < ε := by linarith [hN m hm n hn]

end ClockBarrier.Analysis
