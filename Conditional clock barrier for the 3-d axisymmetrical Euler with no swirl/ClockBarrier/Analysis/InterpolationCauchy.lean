/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Cauchy convergence from a scale-dependent interpolation bound -/
public section
namespace ClockBarrier.Analysis
open Filter

theorem cauchySeq_of_scale_bound {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    (u : ℕ → E) (v : ℕ → F) {B : ℝ} (hB : 0 ≤ B) (K : ℝ → ℝ)
    (hK : ∀ r, 0 < r → 0 < K r)
    (hb : ∀ r, 0 < r → ∀ n m, dist (u n) (u m) ≤ r * B + K r * dist (v n) (v m))
    (hv : CauchySeq v) : CauchySeq u := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  let r := ε / (4 * (B + 1))
  have hr : 0 < r := div_pos hε (by positivity)
  have he : r * (4 * (B + 1)) = ε := div_mul_cancel₀ _ (by positivity)
  have hrB : r * B < ε / 2 := by nlinarith
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hv ((ε / 2) / K r)
    (div_pos (by positivity) (hK r hr))
  refine ⟨N, fun m hm n hn => ?_⟩
  have hvn := (lt_div_iff₀ (hK r hr)).mp (hN m hm n hn)
  exact (hb r hr m n).trans_lt (by nlinarith)

end ClockBarrier.Analysis
