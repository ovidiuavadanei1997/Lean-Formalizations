/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue

/-!
# Scalar facts for axis stretches and radial limits

These lemmas provide positivity and first-order limits used in axis geometry.
The identification of these scalar functions with an Euler flow is a separate obligation.
-/

public section

open Set Filter
open scoped Topology

namespace ClockBarrier.Analysis

/-- A continuous nonvanishing stretch starting positive stays positive throughout an interval. -/
theorem pos_of_continuousOn_of_ne_zero {a : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hcont : ContinuousOn a (Icc s t)) (hstart : 0 < a s)
    (hne : ∀ r ∈ Icc s t, a r ≠ 0) : 0 < a t := by
  by_contra! ht
  obtain ⟨r, hr, har⟩ := intermediate_value_Icc' hst hcont ⟨ht, hstart.le⟩
  exact hne r hr har

/-- The radial quotient has the derivative as its right-hand limit. Only differentiability
at zero and a zero value at the axis are needed. -/
theorem tendsto_div_self_of_hasDerivAt_zero {f : ℝ → ℝ} {a : ℝ}
    (hf : HasDerivAt f a 0) (hzero : f 0 = 0) :
    Tendsto (fun r => f r / r) (𝓝[>] 0) (𝓝 a) := by
  simpa only [zero_add, hzero, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    hf.tendsto_slope_zero_right

/-- The reciprocal radial quotient converges when the radial derivative is nonzero. -/
theorem tendsto_self_div_of_hasDerivAt_zero {f : ℝ → ℝ} {a : ℝ}
    (hf : HasDerivAt f a 0) (hzero : f 0 = 0) (ha : a ≠ 0) :
    Tendsto (fun r => r / f r) (𝓝[>] 0) (𝓝 a⁻¹) := by
  simpa only [inv_div] using (tendsto_div_self_of_hasDerivAt_zero hf hzero).inv₀ ha

end ClockBarrier.Analysis
