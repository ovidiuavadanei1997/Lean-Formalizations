/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.TimeTranslation
public import ClockBarrier.Euler.ClassicalRestriction
public import ClockBarrier.Euler.Uniqueness
import Mathlib.Tactic.Linarith

/-! # Equality of restarted velocities and pressure gradients on an overlap -/
public section
namespace ClockBarrier.Euler
open Set Filter
open scoped Topology NNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Uniqueness identifies a restarted velocity throughout the common interval. -/
theorem classical_euler_on.restart_eq
    {α : ℝ≥0} {T a τ : ℝ} {u v : ℝ → E₃ →ᵇ E₃} {p q : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (hv : classical_euler_on α τ v q)
    (ha : a ∈ Ico 0 T) (hi : v 0 = u a)
    {t : ℝ} (ht : t ∈ Ico a (min T (a + τ))) : u t = v (t - a) := by
  have hS : 0 < min (T - a) τ := lt_min (sub_pos.mpr ha.2) hv.1
  have h₁ := (h.translate_time ha).restrict_time hS (min_le_left _ _)
  have h₂ := hv.restrict_time hS (min_le_right _ _)
  have hs : t - a ∈ Ico 0 (min (T - a) τ) := by
    constructor
    · linarith [ht.1]
    · exact lt_min (by linarith [ht.2.trans_le (min_le_left T (a + τ))])
        (by linarith [ht.2.trans_le (min_le_right T (a + τ))])
  simpa only [add_sub_cancel] using h₁.velocity_eq h₂ (by simpa using hi.symm) hs

/-- Equal velocities on an open time interval have equal Euler pressure gradients.
The scalar pressures may retain different time-dependent gauges. -/
theorem classical_euler_on.restart_gradient_eq
    {α : ℝ≥0} {T a τ : ℝ} {u v : ℝ → E₃ →ᵇ E₃} {p q : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (hv : classical_euler_on α τ v q)
    (ha : a ∈ Ico 0 T) (hi : v 0 = u a)
    {t : ℝ} (ht : t ∈ Ioo a (min T (a + τ))) (x : E₃) :
    gradient (p t) x = gradient (q (t - a)) x := by
  have hto : t ∈ Ioo 0 T := ⟨lt_of_le_of_lt ha.1 ht.1,
    ht.2.trans_le (min_le_left _ _)⟩
  have htn : t - a ∈ Ioo 0 τ := ⟨sub_pos.mpr ht.1, by
    linarith [ht.2.trans_le (min_le_right T (a + τ))]⟩
  have heq : (fun s => u s x) =ᶠ[𝓝 t] (fun s => v (s - a) x) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact congrArg (fun f : E₃ →ᵇ E₃ => f x)
      (h.restart_eq hv ha hi ⟨hs.1.le, hs.2⟩)
  have hd₁ := (h.2.2.2.2.2.2.2.2.2.1 t ⟨hto.1.le, hto.2⟩ x).hasDerivAt
    (Ico_mem_nhds hto.1 hto.2)
  have hd₂ := ((hv.2.2.2.2.2.2.2.2.2.1 (t - a) ⟨htn.1.le, htn.2⟩ x).hasDerivAt
    (Ico_mem_nhds htn.1 htn.2)).scomp t ((hasDerivAt_id t).sub_const a)
  have hh := hd₁.unique (hd₂.congr_of_eventuallyEq heq)
  simpa only [h.restart_eq hv ha hi ⟨ht.1.le, ht.2⟩, one_smul, sub_right_inj] using hh

end ClockBarrier.Euler
