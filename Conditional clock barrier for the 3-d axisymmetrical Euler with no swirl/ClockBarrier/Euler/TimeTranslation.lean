/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.Classical
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Linarith

/-! # Time translation of classical Euler solutions -/
public section
namespace ClockBarrier.Euler
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Restart the time coordinate at any point of the original lifespan. -/
theorem classical_euler_on.translate_time
    {α : ℝ≥0} {T a : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (ha : a ∈ Ico 0 T) :
    classical_euler_on α (T - a) (fun t => u (a + t)) (fun t => p (a + t)) := by
  have hm : MapsTo (fun t => a + t) (Ico 0 (T - a)) (Ico 0 T) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2, ha.1]
  rcases h with ⟨_, hα, hα1, hu, ⟨D, hD, hd, hH⟩, hL, hLt, hp, hg, he, hz⟩
  refine ⟨sub_pos.mpr ha.2, hα, hα1,
    hu.comp (continuous_const.add continuous_id).continuousOn hm,
    ⟨fun t => D (a + t), hD.comp (continuous_const.add continuous_id).continuousOn hm,
      fun t ht => hd _ (hm ht), ?_⟩,
    fun t ht => hL _ (hm ht), ?_, fun t ht => hp _ (hm ht), ?_, ?_,
    fun t ht => hz _ (hm ht)⟩
  · intro b hb
    obtain ⟨H, hH⟩ := hH (a + b) (hm hb)
    refine ⟨H, fun t ht => hH _ ?_⟩
    constructor <;> linarith [ht.1, ht.2, ha.1]
  · intro t ht
    exact (hLt _ (hm ht)).comp
      ((continuous_const.add continuous_id).continuousWithinAt.tendsto_nhdsWithin hm)
  · exact hg.comp
      ((continuous_const.add continuous_fst).prodMk continuous_snd).continuousOn
      (fun q hq => ⟨hm hq.1, mem_univ _⟩)
  · intro t ht x
    simpa only [one_smul, Function.comp_def] using
      (he _ (hm ht) x).scomp t
        ((hasDerivAt_id t).const_add a).hasDerivWithinAt hm

end ClockBarrier.Euler
