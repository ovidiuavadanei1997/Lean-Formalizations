/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.SmoothBoundedField
public import Mathlib.Topology.ContinuousMap.Compact

/-! # Continuous paths of actual smooth fields and their spatial L² jets -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Sobolev
open MeasureTheory SmoothL2Field
local notation "Space" => EuclideanSpace ℝ (Fin 3)
variable {K V : Type*} [TopologicalSpace K] [NormedAddCommGroup V] [NormedSpace ℝ V]

def fieldPath (A : K → SmoothL2Field V) (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) :
    C(K, Lp V 2 (volume : Measure Space)) := ⟨fun t => (A t).toLp, continuous_toLp A (hA 0)⟩

@[simp] theorem fieldPath_apply (A : K → SmoothL2Field V)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) (t : K) : fieldPath A hA t = (A t).toLp := rfl

def jetPath (A : K → SmoothL2Field V) (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) (n : ℕ) :
    C(K, Lp (Space [×n]→L[ℝ] V) 2 (volume : Measure Space)) := ⟨fun t => (A t).jetLp n, hA n⟩

@[simp] theorem jetPath_apply (A : K → SmoothL2Field V)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) (n : ℕ) (t : K) :
    jetPath A hA n t = (A t).jetLp n := rfl

end ClockBarrier.Analysis.Sobolev
