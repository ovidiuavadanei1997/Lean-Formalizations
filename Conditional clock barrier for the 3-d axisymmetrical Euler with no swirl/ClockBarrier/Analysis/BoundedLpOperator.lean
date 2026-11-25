/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.BoundedLp

/-! # The canonical bounded linear inclusion of bounded continuous fields into L∞ -/

@[expose] public noncomputable section
namespace ClockBarrier.Analysis
open MeasureTheory
open scoped BoundedContinuousFunction ENNReal
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def boundedToLpTop : (E₃ →ᵇ F) →L[ℝ] Lp F ∞ (volume : Measure E₃) where
  toFun f := (f.memLp_top (μ := volume)).toLp f
  map_add' f g := MemLp.toLp_add (f.memLp_top (μ := volume)) (g.memLp_top (μ := volume))
  map_smul' c f := MemLp.toLp_const_smul c (f.memLp_top (μ := volume))
  cont := continuous_bounded_toLp_top

end ClockBarrier.Analysis
