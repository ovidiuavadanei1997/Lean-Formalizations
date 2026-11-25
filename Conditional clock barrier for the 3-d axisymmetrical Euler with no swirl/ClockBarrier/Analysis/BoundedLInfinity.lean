/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.BoundedLp
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Equality of spatial supremum and essential supremum norms -/

public section
namespace ClockBarrier.Analysis
open MeasureTheory
open scoped ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Lebesgue measure sees every nonempty open set, so a bounded continuous
field has essential supremum equal to its actual supremum. -/
theorem eLpNorm_top_eq_enorm_bounded {F : Type*} [NormedAddCommGroup F]
    (f : E₃ →ᵇ F) : eLpNorm f ∞ volume = ‖f‖ₑ := by
  rw [eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm, f.enorm_eq_iSup_enorm]
  exact (iSup_eq_essSup (fun {x a} ha =>
    (isOpen_lt continuous_const f.continuous.enorm).measure_ne_zero volume ⟨x, ha⟩)).symm

end ClockBarrier.Analysis
