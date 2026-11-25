/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.L2TensorReconstruction
public import ClockBarrier.Analysis.SmoothWords

/-! # Reconstructing actual spatial jets from coordinate derivatives -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Sobolev
open MeasureTheory ContinuousLinearMap SmoothL2Field Filter
open scoped Topology
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem jetLp_eq_word_reassembly {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (A : SmoothL2Field V) (n : ℕ) :
    A.jetLp n = L2Tensor.tensorLpReassembly (volume : Measure Space) n
      (fun w : Fin n → Fin 3 => (wordField A w).toLp) := by
  apply Lp.ext
  apply (A.jetLp_ae n).trans
  apply Filter.EventuallyEq.symm
  apply L2Tensor.tensorLpReassembly_eq_ae
  intro w
  filter_upwards [(wordField A w).toLp_ae] with x hx
  rw [hx, wordField_field]
  rfl

end ClockBarrier.Analysis.Sobolev
