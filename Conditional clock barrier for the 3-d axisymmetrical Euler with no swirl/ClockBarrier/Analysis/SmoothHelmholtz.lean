/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.SmoothLimit
public import ClockBarrier.Analysis.RegularizedWords
public import ClockBarrier.Analysis.SmoothWordReassembly

/-! # The canonical Helmholtz projection preserves actual smooth finite-energy fields -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Sobolev
open MeasureTheory ContinuousLinearMap SmoothL2Field Solenoidal Filter
open scoped Topology
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem exists_solenoidal_smooth_representative (A : SmoothL2Field Space) :
    ∃ B : SmoothL2Field Space, B.toLp = solenoidalProjection A.toLp := by
  let U (k : ℕ) (_ : Unit) := regularizedSmoothField k A.toLp
  have hc (k n : ℕ) : Continuous (fun t : Unit => (U k t).jetLp n) := by
    change Continuous (fun _ : Unit => (regularizedSmoothField k A.toLp).jetLp n)
    exact continuous_const
  have hb (q : ℕ) : ∃ M : ℝ, ∀ k (t : Unit), WordBound q M (U k t) := by
    refine ⟨Real.sqrt (wordEnergy q A), fun k _ => ?_⟩
    exact regularizedSmoothField_wordBound k A q _ (wordBound_sqrt_energy q A)
  have hu : Tendsto (fun k => fieldPath (U k) (hc k)) atTop
      (𝓝 (ContinuousMap.const Unit (solenoidalProjection A.toLp))) := by
    have h := ((ContinuousLinearMap.const ℝ Unit).continuous.tendsto (solenoidalProjection A.toLp)).comp
      (regularizerMap_tendsto A.toLp)
    have he (k : ℕ) : (ContinuousLinearMap.const ℝ Unit) (regularizerMap k A.toLp) =
        fieldPath (U k) (hc k) := by
      apply ContinuousMap.ext
      intro t
      exact (regularizedSmoothField_toLp k A.toLp).symm
    convert! (by simpa only [Function.comp_def, he] using h) using 1
  obtain ⟨F, hF, hbase, _⟩ := exists_smooth_limit U hc hb hu.cauchySeq
  have he := tendsto_nhds_unique hbase hu
  refine ⟨F (), ?_⟩
  exact congrArg (fun f : C(Unit, L2) => f ()) he

/-- The unique smooth representative of the already constructed orthogonal projection. -/
def solenoidalField (A : SmoothL2Field Space) : SmoothL2Field Space :=
  Classical.choose (exists_solenoidal_smooth_representative A)

theorem solenoidalField_toLp (A : SmoothL2Field Space) :
    (solenoidalField A).toLp = solenoidalProjection A.toLp :=
  Classical.choose_spec (exists_solenoidal_smooth_representative A)

theorem solenoidalField_unique (A B : SmoothL2Field Space)
    (hB : B.toLp = solenoidalProjection A.toLp) : B = solenoidalField A :=
  SmoothL2Field.toLp_injective (hB.trans (solenoidalField_toLp A).symm)

theorem solenoidalField_word (A : SmoothL2Field Space) {n : ℕ} (w : Fin n → Fin 3) :
    (wordField (solenoidalField A) w).toLp = solenoidalProjection (wordField A w).toLp := by
  rw [word_toLp_eq_orbit, solenoidalField_toLp]
  exact (projection_word A w).symm

theorem solenoidalField_continuous {K : Type*} [TopologicalSpace K]
    (A : K → SmoothL2Field Space) (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) (n : ℕ) :
    Continuous (fun t => (solenoidalField (A t)).jetLp n) := by
  simp_rw [jetLp_eq_word_reassembly, solenoidalField_word]
  apply (L2Tensor.tensorLpReassembly (V := Space) (volume : Measure Space) n).continuous.comp
  exact continuous_pi (fun w => solenoidalProjection.continuous.comp (continuous_word_toLp A w (hA n)))

end ClockBarrier.Analysis.Sobolev
