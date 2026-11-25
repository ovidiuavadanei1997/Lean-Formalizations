/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd.
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: focused imports, namespaces, module interface and pinned Mathlib compatibility.
-/
module
public import ClockBarrier.Analysis.SmoothWords
public import ClockBarrier.Analysis.SobolevCoordinates
public import ClockBarrier.Analysis.RealSmoothSobolev
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # Coordinate Sobolev bounds
Port of Euler/OrdinaryWordBounds.lean, omitting the unused cylinder Lp-norm adapter.
-/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Sobolev
open MeasureTheory ContinuousLinearMap SmoothL2Field DirectionalWords SmoothSobolev Finset
open scoped ContDiff ENNReal
local notation "Space" => EuclideanSpace ℝ (Fin 3)
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem jet_norm_le_word_sum (A : SmoothL2Field V) (n : ℕ) :
    ‖A.jetLp n‖ ≤ ∑ w : Fin n → Fin 3, ‖(wordField A w).toLp‖ := by
  let H : (Fin n → Fin 3) → Space → ℝ := fun w x => ‖(wordField A w).field x‖
  have hn (w : Fin n → Fin 3) : (eLpNorm (H w) 2 volume).toReal = ‖(wordField A w).toLp‖ := by
    rw [field_norm,eLpNorm_norm]
  have h := (finite_domination (volume : Measure Space) univ (iteratedFDeriv ℝ n A.field)
    (A.integrable n).aestronglyMeasurable H (fun w _ => (wordField A w).memLp.norm) ?_).2
  · simpa only [norm_jetLp,hn] using h
  · intro x
    have hb := multilinear_norm_le_coordinate_sum 3 n
      (iteratedFDeriv ℝ n A.field x)
    simpa only [H,wordField_field,wordDerivative,axis] using hb

theorem wordBound_mono {s r : ℕ} {M : ℝ} {A : SmoothL2Field V}
    (h : WordBound s M A) (hrs : r ≤ s) : WordBound r M A :=
  fun n hn w => h n (hn.trans hrs) w

theorem wordBound_nonneg {s : ℕ} {M : ℝ} {A : SmoothL2Field V}
    (h : WordBound s M A) : 0 ≤ M :=
  (norm_nonneg _).trans (h 0 (Nat.zero_le s) Fin.elim0)

theorem wordBound_jet_norm {s n : ℕ} {M : ℝ} {A : SmoothL2Field V}
    (h : WordBound s M A) (hn : n ≤ s) : ‖A.jetLp n‖ ≤ (3 : ℝ)^n*M := by
  apply (jet_norm_le_word_sum A n).trans
  calc
    _ ≤ ∑ _w : Fin n → Fin 3, M := sum_le_sum (fun w _ => h n hn w)
    _ = _ := by simp

theorem wordBound_toLp {s : ℕ} {M : ℝ} {A : SmoothL2Field V}
    (h : WordBound s M A) : ‖A.toLp‖ ≤ M :=
  h 0 (Nat.zero_le s) Fin.elim0

theorem wordBound_derivative {s : ℕ} {M : ℝ} {A : SmoothL2Field V}
    (h : WordBound s M A) (hs : 1 ≤ s) : ‖A.derivative.toLp‖ ≤ 3*M := by
  have hb := wordBound_jet_norm h hs
  simpa only [← norm_jetLp_zero A.derivative,norm_derivative_jetLp,pow_one] using hb

theorem wordBound_map {s : ℕ} {M : ℝ} {A : SmoothL2Field V}
    (h : WordBound s M A) (L : V →L[ℝ] W) (hL : ‖L‖ ≤ 1) :
    WordBound s M (mapField L A) := by
  intro n hn w
  rw [wordField_map]
  exact (mapField_norm_le L _).trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans
    (by simpa only [one_mul] using h n hn w))

theorem real_pointwise_H2 (A : SmoothL2Field Space) (x : Space) :
    ‖A.field x‖ ≤ smoothEmbeddingConstant*(∑ j ∈ range 3, ‖A.jetLp j‖) := by
  have hb := smooth_pointwise_le_H2 (complexify 3 ∘ A.field)
    ((complexify 3).contDiff.comp A.smooth)
    (fun j _ => complexification_tensor_memLp 3 j A.field A.smooth (A.integrable j)) x
  rw [Function.comp_apply,(complexify 3).norm_map,
    complexification_sobolevNorm 3 2 A.field A.smooth] at hb
  simpa only [realTensorSobolevNorm,norm_jetLp] using hb

theorem wordBound_pointwise {M : ℝ} {A : SmoothL2Field Space}
    (h : WordBound 2 M A) (x : Space) : ‖A.field x‖ ≤ (13*smoothEmbeddingConstant)*M := by
  apply (real_pointwise_H2 A x).trans
  have hh : (∑ j ∈ range 3, ‖A.jetLp j‖) ≤ 13*M := by
    calc
      _ ≤ ∑ j ∈ range 3, (3 : ℝ)^j*M := sum_le_sum
        (fun j hj => wordBound_jet_norm h (by have := mem_range.mp hj; omega))
      _ = _ := by norm_num [sum_range_succ]; ring
  exact (mul_le_mul_of_nonneg_left hh smoothEmbeddingConstant_nonneg).trans_eq (by ring)

theorem norm_coordinate_le (i : Fin 3) : ‖(EuclideanSpace.proj i : Space →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖x i‖ ≤ 1*‖x‖
  simpa only [one_mul] using PiLp.norm_apply_le x i

theorem wordBound_coordinate {s : ℕ} {M : ℝ} {A : SmoothL2Field Space}
    (h : WordBound s M A) (i : Fin 3) :
    WordBound s M (mapField (EuclideanSpace.proj i) A) :=
  wordBound_map h _ (norm_coordinate_le i)

end ClockBarrier.Analysis.Sobolev
