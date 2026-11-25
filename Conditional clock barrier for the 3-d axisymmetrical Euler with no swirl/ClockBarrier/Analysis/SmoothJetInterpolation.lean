/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.SmoothWordInterpolation
public import ClockBarrier.Analysis.SmoothAdvectionBounds
import ClockBarrier.Analysis.NonnegativeLogConvex

/-! # L² interpolation sufficient to recover convergence of every spatial jet -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Sobolev
open MeasureTheory InnerProductSpace SmoothL2Field Finset
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem wordMaximum_zero (A : SmoothL2Field Space) : wordMaximum 0 A = ‖A.toLp‖ := by
  simp [wordMaximum]

theorem jet_norm_sq_interpolation (A : SmoothL2Field Space) (n : ℕ) (M : ℝ)
    (hM : WordBound (2*n) M A) :
    ‖A.jetLp n‖^2 ≤ (3 : ℝ)^(2*n) * ‖A.toLp‖ * M := by
  have h := NonnegativeLogConvex.between (fun j => wordMaximum j A)
    (wordMaximum_nonneg A) (wordMaximum_logconvex A) 0 n n (Nat.zero_le n) le_rfl
  rw [wordMaximum_zero, Nat.sub_zero, ← two_mul n] at h
  have hh := h.trans (mul_le_mul_of_nonneg_left (wordMaximum_le hM le_rfl) (norm_nonneg _))
  have hj := pow_le_pow_left₀ (norm_nonneg (A.jetLp n)) (jet_norm_le_wordMaximum A n) 2
  calc
    _ ≤ ((3 : ℝ)^n * wordMaximum n A)^2 := hj
    _ = (3 : ℝ)^(2*n) * (wordMaximum n A * wordMaximum n A) := by rw [mul_pow, Nat.mul_comm 2 n, pow_mul]; ring
    _ ≤ (3 : ℝ)^(2*n) * (‖A.toLp‖*M) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

theorem wordField_sub (A B : SmoothL2Field Space) {n : ℕ} (w : Fin n → Fin 3) :
    wordField (fieldSub A B) w = fieldSub (wordField A w) (wordField B w) := by
  simp only [fieldSub, wordField_add, wordField_neg]

theorem wordBound_sub {m : ℕ} {M N : ℝ} {A B : SmoothL2Field Space}
    (hA : WordBound m M A) (hB : WordBound m N B) : WordBound m (M+N) (fieldSub A B) := by
  intro n hn w
  rw [wordField_sub, toLp_fieldSub]
  exact (norm_sub_le _ _).trans (add_le_add (hA n hn w) (hB n hn w))

end ClockBarrier.Analysis.Sobolev
