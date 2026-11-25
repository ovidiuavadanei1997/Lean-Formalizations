/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd.
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: concrete regularizer, direct projected L² right-hand side and coordinate gradient constant.
-/
module
public import ClockBarrier.Analysis.RegularizerApproximation
public import ClockBarrier.Analysis.SmoothAdvectionBounds
public import ClockBarrier.Euler.RegularizedEnergyProduction

/-! # The regularization defect tends to zero uniformly on bounded H⁴ sets -/
@[expose] public noncomputable section
namespace ClockBarrier.Euler.Regularized
open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap ClockBarrier.Analysis
  Solenoidal SmoothL2Field Sobolev SmoothSobolev Finset
open scoped ContDiff Topology
local notation "Space" => EuclideanSpace ℝ (Fin 3)

/-- The literal Helmholtz projection of the actual advective nonlinearity. -/
def projectedRhsL2 (A : SmoothL2Field Space) : L2 :=
  -solenoidalProjection (advectionField A A).toLp

theorem regularizer_error_words (n : ℕ) (A : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) (q : ℕ) (M : ℝ) (hM : WordBound (q+1) M A) :
    WordBound q (regularizerError n*M) (fieldSub (regularizedSmoothField n A.toLp) A) := by
  intro k hk w
  simp only [fieldSub,wordField_add,wordField_neg,toLp_addField,toLp_fieldNeg,
    regularizedSmoothField_word,← sub_eq_add_neg]
  have hp : solenoidalProjection (wordField A w).toLp=(wordField A w).toLp :=
    solenoidalSpace.starProjection_eq_self_iff.mpr (word_solenoidal A hA w)
  have h := regularizer_error_wordBound n (wordField A w) M
    (wordBound_wordField (wordBound_mono hM (by omega : k+1 ≤ q+1)) w)
  simpa only [hp] using h

theorem advection_low_words (A : SmoothL2Field Space) (M : ℝ) (hM : WordBound 4 M A) :
    WordBound 1 (6*h3ProductConstant*M^2) (advectionField A A) := by
  intro k hk w
  apply (source_advection_outer A A M M (wordBound_mono hM (by omega)) hM (by omega) w).trans
  have hcoef : 3*(2 : ℝ)^k ≤ 6 := by interval_cases k <;> norm_num
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef h3ProductConstant_nonneg) (wordBound_nonneg hM))
    (wordBound_nonneg hM)).trans_eq (by ring)

def regularizationCost (M : ℝ) : ℝ := (6*h3ProductConstant+78*smoothEmbeddingConstant)*M^2

theorem regularizationCost_nonneg (M : ℝ) : 0 ≤ regularizationCost M := by
  have := h3ProductConstant_nonneg
  have := smoothEmbeddingConstant_nonneg
  unfold regularizationCost
  positivity

theorem regularized_rhs_error (n : ℕ) (A : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) (M : ℝ) (hM : WordBound 4 M A) :
    ‖(smoothRhs n A).toLp-projectedRhsL2 A‖ ≤
      regularizerError n*regularizationCost M := by
  let B := regularizedSmoothField n A.toLp
  have hB : WordBound 4 M B := regularizedSmoothField_wordBound n A 4 M hM
  have he := regularizer_error_words n A hA 1 M (wordBound_mono hM (by omega))
  have he0 : ‖B.toLp-A.toLp‖ ≤ regularizerError n*M := by
    simpa only [toLp_fieldSub] using wordBound_toLp he
  have he1 : ‖B.jetLp 1-A.jetLp 1‖ ≤ 3*(regularizerError n*M) := by
    simpa only [jetLp_fieldSub,pow_one] using wordBound_jet_norm he (le_refl 1)
  have hadv : ‖(advectionField B B).toLp-(advectionField A A).toLp‖ ≤
      ((39*smoothEmbeddingConstant)*M)*(regularizerError n*M)+
      ((13*smoothEmbeddingConstant)*M)*(3*(regularizerError n*M)) := by
    apply (advection_sub_norm B A _ _ (wordBound_gradient (wordBound_mono hB (by omega)))
      (wordBound_pointwise (wordBound_mono hM (by omega)))).trans
    exact add_le_add (mul_le_mul_of_nonneg_left he0
      (mul_nonneg (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg) (wordBound_nonneg hM)))
      (mul_le_mul_of_nonneg_left he1
      (mul_nonneg (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg) (wordBound_nonneg hM)))
  have hp := regularizer_error_wordBound n (advectionField B B) _ (advection_low_words B M hB)
  have hq : ‖solenoidalProjection (advectionField B B).toLp-
      solenoidalProjection (advectionField A A).toLp‖ ≤
      ‖(advectionField B B).toLp-(advectionField A A).toLp‖ := by
    rw [← map_sub]
    exact solenoidalProjection_apply_norm_le _
  have heq : (smoothRhs n A).toLp-projectedRhsL2 A=
      -(regularizerMap n (advectionField B B).toLp-solenoidalProjection (advectionField A A).toLp) := by
    simp only [smoothRhs_toLp, quadratic_apply, projectedRhsL2, B, advection_toLp]
    abel
  rw [heq,norm_neg]
  apply (norm_sub_le_norm_sub_add_norm_sub (regularizerMap n (advectionField B B).toLp)
    (solenoidalProjection (advectionField B B).toLp)
    (solenoidalProjection (advectionField A A).toLp)).trans
  exact (add_le_add hp (hq.trans hadv)).trans_eq (by unfold regularizationCost; ring)

end ClockBarrier.Euler.Regularized
