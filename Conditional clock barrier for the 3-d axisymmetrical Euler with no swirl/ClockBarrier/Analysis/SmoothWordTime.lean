/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.SmoothTameEnergy
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Strong time derivatives of ordinary spatial words and their energy

The word operator is evaluation of the actual spatial tensor jet, with no
auxiliary Sobolev-space representation.
-/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Sobolev
open MeasureTheory ContinuousLinearMap SmoothL2Field DirectionalWords Finset
open scoped ContDiff
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def wordJetEvaluation {n : ℕ} (w : Fin n → Fin 3) : (E₃ [×n]→L[ℝ] V) →L[ℝ] V :=
  ({ toFun := fun A : E₃ [×n]→L[ℝ] V => A (fun j => axis (w j))
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : (E₃ [×n]→L[ℝ] V) →ₗ[ℝ] V).mkContinuous 1 (by
    intro A
    change ‖A (fun j => axis (w j))‖ ≤ 1 * ‖A‖
    simpa only [axis_norm, prod_const_one, mul_one, one_mul] using
      (A.le_opNorm (fun j => axis (w j))))

def wordJetMap {n : ℕ} (w : Fin n → Fin 3) :
    Lp (E₃ [×n]→L[ℝ] V) 2 (volume : Measure E₃) →L[ℝ] Lp V 2 (volume : Measure E₃) :=
  (wordJetEvaluation w).compLpL 2 volume

theorem wordJetMap_apply (A : SmoothL2Field V) {n : ℕ} (w : Fin n → Fin 3) :
    wordJetMap w (A.jetLp n) = (wordField A w).toLp := by
  apply Lp.ext
  filter_upwards [(wordJetEvaluation (V := V) w).coeFn_compLpL (A.jetLp n),
    A.jetLp_ae n, (wordField A w).toLp_ae] with x he hj hw
  rw [hw, wordField_field]
  exact he.trans (congrArg (wordJetEvaluation w) hj)

variable {K : Type*} [TopologicalSpace K]

theorem continuous_word_toLp (A : K → SmoothL2Field V) {n : ℕ} (w : Fin n → Fin 3)
    (hA : Continuous (fun t => (A t).jetLp n)) :
    Continuous (fun t => (wordField (A t) w).toLp) := by
  simpa only [Function.comp_def, wordJetMap_apply] using (wordJetMap w).continuous.comp hA

theorem word_hasDerivAt {A : ℝ → SmoothL2Field V} {B : SmoothL2Field V} {t : ℝ}
    {n : ℕ} (w : Fin n → Fin 3)
    (hA : HasDerivAt (fun s => (A s).jetLp n) (B.jetLp n) t) :
    HasDerivAt (fun s => (wordField (A s) w).toLp) (wordField B w).toLp t := by
  simpa only [Function.comp_def, wordJetMap_apply] using
    (wordJetMap w).hasFDerivAt.comp_hasDerivAt t hA

theorem wordEnergy_continuous (A : K → SmoothL2Field V)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) (m : ℕ) :
    Continuous (fun t => wordEnergy m (A t)) := by
  exact continuous_finsetSum _ (fun n _ => continuous_finsetSum _
    (fun w _ => (continuous_word_toLp A w (hA n)).norm.pow 2))

theorem wordEnergy_hasDerivAt {A : ℝ → SmoothL2Field E₃} {B : SmoothL2Field E₃}
    {t : ℝ} (hA : ∀ n, HasDerivAt (fun s => (A s).jetLp n) (B.jetLp n) t) (m : ℕ) :
    HasDerivAt (fun s => wordEnergy m (A s)) (integerEnergyProduction m (A t) B) t := by
  have hw (n : ℕ) (w : Fin n → Fin 3) := (word_hasDerivAt w (hA n)).norm_sq
  have hs := HasDerivAt.fun_sum (u := range (m+1))
    (fun n _ => HasDerivAt.fun_sum (u := univ) (fun w _ => hw n w))
  simpa only [wordEnergy, integerEnergyProduction, ← Finset.mul_sum] using hs

end ClockBarrier.Analysis.Sobolev
