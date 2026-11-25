/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.SmoothPaths
public import ClockBarrier.Analysis.SmoothWordReassembly
public import ClockBarrier.Analysis.BoundedLpOperator
import Mathlib.MeasureTheory.Function.Holder

/-! # Continuity of actual product and advection jets in L² -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Sobolev
open MeasureTheory ContinuousLinearMap SmoothL2Field Filter
open scoped ContDiff BoundedContinuousFunction ENNReal Topology
local notation "Space" => EuclideanSpace ℝ (Fin 3)
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def scalarLpProduct : (Space →ᵇ ℝ) →L[ℝ] Lp V 2 (volume : Measure Space) →L[ℝ] Lp V 2 (volume : Measure Space) :=
  ((lsmul ℝ ℝ).holderL (volume : Measure Space) ∞ 2 2).comp boundedToLpTop

theorem scalarProduct_toLp (A : SmoothL2Field ℝ) (B : SmoothL2Field V) :
    (scalarProduct A B).toLp = scalarLpProduct (scalarField A) B.toLp := by
  apply Lp.ext
  filter_upwards [(scalarProduct A B).toLp_ae, B.toLp_ae,
    (lsmul ℝ ℝ).coeFn_holder (r := 2) (boundedToLpTop (scalarField A)) B.toLp,
    ((scalarField A).memLp_top (μ := volume)).coeFn_toLp] with x hp hb he ha
  rw [hp, scalarProduct_field]
  exact (congrArg₂ (fun a : ℝ => fun b : V => a • b) ha hb).symm.trans he.symm

variable {K : Type*} [TopologicalSpace K]

theorem continuous_scalarProduct_toLp (A : K → SmoothL2Field ℝ) (B : K → SmoothL2Field V)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
    (hB : ∀ n, Continuous (fun t => (B t).jetLp n)) :
    Continuous (fun t => (scalarProduct (A t) (B t)).toLp) := by
  simp_rw [scalarProduct_toLp]
  exact (scalarLpProduct.continuous.comp (continuous_scalarField A hA)).clm_apply
    (continuous_toLp B (hB 0))

theorem continuous_word_scalarProduct (A : K → SmoothL2Field ℝ) (B : K → SmoothL2Field V)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
    (hB : ∀ n, Continuous (fun t => (B t).jetLp n)) {n : ℕ} (w : Fin n → Fin 3) :
    Continuous (fun t => (wordField (scalarProduct (A t) (B t)) w).toLp) := by
  induction n generalizing A B with
  | zero => simpa only [wordField_zero] using continuous_scalarProduct_toLp A B hA hB
  | succ n ih =>
    have he (t : K) : wordField (scalarProduct (A t) (B t)) w =
        addField
          (wordField (scalarProduct ((A t).directionalField (axis (w (Fin.last n)))) (B t)) (Fin.init w))
          (wordField (scalarProduct (A t) ((B t).directionalField (axis (w (Fin.last n))))) (Fin.init w)) := by
      conv_lhs => rw [← Fin.snoc_init_self w, wordField_snoc, scalarProduct_directional, wordField_add]
    simp_rw [he, toLp_addField]
    exact (ih (fun t => (A t).directionalField (axis (w (Fin.last n)))) B
      (continuous_jetLp_directionalField A hA _) hB (Fin.init w)).add
      (ih A (fun t => (B t).directionalField (axis (w (Fin.last n)))) hA
        (continuous_jetLp_directionalField B hB _) (Fin.init w))

variable [FiniteDimensional ℝ V]

theorem continuous_scalarProduct_jet (A : K → SmoothL2Field ℝ) (B : K → SmoothL2Field V)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
    (hB : ∀ n, Continuous (fun t => (B t).jetLp n)) (n : ℕ) :
    Continuous (fun t => (scalarProduct (A t) (B t)).jetLp n) := by
  simp_rw [jetLp_eq_word_reassembly]
  exact (L2Tensor.tensorLpReassembly (volume : Measure Space) n).continuous.comp
    (continuous_pi (fun w => continuous_word_scalarProduct A B hA hB w))

theorem continuous_advectionField_jet (A : K → SmoothL2Field Space) (B : K → SmoothL2Field V)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
    (hB : ∀ n, Continuous (fun t => (B t).jetLp n)) (n : ℕ) :
    Continuous (fun t => (advectionField (A t) (B t)).jetLp n) := by
  simp_rw [jetLp_eq_word_reassembly, advectionField, wordField_sum, toLp_sumField]
  apply (L2Tensor.tensorLpReassembly (volume : Measure Space) n).continuous.comp
  apply continuous_pi
  intro w
  apply continuous_finsetSum
  intro i _
  exact continuous_word_scalarProduct (fun t => mapField (EuclideanSpace.proj i) (A t))
    (fun t => (B t).directionalField (axis i))
    (continuous_jetLp_mapField _ A hA) (continuous_jetLp_directionalField B hB _) w

end ClockBarrier.Analysis.Sobolev
