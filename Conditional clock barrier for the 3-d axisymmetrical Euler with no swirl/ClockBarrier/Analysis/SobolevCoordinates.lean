/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd.
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: focused imports, namespaces, module interface and pinned Mathlib compatibility.
-/
module
public import ClockBarrier.Analysis.SmoothL2Algebra
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # Finite coordinate and L² domination estimates
Extracted from EulerProof.lean and GevreyProductLp.lean.
-/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Sobolev
open MeasureTheory Filter
/-- The operator norm of a derivative tensor is bounded by the sum of its coordinate entries. -/
theorem multilinear_norm_le_coordinate_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (d n : ℕ) (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => EuclideanSpace ℝ (Fin d)) F) :
    ‖T‖ ≤ ∑ w : Fin n → Fin d,
      ‖T (fun j => EuclideanSpace.single (w j) 1)‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro m
  have hm (j : Fin n) : (∑ i : Fin d, (m j i) • EuclideanSpace.single i (1 : ℝ)) = m j := by
    ext i
    simp [Pi.single_apply, mul_ite]
  have hexpand : T m = ∑ w : Fin n → Fin d,
      T (fun j => (m j (w j)) • EuclideanSpace.single (w j) (1 : ℝ)) := by
    change T.toMultilinearMap m = ∑ w : Fin n → Fin d,
      T.toMultilinearMap (fun j => (m j (w j)) • EuclideanSpace.single (w j) (1 : ℝ))
    have h := T.toMultilinearMap.map_sum
      (fun (j : Fin n) (i : Fin d) => (m j i) • EuclideanSpace.single i (1 : ℝ))
    simpa only [hm] using h
  rw [hexpand]
  calc
    _ ≤ ∑ w : Fin n → Fin d,
        ‖T (fun j => (m j (w j)) • EuclideanSpace.single (w j) (1 : ℝ))‖ := norm_sum_le _ _
    _ = ∑ w : Fin n → Fin d, (∏ j, ‖m j (w j)‖) *
        ‖T (fun j => EuclideanSpace.single (w j) (1 : ℝ))‖ := by
      apply Finset.sum_congr rfl
      intro w _
      rw [T.map_smul_univ, norm_smul, norm_prod]
    _ ≤ ∑ w : Fin n → Fin d, (∏ j, ‖m j‖) *
        ‖T (fun j => EuclideanSpace.single (w j) (1 : ℝ))‖ := by
      apply Finset.sum_le_sum
      intro w _
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => PiLp.norm_apply_le (m j) (w j))
    _ = _ := by rw [← Finset.mul_sum]; ring


variable {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]
theorem finite_domination {ι : Type*} (μ : Measure X) (I : Finset ι)
    (f : X → V) (hf : AEStronglyMeasurable f μ) (H : ι → X → ℝ)
    (hH : ∀ i ∈ I, MemLp (H i) 2 μ)
    (hdom : ∀ x, ‖f x‖ ≤ ∑ i ∈ I, H i x) :
    MemLp f 2 μ ∧ (eLpNorm f 2 μ).toReal ≤ ∑ i ∈ I, (eLpNorm (H i) 2 μ).toReal := by
  have hsum : MemLp (fun x => ∑ i ∈ I, H i x) 2 μ := memLp_finsetSum I hH
  have hLp := hsum.mono' hf (Eventually.of_forall hdom)
  refine ⟨hLp,?_⟩
  have he : (fun x => ∑ i ∈ I, H i x) = ∑ i ∈ I, H i := by
    funext x
    simp only [Finset.sum_apply]
  have hn : eLpNorm f 2 μ ≤ ∑ i ∈ I, eLpNorm (H i) 2 μ := by
    apply (eLpNorm_mono_ae_real (Eventually.of_forall hdom)).trans
    rw [he]
    exact eLpNorm_sum_le (fun i hi => (hH i hi).aestronglyMeasurable) (by norm_num)
  have hr := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun i hi => (hH i hi).eLpNorm_ne_top)) hn
  rwa [ENNReal.toReal_sum (fun i hi => (hH i hi).eLpNorm_ne_top)] at hr

end ClockBarrier.Analysis.Sobolev
