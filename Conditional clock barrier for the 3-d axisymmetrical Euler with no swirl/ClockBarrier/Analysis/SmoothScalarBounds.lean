/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd.
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: focused imports, namespaces, module interface and pinned Mathlib compatibility.
-/
module
public import ClockBarrier.Analysis.SmoothWordBounds

/-! # Pointwise Sobolev bounds for real scalar fields
The real scalar instance of the same complexification and localization proof.
-/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Sobolev
open MeasureTheory SmoothL2Field SmoothSobolev FourierSobolev Finset
open scoped ContDiff
local notation "Space" => EuclideanSpace ℝ (Fin 3)
theorem scalar_complexification_tensor_norm (j : ℕ) (f : Domain 3 → ℝ)
    (hf : ContDiff ℝ ∞ f) (x : Domain 3) :
    ‖iteratedFDeriv ℝ j (Complex.ofRealLI ∘ f) x‖ = ‖iteratedFDeriv ℝ j f x‖ :=
  Complex.ofRealLI.norm_iteratedFDeriv_comp_left hf.contDiffAt (WithTop.coe_le_coe.mpr le_top)

theorem scalar_complexification_tensor_memLp (j : ℕ) (f : Domain 3 → ℝ)
    (hf : ContDiff ℝ ∞ f) (hfL2 : MemLp (iteratedFDeriv ℝ j f) 2 volume) :
    MemLp (iteratedFDeriv ℝ j (Complex.ofRealLI ∘ f)) 2 volume := by
  have hc : Continuous (iteratedFDeriv ℝ j (Complex.ofRealLI ∘ f)) :=
    (Complex.ofRealLI.contDiff.comp hf).continuous_iteratedFDeriv (m := j) (WithTop.coe_le_coe.mpr le_top)
  apply hfL2.of_le hc.aestronglyMeasurable
  filter_upwards [] with x
  exact (scalar_complexification_tensor_norm j f hf x).le

theorem scalar_complexification_sobolevNorm (s : ℕ) (f : Domain 3 → ℝ)
    (hf : ContDiff ℝ ∞ f) :
    tensorSobolevNorm s (Complex.ofRealLI ∘ f) = (∑ j ∈ Finset.range (s+1), (eLpNorm (iteratedFDeriv ℝ j f) 2 volume).toReal) := by
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact eLpNorm_congr_norm_ae (Filter.Eventually.of_forall (scalar_complexification_tensor_norm j f hf))

theorem scalar_pointwise_H2 (A : SmoothL2Field ℝ) (x : Space) :
    ‖A.field x‖ ≤ smoothEmbeddingConstant*(∑ j ∈ range 3, ‖A.jetLp j‖) := by
  have hb := smooth_pointwise_le_H2 (Complex.ofRealLI ∘ A.field)
    (Complex.ofRealLI.contDiff.comp A.smooth)
    (fun j _ => scalar_complexification_tensor_memLp j A.field A.smooth (A.integrable j)) x
  rw [Function.comp_apply,Complex.ofRealLI.norm_map,
    scalar_complexification_sobolevNorm 2 A.field A.smooth] at hb
  simpa only [norm_jetLp] using hb

theorem scalar_iteratedFDeriv_bounded (A : SmoothL2Field ℝ) (n : ℕ) :
    ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ n A.field x‖ ≤ C := by
  refine ⟨∑ w : Fin n → Fin 3,
    smoothEmbeddingConstant * (∑ j ∈ range 3, ‖(wordField A w).jetLp j‖), ?_⟩
  intro x
  apply (multilinear_norm_le_coordinate_sum 3 n (iteratedFDeriv ℝ n A.field x)).trans
  exact sum_le_sum (fun w _ => by simpa only [wordField_field, DirectionalWords.wordDerivative, axis] using scalar_pointwise_H2 (wordField A w) x)

end ClockBarrier.Analysis.Sobolev
