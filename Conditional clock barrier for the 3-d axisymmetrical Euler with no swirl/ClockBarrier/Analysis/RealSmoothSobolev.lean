/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd.
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: focused imports, namespaces, module interface and pinned Mathlib compatibility.
-/
module
public import ClockBarrier.Analysis.SmoothSobolev

/-! # Real vector-valued Sobolev embedding via isometric complexification
Extracted from Euler/EulerProof.lean.
-/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.SmoothSobolev
open MeasureTheory FourierSobolev
open scoped ContDiff
/-- Coordinatewise complexification is an actual linear isometry of Euclidean spaces. -/
noncomputable def complexify (q : ℕ) :
    Domain q →ₗᵢ[ℝ] EuclideanSpace ℂ (Fin q) where
  toFun x := WithLp.toLp 2 (fun i => (x i : ℂ))
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp [Complex.real_smul]
  norm_map' x := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp

/-- The physical tensor Sobolev norm for real Euclidean vector fields. -/
noncomputable def realTensorSobolevNorm (q s : ℕ) (f : Domain 3 → Domain q) : ℝ :=
  Finset.sum (Finset.range (s+1)) (fun j => (eLpNorm (iteratedFDeriv ℝ j f) 2 volume).toReal)

theorem complexification_tensor_norm (q j : ℕ) (f : Domain 3 → Domain q)
    (hf : ContDiff ℝ ∞ f) (x : Domain 3) :
    ‖iteratedFDeriv ℝ j (complexify q ∘ f) x‖ = ‖iteratedFDeriv ℝ j f x‖ :=
  (complexify q).norm_iteratedFDeriv_comp_left hf.contDiffAt (WithTop.coe_le_coe.mpr le_top)

theorem complexification_tensor_memLp (q j : ℕ) (f : Domain 3 → Domain q)
    (hf : ContDiff ℝ ∞ f) (hfL2 : MemLp (iteratedFDeriv ℝ j f) 2 volume) :
    MemLp (iteratedFDeriv ℝ j (complexify q ∘ f)) 2 volume := by
  have hc : Continuous (iteratedFDeriv ℝ j (complexify q ∘ f)) :=
    ((complexify q).contDiff.comp hf).continuous_iteratedFDeriv (m := j) (WithTop.coe_le_coe.mpr le_top)
  apply hfL2.of_le hc.aestronglyMeasurable
  filter_upwards [] with x
  exact (complexification_tensor_norm q j f hf x).le

theorem complexification_sobolevNorm (q s : ℕ) (f : Domain 3 → Domain q)
    (hf : ContDiff ℝ ∞ f) :
    tensorSobolevNorm s (complexify q ∘ f) = realTensorSobolevNorm q s f := by
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact eLpNorm_congr_norm_ae (Filter.Eventually.of_forall (complexification_tensor_norm q j f hf))

end ClockBarrier.Analysis.SmoothSobolev
