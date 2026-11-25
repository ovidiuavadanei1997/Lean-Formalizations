/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd.
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: focused imports, namespaces, module interface and pinned Mathlib compatibility.
-/
module
public import ClockBarrier.Analysis.FourierSobolev
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Whole-space H² embedding by compact localization
Extracted from Euler/EulerProof.lean.
-/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.SmoothSobolev
open MeasureTheory FourierTransform FourierSobolev
open scoped SchwartzMap ENNReal NNReal ContDiff Topology LineDeriv
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
/-- The sum of the actual L² norms of Fréchet derivatives through order `s`. -/
noncomputable def tensorSobolevNorm (s : ℕ) (f : Domain 3 → F) : ℝ :=
  Finset.sum (Finset.range (s+1)) (fun j => (eLpNorm (iteratedFDeriv ℝ j f) 2 volume).toReal)

omit [CompleteSpace F] in
theorem tensorSobolevNorm_nonneg (s : ℕ) (f : Domain 3 → F) : 0 ≤ tensorSobolevNorm s f :=
  Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)

omit [CompleteSpace F] in
theorem tensorSobolevNorm_mono {s t : ℕ} (hst : s ≤ t) (f : Domain 3 → F) :
    tensorSobolevNorm s f ≤ tensorSobolevNorm t f :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => ENNReal.toReal_nonneg)

/-- Sum of the pointwise norms of all derivatives through a fixed order. -/
noncomputable def derivativeMagnitude (s : ℕ) (f : Domain 3 → F) (x : Domain 3) : ℝ :=
  Finset.sum (Finset.range (s+1)) (fun j => ‖iteratedFDeriv ℝ j f x‖)

omit [CompleteSpace F] in
theorem derivativeMagnitude_nonneg (s : ℕ) (f : Domain 3 → F) (x : Domain 3) :
    0 ≤ derivativeMagnitude s f x := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

omit [CompleteSpace F] in
theorem derivativeMagnitude_memLp (s : ℕ) (f : Domain 3 → F)
    (hfL2 : ∀ j ≤ s, MemLp (iteratedFDeriv ℝ j f) 2 volume) :
    MemLp (derivativeMagnitude s f) 2 volume :=
  memLp_finsetSum _ (fun j hj => (hfL2 j (by have := Finset.mem_range.1 hj; omega)).norm)

omit [CompleteSpace F] in
theorem derivativeMagnitude_L2_le (s : ℕ) (f : Domain 3 → F)
    (hfL2 : ∀ j ≤ s, MemLp (iteratedFDeriv ℝ j f) 2 volume) :
    ‖(derivativeMagnitude_memLp s f hfL2).toLp (derivativeMagnitude s f)‖ ≤ tensorSobolevNorm s f := by
  have he : derivativeMagnitude s f = ∑ j ∈ Finset.range (s+1), fun x => ‖iteratedFDeriv ℝ j f x‖ := by
    funext x
    simp [derivativeMagnitude]
  have hA : eLpNorm (derivativeMagnitude s f) 2 volume ≤
      ∑ j ∈ Finset.range (s+1), eLpNorm (iteratedFDeriv ℝ j f) 2 volume := by
    rw [he]
    simpa only [eLpNorm_norm] using eLpNorm_sum_le (fun j hj =>
      (hfL2 j (by have := Finset.mem_range.1 hj; omega)).1.norm) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hfin (j : ℕ) (hj : j ∈ Finset.range (s+1)) : eLpNorm (iteratedFDeriv ℝ j f) 2 volume ≠ ⊤ :=
    (hfL2 j (by have := Finset.mem_range.1 hj; omega)).eLpNorm_ne_top
  have hB := ENNReal.toReal_mono (ENNReal.sum_ne_top.2 hfin) hA
  rw [ENNReal.toReal_sum hfin] at hB
  rw [Lp.norm_toLp]
  exact hB

/-- A fixed bump equal to one near zero, independent of the function being estimated. -/
noncomputable def unitBump : ContDiffBump (0 : Domain 3) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The same fixed bump as a Schwartz function. -/
noncomputable def unitBumpSchwartz : 𝓢(Domain 3, ℝ) :=
  unitBump.hasCompactSupport.toSchwartzMap unitBump.contDiff

/-- A finite derivative bound for the fixed bump. -/
noncomputable def unitBumpBound (j : ℕ) : NNReal :=
  ⟨SchwartzMap.seminorm ℝ 0 j unitBumpSchwartz, apply_nonneg _ _⟩

/-- The finite Leibniz coefficient for localizing an order `n` derivative. -/
noncomputable def unitBumpCoefficient (n : ℕ) : NNReal :=
  Finset.sum (Finset.range (n+1)) (fun j => (n.choose j : ℝ≥0) * unitBumpBound j)

/-- An actual smooth compact localization of an arbitrary smooth function about `x`. -/
noncomputable def localize (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f) (x : Domain 3) : 𝓢(Domain 3, F) :=
  (unitBump.hasCompactSupport.smul_right (f' := fun z => f (x+z))).toSchwartzMap
    (unitBump.contDiff.smul (hf.comp (contDiff_const.add contDiff_id)))

omit [CompleteSpace F] in
@[simp] theorem localize_apply (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f) (x z : Domain 3) :
    localize f hf x z = unitBump z • f (x+z) := rfl

omit [CompleteSpace F] in
theorem localize_zero (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f) (x : Domain 3) :
    localize f hf x 0 = f x := by
  rw [localize_apply, unitBump.one_of_mem_closedBall (by simp [unitBump]), one_smul, add_zero]

omit [CompleteSpace F] in
/-- Localization obeys the actual tensor Leibniz estimate. -/
theorem localize_tensor_bound (n : ℕ) (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f) (x z : Domain 3) :
    ‖iteratedFDeriv ℝ n (localize f hf x) z‖ ≤
      (unitBumpCoefficient n : ℝ) * derivativeMagnitude n f (x+z) := by
  have hshift : ContDiff ℝ ∞ (fun z => f (x+z)) := hf.comp (contDiff_const.add contDiff_id)
  have hA := norm_iteratedFDeriv_smul_le unitBump.contDiff
    hshift z (WithTop.coe_le_coe.mpr le_top : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  apply hA.trans
  have hb (j : ℕ) : ‖iteratedFDeriv ℝ j unitBump z‖ ≤ unitBumpBound j :=
    SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ unitBumpSchwartz j z
  have hd (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      ‖iteratedFDeriv ℝ (n-j) (fun z => f (x+z)) z‖ ≤ derivativeMagnitude n f (x+z) := by
    rw [iteratedFDeriv_comp_add_left]
    exact Finset.single_le_sum (f := fun k => ‖iteratedFDeriv ℝ k f (x+z)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  calc
    _ ≤ ∑ j ∈ Finset.range (n+1), ((n.choose j : ℝ) * unitBumpBound j) * derivativeMagnitude n f (x+z) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hb j) (Nat.cast_nonneg _)) (hd j hj)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (unitBumpBound j).coe_nonneg)
    _ = _ := by simp only [unitBumpCoefficient, NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_natCast, Finset.sum_mul]

omit [CompleteSpace F] in
/-- Each localized pure derivative is controlled by the global physical Sobolev norm. -/
theorem localize_pureDerivative_L2_le (n : ℕ) (i : Fin 3) (f : Domain 3 → F)
    (hf : ContDiff ℝ ∞ f) (hfL2 : ∀ j ≤ n, MemLp (iteratedFDeriv ℝ j f) 2 volume) (x : Domain 3) :
    ‖(pureDerivative 3 n (EuclideanSpace.single i 1) (localize f hf x)).toLp 2‖ ≤
      (unitBumpCoefficient n : ℝ) * tensorSobolevNorm n f := by
  have hq := derivativeMagnitude_memLp n f hfL2
  have htrans := measurePreserving_add_left (volume : Measure (Domain 3)) x
  have hqt : MemLp (fun z => derivativeMagnitude n f (x+z)) 2 volume := hq.comp_measurePreserving htrans
  have hb (z : Domain 3) :
      ‖pureDerivative 3 n (EuclideanSpace.single i 1) (localize f hf x) z‖ ≤
        (unitBumpCoefficient n : ℝ) * ‖derivativeMagnitude n f (x+z)‖ := by
    rw [pureDerivative, SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv,
      Real.norm_of_nonneg (derivativeMagnitude_nonneg n f (x+z))]
    have hA := (iteratedFDeriv ℝ n (localize f hf x) z).le_opNorm
      (fun _ : Fin n => EuclideanSpace.single i (1 : ℝ))
    simp only [PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one] at hA
    exact hA.trans (localize_tensor_bound n f hf x z)
  have hA := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (μ := (volume : Measure (Domain 3)))
    (Filter.Eventually.of_forall hb) 2
  have hfin : (unitBumpCoefficient n : ℝ≥0∞) *
      eLpNorm (fun z => derivativeMagnitude n f (x+z)) 2 volume ≠ ⊤ := by finiteness
  have hB := ENNReal.toReal_mono hfin hA
  have he : eLpNorm (fun z => derivativeMagnitude n f (x+z)) 2 volume =
      eLpNorm (derivativeMagnitude n f) 2 volume := by
    simpa only [Function.comp_def] using eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞)) hq.1 htrans
  rw [he] at hB
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal] at hB
  rw [SchwartzMap.norm_toLp]
  have hC := mul_le_mul_of_nonneg_left (derivativeMagnitude_L2_le n f hfL2) (unitBumpCoefficient n).coe_nonneg
  rw [Lp.norm_toLp] at hC
  exact hB.trans hC

/-- A fixed finite three-dimensional H² embedding constant. -/
noncomputable def smoothEmbeddingConstant : ℝ :=
  embeddingConstant 3 2 (by norm_num) *
    ((unitBumpCoefficient 0 : ℝ) + (2 * Real.pi)^(-2 : ℤ) * 3 * unitBumpCoefficient 2)

theorem smoothEmbeddingConstant_nonneg : 0 ≤ smoothEmbeddingConstant := by
  have h : 0 ≤ embeddingConstant 3 2 (by norm_num) := norm_nonneg _
  unfold smoothEmbeddingConstant
  positivity

/-- Genuine H² to L∞ embedding for every smooth Hilbert-valued function on R³. -/
theorem smooth_pointwise_le_H2 (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f)
    (hfL2 : ∀ j ≤ 2, MemLp (iteratedFDeriv ℝ j f) 2 volume) (x : Domain 3) :
    ‖f x‖ ≤ smoothEmbeddingConstant * tensorSobolevNorm 2 f := by
  have hzero := localize_pureDerivative_L2_le 0 0 f hf (fun j hj => hfL2 j (by omega)) x
  have he : pureDerivative 3 0 (EuclideanSpace.single 0 1) (localize f hf x) = localize f hf x := by
    ext z
    simp [pureDerivative]
  rw [he] at hzero
  have hzero' := hzero.trans (mul_le_mul_of_nonneg_left (tensorSobolevNorm_mono (show 0 ≤ 2 by omega) f)
    (unitBumpCoefficient 0).coe_nonneg)
  have htwo : (∑ i : Fin 3, ‖(pureDerivative 3 2 (EuclideanSpace.single i 1) (localize f hf x)).toLp 2‖) ≤
      3 * ((unitBumpCoefficient 2 : ℝ) * tensorSobolevNorm 2 f) := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
      localize_pureDerivative_L2_le 2 i f hf hfL2 x)
  have hA := pointwise_le_L2_second_derivatives (localize f hf x) 0
  rw [localize_zero] at hA
  have hB := add_le_add hzero' (mul_le_mul_of_nonneg_left htwo
    (zpow_nonneg (by positivity : (0 : ℝ) ≤ 2*Real.pi) (-2 : ℤ)))
  have hC := mul_le_mul_of_nonneg_left hB (show 0 ≤ embeddingConstant 3 2 (by norm_num) from norm_nonneg _)
  have harith (C A B p S : ℝ) : C * (A*S+p*(3*(B*S))) = (C*(A+p*3*B))*S := by ring
  exact hA.trans (hC.trans_eq (harith _ _ _ _ _))

end ClockBarrier.Analysis.SmoothSobolev
