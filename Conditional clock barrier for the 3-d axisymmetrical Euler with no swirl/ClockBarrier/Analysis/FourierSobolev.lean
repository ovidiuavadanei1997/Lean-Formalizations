/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd.
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: focused imports, namespaces, module interface and pinned Mathlib compatibility.
-/
module
public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Fourier proof of the H² pointwise estimate
Extracted from the ordinary Sobolev sections of Euler/EulerProof.lean.
-/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.FourierSobolev
open MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff LineDeriv
section
/-- The real Euclidean domain of dimension `d`. -/
abbrev Domain (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Fourier weight defining the inhomogeneous Sobolev order `s`. -/
noncomputable def besselWeight (d : ℕ) (s : ℝ) (ξ : Domain d) : ℝ :=
  (1 + ‖ξ‖ ^ 2) ^ (s / 2)

theorem besselWeight_temperate (d : ℕ) (s : ℝ) :
    (besselWeight d s).HasTemperateGrowth :=
  Function.hasTemperateGrowth_one_add_norm_sq_rpow (Domain d) (s / 2)

theorem besselWeight_pos (d : ℕ) (s : ℝ) (ξ : Domain d) : 0 < besselWeight d s ξ := by
  unfold besselWeight
  positivity

theorem besselWeight_neg_mul (d : ℕ) (s : ℝ) (ξ : Domain d) :
    besselWeight d (-s) ξ * besselWeight d s ξ = 1 := by
  unfold besselWeight
  rw [← Real.rpow_add (by positivity)]
  have he : -s / 2 + s / 2 = 0 := by ring
  rw [he, Real.rpow_zero]

theorem besselWeight_add (d : ℕ) (s t : ℝ) (ξ : Domain d) :
    besselWeight d (s + t) ξ = besselWeight d s ξ * besselWeight d t ξ := by
  unfold besselWeight
  rw [← Real.rpow_add (by positivity)]
  congr 1
  ring

/-- One derivative factor is absorbed by one Sobolev order. -/
theorem besselWeight_mul_norm_le (d : ℕ) (s : ℝ) (ξ : Domain d) :
    besselWeight d s ξ * ‖ξ‖ ≤ besselWeight d (s + 1) ξ := by
  have hn : ‖ξ‖ ≤ besselWeight d 1 ξ := by
    unfold besselWeight
    rw [← Real.sqrt_eq_rpow]
    calc
      ‖ξ‖ = Real.sqrt (‖ξ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg ξ)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
  rw [besselWeight_add]
  exact mul_le_mul_of_nonneg_left hn (besselWeight_pos d s ξ).le

/-- The reciprocal Bessel weight is in L² exactly in the range needed here. -/
theorem reciprocal_weight_memLp (d : ℕ) (s : ℝ) (hs : (d : ℝ) < 2 * s) :
    MemLp (besselWeight d (-s)) 2 (volume : Measure (Domain d)) := by
  have hm : AEStronglyMeasurable (besselWeight d (-s)) (volume : Measure (Domain d)) :=
    (besselWeight_temperate d (-s)).1.continuous.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).2
  have hi : Integrable (fun ξ : Domain d => (1 + ‖ξ‖ ^ 2) ^ (-(2 * s) / 2)) volume :=
    integrable_rpow_neg_one_add_norm_sq (by simpa [Domain] using hs)
  apply hi.congr
  filter_upwards with ξ
  dsimp only [besselWeight]
  rw [← Real.rpow_mul_natCast (by positivity)]
  congr 1
  push_cast
  ring

/-- The reciprocal Fourier weight represented as a genuine `L²` element. -/
noncomputable def reciprocalWeightLp (d : ℕ) (s : ℝ) (hs : (d : ℝ) < 2 * s) :
    Lp ℝ 2 (volume : Measure (Domain d)) :=
  (reciprocal_weight_memLp d s hs).toLp (besselWeight d (-s))

/-- A finite Sobolev embedding constant: the `L²` norm of the reciprocal weight. -/
noncomputable def embeddingConstant (d : ℕ) (s : ℝ) (hs : (d : ℝ) < 2 * s) : ℝ :=
  ‖reciprocalWeightLp d s hs‖

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The Fourier transform multiplied by the Sobolev weight. -/
noncomputable def weightedFourier (d : ℕ) (s : ℝ) (f : 𝓢(Domain d, F)) :
    𝓢(Domain d, F) :=
  SchwartzMap.smulLeftCLM F (besselWeight d s) (𝓕 f)

omit [CompleteSpace F] in
theorem weightedFourier_apply (d : ℕ) (s : ℝ) (f : 𝓢(Domain d, F)) (ξ : Domain d) :
    weightedFourier d s f ξ = besselWeight d s ξ • 𝓕 f ξ := by
  simp [weightedFourier, SchwartzMap.smulLeftCLM_apply_apply (besselWeight_temperate d s)]

/-- The inhomogeneous Fourier `Hˢ` norm of a Schwartz function. -/
noncomputable def sobolevNorm (d : ℕ) (s : ℝ) (f : 𝓢(Domain d, F)) : ℝ :=
  ‖(weightedFourier d s f).toLp 2‖

/-- Fourier inversion bounds a Schwartz function pointwise by the L¹ norm of its transform. -/
theorem norm_apply_le_fourier_L1 (d : ℕ) (f : 𝓢(Domain d, F)) (x : Domain d) :
    ‖f x‖ ≤ ‖(𝓕 f).toLp 1‖ := by
  have h := SchwartzMap.norm_fourier_apply_le_toLp_one (𝓕 f) (-x)
  have he : ‖f x‖ = ‖𝓕 (𝓕 f) (-x)‖ := by
    change ‖f x‖ = ‖(𝓕⁻ (𝓕 f)) x‖
    rw [fourierInv_fourier_eq]
  exact he ▸ h

omit [CompleteSpace F] in
/-- Hölder with the reciprocal weight converts the Fourier L¹ norm into the Hˢ norm. -/
theorem fourier_L1_le_sobolevNorm (d : ℕ) (s : ℝ) (hs : (d : ℝ) < 2 * s)
    (f : 𝓢(Domain d, F)) :
    ‖(𝓕 f).toLp 1‖ ≤ embeddingConstant d s hs * sobolevNorm d s f := by
  have hid : (besselWeight d (-s) • (weightedFourier d s f : Domain d → F)) =
      ((𝓕 f : 𝓢(Domain d, F)) : Domain d → F) := by
    ext ξ
    simp only [Pi.smul_apply', weightedFourier_apply, smul_smul, besselWeight_neg_mul, one_smul]
  have hh := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
    ((weightedFourier d s f).memLp 2 volume).1 (reciprocal_weight_memLp d s hs).1
  rw [hid] at hh
  have hfin : eLpNorm (besselWeight d (-s)) 2 volume *
      eLpNorm (weightedFourier d s f) 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top (reciprocal_weight_memLp d s hs).eLpNorm_ne_top
      ((weightedFourier d s f).memLp 2 volume).eLpNorm_ne_top
  have h := ENNReal.toReal_mono hfin hh
  simpa only [SchwartzMap.norm_toLp, embeddingConstant, reciprocalWeightLp,
    Lp.norm_toLp, sobolevNorm, ENNReal.toReal_mul] using h

/-- A genuine pointwise Sobolev embedding for every `s > d/2`. -/
theorem norm_apply_le_sobolevNorm (d : ℕ) (s : ℝ) (hs : (d : ℝ) < 2 * s)
    (f : 𝓢(Domain d, F)) (x : Domain d) :
    ‖f x‖ ≤ embeddingConstant d s hs * sobolevNorm d s f :=
  (norm_apply_le_fourier_L1 d f x).trans (fourier_L1_le_sobolevNorm d s hs f)

end

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
/-- Repeated directional derivatives of a vector-valued Schwartz function. -/
noncomputable def pureDerivative (d n : ℕ) (v : Domain d) (f : 𝓢(Domain d, F)) :
    𝓢(Domain d, F) := ∂^{fun _ : Fin n => v} f

omit [CompleteSpace F] in
theorem fourier_pureDerivative_norm (d n : ℕ) (v : Domain d)
    (f : 𝓢(Domain d, F)) (ξ : Domain d) :
    ‖𝓕 (pureDerivative d n v f) ξ‖ =
      (2 * Real.pi) ^ n * ‖inner ℝ ξ v‖ ^ n * ‖𝓕 f ξ‖ := by
  induction n with
  | zero => simp [pureDerivative]
  | succ n ih =>
    have ht : (fun ξ : Domain d => inner ℝ ξ v).HasTemperateGrowth :=
      ((innerSL ℝ).flip v).hasTemperateGrowth
    have hd : pureDerivative d (n+1) v f = ∂_{v} (pureDerivative d n v f) := rfl
    rw [hd, SchwartzMap.fourier_lineDerivOp_eq]
    simp only [smul_apply,
      SchwartzMap.smulLeftCLM_apply_apply ht, norm_smul]
    have hc : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      simp [Real.pi_pos.le]
    rw [hc, ih, pow_succ, pow_succ]
    ring

/-- The pointwise norm of a Schwartz function, represented in the real `L²` space. -/
noncomputable def normLp (d : ℕ) (f : 𝓢(Domain d, F)) :
    Lp ℝ 2 (volume : Measure (Domain d)) :=
  (f.memLp 2 volume).norm.toLp (fun x => ‖f x‖)

omit [CompleteSpace F] in
theorem norm_normLp (d : ℕ) (f : 𝓢(Domain d, F)) :
    ‖normLp d f‖ = ‖f.toLp 2‖ := by
  simp only [normLp, Lp.norm_toLp, eLpNorm_norm, SchwartzMap.norm_toLp]

omit [CompleteSpace F] in
theorem coe_normLp (d : ℕ) (f : 𝓢(Domain d, F)) :
    (normLp d f : Domain d → ℝ) =ᵐ[volume] (fun x => ‖f x‖) :=
  (f.memLp 2 volume).norm.coeFn_toLp

omit [CompleteSpace F] in
theorem normLp_le_sum {ι : Type*} [Fintype ι] (d : ℕ) (f : 𝓢(Domain d, F))
    (g : ι → 𝓢(Domain d, F)) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x, ‖f x‖ ≤ C * ∑ i, ‖g i x‖) :
    ‖f.toLp 2‖ ≤ C * ∑ i, ‖(g i).toLp 2‖ := by
  have hs : ∀ᵐ x ∂(volume : Measure (Domain d)), ∀ i, normLp d (g i) x = ‖g i x‖ :=
    Filter.eventually_all.2 (fun i => coe_normLp d (g i))
  have hb : ‖f.toLp 2‖ ≤ C * ‖∑ i, normLp d (g i)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [f.coeFn_toLp 2, Lp.coeFn_finsetSum Finset.univ (fun i => normLp d (g i)), hs]
      with x hf hsum hx
    rw [hf, hsum]
    simp only [Finset.sum_apply, hx, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg _))]
    exact h x
  refine hb.trans ?_
  calc
    _ ≤ C * ∑ i, ‖normLp d (g i)‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hC
    _ = _ := by simp only [norm_normLp]

theorem sobolevNorm_two_le_pure_derivatives (d : ℕ) (f : 𝓢(Domain d, F)) :
    sobolevNorm d 2 f ≤ 1 *
      (‖f.toLp 2‖ + (2 * Real.pi) ^ (-2 : ℤ) *
        ∑ i : Fin d, ‖(pureDerivative d 2 (EuclideanSpace.single i 1) f).toLp 2‖) := by
  let g : Option (Fin d) → 𝓢(Domain d, F) := fun i => match i with
    | none => 𝓕 f
    | some i => ((2 * Real.pi) ^ (-2 : ℤ) : ℝ) •
        𝓕 (pureDerivative d 2 (EuclideanSpace.single i 1) f)
  have hpoint (ξ : Domain d) :
      ‖weightedFourier d 2 f ξ‖ ≤ 1 * ∑ i, ‖g i ξ‖ := by
    rw [weightedFourier_apply, norm_smul, Real.norm_of_nonneg (besselWeight_pos d 2 ξ).le]
    have hg : ∑ i, ‖g i ξ‖ = (1 + ∑ i, ‖ξ i‖ ^ 2) * ‖𝓕 f ξ‖ := by
      rw [Fintype.sum_option]
      simp only [g, smul_apply, norm_smul,
        Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi) ^ (-2 : ℤ)),
        fourier_pureDerivative_norm, EuclideanSpace.inner_single_right,
        starRingEnd_apply, star_trivial]
      have hp : (2 * Real.pi) ^ (-2 : ℤ) * (2 * Real.pi) ^ (2 : ℕ) = 1 := by
        rw [show (-2 : ℤ) = -(2 : ℤ) from rfl, zpow_neg]
        exact inv_mul_cancel₀ (by positivity)
      simp_rw [← mul_assoc, hp, one_mul]
      rw [add_mul, one_mul, Finset.sum_mul]
    rw [hg]
    nlinarith [mul_le_mul_of_nonneg_right (le_of_eq (show besselWeight d 2 ξ = 1 + ∑ i, ‖ξ i‖ ^ 2 by norm_num [besselWeight, EuclideanSpace.norm_sq_eq])) (norm_nonneg (𝓕 f ξ))]
  have h := normLp_le_sum d (weightedFourier d 2 f) g 1
    (by norm_num) hpoint
  have hnorm : ∑ i, ‖(g i).toLp 2‖ = ‖f.toLp 2‖ +
      (2 * Real.pi) ^ (-2 : ℤ) * ∑ i : Fin d,
        ‖(pureDerivative d 2 (EuclideanSpace.single i 1) f).toLp 2‖ := by
    rw [Fintype.sum_option]
    simp only [g]
    change ‖(𝓕 f).toLp 2‖ + ∑ i,
      ‖SchwartzMap.toLpCLM ℝ F 2 volume (((2 * Real.pi) ^ (-2 : ℤ)) •
        𝓕 (pureDerivative d 2 (EuclideanSpace.single i 1) f))‖ = _
    simp only [map_smul, norm_smul,
      Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi) ^ (-2 : ℤ)),
      SchwartzMap.toLpCLM_apply, SchwartzMap.norm_fourier_toL2_eq, Finset.mul_sum]
  rw [hnorm] at h
  exact h

/-- The three-dimensional H² pointwise bound in terms of actual second derivatives. -/
theorem pointwise_le_L2_second_derivatives (f : 𝓢(Domain 3, F)) (x : Domain 3) :
    ‖f x‖ ≤ embeddingConstant 3 2 (by norm_num) *
      (‖f.toLp 2‖ + (2 * Real.pi) ^ (-2 : ℤ) *
        ∑ i : Fin 3, ‖(pureDerivative 3 2 (EuclideanSpace.single i 1) f).toLp 2‖) := by
  have hA := norm_apply_le_sobolevNorm 3 2 (by norm_num) f x
  have hB := mul_le_mul_of_nonneg_left (sobolevNorm_two_le_pure_derivatives 3 f)
    (show 0 ≤ embeddingConstant 3 2 (by norm_num) from norm_nonneg _)
  simpa only [one_mul] using hA.trans hB

end ClockBarrier.Analysis.FourierSobolev
