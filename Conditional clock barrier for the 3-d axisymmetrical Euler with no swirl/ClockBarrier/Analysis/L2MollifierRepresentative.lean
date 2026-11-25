/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd,
Euler/EulerProof.lean, EulerSetIntegralL2 and EulerCoverMollificationFubini.
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: ordinary R³ in place of the cylinder, focused imports and modules.
-/
module

public import ClockBarrier.Analysis.L2Mollifier
public import ClockBarrier.Analysis.L2Convolution
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Pointwise representatives of the concrete L² mollifiers

Finite-set Fubini identifies the Bochner average with classical convolution,
without assuming pointwise evaluation is continuous on L².
-/

@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Solenoidal
open MeasureTheory ContinuousLinearMap
open scoped ENNReal NNReal Topology Convolution ContDiff
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

section SetIntegral
variable {X V : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Integration on a finite-measure set as a genuine bounded linear map on L². -/
def setIntegralL2 (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) : Lp V 2 μ →L[ℝ] V :=
  (ContinuousLinearMap.lsmul ℝ ℝ).lpPairing μ 2 2
    (indicatorConstLp 2 hs hμs (1 : ℝ))

theorem setIntegralL2_apply (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ⊤)
    (f : Lp V 2 μ) : setIntegralL2 s hs hμs f = ∫ x in s, f x ∂μ := by
  rw [setIntegralL2, ContinuousLinearMap.lpPairing_eq_integral]
  calc
    _ = ∫ x, s.indicator (fun y => f y) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := (1 : ℝ))] with x hx
      rw [hx]
      by_cases hxs : x ∈ s
      · simp [hxs]
      · simp [hxs]
    _ = _ := integral_indicator hs

/-- Bochner averaging of L² elements commutes with integration on every finite-measure set. -/
theorem setIntegral_integral_L2 {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ⊤)
    (F : Y → Lp V 2 μ) (hF : Integrable F ν) :
    (∫ x in s, (∫ y, F y ∂ν) x ∂μ) = ∫ y, ∫ x in s, F y x ∂μ ∂ν := by
  rw [← setIntegralL2_apply s hs hμs,
    ← (setIntegralL2 s hs hμs).integral_comp_comm hF]
  simp_rw [setIntegralL2_apply]

end SetIntegral

/-- The elementary L²-to-L¹ bound on an arbitrary finite-measure set. -/
theorem finite_set_integral_norm_le (f : E₃ → E₃)
    (hf : MemLp f 2 ((volume : Measure E₃))) (K : Set (E₃))
    (hK : (volume : Measure E₃) K < ⊤) :
    (∫ x in K, ‖f x‖ ∂(volume : Measure E₃)) ≤
      (eLpNorm f 2 ((volume : Measure E₃))).toReal * ((volume : Measure E₃) K).toReal ^ (1/2 : ℝ) := by
  have hA := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := (1 : ℝ≥0∞)) (q := 2)
    (by norm_num) (hf.restrict K).1
  norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat, one_div, inv_one, Measure.restrict_apply_univ] at hA
  have hB : eLpNorm f 2 (((volume : Measure E₃)).restrict K) * ((volume : Measure E₃) K)^(1/2 : ℝ) ≤
      eLpNorm f 2 ((volume : Measure E₃)) * ((volume : Measure E₃) K)^(1/2 : ℝ) :=
    mul_le_mul' (eLpNorm_mono_measure f (Measure.restrict_le_self (s := K))) le_rfl
  have hfin : eLpNorm f 2 ((volume : Measure E₃)) * ((volume : Measure E₃) K) ^ (1/2 : ℝ) ≠ ⊤ := by finiteness
  have hC := ENNReal.toReal_mono hfin (hA.trans hB)
  rw [integral_norm_eq_lintegral_enorm (hf.restrict K).1, ← eLpNorm_one_eq_lintegral_enorm]
  convert hC using 1
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]

/-- The convolution kernel is jointly integrable over the kernel variable and any finite spatial set. -/
theorem kernel_integrable_prod (φ : ContDiffBump (0 : E₃)) (U : L2)
    (K : Set (E₃)) (hK : (volume : Measure E₃) K < ⊤) :
    Integrable (fun p : E₃ × E₃ =>
      φ.normed volume p.1 • U (p.2 - p.1))
      ((volume : Measure (E₃)).prod (((volume : Measure E₃)).restrict K)) := by
  have : Fact ((volume : Measure E₃) K < ⊤) := ⟨hK⟩
  have hmap : Measurable (fun p : E₃ × E₃ => p.2 - p.1) :=
    (continuous_snd.sub continuous_fst).measurable
  have hsm : StronglyMeasurable (fun p : E₃ × E₃ =>
      φ.normed volume p.1 • U (p.2 - p.1)) :=
    ((φ.contDiff_normed (n := (⊤ : ℕ∞))).continuous.comp continuous_fst).stronglyMeasurable.smul
      ((Lp.stronglyMeasurable U).comp_measurable hmap)
  have hshift (y : E₃) : MemLp (fun x => U (x - y)) 2 ((volume : Measure E₃)) := by
    convert! (Lp.memLp U).comp_measurePreserving
      (measurePreserving_add_right (volume : Measure E₃) (-y)) using 1
  apply (integrable_prod_iff hsm.aestronglyMeasurable).2
  constructor
  · filter_upwards [] with y
    have hint : Integrable (fun x => U (x-y)) (((volume : Measure E₃)).restrict K) :=
      ((hshift y).restrict K).integrable (by norm_num)
    exact hint.smul (φ.normed volume y)
  · have hbound (y : E₃) : (∫ x in K, ‖φ.normed volume y • U (x - y)‖ ∂(volume : Measure E₃)) ≤
        ‖φ.normed volume y‖ * (‖U‖ * ((volume : Measure E₃) K).toReal ^ (1/2 : ℝ)) := by
      simp only [norm_smul, integral_const_mul]
      have he : eLpNorm (fun x => U (x - y)) 2 ((volume : Measure E₃)) =
          eLpNorm U 2 ((volume : Measure E₃)) := by
        simpa only [Function.comp_def, sub_eq_add_neg] using
          eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞)) (Lp.aestronglyMeasurable U)
            (measurePreserving_add_right (volume : Measure E₃) (-y))
      have h := finite_set_integral_norm_le _ (hshift y) K hK
      rw [he, ← Lp.norm_def] at h
      exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
    exact (φ.integrable_normed.norm.mul_const (‖U‖ * ((volume : Measure E₃) K).toReal ^ (1/2 : ℝ))).mono'
      hsm.norm.integral_prod_right'.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
        exact hbound y))

/-- The classical spatial convolution is integrable on each finite-measure set. -/
theorem convolution_integrableOn (φ : ContDiffBump (0 : E₃)) (U : L2)
    (K : Set (E₃)) (hK : (volume : Measure E₃) K < ⊤) :
    IntegrableOn (((φ.normed volume) ⋆[lsmul ℝ ℝ, volume] (U : E₃ → E₃))) K ((volume : Measure E₃)) := by
  exact (kernel_integrable_prod φ U K hK).integral_prod_right

/-- Exact Fubini identity for every finite spatial set. -/
theorem setIntegral_convolution (φ : ContDiffBump (0 : E₃)) (U : L2)
    (K : Set (E₃)) (hK : (volume : Measure E₃) K < ⊤) :
    (∫ x in K, ((φ.normed volume) ⋆[lsmul ℝ ℝ, volume] (U : E₃ → E₃)) x ∂(volume : Measure E₃)) =
      ∫ y : E₃, φ.normed volume y • (∫ x in K, U (x-y) ∂(volume : Measure E₃)) := by
  have h := integral_integral_swap (f := fun (y : E₃) (x : E₃) =>
      φ.normed volume y • U (x-y))
    (μ := (volume : Measure (E₃))) (ν := ((volume : Measure E₃)).restrict K)
    (kernel_integrable_prod φ U K hK)
  change (∫ x in K, ∫ y : E₃, φ.normed volume y • U (x-y) ∂volume ∂(volume : Measure E₃)) = _
  rw [← h]
  simp only [integral_smul]

/-- Equality of finite-set integrals identifies a Bochner L² mollifier with the classical smooth field. -/
theorem ae_eq_convolution_of_setIntegrals (φ : ContDiffBump (0 : E₃)) (U V : L2)
    (hV : ∀ K : Set (E₃), MeasurableSet K → (volume : Measure E₃) K < ⊤ →
      (∫ x in K, V x ∂(volume : Measure E₃)) =
        ∫ y : E₃, φ.normed volume y • (∫ x in K, U (x-y) ∂(volume : Measure E₃))) :
    (V : E₃ → E₃) =ᵐ[(volume : Measure E₃)] ((φ.normed volume) ⋆[lsmul ℝ ℝ, volume] (U : E₃ → E₃)) := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro K _ hK
    have : Fact ((volume : Measure E₃) K < ⊤) := ⟨hK⟩
    exact ((Lp.memLp V).restrict K).integrable (by norm_num)
  · intro K _ hK
    exact convolution_integrableOn φ U K hK
  · intro K hK hfin
    exact (hV K hK hfin).trans (setIntegral_convolution φ U K hfin).symm

/-- The Bochner L² mollifier and the classical convolution have the same iterated finite-set integrals. -/
theorem mollify_setIntegral (n : ℕ) (f : L2) (s : Set (E₃))
    (hs : MeasurableSet s) (hμs : (volume : Measure E₃) s ≠ ⊤) :
    (∫ x in s, mollify n f x ∂(volume : Measure E₃)) =
      ∫ y : E₃, ∫ x in s, kernel n y • f (x - y)
        ∂(volume : Measure E₃) := by
  rw [mollify_eq_integral, setIntegral_integral_L2 s hs hμs _ (kernel_orbit_integrable n f)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul (kernel n y) (translation (-y) f)),
    ae_restrict_of_ae (translation_ae (-y) f)] with x hx hy
  rw [hx]
  change kernel n y • (translation (-y) f) x = _
  rw [hy, sub_eq_add_neg]

/-- Bochner L² mollification is represented by the classical convolution. -/
theorem mollify_ae_convolution (n : ℕ) (u : L2) :
    mollify n u =ᵐ[volume] (kernel n ⋆[lsmul ℝ ℝ, volume] (u : E₃ → E₃)) := by
  apply ae_eq_convolution_of_setIntegrals (bump n) u (mollify n u)
  exact fun K hK hfin => by
    simpa only [kernel, integral_smul] using mollify_setIntegral n u K hK hfin.ne

end ClockBarrier.Analysis.Solenoidal
