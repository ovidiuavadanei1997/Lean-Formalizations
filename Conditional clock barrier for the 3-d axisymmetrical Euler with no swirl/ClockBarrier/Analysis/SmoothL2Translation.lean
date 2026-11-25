/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd.
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: focused imports, namespaces, module interface and pinned Mathlib compatibility.
-/
module
import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import ClockBarrier.Analysis.L2SmoothApproximation
public import ClockBarrier.Analysis.SmoothL2Algebra

/-! # Translation regularity from actual L² spatial derivatives
Extracted from Euler/LpSmoothField.lean and LpSmoothFieldJets.lean.
-/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis
open MeasureTheory L2Derivative L2Translation Filter
open scoped ContDiff Topology
local notation "Space" => EuclideanSpace ℝ (Fin 3)
universe u
variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace L2Translation
theorem derivativeMap_translation (D : L2Space (Space →L[ℝ] V)) (a : Space) :
    derivativeMap volume (translation a D) =
      (translation a).toContinuousLinearMap.comp (derivativeMap volume D) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [derivativeMap_ae volume (translation a D) v, translation_ae a D,
    translation_ae a (derivativeMap volume D v),
    (measurePreserving_add_right (volume : Measure Space) a).quasiMeasurePreserving.ae
      (derivativeMap_ae volume D v)] with x hm ht hv hd
  change derivativeMap volume (translation a D) v x = translation a (derivativeMap volume D v) x
  rw [hm, ht, hv, hd]

end L2Translation
namespace SmoothL2Field
theorem translation_hasFDerivAt (A : SmoothL2Field V) (a : Space) :
    HasFDerivAt (fun b : Space => translation b A.toLp)
      (derivativeMap volume (translation a A.derivative.toLp)) a := by
  rw [derivativeMap_translation]
  exact translation_hasFDerivAt_all A.toLp (derivativeMap volume A.derivative.toLp)
    (smooth_hasFDerivAt A.field A.smooth A.memLp A.derivative.memLp) a

theorem translation_fderiv (A : SmoothL2Field V) :
    fderiv ℝ (fun a : Space => translation a A.toLp) =
      fun a => derivativeBundling volume (translation a A.derivative.toLp) :=
  funext (fun a => (A.translation_hasFDerivAt a).fderiv)

private theorem translation_contDiff_nat_aux (n : ℕ) :
    ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] (A : SmoothL2Field V),
      ContDiff ℝ n (fun a : Space => translation a A.toLp) := by
  induction n with
  | zero =>
    intro V _ _ A
    exact contDiff_zero.mpr (translation_continuous A.toLp)
  | succ n ih =>
    intro V _ _ A
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨fun a => (A.translation_hasFDerivAt a).differentiableAt, by simp, ?_⟩
    rw [A.translation_fderiv]
    exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := (n : WithTop ℕ∞))
      (E := L2Space (Space →L[ℝ] V)) (F := Space →L[ℝ] L2Space V)
      (derivativeBundling volume)).comp (ih (Space →L[ℝ] V) A.derivative)

/-- Genuine all-order smoothness of the translation orbit follows from the ordinary spatial L² jets. -/
theorem translation_contDiff (A : SmoothL2Field V) :
    ContDiff ℝ ∞ (fun a : Space => translation a A.toLp) :=
  contDiff_infty.mpr (fun n => translation_contDiff_nat_aux n V A)

private theorem norm_iteratedFDeriv_translation_aux (n : ℕ) :
    ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] (A : SmoothL2Field V) (a : Space),
      ‖iteratedFDeriv ℝ n (fun b : Space => translation b A.toLp) a‖ ≤ ‖A.jetLp n‖ := by
  induction n with
  | zero =>
    intro V _ _ A a
    rw [norm_iteratedFDeriv_zero, (translation a).norm_map, A.norm_jetLp_zero]
  | succ n ih =>
    intro V _ _ A a
    rw [← norm_iteratedFDeriv_fderiv, A.translation_fderiv]
    have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := Space)
      (F := L2Space (Space →L[ℝ] V)) (G := Space →L[ℝ] L2Space V)
      (derivativeBundling volume)
      (A.derivative.translation_contDiff.contDiffAt (x := a)) (n := n) (WithTop.coe_le_coe.mpr le_top)
    exact h.trans ((mul_le_mul_of_nonneg_right
      (derivativeBundling_norm_le_one (P := Space) (V := V) volume) (norm_nonneg _)).trans
      (by simpa only [one_mul, A.norm_derivative_jetLp n] using ih (Space →L[ℝ] V) A.derivative a))

/-- Translation jets are controlled with constant one by the actual ordinary spatial L² jets. -/
theorem norm_iteratedFDeriv_translation_le (A : SmoothL2Field V) (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => translation b A.toLp) a‖ ≤ ‖A.jetLp n‖ :=
  norm_iteratedFDeriv_translation_aux n V A a

private theorem iteratedFDeriv_translation_ae_aux (n : ℕ) :
    ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] (A : SmoothL2Field V)
      (a : Space) (v : Fin n → Space),
      iteratedFDeriv ℝ n (fun b : Space => translation b A.toLp) a v =ᵐ[volume]
        fun x => iteratedFDeriv ℝ n A.field (x+a) v := by
  induction n with
  | zero =>
    intro V _ _ A a v
    simp only [iteratedFDeriv_zero_apply]
    filter_upwards [translation_ae a A.toLp,
      (measurePreserving_add_right (volume : Measure Space) a).quasiMeasurePreserving.ae
        A.toLp_ae] with x ht hf
    exact ht.trans hf
  | succ n ih =>
    intro V _ _ A a v
    have he : iteratedFDeriv ℝ (n+1) (fun b : Space => translation b A.toLp) a v =
        derivativeMap volume
          (iteratedFDeriv ℝ n (fun b : Space => translation b A.derivative.toLp) a (Fin.init v))
          (v (Fin.last n)) := by
      rw [iteratedFDeriv_succ_apply_right, A.translation_fderiv]
      change (iteratedFDeriv ℝ n
        ((derivativeBundling (P := Space) (V := V) volume) ∘
          fun b : Space => translation b A.derivative.toLp) a (Fin.init v)) (v (Fin.last n)) = _
      rw [(derivativeBundling (P := Space) (V := V) volume).iteratedFDeriv_comp_left
        (A.derivative.translation_contDiff.contDiffAt (x := a)) (WithTop.coe_le_coe.mpr le_top)]
      rfl
    rw [he]
    filter_upwards [derivativeMap_ae volume
      (iteratedFDeriv ℝ n (fun b : Space => translation b A.derivative.toLp) a (Fin.init v))
      (v (Fin.last n)), ih (Space →L[ℝ] V) A.derivative a (Fin.init v)] with x hm hi
    rw [hm, hi]
    exact (iteratedFDeriv_succ_apply_right (f := A.field) (x := x+a) v).symm

theorem iteratedFDeriv_translation_ae (A : SmoothL2Field V) (n : ℕ)
    (a : Space) (v : Fin n → Space) :
    iteratedFDeriv ℝ n (fun b : Space => translation b A.toLp) a v =ᵐ[volume]
      fun x => iteratedFDeriv ℝ n A.field (x+a) v :=
  iteratedFDeriv_translation_ae_aux n V A a v

end SmoothL2Field
end ClockBarrier.Analysis
