/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd.
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: focused imports, namespaces, module interface and pinned Mathlib compatibility.
-/
module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Directional differentiation of transport
Extracted from Euler/EulerProof.lean.
-/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.TransportDerivatives
open scoped ContDiff
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
/-- The actual Fréchet directional derivative along a constant vector. -/
def directionalDerivative (a : V) (f : V → W) (x : V) : W := fderiv ℝ f x a

/-- Differentiation of a field in the direction of a variable transport field. -/
def transport (b : V → V) (f : V → W) (x : V) : W := fderiv ℝ f x (b x)

theorem directionalDerivative_smooth (a : V) (f : V → W) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (directionalDerivative a f) := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem transport_smooth (b : V → V) (f : V → W)
    (hb : ContDiff ℝ ∞ b) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (transport b f) := by
  exact (hf.fderiv_right (by simp)).clm_apply hb

theorem directional_transport_commutator (a : V) (b : V → V) (f : V → W)
    (hb : ContDiff ℝ ∞ b) (hf : ContDiff ℝ ∞ f) (x : V) :
    directionalDerivative a (transport b f) x =
      transport b (directionalDerivative a f) x +
        fderiv ℝ f x (directionalDerivative a b x) := by
  have hdf := (((hf.fderiv_right (m := ∞) (by simp)).differentiable
    (by simp)) x).hasFDerivAt
  have hdb := (hb.differentiable (by simp)).differentiableAt.hasFDerivAt (x := x)
  have hdT := congrArg (fun L : V →L[ℝ] W => L a) (hdf.clm_apply hdb).fderiv
  have hdA := congrArg (fun L : V →L[ℝ] W => L (b x))
    (hdf.clm_apply (hasFDerivAt_const a x)).fderiv
  have hs := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simpa using
    (ENat.natCast_le_of_coe_top_le_withTop (N := (∞ : ℕ∞ω)) le_rfl 2)) a (b x)
  change fderiv ℝ (transport b f) x a = _ at hdT
  change fderiv ℝ (directionalDerivative a f) x (b x) = _ at hdA
  change fderiv ℝ (transport b f) x a =
    fderiv ℝ (directionalDerivative a f) x (b x) + fderiv ℝ f x (fderiv ℝ b x a)
  rw [hdT, hdA]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    zero_apply, map_zero, zero_add]
  rw [hs]
  exact add_comm _ _

end ClockBarrier.Analysis.TransportDerivatives
