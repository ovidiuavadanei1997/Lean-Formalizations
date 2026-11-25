/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd,
Euler/OrdinaryMollifier.lean and Euler/EulerProof.lean (cutoffScale).
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: focused imports, module interface, project namespace and carrier.
-/
module

public import ClockBarrier.Analysis.SolenoidalTranslation
public import ClockBarrier.Analysis.HolderMollification
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Concrete symmetric spatial mollifiers on L²

The kernel has inner radius `(n+1)⁻¹`, outer radius `2*(n+1)⁻¹`,
and unit integral. Averaging the strongly continuous translation action gives
a self-adjoint contraction that converges strongly to the identity.
-/

@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Solenoidal
open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap
open scoped ContDiff Topology Convolution
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

def cutoffScale (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem cutoffScale_pos (n : ℕ) : 0 < cutoffScale n := by
  exact inv_pos.mpr (by positivity)

theorem cutoffScale_tendsto : Tendsto cutoffScale atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp
    (Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ) tendsto_natCast_atTop_atTop)

def bump (n : ℕ) : ContDiffBump (0 : E₃) where
  rIn := cutoffScale n
  rOut := 2*cutoffScale n
  rIn_pos := cutoffScale_pos n
  rIn_lt_rOut := by have h := cutoffScale_pos n; linarith

def kernel (n : ℕ) : E₃ → ℝ := (bump n).normed volume

theorem kernel_smooth (n : ℕ) : ContDiff ℝ ∞ (kernel n) := (bump n).contDiff_normed
theorem kernel_compact (n : ℕ) : HasCompactSupport (kernel n) := (bump n).hasCompactSupport_normed
theorem kernel_nonneg (n : ℕ) (x : E₃) : 0 ≤ kernel n x := (bump n).nonneg_normed x
theorem kernel_integral (n : ℕ) : ∫ x, kernel n x = 1 := (bump n).integral_normed
theorem kernel_integrable (n : ℕ) : Integrable (kernel n) := (bump n).integrable_normed
theorem kernel_neg (n : ℕ) (x : E₃) : kernel n (-x)=kernel n x := (bump n).normed_neg x

def smoothOrbit (n : ℕ) (u : L2) : E₃ → L2 :=
  convolution (kernel n) (fun a => translation a u) (ContinuousLinearMap.lsmul ℝ ℝ) volume

def mollify (n : ℕ) (u : L2) : L2 := smoothOrbit n u 0

theorem smoothOrbit_contDiff (n : ℕ) (u : L2) : ContDiff ℝ ∞ (smoothOrbit n u) :=
  (kernel_compact n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (kernel_smooth n) (translation_continuous u).locallyIntegrable

theorem mollify_tendsto (u : L2) : Tendsto (fun n => mollify n u) atTop (𝓝 u) := by
  have hr : Tendsto (fun n => (bump n).rOut) atTop (𝓝 (0 : ℝ)) := by
    simpa only [bump,mul_zero] using cutoffScale_tendsto.const_mul 2
  have h := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := (volume : Measure E₃)) hr (translation_continuous u) 0
  simpa only [translation_zero,mollify,smoothOrbit,kernel] using h

theorem mollify_eq_integral (n : ℕ) (u : L2) :
    mollify n u=∫ y : E₃, kernel n y • translation (-y) u := by
  simp only [mollify,smoothOrbit,convolution_def,ContinuousLinearMap.lsmul_apply,zero_sub]

theorem kernel_orbit_integrable (n : ℕ) (u : L2) :
    Integrable (fun y : E₃ => kernel n y • translation (-y) u) :=
  ((kernel_smooth n).continuous.smul
    ((translation_continuous u).comp continuous_neg)).integrable_of_hasCompactSupport
      (kernel_compact n).smul_right

theorem mollify_norm_le (n : ℕ) (u : L2) : ‖mollify n u‖ ≤ ‖u‖ := by
  rw [mollify_eq_integral]
  have h := norm_integral_le_of_norm_le ((kernel_integrable n).mul_const ‖u‖)
    (f := fun y : E₃ => kernel n y • translation (-y) u) ?_
  · simpa only [integral_mul_const,kernel_integral,one_mul] using h
  exact Eventually.of_forall (fun y => by
    rw [norm_smul,LinearIsometry.norm_map,Real.norm_eq_abs,abs_of_nonneg (kernel_nonneg n y)])

theorem mollify_add (n : ℕ) (u v : L2) : mollify n (u+v)=mollify n u+mollify n v := by
  simp only [mollify_eq_integral,map_add,smul_add]
  exact integral_add (kernel_orbit_integrable n u) (kernel_orbit_integrable n v)

theorem mollify_smul (n : ℕ) (c : ℝ) (u : L2) : mollify n (c • u)=c • mollify n u := by
  simp only [mollify_eq_integral,map_smul]
  simp_rw [smul_comm (kernel n _) c]
  exact integral_smul c _

def mollifierLinear (n : ℕ) : L2 →ₗ[ℝ] L2 where
  toFun := mollify n
  map_add' := mollify_add n
  map_smul' := mollify_smul n

def mollifier (n : ℕ) : L2 →L[ℝ] L2 :=
  (mollifierLinear n).mkContinuous 1 (fun u => by
    change ‖mollify n u‖ ≤ 1*‖u‖
    simpa only [one_mul] using mollify_norm_le n u)

@[simp] theorem mollifier_apply (n : ℕ) (u : L2) : mollifier n u=mollify n u := rfl

theorem mollify_translation (n : ℕ) (a : E₃) (u : L2) :
    translation a (mollify n u)=mollify n (translation a u) := by
  rw [mollify_eq_integral,mollify_eq_integral]
  change (translation a).toContinuousLinearMap
    (∫ y : E₃, kernel n y • translation (-y) u)=_
  rw [← (translation a).toContinuousLinearMap.integral_comp_comm (kernel_orbit_integrable n u)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by
    simp only [map_smul,LinearIsometry.coe_toContinuousLinearMap]
    rw [translation_add,translation_add,add_comm a])

theorem smoothOrbit_eq (n : ℕ) (u : L2) (x : E₃) :
    smoothOrbit n u x=translation x (mollify n u) := by
  rw [mollify_eq_integral]
  change _=(translation x).toContinuousLinearMap
    (∫ y : E₃, kernel n y • translation (-y) u)
  rw [← (translation x).toContinuousLinearMap.integral_comp_comm (kernel_orbit_integrable n u)]
  simp only [smoothOrbit,convolution_def,ContinuousLinearMap.lsmul_apply]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by
    simp only [map_smul,LinearIsometry.coe_toContinuousLinearMap,translation_add,sub_eq_add_neg])

theorem mollify_smooth (n : ℕ) (u : L2) :
    ContDiff ℝ ∞ (fun a => translation a (mollify n u)) := by
  convert smoothOrbit_contDiff n u using 1
  exact funext (fun a => (smoothOrbit_eq n u a).symm)

theorem translation_inner_shift (a : E₃) (u v : L2) :
    ⟪translation a u,v⟫_ℝ=⟪u,translation (-a) v⟫_ℝ := by
  calc
    _=⟪translation a u,translation a (translation (-a) v)⟫_ℝ := by
      rw [translation_add,add_neg_cancel,translation_zero]
    _=_ := (translation a).inner_map_map _ _

theorem mollify_symmetric (n : ℕ) (u v : L2) :
    ⟪mollify n u,v⟫_ℝ=⟪u,mollify n v⟫_ℝ := by
  rw [mollify_eq_integral,mollify_eq_integral]
  rw [real_inner_comm v _,← integral_inner (kernel_orbit_integrable n u) v,
    ← integral_inner (kernel_orbit_integrable n v) u]
  rw [← integral_neg_eq_self (fun y : E₃ => ⟪v,kernel n y • translation (-y) u⟫_ℝ)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by
    dsimp only
    rw [kernel_neg,neg_neg,real_inner_smul_right,real_inner_smul_right,
      real_inner_comm _ v,translation_inner_shift])

end ClockBarrier.Analysis.Solenoidal
