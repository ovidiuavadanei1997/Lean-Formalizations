/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd.
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: focused imports, namespaces, module interface and pinned Mathlib compatibility.
-/
module
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Normed.Operator.Bilinear
/-! # L2DerivativeMap
Selective port of ordinary-space L² calculus from NavierStokesAndEuler.
-/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.L2Derivative
open MeasureTheory
variable {X P V : Type*} [MeasurableSpace X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (μ : Measure X)

def applyDerivative (D : Lp (P →L[ℝ] V) 2 μ) (a : P) : Lp V 2 μ :=
  (ContinuousLinearMap.apply ℝ V a).compLpL 2 μ D

theorem applyDerivative_ae (D : Lp (P →L[ℝ] V) 2 μ) (a : P) :
    applyDerivative μ D a =ᵐ[μ] fun x => D x a :=
  (ContinuousLinearMap.apply ℝ V a).coeFn_compLp D

theorem applyDerivative_norm_le (D : Lp (P →L[ℝ] V) 2 μ) (a : P) :
    ‖applyDerivative μ D a‖ ≤ ‖D‖ * ‖a‖ := by
  rw [mul_comm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [applyDerivative_ae μ D a] with x hx
  rw [hx, mul_comm]
  exact (D x).le_opNorm a

def derivativeLinear (D : Lp (P →L[ℝ] V) 2 μ) : P →ₗ[ℝ] Lp V 2 μ where
  toFun := applyDerivative μ D
  map_add' a b := by
    apply Lp.ext
    filter_upwards [applyDerivative_ae μ D (a+b), applyDerivative_ae μ D a,
      applyDerivative_ae μ D b, Lp.coeFn_add (applyDerivative μ D a) (applyDerivative μ D b)]
      with x hab ha hb hs
    rw [hab, hs]
    simp only [Pi.add_apply]
    rw [ha, hb, map_add]
  map_smul' c a := by
    apply Lp.ext
    filter_upwards [applyDerivative_ae μ D (c • a), applyDerivative_ae μ D a,
      Lp.coeFn_smul c (applyDerivative μ D a)] with x hca ha hs
    change (applyDerivative μ D (c • a)) x = (c • applyDerivative μ D a) x
    rw [hca, hs]
    simp only [Pi.smul_apply]
    rw [ha, map_smul]

/-- This is a concrete bounded derivative with values in the actual L² function space. -/
def derivativeMap (D : Lp (P →L[ℝ] V) 2 μ) : P →L[ℝ] Lp V 2 μ :=
  (derivativeLinear μ D).mkContinuous ‖D‖ (applyDerivative_norm_le μ D)

theorem derivativeMap_ae (D : Lp (P →L[ℝ] V) 2 μ) (a : P) :
    derivativeMap μ D a =ᵐ[μ] fun x => D x a := applyDerivative_ae μ D a

theorem derivativeMap_norm_le (D : Lp (P →L[ℝ] V) 2 μ) : ‖derivativeMap μ D‖ ≤ ‖D‖ :=
  (derivativeMap μ D).opNorm_le_bound (norm_nonneg D) (applyDerivative_norm_le μ D)

def bundlingLinear : Lp (P →L[ℝ] V) 2 μ →ₗ[ℝ] (P →L[ℝ] Lp V 2 μ) where
  toFun := derivativeMap μ
  map_add' D E := by
    apply ContinuousLinearMap.ext
    intro a
    exact ((ContinuousLinearMap.apply ℝ V a).compLpL 2 μ).map_add D E
  map_smul' c D := by
    apply ContinuousLinearMap.ext
    intro a
    exact ((ContinuousLinearMap.apply ℝ V a).compLpL 2 μ).map_smul c D

def derivativeBundling : Lp (P →L[ℝ] V) 2 μ →L[ℝ] (P →L[ℝ] Lp V 2 μ) where
  toLinearMap := bundlingLinear μ
  cont := AddMonoidHomClass.continuous_of_bound (bundlingLinear (P := P) (V := V) μ) 1
    (fun D => by
      change ‖derivativeMap μ D‖ ≤ 1 * ‖D‖
      simpa only [one_mul] using derivativeMap_norm_le μ D)

@[simp] theorem derivativeBundling_apply (D : Lp (P →L[ℝ] V) 2 μ) :
    derivativeBundling μ D = derivativeMap μ D := rfl

theorem derivativeBundling_norm_le_one : ‖derivativeBundling (P := P) (V := V) μ‖ ≤ 1 :=
  (derivativeBundling (P := P) (V := V) μ).opNorm_le_bound zero_le_one (fun D => by
    change ‖derivativeMap μ D‖ ≤ 1 * ‖D‖
    simpa only [one_mul] using derivativeMap_norm_le μ D)

end ClockBarrier.Analysis.L2Derivative
