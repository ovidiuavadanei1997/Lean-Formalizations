/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.BoundedLp
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! # Bounded continuous representatives of L² convolutions -/

@[expose] public noncomputable section
namespace ClockBarrier.Analysis.L2Convolution
open MeasureTheory ContinuousLinearMap
open scoped BoundedContinuousFunction Convolution
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Translate and reflect an actual L² equivalence class. -/
def shift (x : E₃) : Lp F 2 (volume : Measure E₃) →ₗᵢ[ℝ] Lp F 2 (volume : Measure E₃) :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun y : E₃ => x - y)
    (volume.measurePreserving_sub_left x)

theorem shift_ae (x : E₃) (k : Lp F 2 volume) :
    shift x k =ᵐ[volume] fun y => k (x - y) :=
  Lp.coeFn_compMeasurePreserving k (volume.measurePreserving_sub_left x)

theorem continuous_shift (k : Lp F 2 (volume : Measure E₃)) :
    Continuous (fun x : E₃ => shift x k) := by
  let g : E₃ → C(E₃, E₃) := fun x => ⟨fun y => x - y, continuous_const.sub continuous_id⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g
    (continuous_fst.sub continuous_snd)
  exact continuous_const.compMeasurePreservingLp hg
    (fun x => volume.measurePreserving_sub_left x) (by norm_num)

variable (B : F →L[ℝ] E₃ →L[ℝ] G) (k : Lp F 2 (volume : Measure E₃))

/-- Evaluation of convolution, using the bounded L² pairing. -/
def value (u : Lp E₃ 2 (volume : Measure E₃)) (x : E₃) : G :=
  B.lpPairing (volume : Measure E₃) 2 2 (shift x k) u

theorem value_continuous (u : Lp E₃ 2 (volume : Measure E₃)) : Continuous (value B k u) :=
  ((B.lpPairing (volume : Measure E₃) 2 2).continuous.comp (continuous_shift k)).clm_apply continuous_const

theorem value_norm_le (u : Lp E₃ 2 (volume : Measure E₃)) (x : E₃) :
    ‖value B k u x‖ ≤ (‖B.lpPairing (volume : Measure E₃) 2 2‖ * ‖k‖) * ‖u‖ := by
  exact ((B.lpPairing (volume : Measure E₃) 2 2 (shift x k)).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right
      (by simpa only [LinearIsometry.norm_map] using
        (B.lpPairing (volume : Measure E₃) 2 2).le_opNorm (shift x k)) (norm_nonneg u))

def bounded (u : Lp E₃ 2 (volume : Measure E₃)) : E₃ →ᵇ G :=
  BoundedContinuousFunction.ofNormedAddCommGroup (value B k u) (value_continuous B k u)
    ((‖B.lpPairing (volume : Measure E₃) 2 2‖ * ‖k‖) * ‖u‖) (value_norm_le B k u)

def linear : Lp E₃ 2 (volume : Measure E₃) →ₗ[ℝ] (E₃ →ᵇ G) where
  toFun := bounded B k
  map_add' u v := BoundedContinuousFunction.ext
    (fun x => (B.lpPairing (volume : Measure E₃) 2 2 (shift x k)).map_add u v)
  map_smul' c u := BoundedContinuousFunction.ext
    (fun x => (B.lpPairing (volume : Measure E₃) 2 2 (shift x k)).map_smul c u)

/-- Convolution with an L² kernel maps L² continuously into bounded continuous functions. -/
def operator : Lp E₃ 2 (volume : Measure E₃) →L[ℝ] (E₃ →ᵇ G) :=
  (linear B k).mkContinuous (‖B.lpPairing (volume : Measure E₃) 2 2‖ * ‖k‖)
    (fun u => (BoundedContinuousFunction.norm_le (f := bounded B k u)
      (mul_nonneg (mul_nonneg (norm_nonneg
        (B.lpPairing (volume : Measure E₃) 2 2)) (norm_nonneg k)) (norm_nonneg u))).mpr
        (value_norm_le B k u))

theorem operator_apply (u : Lp E₃ 2 (volume : Measure E₃)) (x : E₃) :
    operator B k u x = value B k u x := rfl

/-- The bounded representative is the literal convolution, at every point. -/
theorem value_eq_convolution {f : E₃ → F} (hf : MemLp f 2 volume)
    (u : Lp E₃ 2 (volume : Measure E₃)) (x : E₃) :
    value B (hf.toLp f) u x = (f ⋆[B, volume] (u : E₃ → E₃)) x := by
  rw [value, lpPairing_eq_integral, convolution_eq_swap]
  apply integral_congr_ae
  filter_upwards [shift_ae x (hf.toLp f),
    (volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae hf.coeFn_toLp]
    with y hy hz using congrArg (fun z => B z (u y)) (hy.trans hz)

end ClockBarrier.Analysis.L2Convolution
