/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.SmoothInitialData
public import ClockBarrier.Analysis.SmoothFieldScaling
public import ClockBarrier.Analysis.L2ConvolutionBounds

/-! # Bounded operators for every jet of the concrete regularizer -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Solenoidal
open MeasureTheory ContinuousLinearMap SmoothL2Field Sobolev
open scoped ContDiff Convolution BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem mollifiedSmoothField_add (n : ℕ) (u v : L2) :
    mollifiedSmoothField n (u+v) = addField (mollifiedSmoothField n u) (mollifiedSmoothField n v) :=
  SmoothL2Field.field_ext (congrArg (fun f : E₃ →ᵇ E₃ => (f : E₃ → E₃))
    ((mollifierField n).map_add u v))

theorem mollifiedSmoothField_smul (n : ℕ) (c : ℝ) (u : L2) :
    mollifiedSmoothField n (c • u) = scaleField c (mollifiedSmoothField n u) :=
  SmoothL2Field.field_ext (congrArg (fun f : E₃ →ᵇ E₃ => (f : E₃ → E₃))
    ((mollifierField n).map_smul c u))

def mollifiedJetLinear (n m : ℕ) : L2 →ₗ[ℝ] Lp (E₃ [×m]→L[ℝ] E₃) 2 (volume : Measure E₃) where
  toFun u := (mollifiedSmoothField n u).jetLp m
  map_add' u v := by rw [mollifiedSmoothField_add, jetLp_addField]
  map_smul' c u := by simp only [mollifiedSmoothField_smul, scaleField_jetLp, RingHom.id_apply]

theorem mollifiedJetLinear_bounded (n m : ℕ) :
    ∃ C : ℝ, ∀ u, ‖mollifiedJetLinear n m u‖ ≤ C * ‖u‖ := by
  obtain ⟨C, _, hb⟩ := L2Convolution.iteratedFDeriv_convolution_l2_bounded m
    (lsmul ℝ ℝ) (kernel n) (kernel_smooth n) (kernel_compact n)
  refine ⟨C, fun u => ?_⟩
  change ‖(mollifiedSmoothField n u).jetLp m‖ ≤ C * ‖u‖
  rw [norm_jetLp]
  simpa only [mollifiedSmoothField_field, show (mollifierField n u : E₃ → E₃) =
    kernel n ⋆[lsmul ℝ ℝ, volume] (u : E₃ → E₃) from funext (mollifierField_apply n u)] using hb u

/-- The actual spatial jet of convolution as a bounded operator on L². -/
def mollifiedJetMap (n m : ℕ) : L2 →L[ℝ] Lp (E₃ [×m]→L[ℝ] E₃) 2 (volume : Measure E₃) :=
  (mollifiedJetLinear n m).mkContinuousOfExistsBound (mollifiedJetLinear_bounded n m)

@[simp] theorem mollifiedJetMap_apply (n m : ℕ) (u : L2) :
    mollifiedJetMap n m u = (mollifiedSmoothField n u).jetLp m := rfl

/-- The literal smooth representative of `P Jₙ P = Jₙ P`. -/
def regularizedSmoothField (n : ℕ) (u : L2) : SmoothL2Field E₃ :=
  mollifiedSmoothField n (solenoidalProjection u)

@[simp] theorem regularizedSmoothField_field (n : ℕ) (u : L2) :
    (regularizedSmoothField n u).field = regularizedField n u := rfl

theorem regularizedSmoothField_toLp (n : ℕ) (u : L2) :
    (regularizedSmoothField n u).toLp = regularizerMap n u := by
  rw [regularizerMap_eq_mollify_projection]
  exact mollifiedSmoothField_toLp n _

def regularizedJetMap (n m : ℕ) : L2 →L[ℝ] Lp (E₃ [×m]→L[ℝ] E₃) 2 (volume : Measure E₃) :=
  (mollifiedJetMap n m).comp solenoidalProjection

@[simp] theorem regularizedJetMap_apply (n m : ℕ) (u : L2) :
    regularizedJetMap n m u = (regularizedSmoothField n u).jetLp m := rfl

theorem continuous_regularizedSmoothField_jets {K : Type*} [TopologicalSpace K]
    (n m : ℕ) {u : K → L2} (hu : Continuous u) :
    Continuous (fun t => (regularizedSmoothField n (u t)).jetLp m) :=
  (regularizedJetMap n m).continuous.comp hu

end ClockBarrier.Analysis.Solenoidal
