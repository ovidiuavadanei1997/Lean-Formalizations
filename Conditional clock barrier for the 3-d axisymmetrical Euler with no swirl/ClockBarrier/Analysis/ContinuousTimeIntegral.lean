/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd,
Euler/ContinuousTimeIntegral.lean. See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: focused ordinary path interface and pinned Mathlib compatibility.
-/
module
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith

/-! # The actual integral as a bounded operator on compact time paths -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.ContinuousTimeIntegral
open Set ContinuousLinearMap
open scoped Topology Interval
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def extendPath (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, E)) : ℝ → E :=
  fun t => f (projIcc 0 T hT t)

omit [NormedSpace ℝ E] in
theorem extendPath_continuous (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, E)) :
    Continuous (extendPath T hT f) := f.continuous.comp continuous_projIcc

section Primitive

variable [CompleteSpace E] (T : ℝ) (hT : 0 ≤ T)

/-- The literal zero-initial-time integral. -/
def realIntegral (f : C(Icc (0 : ℝ) T,E)) : ℝ → E :=
  fun t => ∫ s in (0 : ℝ)..t, extendPath T hT f s

/-- The integral has the actual classical derivative. -/
theorem realIntegral_hasDerivAt (f : C(Icc (0 : ℝ) T,E)) (t : ℝ) :
    HasDerivAt (realIntegral T hT f) (extendPath T hT f t) t := by
  have hc := extendPath_continuous T hT f
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- The actual integral is a continuous time path. -/
def integralLinear : C(Icc (0 : ℝ) T,E) →ₗ[ℝ] C(Icc (0 : ℝ) T,E) where
  toFun f := ⟨fun t => realIntegral T hT f t,
    ((show Differentiable ℝ (realIntegral T hT f) from fun t =>
      (realIntegral_hasDerivAt T hT f t).differentiableAt).continuous).comp continuous_subtype_val⟩
  map_add' f g := by
    ext t
    exact intervalIntegral.integral_add ((extendPath_continuous T hT f).intervalIntegrable 0 t)
      ((extendPath_continuous T hT g).intervalIntegrable 0 t)
  map_smul' r f := by
    ext t
    exact intervalIntegral.integral_smul r (extendPath T hT f)

/-- The uniform norm of the primitive is bounded by time length times the input norm. -/
theorem integralLinear_bound (f : C(Icc (0 : ℝ) T,E)) :
    ‖integralLinear T hT f‖ ≤ T*‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg hT (norm_nonneg f))).2
  intro t
  have hp : ‖realIntegral T hT f t‖ ≤ ‖f‖ * (t : ℝ) := by
    simpa only [realIntegral, extendPath, sub_zero, abs_of_nonneg t.property.1] using
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (fun s (_ : s ∈ Ι (0 : ℝ) (t : ℝ)) => f.norm_coe_le_norm (projIcc 0 T hT s)))
  exact hp.trans (by nlinarith [t.property.2, norm_nonneg f])

/-- The zero-initial-time integral as a bounded linear operator. -/
def integral : C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E) :=
  (integralLinear T hT).mkContinuous T (integralLinear_bound T hT)

@[simp] theorem integral_apply (f : C(Icc (0 : ℝ) T,E)) (t : Icc (0 : ℝ) T) :
    integral T hT f t = realIntegral T hT f t := rfl

/-- The exact operator bound for the initial primitive. -/
theorem integral_norm : ‖integral (E := E) T hT‖ ≤ T := by
  apply opNorm_le_bound _ hT
  intro f
  exact integralLinear_bound T hT f

@[simp] theorem integral_initial (f : C(Icc (0 : ℝ) T,E)) :
    integral T hT f ⟨0,le_rfl,hT⟩ = 0 := by
  exact intervalIntegral.integral_same

/-- The primitive has the prescribed within-interval derivative at every time. -/
theorem integral_hasDerivWithinAt (f : C(Icc (0 : ℝ) T,E)) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (integral T hT f)) (f t) (Icc (0 : ℝ) T) t := by
  have hd : HasDerivWithinAt (realIntegral T hT f) (f t) (Icc (0 : ℝ) T) t := by
    simpa only [extendPath, projIcc_of_mem hT t.property] using
      (realIntegral_hasDerivAt T hT f t).hasDerivWithinAt (s := Icc (0 : ℝ) T)
  apply hd.congr_of_mem _ t.property
  intro s hs
  simp only [extendPath, projIcc_of_mem hT hs, integral_apply]

/-- A path with this derivative is its initial value plus the actual integral. -/
theorem eq_initial_add_integral (f : C(Icc (0 : ℝ) T,E)) (a : ℝ → E)
    (ha : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt a (f t) (Icc (0 : ℝ) T) t)
    (t : Icc (0 : ℝ) T) : a t = a 0 + integral T hT f t := by
  have hd : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun r => a r - realIntegral T hT f r) 0 (Icc (0 : ℝ) T) s := by
    intro s hs
    have hp := (ha ⟨s,hs⟩).sub (realIntegral_hasDerivAt T hT f s).hasDerivWithinAt
    change HasDerivWithinAt (a - realIntegral T hT f) 0 (Icc (0 : ℝ) T) s
    simpa only [extendPath, projIcc_of_mem hT hs, sub_self] using hp
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hd
    (fun s hs => by simp) (convex_Icc (0 : ℝ) T)
    (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩) t.property
  have he : a t - realIntegral T hT f t = a 0 := by
    simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero, realIntegral,
      intervalIntegral.integral_same, sub_zero] using hb
  exact sub_eq_iff_eq_add.mp he

end Primitive

end ClockBarrier.Analysis.ContinuousTimeIntegral
