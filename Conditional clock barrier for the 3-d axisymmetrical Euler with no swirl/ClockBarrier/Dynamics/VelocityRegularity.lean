/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Dynamics.FlowVolume
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Supplying flow hypotheses from time-continuous bounded fields

Velocity and gradient fields continuous in their spatial supremum norms give
the joint continuity and compact-time bounds used in flow construction.
The gradient must be the genuine spatial derivative, not an independent field.
This is a generic interface, not a definition of a manuscript Euler solution.
-/

public section

namespace ClockBarrier.Dynamics

open Set MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] {T : ℝ}

/-- Supremum-norm continuity in time implies joint continuity in time and space. -/
theorem continuousOn_uncurry_of_boundedContinuousFunction
    {U : ℝ → E →ᵇ F} (hU : ContinuousOn U (Ico 0 T)) :
    ContinuousOn (fun p : ℝ × E => U p.1 p.2) (Ico 0 T ×ˢ univ) := by
  exact continuous_eval.comp_continuousOn
    ((hU.comp continuousOn_fst (fun p hp => hp.1)).prodMk continuousOn_snd)

/-- Time continuity in the supremum norm supplies a uniform spatial bound on every
earlier compact time interval. -/
theorem exists_bound_Ico_of_boundedContinuousFunction
    {D : ℝ → E →ᵇ F} (hD : ContinuousOn D (Ico 0 T)) :
    ∀ b ∈ Ico 0 T, ∃ K : ℝ≥0, ∀ t ∈ Ico 0 b, ∀ x, ‖D t x‖₊ ≤ K := by
  intro b hb
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hD.mono (show Icc 0 b ⊆ Ico 0 T from fun _ ht => ⟨ht.1, ht.2.trans_lt hb.2⟩))
  exact ⟨⟨max C 0, le_max_right _ _⟩, fun t ht x =>
    show ‖D t x‖ ≤ max C 0 from
      ((D t).norm_coe_le_norm x).trans ((hC t (Ico_subset_Icc_self ht)).trans (le_max_left _ _))⟩

/-- Time-continuous bounded velocity and genuine gradient fields supply all velocity
hypotheses for the constructed incompressible flow. -/
theorem exists_flow_volume_image_eq_of_boundedContinuousFunction
    (hT : 0 < T)
    (U : ℝ → EuclideanSpace ℝ (Fin 3) →ᵇ EuclideanSpace ℝ (Fin 3))
    (D : ℝ → EuclideanSpace ℝ (Fin 3) →ᵇ
      (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)))
    (hU : ContinuousOn U (Ico 0 T)) (hD : ContinuousOn D (Ico 0 T))
    (hspace : ∀ t ∈ Ico 0 T, ∀ x, HasFDerivAt (U t) (D t x) x)
    (hdiv : ∀ t ∈ Ico 0 T, ∀ x,
      LinearMap.trace ℝ (EuclideanSpace ℝ (Fin 3)) (D t x).toLinearMap = 0) :
    ∃ Φ : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      (∀ x, Φ 0 x = x) ∧ (∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T)) ∧
      (∀ x, ∀ t ∈ Ico 0 T,
        HasDerivWithinAt (fun s => Φ s x) (U t (Φ t x)) (Ici t) t) ∧
      ∀ t ∈ Ico 0 T, ContDiff ℝ 1 (Φ t) ∧ Function.Injective (Φ t) ∧
        (∀ x, HasDerivWithinAt (fun s => fderiv ℝ (Φ s) x)
          ((fderiv ℝ (U t) (Φ t x)).comp (fderiv ℝ (Φ t) x)) (Ici t) t ∧
          (fderiv ℝ (Φ t) x).toLinearMap.det = 1) ∧
        ∀ s : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet s → volume (Φ t '' s) = volume s := by
  have hfd (t : ℝ) (ht : t ∈ Ico 0 T) (x : EuclideanSpace ℝ (Fin 3)) :
      fderiv ℝ (U t) x = D t x := (hspace t ht x).fderiv
  apply exists_flow_volume_image_eq_Ico (u := fun t => U t) hT
    (continuousOn_uncurry_of_boundedContinuousFunction hU)
    (fun t ht x => (hspace t ht x).differentiableAt)
  · exact (continuousOn_uncurry_of_boundedContinuousFunction hD).congr
      (fun p hp => hfd p.1 hp.1 p.2)
  · intro b hb
    obtain ⟨K, hK⟩ := exists_bound_Ico_of_boundedContinuousFunction hD b hb
    exact ⟨K, fun t ht x => (hfd t ⟨ht.1, ht.2.trans hb.2⟩ x) ▸ hK t ht x⟩
  · intro t ht x
    simpa only [hfd t ht x] using hdiv t ht x

end ClockBarrier.Dynamics
