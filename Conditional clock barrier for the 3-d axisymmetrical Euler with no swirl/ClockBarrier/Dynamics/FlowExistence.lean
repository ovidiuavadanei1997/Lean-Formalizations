/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.PathIntegral
public import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Construction of trajectories on compact time intervals

The Picard map acts on all continuous paths. A globally Lipschitz velocity
has a contracting iterate on every compact interval, with factorial decay.
No trajectory existence or spatial regularity of a flow is assumed.
-/

@[expose] public section

namespace ClockBarrier.Dynamics

open ClockBarrier.Analysis Set MeasureTheory
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {T : ℝ}

/-- The Picard integral map with a prescribed initial position. -/
noncomputable def pathPicard (hT : 0 ≤ T) (u : C(Icc 0 T × E, E)) (x : E)
    (γ : C(Icc 0 T, E)) : C(Icc 0 T, E) :=
  ContinuousMap.const _ x + pathIntegral hT (pathSuperposition u γ)

/-- Picard iterates have a factorial Lipschitz bound at each time. -/
theorem dist_iterate_pathPicard_apply_le (hT : 0 ≤ T) (u : C(Icc 0 T × E, E))
    {K : ℝ≥0} (hLip : ∀ s, LipschitzWith K (fun y => u (s, y)))
    (x : E) (γ δ : C(Icc 0 T, E)) (n : ℕ) (t : Icc 0 T) :
    dist ((pathPicard hT u x)^[n] γ t) ((pathPicard hT u x)^[n] δ t) ≤
      (K : ℝ) ^ n * t.1 ^ n / n.factorial * dist γ δ := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := γ) (g := δ) t
  | succ n hn =>
    simp only [Function.iterate_succ_apply', pathPicard, ContinuousMap.add_apply,
      ContinuousMap.const_apply, dist_eq_norm, add_sub_add_left_eq_sub]
    rw [← ContinuousMap.sub_apply, ← map_sub, pathIntegral_apply]
    have hbound : ∀ s ∈ Ioc 0 t.1,
        ‖(pathSuperposition u ((pathPicard hT u x)^[n] γ) -
          pathSuperposition u ((pathPicard hT u x)^[n] δ)) (projIcc 0 T hT s)‖ ≤
            (K : ℝ) ^ (n + 1) * s ^ n / n.factorial * ‖γ - δ‖ := by
      intro s hs
      rw [projIcc_of_mem hT (show s ∈ Icc 0 T from ⟨hs.1.le, hs.2.trans t.2.2⟩)]
      calc
        _ ≤ K * dist (((pathPicard hT u x)^[n] γ) ⟨s, ⟨hs.1.le, hs.2.trans t.2.2⟩⟩)
            (((pathPicard hT u x)^[n] δ) ⟨s, ⟨hs.1.le, hs.2.trans t.2.2⟩⟩) :=
          by simpa only [dist_eq_norm, ContinuousMap.sub_apply, pathSuperposition,
            ContinuousMap.coe_mk] using
            (hLip ⟨s, ⟨hs.1.le, hs.2.trans t.2.2⟩⟩).dist_le_mul
              (((pathPicard hT u x)^[n] γ) ⟨s, ⟨hs.1.le, hs.2.trans t.2.2⟩⟩)
              (((pathPicard hT u x)^[n] δ) ⟨s, ⟨hs.1.le, hs.2.trans t.2.2⟩⟩)
        _ ≤ K * ((K : ℝ) ^ n * s ^ n / n.factorial * dist γ δ) :=
          mul_le_mul_of_nonneg_left (hn _) K.2
        _ = _ := by simp only [dist_eq_norm, pow_succ]; ring
    have hi := intervalIntegral.norm_integral_le_of_norm_le t.2.1
      (Filter.Eventually.of_forall hbound)
      (show IntervalIntegrable (fun s : ℝ => (K : ℝ) ^ (n + 1) * s ^ n /
        n.factorial * ‖γ - δ‖) volume 0 t.1 from
          (by fun_prop : Continuous _).intervalIntegrable _ _)
    convert hi using 1
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul, integral_pow]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      pow_succ, mul_zero, sub_zero, div_mul_eq_div_div]
    ring

/-- A uniform bound for the Lipschitz constants of the Picard iterates. -/
theorem dist_iterate_pathPicard_le (hT : 0 ≤ T) (u : C(Icc 0 T × E, E))
    {K : ℝ≥0} (hLip : ∀ s, LipschitzWith K (fun y => u (s, y)))
    (x : E) (γ δ : C(Icc 0 T, E)) (n : ℕ) :
    dist ((pathPicard hT u x)^[n] γ) ((pathPicard hT u x)^[n] δ) ≤
      ((K : ℝ) * T) ^ n / n.factorial * dist γ δ := by
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro t
  refine (dist_iterate_pathPicard_apply_le hT u hLip x γ δ n t).trans ?_
  rw [mul_pow]
  gcongr <;> first | exact t.2.1 | exact t.2.2

/-- There is a unique continuous path satisfying the Picard equation on the whole interval. -/
theorem existsUnique_fixedPoint_pathPicard (hT : 0 ≤ T) (u : C(Icc 0 T × E, E))
    {K : ℝ≥0} (hLip : ∀ s, LipschitzWith K (fun y => u (s, y))) (x : E) :
    ∃! γ : C(Icc 0 T, E), Function.IsFixedPt (pathPicard hT u x) γ := by
  obtain ⟨n, hn⟩ := (FloorSemiring.tendsto_pow_div_factorial_atTop ((K : ℝ) * T)).eventually
    (gt_mem_nhds zero_lt_one) |>.exists
  have hc : ContractingWith ⟨((K : ℝ) * T) ^ n / n.factorial, by positivity⟩
      (pathPicard hT u x)^[n] :=
    ⟨hn, LipschitzWith.of_dist_le_mul fun γ δ => dist_iterate_pathPicard_le hT u hLip x γ δ n⟩
  refine ⟨_, hc.isFixedPt_fixedPoint_iterate, fun γ hγ => ?_⟩
  exact hc.fixedPoint_unique (hγ.iterate n)

/-- A Picard fixed point gives a trajectory with the prescribed initial value and ODE. -/
theorem trajectory_of_fixedPoint_pathPicard (hT : 0 ≤ T)
    (u : C(Icc 0 T × E, E)) (x : E) {γ : C(Icc 0 T, E)}
    (hγ : Function.IsFixedPt (pathPicard hT u x) γ) :
    γ ⟨0, ⟨le_rfl, hT⟩⟩ = x ∧
      ∀ t (ht : t ∈ Icc 0 T), HasDerivWithinAt (fun s => γ (projIcc 0 T hT s))
        (u (⟨t, ht⟩, γ ⟨t, ht⟩)) (Icc 0 T) t := by
  have heq (t : Icc 0 T) : γ t = x +
      ∫ s in 0..t.1, u (projIcc 0 T hT s, γ (projIcc 0 T hT s)) :=
    congrArg (fun f : C(Icc 0 T, E) => f t) hγ.symm
  refine ⟨by simpa using heq ⟨0, ⟨le_rfl, hT⟩⟩, fun t ht => ?_⟩
  have hc : Continuous (fun s => u (projIcc 0 T hT s, γ (projIcc 0 T hT s))) :=
    (pathSuperposition u γ).continuous.comp (continuous_projIcc (h := hT))
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add x
  have hd' := hd.hasDerivWithinAt.congr_of_mem
    (f₁ := fun s => γ (projIcc 0 T hT s))
    (fun s hs => by simpa only [projIcc_of_mem hT hs] using heq ⟨s, hs⟩) ht
  simpa only [projIcc_of_mem hT ht] using hd'

/-- A jointly continuous, uniformly spatially Lipschitz velocity admits trajectories
for all initial labels on any selected compact interval. -/
theorem exists_flow_Icc (hT : 0 ≤ T) {u : ℝ → E → E} {K : ℝ≥0}
    (hu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set E)))
    (hLip : ∀ t ∈ Icc 0 T, LipschitzWith K (u t)) :
    ∃ Φ : ℝ → E → E, (∀ x, Φ 0 x = x) ∧
      (∀ x, ContinuousOn (fun t => Φ t x) (Icc 0 T)) ∧
      ∀ x, ∀ t ∈ Ico 0 T,
        HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t := by
  let U : C(Icc 0 T × E, E) :=
    ⟨fun p => u p.1.1 p.2, hu.comp_continuous (continuous_subtype_val.prodMap continuous_id)
      (fun p => ⟨p.1.2, mem_univ _⟩)⟩
  choose γ hγ using fun x => (existsUnique_fixedPoint_pathPicard hT U
    (fun t => hLip t.1 t.2) x).exists
  have htraj (x : E) := trajectory_of_fixedPoint_pathPicard hT U x (hγ x)
  refine ⟨fun t x => γ x (projIcc 0 T hT t),
    fun x => by simpa only [projIcc_of_mem hT (show 0 ∈ Icc 0 T from ⟨le_rfl, hT⟩)]
      using (htraj x).1,
    fun x => ((γ x).continuous.comp continuous_projIcc).continuousOn, fun x t ht => ?_⟩
  have hd : HasDerivWithinAt (fun s => γ x (projIcc 0 T hT s))
      (u t (γ x (projIcc 0 T hT t))) (Icc 0 T) t := by
    simpa only [U, ContinuousMap.coe_mk, projIcc_of_mem hT (Ico_subset_Icc_self ht)]
      using (htraj x).2 t (Ico_subset_Icc_self ht)
  apply hd.mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds ht.2)] with s hs hsT
  exact ⟨ht.1.trans hs, hsT.le⟩

end ClockBarrier.Dynamics
