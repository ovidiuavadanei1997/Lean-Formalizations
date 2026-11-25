/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.ExactInitialLimit
public import ClockBarrier.Euler.ExactProjectedLimit
public import ClockBarrier.Analysis.C1Solenoidal

/-! # Rough-data Euler limits on a common lifespan, in the projected equation

The lifespan and bounds are chosen before the datum. This is not the full
classical-existence theorem: it does not yet assert a continuous pressure gradient.
-/
@[expose] public noncomputable section
namespace ClockBarrier.Euler.Smooth
open Set Filter MeasureTheory ContinuousLinearMap ClockBarrier.Analysis
  Solenoidal SmoothL2Field Sobolev ContinuousTimeIntegral
open scoped Topology NNReal BoundedContinuousFunction
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem exists_uniform_rough_projected (α : ℝ≥0) (hα : 0 < α) (hα1 : α < 1) (M : ℝ≥0) :
    ∃ T : ℝ, ∃ hT : 0 < T, ∃ R : ℝ≥0, 0 < R ∧
      ∀ (u₀ : Space →ᵇ Space) (D₀ : Space →ᵇ (Space →L[ℝ] Space))
        (hLp : MemLp (u₀ : Space → Space) 2 volume),
        (∀ x, HasFDerivAt (u₀ : Space → Space) (D₀ x) x) →
        (∀ x, LinearMap.trace ℝ Space (D₀ x).toLinearMap = 0) →
        ‖D₀‖ ≤ (M : ℝ) → HolderWith M α (D₀ : Space → Space →L[ℝ] Space) →
        (eLpNorm (u₀ : Space → Space) 2 volume).toReal ≤ (M : ℝ) →
      ∃ V : C(Icc (0 : ℝ) T, L2), ∃ v : C(Icc (0 : ℝ) T, Space →ᵇ Space),
      ∃ D : C(Icc (0 : ℝ) T, Space →ᵇ (Space →L[ℝ] Space)),
        V ⟨0, le_rfl, hT.le⟩ = hLp.toLp u₀ ∧
        v ⟨0, le_rfl, hT.le⟩ = u₀ ∧ D ⟨0, le_rfl, hT.le⟩ = D₀ ∧
        ∀ t, V t =ᵐ[volume] (v t : Space → Space) ∧
          MemLp (v t : Space → Space) 2 volume ∧
          (∀ x, HasFDerivAt (v t : Space → Space) (D t x) x) ∧
          ‖v t‖ ≤ (R : ℝ) ∧ ‖D t‖ ≤ (R : ℝ) ∧
          HolderWith R α (D t : Space → Space →L[ℝ] Space) ∧ ‖V t‖ ≤ (M : ℝ) ∧
          (∀ x, LinearMap.trace ℝ Space (D t x).toLinearMap = 0) ∧
          HasDerivWithinAt (extendPath T hT.le V)
            (-solenoidalProjection (boundedApplyL2 (D t) (V t))) (Icc 0 T) t := by
  obtain ⟨τ, hτ, R, hR, hex⟩ := exists_exact_mollified_family α hα hα1 M
  let T := τ / 2
  have hT : 0 < T := half_pos hτ
  have hTτ : T < τ := half_lt_self hτ
  refine ⟨T, hT, R, hR, ?_⟩
  intro u₀ D₀ hLp hd htr hDn hDH hE
  obtain ⟨U, hU⟩ := hex u₀ D₀ hLp hd htr hDn hDH hE
  have hc (k m : ℕ) := (hU k).2.1 m
  have hs (t : ℝ) (ht : t ∈ Icc 0 T) : t ∈ Ico 0 τ :=
    ⟨ht.1, ht.2.trans_lt hTτ⟩
  have htime (k m : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (fun s => (U k s).jetLp m) ((rhs (U k t)).jetLp m) (Icc 0 T) t :=
    ((hU k).2.2.1 m t (Ico_subset_Icc_self (hs t ht))).mono
      (fun _ hr => Ico_subset_Icc_self (hs _ hr))
  have hsol (k : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) :=
    (hU k).2.2.2.1 t (Ico_subset_Icc_self (hs t ht))
  have hb (k : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) := (hU k).2.2.2.2.2 t (hs t ht)
  have hinit : CauchySeq (fun k => (U k 0).toLp) := by
    simpa only [(hU _).1] using (mollifiedSmoothField_tendsto (hLp.toLp u₀)).cauchySeq
  obtain ⟨V, v, D, hV, hv, hD, hp⟩ := exact_spatial_limit U hc htime hsol R α hα
    (fun k t ht => (hb k t ht).2.1) (fun k t ht => (hb k t ht).2.2.1) hinit
  have hi := exact_initial_limit hT.le u₀ D₀ hLp hd hα hDH U hc
    (fun k => (hU k).1) V v D hV hv hD
  refine ⟨V, v, D, hi.1, hi.2.1, hi.2.2, fun t => ?_⟩
  have hVt := ((ContinuousMap.evalCLM ℝ t).continuous.tendsto V).comp hV
  have hvt := ((ContinuousMap.evalCLM ℝ t).continuous.tendsto v).comp hv
  have hVs : V t ∈ solenoidalSpace := gradientSpace.isClosed_orthogonal.mem_of_tendsto hVt
    (Eventually.of_forall (fun k => hsol k t t.property))
  have hVn : ‖V t‖ ≤ (M : ℝ) := le_of_tendsto hVt.norm
    (Eventually.of_forall (fun k => (hb k t t.property).2.2.2))
  have hvn : ‖v t‖ ≤ (R : ℝ) := le_of_tendsto hvt.norm
    (Eventually.of_forall (fun k => (hb k t t.property).1))
  exact ⟨(hp t).1, (hp t).2.1, (hp t).2.2.1, hvn,
    (hp t).2.2.2.1, (hp t).2.2.2.2, hVn,
    c1_solenoidal_trace (V t) hVs (v t) (D t) (hp t).1 (hp t).2.2.1,
    exact_projected_limit hT.le U hc htime V D hV hD t⟩

end ClockBarrier.Euler.Smooth
