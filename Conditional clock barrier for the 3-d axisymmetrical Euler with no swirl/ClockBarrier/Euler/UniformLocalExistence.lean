/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.Classical
import ClockBarrier.Euler.ExactInitialLimit
import ClockBarrier.Euler.ExactClassicalTimeLimit
import ClockBarrier.Analysis.C1Solenoidal

/-! # Uniform classical Euler local existence

Exact smooth approximations have a common lifespan. Their strong spatial and
pressure limits solve the pointwise Euler equation in the class.
-/
public section
namespace ClockBarrier.Euler
open Set Filter MeasureTheory ContinuousLinearMap ClockBarrier.Analysis
  Solenoidal SmoothL2Field Sobolev ContinuousTimeIntegral Smooth
open scoped Topology NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem exists_uniform_local_classical_euler :
  ∀ (α : ℝ≥0), 0 < α → α < 1 →
  ∀ M : ℝ≥0, ∃ τ : ℝ, 0 < τ ∧
    ∀ (u₀ : E₃ →ᵇ E₃) (D₀ : E₃ →ᵇ (E₃ →L[ℝ] E₃)),
      (∀ x, HasFDerivAt (u₀ : E₃ → E₃) (D₀ x) x) →
      ‖u₀‖ ≤ (M : ℝ) → ‖D₀‖ ≤ (M : ℝ) →
      HolderWith M α (D₀ : E₃ → E₃ →L[ℝ] E₃) →
      MemLp (u₀ : E₃ → E₃) 2 volume →
      (eLpNorm (u₀ : E₃ → E₃) 2 volume).toReal ≤ (M : ℝ) →
      (∀ x, LinearMap.trace ℝ E₃ (D₀ x).toLinearMap = 0) →
      ∃ v : ℝ → E₃ →ᵇ E₃, ∃ p : ℝ → E₃ → ℝ,
        classical_euler_on α τ v p ∧ v 0 = u₀ := by
  intro α hα hα1 M
  obtain ⟨τ, hτ, R, hR, hex⟩ := exists_exact_mollified_family α hα hα1 M
  let T := τ / 2
  have hT : 0 < T := half_pos hτ
  have hTτ : T < τ := half_lt_self hτ
  refine ⟨T, hT, ?_⟩
  intro u₀ D₀ hd _hUn hDn hDH hLp hE htr
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
  obtain ⟨P, hP, hpot⟩ := exact_pressure_limit (fun k (t : Icc (0 : ℝ) T) => U k t)
    (fun k m => (hc k m).comp continuous_subtype_val) (fun k t => hsol k t t.property)
    (R : ℝ) (fun k t => (hb k t t.property).2.1) V D hV hD
  let w := extendPath T hT.le v
  let d (t : ℝ) := D (projIcc 0 T hT.le t)
  let g := extendPath T hT.le P
  let p (t : ℝ) := SmoothPressure.radialPotential (g t)
  refine ⟨w, p, ?_, ?_⟩
  · have hwd (t : ℝ) (x : E₃) : HasFDerivAt (w t : E₃ → E₃) (d t x) x :=
      (hp (projIcc 0 T hT.le t)).2.2.1 x
    have hgrad (t : ℝ) (x : E₃) : gradient (p t) x = g t x :=
      (hpot (projIcc 0 T hT.le t)).2 x
    refine ⟨hT, hα, hα1, (extendPath_continuous T hT.le v).continuousOn,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨d, (D.continuous.comp continuous_projIcc).continuousOn, fun t _ x => hwd t x, ?_⟩
      intro b _
      exact ⟨R, fun t _ => (hp (projIcc 0 T hT.le t)).2.2.2.2⟩
    · intro t _
      exact (hp (projIcc 0 T hT.le t)).2.1
    · intro t _
      have hcont : Tendsto (extendPath T hT.le V) (𝓝[Ico 0 T] t)
          (𝓝 (extendPath T hT.le V t)) :=
        ((extendPath_continuous T hT.le V).tendsto t).mono_left nhdsWithin_le_nhds
      have hh := hcont.edist (tendsto_const_nhds (x := extendPath T hT.le V t))
      simp only [edist_self] at hh
      convert! hh using 1
      funext s
      rw [Lp.edist_def]
      apply eLpNorm_congr_ae
      exact ((hp (projIcc 0 T hT.le s)).1.sub (hp (projIcc 0 T hT.le t)).1).symm
    · intro t _
      exact (hpot (projIcc 0 T hT.le t)).1
    · have hgc := extendPath_continuous T hT.le P
      have hj : Continuous (fun q : ℝ × E₃ => g q.1 q.2) :=
        ContinuousEval.continuous_eval.comp ((hgc.comp continuous_fst).prodMk continuous_snd)
      simpa only [hgrad] using hj.continuousOn
    · intro t ht x
      have htt : t ∈ Icc 0 T := Ico_subset_Icc_self ht
      have hh := exact_classical_time_limit hT.le U hc htime v P D hv hD hP ⟨t, htt⟩ x
      rw [(hwd t x).fderiv, hgrad t x]
      simpa only [w, d, g, extendPath, projIcc_of_mem hT.le htt] using
        hh.mono Ico_subset_Icc_self
    · intro t _ x
      rw [(hwd t x).fderiv]
      let s := projIcc 0 T hT.le t
      have hVt := ((ContinuousMap.evalCLM ℝ s).continuous.tendsto V).comp hV
      have hVs : V s ∈ solenoidalSpace := gradientSpace.isClosed_orthogonal.mem_of_tendsto hVt
        (Eventually.of_forall (fun k => hsol k s s.property))
      exact c1_solenoidal_trace (V s) hVs (v s) (D s) (hp s).1 (hp s).2.2.1 x
  · change v (projIcc 0 T hT.le 0) = u₀
    simpa only [projIcc_of_mem hT.le (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT.le⟩)] using hi.2.1

end ClockBarrier.Euler
