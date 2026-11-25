/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.RegularizedCauchy
public import ClockBarrier.Euler.SmoothRhsConvergence
public import ClockBarrier.Analysis.ContinuousOdeLimit

/-! # Constructing actual smooth Euler trajectories from the regularized equations -/
@[expose] public noncomputable section
namespace ClockBarrier.Euler.Smooth
open Set MeasureTheory ContinuousLinearMap ClockBarrier.Analysis
  Sobolev Solenoidal SmoothL2Field Regularized Filter Topology
local notation "Space" => EuclideanSpace ℝ (Fin 3)

/-- The short-time solution is constructed from the fixed initial field. The
initial interval depends on its H³ energy; no exact solution is an input. -/
theorem exists_smooth_local (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace) :
    ∃ V : ℝ → SmoothL2Field Space,
      V 0 = A ∧ (∀ n, Continuous (fun t => (V t).jetLp n)) ∧
      (∀ n, ∀ t ∈ Icc 0 (regularizedTime A),
        HasDerivWithinAt (fun s => (V s).jetLp n) ((rhs (V t)).jetLp n)
          (Icc 0 (regularizedTime A)) t) ∧
      ∀ t ∈ Icc 0 (regularizedTime A),
        (V t).toLp ∈ solenoidalSpace ∧ ‖(V t).toLp‖ = ‖A.toLp‖ := by
  let T := regularizedTime A
  have hT : 0 ≤ T := (regularizedTime_pos A).le
  let K := Icc (0 : ℝ) T
  letI : Nonempty K := ⟨⟨0, le_rfl, hT⟩⟩
  obtain ⟨U, hU⟩ := exists_smooth_family_uniform A hA
  have hc k := (hU k).2.1
  have hd k := (hU k).2.2.1
  have hs k := (hU k).2.2.2.1
  have hb k := (hU k).2.2.2.2
  let W (k : ℕ) (t : K) := U k t
  have hW (k n : ℕ) : Continuous (fun t => (W k t).jetLp n) :=
    (hc k n).comp continuous_subtype_val
  have hw : CauchySeq (fun k => fieldPath (W k) (hW k)) :=
    regularized_cauchy hT hc hd (fun k t ht => (hs k t ht).1)
      (regularizedWordBound A 4) (fun k => hb k 4)
      (fun j k => by rw [(hU k).1, (hU j).1])
  obtain ⟨F, hF, hf, hj, _⟩ := exists_smooth_limit W hW
    (fun q => ⟨regularizedWordBound A q, fun k t => hb k q t t.property⟩) hw
  have hpoint (t : K) : Tendsto (fun k => (W k t).toLp) atTop (𝓝 (F t).toLp) :=
    ((ContinuousMap.evalCLM ℝ t).continuous.tendsto _).comp hf
  have hFs (t : K) : (F t).toLp ∈ solenoidalSpace :=
    gradientSpace.isClosed_orthogonal.mem_of_tendsto (hpoint t)
      (Eventually.of_forall (fun k => (hs k t t.property).1))
  have hnorm (t : K) : ‖(F t).toLp‖ = ‖A.toLp‖ := by
    have hh := (hpoint t).norm
    have he (k : ℕ) : ‖(W k t).toLp‖ = ‖A.toLp‖ := (hs k t t.property).2
    simp only [he] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  let z : K := ⟨0, le_rfl, hT⟩
  have hini : F z = A := by
    apply SmoothL2Field.toLp_injective
    have hh := hpoint z
    have he (k : ℕ) : (W k z).toLp = A.toLp := congrArg SmoothL2Field.toLp (hU k).1
    simp only [he] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  let V (t : ℝ) := F (projIcc 0 T hT t)
  have hv (t : ℝ) (ht : t ∈ Icc 0 T) : V t = F ⟨t, ht⟩ := by
    simp only [V, projIcc_of_mem hT ht]
  refine ⟨V, ?_, fun n => (hF n).comp continuous_projIcc, ?_, ?_⟩
  · exact (hv 0 z.property).trans hini
  · intro n t ht
    have hQ k := continuous_smooth_iff.mp ((smoothRhs_continuous k).comp
      (continuous_smooth_iff.mpr (hW k)))
    have hR := continuous_smooth_iff.mp (continuous_rhs.comp (continuous_smooth_iff.mpr hF))
    have hlim := smoothRhs_tendsto W hW F hF hj hFs n
    have hder := ContinuousTimeIntegral.hasDerivWithinAt_of_path_limits T hT
      (fun k => jetPath (W k) (hW k) n)
      (fun k => jetPath (fun r => smoothRhs k (W k r)) (hQ k) n)
      (jetPath F hF n) (jetPath (fun r => rhs (F r)) hR n) (hj n) hlim
      (fun k r => ?_) ⟨t, ht⟩
    · convert! hder using 1
      rw [hv t ht]
      rfl
    · apply (hd k n r r.property).hasDerivWithinAt.congr_of_mem _ r.property
      intro s hss
      simp only [ContinuousTimeIntegral.extendPath, projIcc_of_mem hT hss, jetPath_apply]
      rfl
  · intro t ht
    rw [hv t ht]
    exact ⟨hFs ⟨t, ht⟩, hnorm ⟨t, ht⟩⟩

end ClockBarrier.Euler.Smooth
