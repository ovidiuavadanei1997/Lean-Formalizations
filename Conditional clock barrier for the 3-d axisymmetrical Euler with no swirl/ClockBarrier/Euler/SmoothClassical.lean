/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.SmoothProjectedEquation
public import ClockBarrier.Analysis.SmoothHolderPath
public import ClockBarrier.Euler.Classical

/-! # Actual smooth trajectories satisfy the classical Euler interface -/
@[expose] public noncomputable section
namespace ClockBarrier.Euler.Smooth
open Set MeasureTheory ContinuousLinearMap ClockBarrier.Analysis
  Sobolev Solenoidal SmoothL2Field Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem classical_of_smooth (α : ℝ≥0) (hα : 0 < α) (hα1 : α < 1)
    (T : ℝ) (hT : 0 < T) (A : ℝ → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
    (hd : ∀ n, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => (A s).jetLp n)
      ((rhs (A t)).jetLp n) (Icc 0 T) t)
    (hs : ∀ t ∈ Icc 0 T, (A t).toLp ∈ solenoidalSpace) :
    classical_euler_on α T (fun t => finiteField (A t)) (fun t => pressure (A t)) := by
  have he (t : ℝ) : (finiteField (A t) : Space → Space) = (A t).field := funext (finiteField_apply _)
  have hc := continuous_finiteField A hA
  have hD := continuous_finiteField (fun t => (A t).derivative) (continuous_jetLp_derivative A hA)
  refine ⟨hT, hα, hα1, hc.continuousOn, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun t => finiteField (A t).derivative, hD.continuousOn, ?_, ?_⟩
    · intro t _ x
      rw [he, finiteField_apply]
      exact ((A t).smooth.differentiable (by simp) x).hasFDerivAt
    · intro b hb
      obtain ⟨H, hH⟩ := compact_holder (fun t : Icc (0 : ℝ) T => (A t).derivative)
        (fun n => (continuous_jetLp_derivative A hA n).comp continuous_subtype_val) α hα1.le
      refine ⟨H, fun t ht => ?_⟩
      have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.trans hb.2.le⟩
      intro x y
      simpa only [finiteField_apply] using hH ⟨t, htT⟩ x y
  · intro t _
    rw [he]
    exact (A t).memLp
  · intro t _
    have hcont : Tendsto (fun s => (A s).toLp) (𝓝[Ico 0 T] t) (𝓝 (A t).toLp) :=
      ((continuous_toLp A (hA 0)).tendsto t).mono_left nhdsWithin_le_nhds
    have hh := hcont.edist (tendsto_const_nhds (x := (A t).toLp))
    simp only [edist_self] at hh
    convert! hh using 1
    funext s
    rw [Lp.edist_def, he s, he t]
    apply eLpNorm_congr_ae
    exact ((A s).toLp_ae.sub (A t).toLp_ae).symm
  · intro t _
    exact (pressure_smooth (A t)).differentiable (by simp)
  · have hpf := continuous_finiteField (fun t => pressureForce (A t))
      (continuous_smooth_iff.mp (continuous_pressureForce.comp (continuous_smooth_iff.mpr hA)))
    have hh : Continuous (fun q : ℝ × Space => finiteField (pressureForce (A q.1)) q.2) :=
      ContinuousEval.continuous_eval.comp ((hpf.comp continuous_fst).prodMk continuous_snd)
    simpa only [finiteField_apply, pressure_gradient] using hh.continuousOn
  · intro t ht x
    have hh := field_hasDerivWithinAt A (rhs (A t)) (Icc 0 T) t
      (fun n => hd n t (Ico_subset_Icc_self ht)) x
    have heq : (rhs (A t)).field x = -(fderiv ℝ (A t).field x) ((A t).field x) - gradient (pressure (A t)) x := by
      have hh := eq_neg_of_add_eq_zero_left (by
        simpa only [add_assoc] using equation (A t) x)
      exact hh.trans (by abel)
    simpa only [he, heq] using hh.mono Ico_subset_Icc_self
  · intro t ht x
    rw [he]
    simpa [LinearMap.trace_eq_matrix_trace ℝ (PiLp.basisFun 2 ℝ (Fin 3)),
      Matrix.trace, LinearMap.toMatrix_apply] using solenoidal_divergence (A t) (hs t (Ico_subset_Icc_self ht)) x

end ClockBarrier.Euler.Smooth
