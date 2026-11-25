/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.ContinuousTimeIntegral

/-! # Limits of actual integral equations on a closed time interval -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.ContinuousTimeIntegral
open Set ContinuousLinearMap Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem hasDerivWithinAt_of_path_limits (T : ℝ) (hT : 0 ≤ T)
    (U Q : ℕ → C(Icc (0 : ℝ) T, E)) (F G : C(Icc (0 : ℝ) T, E))
    (hU : Tendsto U atTop (𝓝 F)) (hQ : Tendsto Q atTop (𝓝 G))
    (hd : ∀ k (t : Icc (0 : ℝ) T),
      HasDerivWithinAt (extendPath T hT (U k)) (Q k t) (Icc (0 : ℝ) T) t)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT F) (G t) (Icc (0 : ℝ) T) t := by
  let z : Icc (0 : ℝ) T := ⟨0, le_rfl, hT⟩
  have he (k : ℕ) : U k = ContinuousMap.const _ (U k z) + integral T hT (Q k) := by
    apply ContinuousMap.ext
    intro s
    have hh := eq_initial_add_integral T hT (Q k) (extendPath T hT (U k)) (hd k) s
    convert! (by simpa only [extendPath, projIcc_of_mem hT s.property,
      projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩)] using hh) using 1
  have hi := ((integral (E := E) T hT).continuous.tendsto G).comp hQ
  have hz := ((ContinuousMap.evalCLM ℝ z).continuous.tendsto F).comp hU
  have hc := ((ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T)).continuous.tendsto (F z)).comp hz
  have hlim := hc.add hi
  have heq : F = ContinuousMap.const _ (F z) + integral T hT G := by
    apply tendsto_nhds_unique hU
    convert! hlim using 1
    exact funext he
  have hder := (integral_hasDerivWithinAt T hT G t).const_add (F z)
  apply hder.congr_of_mem _ t.property
  intro s _
  conv_lhs => rw [heq]
  rfl

end ClockBarrier.Analysis.ContinuousTimeIntegral
