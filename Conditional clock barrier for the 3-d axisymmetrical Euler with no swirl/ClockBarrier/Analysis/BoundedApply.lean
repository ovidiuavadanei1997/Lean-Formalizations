/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Continuous pointwise application in bounded-function spaces -/

public section

namespace ClockBarrier.Analysis

open scoped BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Pointwise application of continuous bounded operator and vector families
is again a continuous family in the bounded-function norm. -/
theorem exists_continuous_bounded_apply
    {S : Type*} [TopologicalSpace S]
    (D : S → E₃ →ᵇ (E₃ →L[ℝ] E₃)) (u : S → E₃ →ᵇ E₃)
    (hD : Continuous D) (hu : Continuous u) :
    ∃ N : S → E₃ →ᵇ E₃, Continuous N ∧ ∀ t x, N t x = D t x (u t x) := by
  let a (d : E₃ →ᵇ (E₃ →L[ℝ] E₃)) (v : E₃ →ᵇ E₃) : E₃ →ᵇ E₃ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun x => d x (v x))
      (d.continuous.clm_apply v.continuous) (‖d‖ * ‖v‖)
      (fun x => ((d x).le_opNorm (v x)).trans
        (mul_le_mul (d.norm_coe_le_norm x) (v.norm_coe_le_norm x)
          (norm_nonneg (v x)) (norm_nonneg d)))
  have ha (d : E₃ →ᵇ (E₃ →L[ℝ] E₃)) (v : E₃ →ᵇ E₃) (x : E₃) : a d v x = d x (v x) := rfl
  let B : (E₃ →ᵇ (E₃ →L[ℝ] E₃)) →ₗ[ℝ] (E₃ →ᵇ E₃) →ₗ[ℝ] (E₃ →ᵇ E₃) :=
    LinearMap.mk₂ ℝ a
      (by intro d e v; ext x; simp [ha])
      (by intro c d v; ext x; simp [ha])
      (by intro d v w; ext x; simp [ha])
      (by intro c d v; ext x; simp [ha])
  have hb (d : E₃ →ᵇ (E₃ →L[ℝ] E₃)) (v : E₃ →ᵇ E₃) :
      ‖B d v‖ ≤ 1 * ‖d‖ * ‖v‖ := by
    rw [one_mul]
    exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
      (mul_nonneg (norm_nonneg d) (norm_nonneg v))
      (fun x => ((d x).le_opNorm (v x)).trans
        (mul_le_mul (d.norm_coe_le_norm x) (v.norm_coe_le_norm x)
          (norm_nonneg (v x)) (norm_nonneg d)))
  let A : (E₃ →ᵇ (E₃ →L[ℝ] E₃)) →L[ℝ] (E₃ →ᵇ E₃) →L[ℝ] (E₃ →ᵇ E₃) :=
    LinearMap.mkContinuous₂ (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜₃ := ℝ)
      (E := E₃ →ᵇ (E₃ →L[ℝ] E₃)) (F := E₃ →ᵇ E₃) (G := E₃ →ᵇ E₃) B 1 hb
  exact ⟨fun t => A (D t) (u t), (A.continuous.comp hD).clm_apply hu, fun _ _ => rfl⟩

end ClockBarrier.Analysis
