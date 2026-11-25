/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.Axisymmetry
public import ClockBarrier.Euler.VorticityRegularity
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.InnerProductSpace.SingularValues

/-! # Uniformly finite general coherence

Source: Section 2, general labels, of arXiv:2605.31587v3.
See docs/ERRATA-AND-DEVIATIONS.md for the conventions.
-/

@[expose] public section

namespace ClockBarrier.Euler

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

/-- The general coherent Euler class with all coherence constants uniformly finite.
The same measurable right singular frame is used for every block and slice.
Nonnegative extended integrals and sums enforce genuine finiteness. -/
def general_coherent_on (α : ℝ≥0) (T : ℝ) (u : ℝ → E₃ →ᵇ E₃) : Prop :=
  ∃ p : ℝ → E₃ → ℝ, ∃ h : classical_euler_on α T u p,
    (∀ t ∈ Ico 0 T, axisymmetric_no_swirl (u t)) ∧
    ∃ Φ : ℝ → E₃ → E₃,
      (∀ x, Φ 0 x = x) ∧
      (∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T)) ∧
      (∀ x, ∀ t ∈ Ico 0 T,
        HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t) ∧
      let F : ℝ → E₃ → E₃ →L[ℝ] E₃ := fun t a => fderiv ℝ (Φ t) a
      let σ : ℝ → E₃ → Fin 3 → ℝ := fun t a i => (F t a).toLinearMap.singularValues i
      let ω₀ : E₃ → E₃ := vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩)
      ∃ V : ℝ → E₃ → E₃ ≃ₗᵢ[ℝ] E₃,
        (∀ t ∈ Ico 0 T, ∀ i j : Fin 3,
          Measurable (fun a : E₃ => V t a (EuclideanSpace.single j 1) i)) ∧
        (∀ t ∈ Ico 0 T, ∀ a : E₃, ∃ U : E₃ ≃ₗᵢ[ℝ] E₃, ∀ η : E₃,
          F t a (V t a η) = U !₂[σ t a 0 * η 0, σ t a 1 * η 1, σ t a 2 * η 2]) ∧
        ∃ L ℓ c₁ c₂ M Tail K : {r : ℝ // 0 < r},
        ∃ b : ℝ → E₃ → ℤ → ℝ, ∃ BF Bparallel BR : ℝ → ℝ,
          let E : ℝ → E₃ → (Fin 3 → ℤ) → Set E₃ := fun t aStar k =>
            {a | let η := (V t aStar).symm (a - aStar)
              (2 : ℝ) ^ (k 2) ≤ |η 2| ∧ |η 2| < 2 * (2 : ℝ) ^ (k 2) ∧
              (2 : ℝ) ^ (k 0) * σ t aStar 2 * (2 : ℝ) ^ (k 2) / σ t aStar 0 ≤ |η 0| ∧
              |η 0| < 2 * ((2 : ℝ) ^ (k 0) * σ t aStar 2 * (2 : ℝ) ^ (k 2) /
                σ t aStar 0) ∧
              (2 : ℝ) ^ (k 1) * σ t aStar 2 * (2 : ℝ) ^ (k 2) / σ t aStar 1 ≤ |η 1| ∧
              |η 1| < 2 * ((2 : ℝ) ^ (k 1) * σ t aStar 2 * (2 : ℝ) ^ (k 2) /
                σ t aStar 1)}
          let Ec : ℝ → E₃ → (Fin 3 → ℤ) → Set E₃ := fun t aStar k =>
            E t aStar k ∩ {a | ‖a - aStar‖ < ℓ.val} ∩
              {a | ‖Φ t a - Φ t aStar‖ ≤ L.val}
          let A : ℝ → E₃ → (Fin 3 → ℤ) → ℝ → Set E₂ := fun t aStar k s =>
            {q | aStar + V t aStar !₂[q 0, q 1, s] ∈ Ec t aStar k}
          let avg : ℝ → E₃ → (Fin 3 → ℤ) → ℝ → E₃ := fun t aStar k s =>
            if volume (A t aStar k s) = 0 then 0 else
              (volume (A t aStar k s)).toReal⁻¹ •
                ∫ q in A t aStar k s, ω₀ (aStar + V t aStar !₂[q 0, q 1, s])
          IntegrableOn BF (Ico 0 T) volume ∧
          IntegrableOn Bparallel (Ico 0 T) volume ∧
          IntegrableOn BR (Ico 0 T) volume ∧
          (∀ t ∈ Ico 0 T, 0 ≤ BF t ∧ 0 ≤ Bparallel t ∧ 0 ≤ BR t) ∧
          (∀ t ∈ Ico 0 T, ∀ aStar a : E₃, ‖Φ t a - Φ t aStar‖ ≤ L.val →
            c₁.val * ‖F t aStar (a - aStar)‖ ≤ ‖Φ t a - Φ t aStar‖ ∧
            ‖Φ t a - Φ t aStar‖ ≤ c₂.val * ‖F t aStar (a - aStar)‖) ∧
          (∀ t ∈ Ico 0 T,
            (⨆ aStar : E₃, ∑' k : Fin 3 → ℤ,
              ∫⁻ a in E t aStar k ∩ {a | ‖Φ t a - Φ t aStar‖ ≤ L.val},
                ENNReal.ofReal (‖(F t a - F t aStar) (ω₀ a)‖ /
                  ‖Φ t a - Φ t aStar‖ ^ 3)) ≤ ENNReal.ofReal (BF t)) ∧
          (∀ t ∈ Ico 0 T, ∀ aStar : E₃, ∀ k : Fin 3 → ℤ,
            (∫⁻ a in Ec t aStar k,
              ENNReal.ofReal (‖ω₀ a - avg t aStar k ((V t aStar).symm (a - aStar) 2)‖)) ≤
            ENNReal.ofReal ((M.val * b t aStar (k 2)) *
              (Real.sqrt (((2 : ℝ) ^ (k 0)) ^ 2 + ((2 : ℝ) ^ (k 1)) ^ 2) *
                σ t aStar 2 * (2 : ℝ) ^ (k 2) / σ t aStar 1) ^ (α : ℝ) *
              ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1) * (σ t aStar 2) ^ 2 *
                ((2 : ℝ) ^ (k 2)) ^ 3 / (σ t aStar 0 * σ t aStar 1)))) ∧
          (∀ t ∈ Ico 0 T, ∀ aStar : E₃, ∀ n : ℤ, 0 ≤ b t aStar n) ∧
          (∀ t ∈ Ico 0 T,
            (⨆ aStar : E₃, ∑' n : ℤ, if (2 : ℝ) ^ n ≤ ℓ.val then
              ENNReal.ofReal (b t aStar n * ((2 : ℝ) ^ n) ^ (α : ℝ)) else 0) ≤
                ENNReal.ofReal Tail.val) ∧
          (∀ t ∈ Ico 0 T,
            (⨆ aStar : E₃, ∑' k : Fin 3 → ℤ,
              ∫⁻ a in Ec t aStar k,
                ENNReal.ofReal (σ t aStar 0 *
                  ‖avg t aStar k ((V t aStar).symm (a - aStar) 2) - ω₀ aStar‖ /
                    ‖Φ t a - Φ t aStar‖ ^ 3)) ≤ ENNReal.ofReal (Bparallel t)) ∧
          (∀ t ∈ Ico 0 T,
            (⨆ aStar : E₃,
              ∫⁻ a in {a : E₃ | ℓ.val ≤ ‖a - aStar‖ ∧ ‖Φ t a - Φ t aStar‖ ≤ L.val},
                ENNReal.ofReal (σ t aStar 0 * ‖ω₀ a - ω₀ aStar‖ /
                  ‖Φ t a - Φ t aStar‖ ^ 3)) ≤ ENNReal.ofReal (BR t)) ∧
          ∀ t ∈ Ico 0 T, ∀ aStar : E₃, σ t aStar 0 / σ t aStar 1 ≤ K.val

end ClockBarrier.Euler
