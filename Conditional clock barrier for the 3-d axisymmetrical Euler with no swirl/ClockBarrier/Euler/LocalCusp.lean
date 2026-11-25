/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.LocalSliceHolder
public import ClockBarrier.Euler.GeneralCoherenceWellDefined
import ClockBarrier.Analysis.RotatedBoxVolume
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The local transverse cusp estimate for classical Euler flows

The initial vorticity Hölder bound supplies one constant for all times and
orthogonal frames. The enclosing-box volume factor is absorbed in this constant.
-/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

/-- The exact integrated transverse cusp estimate holds with one positive
constant and `b = 1`; no deformation-smallness or singular-value gap is required. -/
theorem classical_euler_on.exists_local_cusp_bound
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x) :
    ∃ M : ℝ, 0 < M ∧ ∀ t ∈ Ico 0 T, ∀ (aStar : E₃) (V : E₃ ≃ₗᵢ[ℝ] E₃)
      (k : Fin 3 → ℤ) (ℓ L : ℝ),
    let σ := fun i : Fin 3 => (fderiv ℝ (Φ t) aStar).toLinearMap.singularValues i
    let w₀ := vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩)
    let E := {a : E₃ | let η := V.symm (a - aStar)
      (2 : ℝ) ^ (k 2) ≤ |η 2| ∧ |η 2| < 2 * (2 : ℝ) ^ (k 2) ∧
      (2 : ℝ) ^ (k 0) * σ 2 * (2 : ℝ) ^ (k 2) / σ 0 ≤ |η 0| ∧
      |η 0| < 2 * ((2 : ℝ) ^ (k 0) * σ 2 * (2 : ℝ) ^ (k 2) / σ 0) ∧
      (2 : ℝ) ^ (k 1) * σ 2 * (2 : ℝ) ^ (k 2) / σ 1 ≤ |η 1| ∧
      |η 1| < 2 * ((2 : ℝ) ^ (k 1) * σ 2 * (2 : ℝ) ^ (k 2) / σ 1)}
    let Ec := E ∩ {a | ‖a - aStar‖ < ℓ} ∩ {a | ‖Φ t a - Φ t aStar‖ ≤ L}
    let A := fun z : ℝ => {q : E₂ | aStar + V !₂[q 0, q 1, z] ∈ Ec}
    let avg := fun z => if volume (A z) = 0 then (0 : E₃) else
      (volume (A z)).toReal⁻¹ • ∫ q in A z, w₀ (aStar + V !₂[q 0, q 1, z])
    (∫⁻ a in Ec, ENNReal.ofReal ‖w₀ a - avg (V.symm (a - aStar) 2)‖) ≤
      ENNReal.ofReal (M *
        (Real.sqrt (((2 : ℝ) ^ (k 0)) ^ 2 + ((2 : ℝ) ^ (k 1)) ^ 2) *
          σ 2 * (2 : ℝ) ^ (k 2) / σ 1) ^ (α : ℝ) *
        ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1) * (σ 2) ^ 2 *
          ((2 : ℝ) ^ (k 2)) ^ 3 / (σ 0 * σ 1))) := by
  obtain ⟨W, _, hW, hHolder⟩ := h.exists_boundedContinuous_vorticity
  obtain ⟨H, hH⟩ := hHolder 0 ⟨le_rfl, h.1⟩
  refine ⟨64 * ((H : ℝ) * (4 : ℝ) ^ (α : ℝ)) + 1, by positivity,
    fun t ht aStar V k ℓ L => ?_⟩
  intro σ w₀
  have hw : w₀ = W 0 := (funext (hW 0 ⟨le_rfl, h.1⟩)).symm
  simp (config := { zeta := false }) only [hw]
  intro E Ec A avg
  have hσ (i : Fin 3) : 0 < σ i :=
    h.singularValues_fderiv_flow_pos hcont hode hinit ht aStar i
  have hσ₀ := hσ 0
  have hσ₁ := hσ 1
  have hσ₂ := hσ 2
  have horder : σ 1 ≤ σ 0 :=
    (fderiv ℝ (Φ t) aStar).toLinearMap.singularValues_antitone (by decide : 0 ≤ 1)
  have hm : MeasurableSet Ec := measurableSet_singular_clock_block
    (h.contDiff_bijective_measurePreserving_flow hcont hode hinit ht).1.continuous
    aStar V σ k ℓ L
  have havg : ∀ᵐ a ∂volume.restrict Ec, ‖avg (V.symm (a - aStar) 2) - W 0 a‖ ≤
      ((H : ℝ) * (4 : ℝ) ^ (α : ℝ)) *
        ((σ 2 * (2 : ℝ) ^ (k 2) / σ 1) *
          Real.sqrt (((2 : ℝ) ^ (k 0)) ^ 2 + ((2 : ℝ) ^ (k 1)) ^ 2)) ^ (α : ℝ) := by
    apply ae_norm_clock_average_sub_value_le aStar V (W 0) (hH 0 ⟨le_rfl, le_rfl⟩)
      hm (fun _ ha => ha.1.2) (by positivity) (by positivity) (by positivity)
    intro a ha
    have he := ha.1.1
    refine ⟨he.2.2.2.1.le.trans ?_, ?_⟩
    · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      calc
        _ ≤ (2 : ℝ) ^ (k 0) * σ 2 * (2 : ℝ) ^ (k 2) / σ 1 :=
          div_le_div_of_nonneg_left (by positivity) hσ₁ horder
        _ = _ := by ring
    · simpa only [mul_div_assoc, mul_assoc] using he.2.2.2.2.2.le
  have hvol : volume Ec ≤ ENNReal.ofReal
      (64 * ((2 : ℝ) ^ (k 0) * σ 2 * (2 : ℝ) ^ (k 2) / σ 0) *
        ((2 : ℝ) ^ (k 1) * σ 2 * (2 : ℝ) ^ (k 2) / σ 1) * (2 : ℝ) ^ (k 2)) := by
    apply Analysis.volume_le_rotated_shell_box aStar V
      ![(2 : ℝ) ^ (k 0) * σ 2 * (2 : ℝ) ^ (k 2) / σ 0,
        (2 : ℝ) ^ (k 1) * σ 2 * (2 : ℝ) ^ (k 2) / σ 1, (2 : ℝ) ^ (k 2)]
    · intro i
      fin_cases i <;> dsimp <;> positivity
    · intro a ha i
      have he := ha.1.1
      fin_cases i
      · exact he.2.2.2.1.le
      · exact he.2.2.2.2.2.le
      · exact he.2.1.le
  let Q := Real.sqrt (((2 : ℝ) ^ (k 0)) ^ 2 + ((2 : ℝ) ^ (k 1)) ^ 2) *
    σ 2 * (2 : ℝ) ^ (k 2) / σ 1
  let J := (2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1) * (σ 2) ^ 2 *
    ((2 : ℝ) ^ (k 2)) ^ 3 / (σ 0 * σ 1)
  have hQ : (σ 2 * (2 : ℝ) ^ (k 2) / σ 1) *
      Real.sqrt (((2 : ℝ) ^ (k 0)) ^ 2 + ((2 : ℝ) ^ (k 1)) ^ 2) = Q := by
    dsimp [Q]
    ring
  rw [hQ] at havg
  have hJ : 64 * ((2 : ℝ) ^ (k 0) * σ 2 * (2 : ℝ) ^ (k 2) / σ 0) *
      ((2 : ℝ) ^ (k 1) * σ 2 * (2 : ℝ) ^ (k 2) / σ 1) * (2 : ℝ) ^ (k 2) =
      64 * J := by
    dsimp [J]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hJ] at hvol
  have hQ₀ : 0 ≤ Q := by dsimp [Q]; positivity
  have hJ₀ : 0 ≤ J := by dsimp [J]; positivity
  change _ ≤ ENNReal.ofReal ((64 * ((H : ℝ) * (4 : ℝ) ^ (α : ℝ)) + 1) *
    Q ^ (α : ℝ) * J)
  calc
    _ ≤ ∫⁻ _a in Ec, ENNReal.ofReal (((H : ℝ) * (4 : ℝ) ^ (α : ℝ)) * Q ^ (α : ℝ)) := by
      apply lintegral_mono_ae
      filter_upwards [havg] with a ha
      apply ENNReal.ofReal_le_ofReal
      rw [norm_sub_rev]
      exact ha
    _ = ENNReal.ofReal (((H : ℝ) * (4 : ℝ) ^ (α : ℝ)) * Q ^ (α : ℝ)) * volume Ec := by
      simp only [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal (((H : ℝ) * (4 : ℝ) ^ (α : ℝ)) * Q ^ (α : ℝ)) *
        ENNReal.ofReal (64 * J) := mul_le_mul_right hvol _
    _ = ENNReal.ofReal ((64 * ((H : ℝ) * (4 : ℝ) ^ (α : ℝ))) * Q ^ (α : ℝ) * J) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        (Real.rpow_nonneg hQ₀ _)) hJ₀)

end ClockBarrier.Euler
