/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.GeneralTransverseSum
public import ClockBarrier.Euler.GeneralBlockMeasure
public import ClockBarrier.Analysis.CoherenceAssembly

/-! # Combining the initial-vorticity contributions -/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

/-- The clock transverse and longitudinal budgets, together with the off-clock
budget, control the full initial-vorticity increment on the physical near region. -/
theorem classical_euler_on.initial_increment_lintegral_bound
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x) {t : ℝ} (ht : t ∈ Ico 0 T)
    (aStar : E₃) (U V : E₃ ≃ₗᵢ[ℝ] E₃) (L ℓ : ℝ)
    {c M Tail K BP BR : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hTail : 0 ≤ Tail) (hK : 0 < K) (b : ℤ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (hBP : 0 ≤ BP) (hBR : 0 ≤ BR) :
    let F := fderiv ℝ (Φ t) aStar
    let σ := fun i : Fin 3 => F.toLinearMap.singularValues i
    let w₀ := vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩)
    let d := fun a => Φ t a - Φ t aStar
    let E := fun k : Fin 3 → ℤ => {a : E₃ | let η := V.symm (a - aStar)
      ((2 : ℝ) ^ (k 2)) ≤ |η 2| ∧ |η 2| < 2 * ((2 : ℝ) ^ (k 2)) ∧
      ((2 : ℝ) ^ (k 0)) * σ 2 * ((2 : ℝ) ^ (k 2)) / σ 0 ≤ |η 0| ∧ |η 0| < 2 * (((2 : ℝ) ^ (k 0)) * σ 2 * ((2 : ℝ) ^ (k 2)) / σ 0) ∧
      ((2 : ℝ) ^ (k 1)) * σ 2 * ((2 : ℝ) ^ (k 2)) / σ 1 ≤ |η 1| ∧ |η 1| < 2 * (((2 : ℝ) ^ (k 1)) * σ 2 * ((2 : ℝ) ^ (k 2)) / σ 1)} ∩
      {a | ‖a - aStar‖ < ℓ} ∩ {a | ‖d a‖ ≤ L}
    let A := fun (k : Fin 3 → ℤ) (z : ℝ) => {q : E₂ | aStar + V !₂[q 0, q 1, z] ∈ E k}
    let avg := fun (k : Fin 3 → ℤ) (z : ℝ) => if volume (A k z) = 0 then (0 : E₃) else
      (volume (A k z)).toReal⁻¹ • ∫ q in A k z, w₀ (aStar + V !₂[q 0, q 1, z])
    let v := fun k a => w₀ a - avg k (V.symm (a - aStar) 2)
    (∀ η : E₃, F (V η) = U !₂[σ 0 * η 0, σ 1 * η 1, σ 2 * η 2]) →
    (∀ a, ‖d a‖ ≤ L → c * ‖F (a - aStar)‖ ≤ ‖d a‖) →
    (∀ k, (∫⁻ a in E k, ENNReal.ofReal (‖v k a‖)) ≤ ENNReal.ofReal
      ((M * b (k 2)) * (Real.sqrt (((2 : ℝ) ^ (k 0)) ^ 2 + ((2 : ℝ) ^ (k 1)) ^ 2) * σ 2 * ((2 : ℝ) ^ (k 2)) / σ 1) ^ (α : ℝ) *
        (((2 : ℝ) ^ (k 0)) * ((2 : ℝ) ^ (k 1)) * (σ 2) ^ 2 * ((2 : ℝ) ^ (k 2)) ^ 3 / (σ 0 * σ 1)))) →
    (∑' n : ℤ, if (2 : ℝ) ^ n ≤ ℓ then
      ENNReal.ofReal (b n * ((2 : ℝ) ^ n) ^ (α : ℝ)) else 0) ≤ ENNReal.ofReal Tail →
    σ 0 / σ 1 ≤ K →
    let w := fun j : ℤ × ℤ =>
      (Real.sqrt (((2 : ℝ) ^ j.1) ^ 2 + ((2 : ℝ) ^ j.2) ^ 2)) ^ (α : ℝ) *
        (2 : ℝ) ^ j.1 * (2 : ℝ) ^ j.2 /
      (Real.sqrt (1 + ((2 : ℝ) ^ j.1) ^ 2 + ((2 : ℝ) ^ j.2) ^ 2)) ^ 3
    (∑' k, ∫⁻ a in E k, ENNReal.ofReal (σ 0 *
      ‖avg k (V.symm (a - aStar) 2) - w₀ aStar‖ / ‖d a‖ ^ 3)) ≤ ENNReal.ofReal BP →
    (∫⁻ a in {a : E₃ | ℓ ≤ ‖a - aStar‖ ∧ ‖d a‖ ≤ L},
      ENNReal.ofReal (σ 0 * ‖w₀ a - w₀ aStar‖ / ‖d a‖ ^ 3)) ≤ ENNReal.ofReal BR →
    (∫⁻ a in {a : E₃ | ‖d a‖ ≤ L},
      ENNReal.ofReal (σ 0 * ‖w₀ a - w₀ aStar‖ / ‖d a‖ ^ 3)) ≤
      ENNReal.ofReal (BP + BR + (2 * (M / c ^ 3) * K ^ (((α : ℝ) + 1) / 2) *
        (∑' j, w j) * Tail) * (σ 2) ^ ((3 * (α : ℝ) - 1) / 2)) := by
  intro F σ w₀ d E A avg v hframe hnear hmass htail hdist w hlong hoff
  have hσ (i : Fin 3) : 0 < σ i :=
    h.singularValues_fderiv_flow_pos hcont hode hinit ht aStar i
  have htrans := h.transverse_majorant_sum_bound hcont hode hinit ht aStar U V L ℓ
    hc hM hTail hK b hb hframe hnear hmass htail hdist
  have hreg := (h.contDiff_bijective_measurePreserving_flow hcont hode hinit ht).1
  have hd : Continuous d := hreg.continuous.sub continuous_const
  have hE (k : Fin 3 → ℤ) : MeasurableSet (E k) :=
    measurableSet_singular_clock_block hreg.continuous aStar V σ k ℓ L
  have havg (k : Fin 3 → ℤ) : StronglyMeasurable (avg k) :=
    (h.initial_vorticity_clock_slices aStar V (hE k) (fun a ha => ha.1.2)).2
  have hz : Continuous (fun a : E₃ => V.symm (a - aStar) 2) := by fun_prop
  let q := (2 * (M / c ^ 3) * K ^ (((α : ℝ) + 1) / 2) *
    (∑' j, w j) * Tail) * (σ 2) ^ ((3 * (α : ℝ) - 1) / 2)
  let g := fun a => σ 0 * ‖w₀ a - w₀ aStar‖ / ‖d a‖ ^ 3
  let gT := fun k a => σ 0 * ‖v k a‖ / ‖d a‖ ^ 3
  let gP := fun k a => σ 0 * ‖avg k (V.symm (a - aStar) 2) - w₀ aStar‖ / ‖d a‖ ^ 3
  let sc := {a : E₃ | ‖a - aStar‖ < ℓ ∧ ‖d a‖ ≤ L}
  let sr := {a : E₃ | ℓ ≤ ‖a - aStar‖ ∧ ‖d a‖ ≤ L}
  have hcover : (⋃ k, E k) =ᵐ[volume] sc := by
    simpa only [E, sc, inter_assoc, setOf_and] using
      iUnion_singular_shell_inter_ae_eq aStar V hσ sc
  have hgT (k : Fin 3 → ℤ) : Measurable (gT k) := by
    have hv : Measurable (v k) := (h.continuous_vorticity 0 ⟨le_rfl, h.1⟩).measurable.sub
      ((havg k).measurable.comp hz.measurable)
    exact (measurable_const.mul hv.norm).div ((hd.norm.pow 3).measurable)
  have hgT₀ (k : Fin 3 → ℤ) (a : E₃) : 0 ≤ gT k a :=
    div_nonneg (mul_nonneg (hσ 0).le (norm_nonneg _)) (pow_nonneg (norm_nonneg _) 3)
  have hgP₀ (k : Fin 3 → ℤ) (a : E₃) : 0 ≤ gP k a :=
    div_nonneg (mul_nonneg (hσ 0).le (norm_nonneg _)) (pow_nonneg (norm_nonneg _) 3)
  have hpoint (k : Fin 3 → ℤ) (a : E₃) :
      ENNReal.ofReal (g a) ≤ ENNReal.ofReal (gT k a) + ENNReal.ofReal (gP k a) := by
    rw [← ENNReal.ofReal_add (hgT₀ k a) (hgP₀ k a)]
    apply ENNReal.ofReal_le_ofReal
    dsimp only [g, gT, gP, v]
    rw [← add_div, ← mul_add]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (norm_sub_le_norm_sub_add_norm_sub (w₀ a) (avg k (V.symm (a - aStar) 2)) (w₀ aStar)) (hσ 0).le)
      (pow_nonneg (norm_nonneg _) 3)
  have hclock : (∫⁻ a in sc, ENNReal.ofReal (g a)) ≤ ENNReal.ofReal q + ENNReal.ofReal BP :=
    (Analysis.lintegral_le_of_cover_add hcover hE (fun k => (hgT k).ennreal_ofReal)
      (fun k a _ => hpoint k a)).trans (add_le_add htrans hlong)
  have hw₀ (j : ℤ × ℤ) : 0 ≤ w j := by dsimp only [w]; positivity
  have hq : 0 ≤ q := by
    have hws : 0 ≤ ∑' j, w j := tsum_nonneg hw₀
    have hν := (hσ 2).le
    dsimp only [q]
    positivity
  have hs : {a : E₃ | ‖d a‖ ≤ L} = sc ∪ sr := by
    ext a
    change ‖d a‖ ≤ L ↔ (‖a - aStar‖ < ℓ ∧ ‖d a‖ ≤ L) ∨
      (ℓ ≤ ‖a - aStar‖ ∧ ‖d a‖ ≤ L)
    exact ⟨fun ha => (lt_or_ge ‖a - aStar‖ ℓ).elim
      (fun hc => Or.inl ⟨hc, ha⟩) (fun hr => Or.inr ⟨hr, ha⟩),
      fun ha => ha.elim And.right And.right⟩
  calc
    (∫⁻ a in {a : E₃ | ‖d a‖ ≤ L}, ENNReal.ofReal (g a)) ≤
        (∫⁻ a in sc, ENNReal.ofReal (g a)) + ∫⁻ a in sr, ENNReal.ofReal (g a) := by
      rw [hs]
      exact lintegral_union_le _ _ _
    _ ≤ (ENNReal.ofReal q + ENNReal.ofReal BP) + ENNReal.ofReal BR :=
      add_le_add hclock hoff
    _ = ENNReal.ofReal (BP + BR + q) := by
      rw [← ENNReal.ofReal_add hq hBP, ← ENNReal.ofReal_add (add_nonneg hq hBP) hBR]
      congr 1
      ring

end ClockBarrier.Euler
