/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.GeneralTransverseMajorant
public import ClockBarrier.Analysis.GeneralClockSeries

/-! # Summing the actual transverse clock contributions -/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

/-- The two angular regions share a uniform constant after axial truncation
and bounded transverse distortion are applied to the actual block integrals. -/
theorem classical_euler_on.transverse_majorant_sum_bound
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x) {t : ℝ} (ht : t ∈ Ico 0 T)
    (aStar : E₃) (U V : E₃ ≃ₗᵢ[ℝ] E₃) (L ℓ : ℝ)
    {c M Tail K : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hTail : 0 ≤ Tail) (hK : 0 < K) (b : ℤ → ℝ) (hb : ∀ n, 0 ≤ b n)
    :
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
    (∑' k, ∫⁻ a in E k, ENNReal.ofReal (σ 0 * ‖v k a‖ / ‖d a‖ ^ 3)) ≤
      ENNReal.ofReal ((2 * (M / c ^ 3) * K ^ (((α : ℝ) + 1) / 2) *
        (∑' j, w j) * Tail) * (σ 2) ^ ((3 * (α : ℝ) - 1) / 2)) := by
  intro F σ w₀ d E A avg v hframe hnear hmass htail hdist w
  have hσ (i : Fin 3) : 0 < σ i :=
    h.singularValues_fderiv_flow_pos hcont hode hinit ht aStar i
  have hblock (k : Fin 3 → ℤ) := h.transverse_majorant_block_bound
    hcont hode hinit ht aStar U V k L ℓ hc hM (hb (k 2)) hframe hnear (hmass k)
  let f := fun (k : Fin 3 → ℤ) a => σ 0 * ‖v k a‖ / ‖d a‖ ^ 3
  let r := fun k => ∫ a in E k, f k a
  let bt := fun n : ℤ => if (2 : ℝ) ^ n ≤ ℓ then b n * ((2 : ℝ) ^ n) ^ (α : ℝ) else 0
  let C := (M / c ^ 3) * (σ 2) ^ ((3 * (α : ℝ) - 1) / 2) *
    K ^ (((α : ℝ) + 1) / 2)
  have hf₀ (k : Fin 3 → ℤ) (a : E₃) : 0 ≤ f k a :=
    div_nonneg (mul_nonneg (hσ 0).le (norm_nonneg _)) (pow_nonneg (norm_nonneg _) 3)
  have hr₀ (k : Fin 3 → ℤ) : 0 ≤ r k := integral_nonneg (hf₀ k)
  have hbt := Analysis.summable_truncated_axial_tail_of_budget hb hTail htail
  have hbt₀ (n : ℤ) : 0 ≤ bt n := by
    dsimp only [bt]
    split_ifs
    · exact mul_nonneg (hb n) (Real.rpow_nonneg (zpow_nonneg (by norm_num) n) _)
    · exact le_rfl
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg (div_nonneg hM (pow_nonneg hc.le 3)) (Real.rpow_nonneg (hσ 2).le _))
    (Real.rpow_nonneg hK.le _)
  have hκ : (σ 0 / σ 1) ^ (((α : ℝ) + 1) / 2) ≤ K ^ (((α : ℝ) + 1) / 2) :=
    Real.rpow_le_rpow (div_nonneg (hσ 0).le (hσ 1).le) hdist (by positivity)
  have hbound (k : Fin 3 → ℤ) : r k ≤ C * (w (k 0, k 1) * bt (k 2)) := by
    by_cases hk : (2 : ℝ) ^ (k 2) ≤ ℓ
    · have hr := (hblock k).2
      change r k ≤ (M * b (k 2) / c ^ 3) * ((2 : ℝ) ^ (k 2)) ^ (α : ℝ) *
        (σ 2) ^ ((3 * (α : ℝ) - 1) / 2) * (σ 0 / σ 1) ^ (((α : ℝ) + 1) / 2) *
        w (k 0, k 1) at hr
      have hbk := hb (k 2)
      have hν := (hσ 2).le
      have hw : 0 ≤ w (k 0, k 1) := by dsimp only [w]; positivity
      refine hr.trans ((mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hκ (by positivity)) hw).trans_eq ?_)
      dsimp only [C, bt]
      rw [if_pos hk]
      ring
    · have hE : E k = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro a ha
        exact hk (Geometry.axial_shell_lt_clock_radius V ha.1.1.1 ha.1.2).le
      simp only [r, hE, setIntegral_empty, bt, if_neg hk, mul_zero, le_refl]
  obtain ⟨hrsum, _, hregions⟩ := Analysis.summable_general_clock_subseries
    α.coe_nonneg h.2.2.1 hC hbt.1 hbt₀ hbt.2 hr₀ hbound
  let cone : Set (ℤ × ℤ) := {j | (1 / 2 : ℝ) ≤
    Real.sqrt (((2 : ℝ) ^ j.1) ^ 2 + ((2 : ℝ) ^ j.2) ^ 2) ∧
    Real.sqrt (((2 : ℝ) ^ j.1) ^ 2 + ((2 : ℝ) ^ j.2) ^ 2) ≤ 2}
  have hsum : (∑' k, r k) ≤ 2 * (C * (∑' j, w j) * Tail) := by
    rw [← hrsum.tsum_subtype_add_tsum_subtype_compl {k | (k 0, k 1) ∈ cone}]
    exact (add_le_add (hregions cone).2 (hregions coneᶜ).2).trans_eq (by ring)
  calc
    (∑' k, ∫⁻ a in E k, ENNReal.ofReal (f k a)) = ∑' k, ENNReal.ofReal (r k) := by
      apply tsum_congr
      intro k
      exact (ofReal_integral_eq_lintegral_ofReal (hblock k).1
        (Filter.Eventually.of_forall (hf₀ k))).symm
    _ = ENNReal.ofReal (∑' k, r k) := (ENNReal.ofReal_tsum_of_nonneg hr₀ hrsum).symm
    _ ≤ ENNReal.ofReal (2 * (C * (∑' j, w j) * Tail)) := ENNReal.ofReal_le_ofReal hsum
    _ = _ := by congr 1; dsimp only [C]; ring

end ClockBarrier.Euler
