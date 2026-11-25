/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.GeneralAngular

/-! # Summing both integer angular indices without finite pair counting -/

public section
namespace ClockBarrier.Analysis

/-- The gap between two ordered angular indices supplies a summable geometric factor. -/
theorem general_angular_weight_le_geometric_gap {α : ℝ} (hα : 0 ≤ α) (m : ℤ) (n : ℕ) :
    let a := (2 : ℝ) ^ (m - (n : ℤ))
    let b := (2 : ℝ) ^ m
    (Real.sqrt (a ^ 2 + b ^ 2)) ^ α * a * b /
      (Real.sqrt (1 + a ^ 2 + b ^ 2)) ^ 3 ≤
      (2 : ℝ) ^ α * min (b ^ (α + 2)) (b ^ (α - 1)) * (2⁻¹ : ℝ) ^ n := by
  intro a b
  have hb : 0 < b := zpow_pos (by norm_num) m
  have ha : 0 < a := zpow_pos (by norm_num) _
  have hab : a ≤ b := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have haeq : a = b * (2⁻¹ : ℝ) ^ n := by
    dsimp only [a, b]
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, div_eq_mul_inv, inv_pow]
  have hs := general_angular_weight_le_small ha hb hab hα
  have hl := general_angular_weight_le_large ha hb hab hα
  rw [mul_min_of_nonneg _ _ (by positivity), min_mul_of_nonneg _ _ (by positivity)]
  refine le_min (hs.trans_eq ?_) (hl.trans_eq ?_)
  · rw [haeq, show α + 2 = (α + 1) + 1 by ring]
    simp only [Real.rpow_add hb, Real.rpow_one]
    ring
  · rw [haeq, show α - 1 = (α - 2) + 1 by ring]
    simp only [Real.rpow_add hb, Real.rpow_one]
    ring

/-- Ordered angular pairs are summable through their maximum scale and nonnegative gap. -/
theorem summable_general_angular_gap {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1) :
    Summable (fun p : ℤ × ℕ =>
      let a := (2 : ℝ) ^ (p.1 - (p.2 : ℤ))
      let b := (2 : ℝ) ^ p.1
      (Real.sqrt (a ^ 2 + b ^ 2)) ^ α * a * b /
        (Real.sqrt (1 + a ^ 2 + b ^ 2)) ^ 3) := by
  have hs := (summable_general_radial_weight (by linarith : -2 < α) hα₁).mul_of_nonneg
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1))
    (fun k => le_min (by positivity) (by positivity)) (fun n => pow_nonneg (by norm_num) n)
  refine (hs.mul_left ((2 : ℝ) ^ α)).of_nonneg_of_le (fun p => by dsimp; positivity) ?_
  intro p
  simpa only [mul_assoc] using general_angular_weight_le_geometric_gap hα₀ p.1 p.2

/-- Both angular indices range over all integers. Infinite fibers are controlled by
geometric weights, with no finite-count assertion about dyadic pairs. -/
theorem summable_general_angular_weight {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1) :
    Summable (fun k : ℤ × ℤ =>
      (Real.sqrt (((2 : ℝ) ^ k.1) ^ 2 + ((2 : ℝ) ^ k.2) ^ 2)) ^ α *
        (2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2 /
      (Real.sqrt (1 + ((2 : ℝ) ^ k.1) ^ 2 + ((2 : ℝ) ^ k.2) ^ 2)) ^ 3) := by
  let w := fun k : ℤ × ℤ =>
    (Real.sqrt (((2 : ℝ) ^ k.1) ^ 2 + ((2 : ℝ) ^ k.2) ^ 2)) ^ α *
      (2 : ℝ) ^ k.1 * (2 : ℝ) ^ k.2 /
    (Real.sqrt (1 + ((2 : ℝ) ^ k.1) ^ 2 + ((2 : ℝ) ^ k.2) ^ 2)) ^ 3
  have hw (i j : ℤ) : w (i, j) = w (j, i) := by
    dsimp only [w]
    simp only [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm]
  let g : (ℤ × ℕ) ⊕ (ℤ × ℕ) → ℤ × ℤ :=
    Sum.elim (fun p => (p.1 - (p.2 : ℤ), p.1)) (fun p => (p.1, p.1 - (p.2 : ℤ)))
  have hl : Summable (fun p : ℤ × ℕ => w (g (Sum.inl p))) :=
    summable_general_angular_gap hα₀ hα₁
  have hr : Summable (fun p : ℤ × ℕ => w (g (Sum.inr p))) :=
    hl.congr (fun p => hw (p.1 - (p.2 : ℤ)) p.1)
  have hsum : Summable (w ∘ g) := Summable.sum _ hl hr
  have hg : Function.Surjective g := by
    rintro ⟨i, j⟩
    by_cases hij : i ≤ j
    · refine ⟨Sum.inl (j, (j - i).toNat), ?_⟩
      change (j - ((j - i).toNat : ℤ), j) = (i, j)
      congr 1
      omega
    · refine ⟨Sum.inr (i, (i - j).toNat), ?_⟩
      change (i, i - ((i - j).toNat : ℤ)) = (i, j)
      congr 1
      omega
  simpa only [Function.comp_def, Function.surjInv_eq hg] using
    hsum.comp_injective (Function.injective_surjInv hg)

end ClockBarrier.Analysis
