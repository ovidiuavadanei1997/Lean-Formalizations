/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisBlockMeasure
public import ClockBarrier.Analysis.AxisBlockIntegral
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

/-! # Integrating over the actual clock-local dyadic blocks

These are conditional analytic helpers. Euler transport, the strain representation,
and the geometric comparisons for the actual flow remain separate obligations.
-/

public section

namespace ClockBarrier.Euler

open Set MeasureTheory ClockBarrier.Analysis

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- A continuous initial field is integrable on each actual bounded clock-local block. -/
theorem integrableOn_axisClockBlock_of_continuous
    {E : Type*} [NormedAddCommGroup E] {f : E₃ → E} (hf : Continuous f)
    (Φ : E₃ → E₃) (J : {j : ℝ // 0 < j}) (z : ℝ) (L ℓ : {r : ℝ // 0 < r}) (k n : ℤ) :
    IntegrableOn f (axisClockBlock Φ J z L ℓ k n) := by
  have hi : IntegrableOn f (Metric.closedBall (!₂[0, 0, z] : E₃) ℓ.val) :=
    hf.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  exact hi.mono_set (fun a ha => by
    simpa only [Metric.mem_closedBall, dist_eq_norm, mem_setOf_eq] using ha.1.2)

/-- Summable absolute block integrals establish integrability and the genuine sum
of block integrals over the entire clock-local region. -/
theorem integrableOn_and_hasSum_axisClockBlock
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : E₃ → E}
    {Φ : E₃ → E₃} (hΦ : Continuous Φ) (J : {j : ℝ // 0 < j})
    (z : ℝ) (L ℓ : {r : ℝ // 0 < r})
    (hi : ∀ p : ℤ × ℤ, IntegrableOn f (axisClockBlock Φ J z L ℓ p.1 p.2))
    (hsum : Summable (fun p : ℤ × ℤ => ∫ a in axisClockBlock Φ J z L ℓ p.1 p.2, ‖f a‖)) :
    IntegrableOn f {a | ‖a - !₂[0, 0, z]‖ ≤ ℓ.val ∧ ‖Φ a - Φ !₂[0, 0, z]‖ ≤ L.val} ∧
      HasSum (fun p : ℤ × ℤ => ∫ a in axisClockBlock Φ J z L ℓ p.1 p.2, f a)
        (∫ a in {a | ‖a - !₂[0, 0, z]‖ ≤ ℓ.val ∧ ‖Φ a - Φ !₂[0, 0, z]‖ ≤ L.val}, f a) := by
  have hu := integrableOn_iUnion_of_summable_integral_norm hi hsum
  have heq := iUnion_axisClockBlock_ae_eq Φ J z L ℓ
  refine ⟨hu.congr_set_ae heq.symm, ?_⟩
  rw [← setIntegral_congr_set heq]
  exact hasSum_integral_iUnion (fun p => measurableSet_axisClockBlock hΦ J z L ℓ p.1 p.2)
    (pairwise_disjoint_axisClockBlock Φ J z L ℓ) hu

/-- Apply the cusp/tail bound to the actual clock blocks and geometric kernel.
The geometric and transported-vorticity comparisons are needed only at strict
label distance. Tail control is needed only for axial scales at most ℓ.
Integrability of the singular kernel product is a conclusion. -/
theorem integrableOn_axisClockKernel_of_cusp
    {Φ : E₃ → E₃} (hΦ : Continuous Φ) {v : E₃ → ℝ} (hvm : Measurable v)
    {ω₀ : E₃ → E₃} (hω : Continuous ω₀)
    (J : {j : ℝ // 0 < j}) (z : ℝ) (L ℓ : {r : ℝ // 0 < r})
    {α cR cd CV M B : ℝ} {b : ℤ → ℝ}
    (hα₀ : -3 < α) (hα₁ : α < 1) (hcR : 0 ≤ cR) (hcd : 0 < cd)
    (hCV : 0 ≤ CV) (hM : 0 ≤ M)
    (hrR : ∀ p : ℤ × ℤ, ∀ a ∈ axisClockBlock Φ J z L ℓ p.1 p.2,
      ‖a - !₂[0, 0, z]‖ < ℓ.val →
        Real.sqrt ((Φ a 0)^2 + (Φ a 1)^2) ≤ cR * (2 : ℝ) ^ p.1 * J.val ^ 2 * (2 : ℝ) ^ p.2)
    (hDd : ∀ p : ℤ × ℤ, ∀ a ∈ axisClockBlock Φ J z L ℓ p.1 p.2,
      ‖a - !₂[0, 0, z]‖ < ℓ.val →
        cd * J.val ^ 2 * (2 : ℝ) ^ p.2 * Real.sqrt (1 + ((2 : ℝ) ^ p.1)^2) ≤
          ‖Φ a - Φ !₂[0, 0, z]‖)
    (hv : ∀ p : ℤ × ℤ, ∀ a ∈ axisClockBlock Φ J z L ℓ p.1 p.2,
      ‖a - !₂[0, 0, z]‖ < ℓ.val → |v a| ≤ CV * J.val⁻¹ * ‖ω₀ a‖)
    (hmass : ∀ p : ℤ × ℤ, (∫ a in axisClockBlock Φ J z L ℓ p.1 p.2, ‖ω₀ a‖) ≤
      (M * b p.2) * (((2 : ℝ) ^ p.1) ^ (α + 2) * J.val ^ (3 * α + 6) *
        ((2 : ℝ) ^ p.2) ^ (α + 3)))
    (hb : ∀ n, 0 ≤ b n)
    (hB : ∀ q : Finset ℤ, (∀ n ∈ q, (2 : ℝ) ^ n ≤ ℓ.val) →
      ∑ n ∈ q, ((2 : ℝ) ^ n) ^ α * b n ≤ B) :
    IntegrableOn (fun a =>
      (Real.sqrt ((Φ a 0)^2 + (Φ a 1)^2) * (Φ a 2 - Φ !₂[0, 0, z] 2) /
        ‖Φ a - Φ !₂[0, 0, z]‖ ^ 5) * v a)
      {a | ‖a - !₂[0, 0, z]‖ ≤ ℓ.val ∧ ‖Φ a - Φ !₂[0, 0, z]‖ ≤ L.val} ∧
    (∫ a in {a | ‖a - !₂[0, 0, z]‖ ≤ ℓ.val ∧ ‖Φ a - Φ !₂[0, 0, z]‖ ≤ L.val},
      |(Real.sqrt ((Φ a 0)^2 + (Φ a 1)^2) * (Φ a 2 - Φ !₂[0, 0, z] 2) /
        ‖Φ a - Φ !₂[0, 0, z]‖ ^ 5) * v a|) ≤
      ((cR / cd ^ 4) * CV * M) *
        (∑' k : ℤ, ((2 : ℝ) ^ k) ^ (α + 3) / (1 + ((2 : ℝ) ^ k)^2)^2) *
          B * J.val ^ (3 * α - 1) := by
  let s : ℤ × ℤ → Set E₃ := fun p =>
    axisClockBlock Φ J z L ℓ p.1 p.2 ∩ {a | ‖a - !₂[0, 0, z]‖ < ℓ.val}
  have hs (p) : MeasurableSet (s p) :=
    (measurableSet_axisClockBlock hΦ J z L ℓ p.1 p.2).inter
      (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have hd : Pairwise (fun p q => Disjoint (s p) (s q)) := fun p q hpq =>
    ((pairwise_disjoint_axisClockBlock Φ J z L ℓ) hpq).mono inter_subset_left inter_subset_left
  have hprod : Measurable (fun a : E₃ =>
      (Real.sqrt ((Φ a 0)^2 + (Φ a 1)^2) * (Φ a 2 - Φ !₂[0, 0, z] 2) /
        ‖Φ a - Φ !₂[0, 0, z]‖ ^ 5) * v a) := by fun_prop
  have hmass' (p : ℤ × ℤ) : (∫ a in s p, ‖ω₀ a‖) ≤
      (M * (if (2 : ℝ) ^ p.2 ≤ ℓ.val then b p.2 else 0)) *
        (((2 : ℝ) ^ p.1) ^ (α + 2) * J.val ^ (3 * α + 6) *
          ((2 : ℝ) ^ p.2) ^ (α + 3)) := by
    by_cases hp : (2 : ℝ) ^ p.2 ≤ ℓ.val
    · calc
        _ = ∫ a in axisClockBlock Φ J z L ℓ p.1 p.2, ‖ω₀ a‖ :=
          setIntegral_congr_set (axisClockBlock_ae_eq_inter_strict Φ J z L ℓ p.1 p.2).symm
        _ ≤ _ := by simpa only [if_pos hp] using hmass p
    · have he : axisClockBlock Φ J z L ℓ p.1 p.2 = ∅ :=
        axisClockBlock_eq_empty_of_lt_scale (lt_of_not_ge hp)
      simp only [s, he, empty_inter, setIntegral_empty, if_neg hp, mul_zero, zero_mul, le_refl]
  obtain ⟨hi, hbound⟩ := integrableOn_axis_driver_of_cusp
    (r := fun a => Real.sqrt ((Φ a 0)^2 + (Φ a 1)^2))
    (z := fun a => Φ a 2 - Φ !₂[0, 0, z] 2) (d := fun a => ‖Φ a - Φ !₂[0, 0, z]‖)
    (b := fun n => if (2 : ℝ) ^ n ≤ ℓ.val then b n else 0)
    J.property hα₀ hα₁ hcR hcd hCV hM hs hd
    (fun _ => hprod.aestronglyMeasurable.restrict)
    (fun p => (integrableOn_axisClockBlock_of_continuous hω Φ J z L ℓ p.1 p.2).mono_set inter_subset_left)
    (fun _ a _ => Real.sqrt_nonneg _)
    (fun _ a _ => by simpa using PiLp.norm_apply_le (Φ a - Φ !₂[0, 0, z]) (2 : Fin 3))
    (fun p a ha => hrR p a ha.1 ha.2) (fun p a ha => hDd p a ha.1 ha.2)
    (fun p a ha => hv p a ha.1 ha.2) hmass'
    (fun n => by split <;> simp_all only [le_refl])
    (axial_tail_indicator_finset_sum_le hB)
  have heq := iUnion_axisClockBlock_inter_strict_ae_eq Φ J z L ℓ
  refine ⟨hi.congr_set_ae heq.symm, ?_⟩
  rw [← setIntegral_congr_set heq]
  exact hbound

end ClockBarrier.Euler
