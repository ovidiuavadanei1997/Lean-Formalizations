/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisClockBlock
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Geometry of the axis dyadic blocks -/

public section

namespace ClockBarrier.Euler

open Set

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Every dyadic axis block is Borel measurable. -/
theorem measurableSet_axisDyadicBlock (J : {j : ℝ // 0 < j}) (z : ℝ) (k n : ℤ) :
    MeasurableSet (axisDyadicBlock J z k n) := by
  unfold axisDyadicBlock
  have hz : Continuous (fun a : E₃ => |a 2 - z|) := by fun_prop
  have hr : Continuous (fun a : E₃ => Real.sqrt ((a 0)^2 + (a 1)^2)) := by fun_prop
  exact (isClosed_le continuous_const hz).measurableSet.inter
    ((isOpen_lt hz continuous_const).measurableSet.inter
      ((isClosed_le continuous_const hr).measurableSet.inter
        (isOpen_lt hr continuous_const).measurableSet))

/-- A continuous flow map makes every clock-local block Borel measurable. -/
theorem measurableSet_axisClockBlock {Φ : E₃ → E₃} (hΦ : Continuous Φ)
    (J : {j : ℝ // 0 < j}) (z : ℝ) (L ℓ : {r : ℝ // 0 < r}) (k n : ℤ) :
    MeasurableSet (axisClockBlock Φ J z L ℓ k n) := by
  unfold axisClockBlock
  exact ((measurableSet_axisDyadicBlock J z k n).inter
    (isClosed_le (by fun_prop) continuous_const).measurableSet).inter
    (isClosed_le (by fun_prop) continuous_const).measurableSet

/-- A nonempty clock-local block has axial scale at most the clock radius. -/
theorem axial_scale_le_of_mem_axisClockBlock
    {Φ : E₃ → E₃} {J : {j : ℝ // 0 < j}} {z : ℝ}
    {L ℓ : {r : ℝ // 0 < r}} {k n : ℤ} {a : E₃}
    (ha : a ∈ axisClockBlock Φ J z L ℓ k n) : (2 : ℝ) ^ n ≤ ℓ.val := by
  have hz : |a 2 - z| ≤ ‖a - !₂[0, 0, z]‖ := by
    simpa using PiLp.norm_apply_le (a - !₂[0, 0, z]) (2 : Fin 3)
  exact ha.1.1.1.trans (hz.trans ha.1.2)

/-- Larger axial scales contribute no clock-local mass. -/
theorem axisClockBlock_eq_empty_of_lt_scale
    {Φ : E₃ → E₃} {J : {j : ℝ // 0 < j}} {z : ℝ}
    {L ℓ : {r : ℝ // 0 < r}} {k n : ℤ} (hn : ℓ.val < (2 : ℝ) ^ n) :
    axisClockBlock Φ J z L ℓ k n = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro a ha
  exact (not_le_of_gt hn) (axial_scale_le_of_mem_axisClockBlock ha)

/-- Half-open shell endpoints give unique angular and axial integer indices. -/
theorem indices_eq_of_mem_axisDyadicBlock
    {J : {j : ℝ // 0 < j}} {z : ℝ} {k n k' n' : ℤ} {a : E₃}
    (ha : a ∈ axisDyadicBlock J z k n) (ha' : a ∈ axisDyadicBlock J z k' n') :
    k = k' ∧ n = n' := by
  have hle {c x : ℝ} (hc : 0 < c) (m q : ℤ)
      (hm : (2 : ℝ) ^ m * c ≤ x ∧ x < 2 * ((2 : ℝ) ^ m * c))
      (hq : (2 : ℝ) ^ q * c ≤ x ∧ x < 2 * ((2 : ℝ) ^ q * c)) : m ≤ q := by
    by_contra hmq
    have hgap : (2 : ℝ) ^ (q + 1) ≤ (2 : ℝ) ^ m :=
      zpow_le_zpow_right₀ (by norm_num) (Int.add_one_le_iff.mpr (lt_of_not_ge hmq))
    have hx : 2 * ((2 : ℝ) ^ q * c) ≤ x := by
      calc
        2 * ((2 : ℝ) ^ q * c) = (2 : ℝ) ^ (q + 1) * c := by
          rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
          ring
        _ ≤ (2 : ℝ) ^ m * c := mul_le_mul_of_nonneg_right hgap hc.le
        _ ≤ x := hm.1
    exact (not_lt_of_ge hx) hq.2
  have huniq {c x : ℝ} (hc : 0 < c) (m q : ℤ)
      (hm : (2 : ℝ) ^ m * c ≤ x ∧ x < 2 * ((2 : ℝ) ^ m * c))
      (hq : (2 : ℝ) ^ q * c ≤ x ∧ x < 2 * ((2 : ℝ) ^ q * c)) : m = q :=
    le_antisymm (hle hc m q hm hq) (hle hc q m hq hm)
  have hn : n = n' := huniq (by norm_num : (0 : ℝ) < 1) n n'
    (by simpa only [mul_one] using And.intro ha.1 ha.2.1)
    (by simpa only [mul_one] using And.intro ha'.1 ha'.2.1)
  subst n'
  refine ⟨huniq (x := Real.sqrt ((a 0)^2 + (a 1)^2)) (mul_pos (pow_pos J.property 3)
    (zpow_pos (by norm_num : (0 : ℝ) < 2) n)) k k' ?_ ?_, rfl⟩
  · simpa only [mul_assoc] using ha.2.2
  · simpa only [mul_assoc] using ha'.2.2

/-- Distinct index pairs describe disjoint dyadic blocks. -/
theorem pairwise_disjoint_axisDyadicBlock (J : {j : ℝ // 0 < j}) (z : ℝ) :
    Pairwise (fun p q : ℤ × ℤ =>
      Disjoint (axisDyadicBlock J z p.1 p.2) (axisDyadicBlock J z q.1 q.2)) := by
  intro p q hpq
  apply disjoint_left.mpr
  intro a ha ha'
  have h := indices_eq_of_mem_axisDyadicBlock ha ha'
  exact hpq (Prod.ext h.1 h.2)

/-- Clock-local restriction preserves the disjointness of the dyadic blocks. -/
theorem pairwise_disjoint_axisClockBlock
    (Φ : E₃ → E₃) (J : {j : ℝ // 0 < j}) (z : ℝ) (L ℓ : {r : ℝ // 0 < r}) :
    Pairwise (fun p q : ℤ × ℤ =>
      Disjoint (axisClockBlock Φ J z L ℓ p.1 p.2) (axisClockBlock Φ J z L ℓ q.1 q.2)) := by
  intro p q hpq
  exact ((pairwise_disjoint_axisDyadicBlock J z) hpq).mono
    (fun _ h => h.1.1) (fun _ h => h.1.1)

/-- Every point with positive radius and nonzero axial displacement belongs to a block. -/
theorem exists_mem_axisDyadicBlock
    (J : {j : ℝ // 0 < j}) (z : ℝ) {a : E₃}
    (hz : a 2 ≠ z) (hr : 0 < Real.sqrt ((a 0)^2 + (a 1)^2)) :
    ∃ k n : ℤ, a ∈ axisDyadicBlock J z k n := by
  obtain ⟨n, hn⟩ := exists_mem_Ico_zpow (abs_pos.mpr (sub_ne_zero.mpr hz))
    (by norm_num : (1 : ℝ) < 2)
  have hc : 0 < J.val ^ 3 * (2 : ℝ) ^ n :=
    mul_pos (pow_pos J.property 3) (zpow_pos (by norm_num) n)
  obtain ⟨k, hk⟩ := exists_mem_Ico_zpow (div_pos hr hc) (by norm_num : (1 : ℝ) < 2)
  refine ⟨k, n, hn.1, ?_, ?_, ?_⟩
  · simpa only [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0), mul_comm] using hn.2
  · simpa only [mul_assoc] using (le_div_iff₀ hc).mp hk.1
  · have h := (div_lt_iff₀ hc).mp hk.2
    rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)] at h
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h

/-- The union excludes exactly the axis and the plane through the chosen axis label. -/
theorem mem_iUnion_axisDyadicBlock_iff
    (J : {j : ℝ // 0 < j}) (z : ℝ) (a : E₃) :
    a ∈ (⋃ p : ℤ × ℤ, axisDyadicBlock J z p.1 p.2) ↔
      a 2 ≠ z ∧ 0 < Real.sqrt ((a 0)^2 + (a 1)^2) := by
  constructor
  · intro ha
    obtain ⟨p, hp⟩ := mem_iUnion.mp ha
    refine ⟨?_, ?_⟩
    · exact sub_ne_zero.mp (abs_pos.mp ((zpow_pos (by norm_num) p.2).trans_le hp.1))
    · exact (mul_pos (mul_pos (zpow_pos (by norm_num) p.1) (pow_pos J.property 3))
        (zpow_pos (by norm_num) p.2)).trans_le hp.2.2.1
  · rintro ⟨hz, hr⟩
    obtain ⟨k, n, ha⟩ := exists_mem_axisDyadicBlock J z hz hr
    exact mem_iUnion.mpr ⟨(k, n), ha⟩

/-- Clock-local blocks cover exactly the clock-local region off the excluded axis and plane. -/
theorem mem_iUnion_axisClockBlock_iff
    (Φ : E₃ → E₃) (J : {j : ℝ // 0 < j}) (z : ℝ) (L ℓ : {r : ℝ // 0 < r}) (a : E₃) :
    a ∈ (⋃ p : ℤ × ℤ, axisClockBlock Φ J z L ℓ p.1 p.2) ↔
      (a 2 ≠ z ∧ 0 < Real.sqrt ((a 0)^2 + (a 1)^2)) ∧
        ‖a - !₂[0, 0, z]‖ ≤ ℓ.val ∧ ‖Φ a - Φ !₂[0, 0, z]‖ ≤ L.val := by
  constructor
  · intro ha
    obtain ⟨p, hp⟩ := mem_iUnion.mp ha
    exact ⟨(mem_iUnion_axisDyadicBlock_iff J z a).mp (mem_iUnion.mpr ⟨p, hp.1.1⟩),
      hp.1.2, hp.2⟩
  · rintro ⟨h, hℓ, hL⟩
    obtain ⟨p, hp⟩ := mem_iUnion.mp ((mem_iUnion_axisDyadicBlock_iff J z a).mpr h)
    exact mem_iUnion.mpr ⟨p, ⟨hp, hℓ⟩, hL⟩

end ClockBarrier.Euler
