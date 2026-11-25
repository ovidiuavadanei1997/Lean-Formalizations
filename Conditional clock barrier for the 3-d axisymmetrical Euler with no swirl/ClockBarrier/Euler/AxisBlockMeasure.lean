/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisBlocks
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.Linarith

/-! # Null exceptional sets and almost-everywhere axis-block coverage -/

public section

namespace ClockBarrier.Euler

open Set MeasureTheory

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Every Cartesian coordinate plane has zero Euclidean volume. -/
theorem volume_coordinate_plane (i : Fin 3) (z : ℝ) :
    volume {a : E₃ | a i = z} = 0 := by
  calc
    volume {a : E₃ | a i = z} = volume {a : Fin 3 → ℝ | a i = z} :=
      (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
        (isClosed_eq (continuous_apply i) continuous_const).measurableSet.nullMeasurableSet
    _ = 0 := Measure.pi_hyperplane (fun _ : Fin 3 => (volume : Measure ℝ)) i z

/-- Zero transverse radius occurs only on a set of zero three-dimensional volume. -/
theorem volume_zero_cylindrical_radius :
    volume {a : E₃ | Real.sqrt ((a 0)^2 + (a 1)^2) = 0} = 0 := by
  apply measure_mono_null (t := {a : E₃ | a 0 = 0}) ?_ (volume_coordinate_plane 0 0)
  intro a ha
  have hs : (a 0)^2 + (a 1)^2 = 0 :=
    (Real.sqrt_eq_zero (by positivity)).mp ha
  dsimp
  nlinarith [sq_nonneg (a 1)]

/-- Almost every label has nonzero axial displacement and positive transverse radius. -/
theorem ae_axis_block_coordinates (z : ℝ) :
    ∀ᵐ a : E₃, a 2 ≠ z ∧ 0 < Real.sqrt ((a 0)^2 + (a 1)^2) := by
  have hz : ∀ᵐ a : E₃, a 2 ≠ z :=
    (measure_eq_zero_iff_ae_notMem.mp (volume_coordinate_plane 2 z))
  have hr : ∀ᵐ a : E₃, Real.sqrt ((a 0)^2 + (a 1)^2) ≠ 0 :=
    measure_eq_zero_iff_ae_notMem.mp volume_zero_cylindrical_radius
  filter_upwards [hz, hr] with a ha hb
  exact ⟨ha, lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hb)⟩

/-- The dyadic blocks cover Euclidean space up to a volume-null exceptional set. -/
theorem iUnion_axisDyadicBlock_ae_eq_univ (J : {j : ℝ // 0 < j}) (z : ℝ) :
    (⋃ p : ℤ × ℤ, axisDyadicBlock J z p.1 p.2) =ᵐ[volume] (univ : Set E₃) := by
  filter_upwards [ae_axis_block_coordinates z] with a ha
  exact propext ⟨fun _ => True.intro, fun _ => (mem_iUnion_axisDyadicBlock_iff J z a).mpr ha⟩

/-- The actual clock blocks cover the entire closed clock-local region almost everywhere. -/
theorem iUnion_axisClockBlock_ae_eq
    (Φ : E₃ → E₃) (J : {j : ℝ // 0 < j}) (z : ℝ) (L ℓ : {r : ℝ // 0 < r}) :
    (⋃ p : ℤ × ℤ, axisClockBlock Φ J z L ℓ p.1 p.2) =ᵐ[volume]
      {a | ‖a - !₂[0, 0, z]‖ ≤ ℓ.val ∧ ‖Φ a - Φ !₂[0, 0, z]‖ ≤ L.val} := by
  filter_upwards [ae_axis_block_coordinates z] with a ha
  exact propext ((mem_iUnion_axisClockBlock_iff Φ J z L ℓ a).trans (and_iff_right ha))

/-- Removing the label-distance boundary changes a clock block only on a null sphere. -/
theorem axisClockBlock_ae_eq_inter_strict
    (Φ : E₃ → E₃) (J : {j : ℝ // 0 < j}) (z : ℝ) (L ℓ : {r : ℝ // 0 < r}) (k n : ℤ) :
    axisClockBlock Φ J z L ℓ k n =ᵐ[volume]
      (axisClockBlock Φ J z L ℓ k n ∩ {a | ‖a - !₂[0, 0, z]‖ < ℓ.val} : Set E₃) := by
  have hzero : volume {a : E₃ | ‖a - !₂[0, 0, z]‖ = ℓ.val} = 0 := by
    simpa only [Metric.sphere, dist_eq_norm] using
      Measure.addHaar_sphere volume (!₂[0, 0, z] : E₃) ℓ.val
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with a ha
  exact propext ⟨fun h => ⟨h, lt_of_le_of_ne h.1.2 ha⟩, fun h => h.1⟩

/-- Strict clock-block interiors still cover the whole closed clock-local region almost everywhere. -/
theorem iUnion_axisClockBlock_inter_strict_ae_eq
    (Φ : E₃ → E₃) (J : {j : ℝ // 0 < j}) (z : ℝ) (L ℓ : {r : ℝ // 0 < r}) :
    (⋃ p : ℤ × ℤ, axisClockBlock Φ J z L ℓ p.1 p.2 ∩
      {a | ‖a - !₂[0, 0, z]‖ < ℓ.val}) =ᵐ[volume]
        {a | ‖a - !₂[0, 0, z]‖ ≤ ℓ.val ∧ ‖Φ a - Φ !₂[0, 0, z]‖ ≤ L.val} := by
  exact (Filter.EventuallyEq.countable_iUnion
    (fun p : ℤ × ℤ => (axisClockBlock_ae_eq_inter_strict Φ J z L ℓ p.1 p.2).symm)).trans
      (iUnion_axisClockBlock_ae_eq Φ J z L ℓ)

end ClockBarrier.Euler
