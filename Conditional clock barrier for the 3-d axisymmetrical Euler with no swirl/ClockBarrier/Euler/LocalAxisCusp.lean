/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisBlocks
public import ClockBarrier.Euler.VorticityRegularity
import ClockBarrier.Analysis.RotatedBoxVolume
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith

/-! # Initial-vorticity cusp bounds on the exact axis blocks -/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The enclosing Cartesian box bounds every clock-local axis block. -/
theorem volume_axisClockBlock_le (Φ : E₃ → E₃) (J : {j : ℝ // 0 < j})
    (z : ℝ) (L ℓ : {r : ℝ // 0 < r}) (k n : ℤ) :
    volume (axisClockBlock Φ J z L ℓ k n) ≤
      ENNReal.ofReal (64 * ((2 : ℝ)^k * J.val^3 * (2 : ℝ)^n)^2 * (2 : ℝ)^n) := by
  have hJ := J.property
  apply (Analysis.volume_le_rotated_shell_box (!₂[0, 0, z] : E₃)
    (LinearIsometryEquiv.refl ℝ E₃)
    ![(2 : ℝ)^k * J.val^3 * (2 : ℝ)^n,
      (2 : ℝ)^k * J.val^3 * (2 : ℝ)^n, (2 : ℝ)^n] ?_ ?_).trans_eq
      (congrArg ENNReal.ofReal (by dsimp; ring))
  · intro i
    fin_cases i <;> dsimp <;> positivity
  · intro a ha i
    change |(a - !₂[0, 0, z]) i| ≤ _
    fin_cases i
    · simpa using (Real.abs_le_sqrt (x := a 0)
        (le_add_of_nonneg_right (sq_nonneg (a 1)))).trans ha.1.1.2.2.2.le
    · simpa using (Real.abs_le_sqrt (x := a 1)
        (le_add_of_nonneg_left (sq_nonneg (a 0)))).trans ha.1.1.2.2.2.le
    · exact ha.1.1.2.1.le

/-- One initial Hölder constant controls every exact axis cusp block. -/
theorem classical_euler_on.exists_local_axis_cusp_bound
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p)
    (haxis : ∀ t ∈ Ico 0 T, axisymmetric_no_swirl (u t)) :
    ∃ M : ℝ, 0 < M ∧ ∀ (Φ : E₃ → E₃) (J : {j : ℝ // 0 < j}) (z : ℝ)
      (L ℓ : {r : ℝ // 0 < r}) (k n : ℤ),
      let w₀ := vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩)
      IntegrableOn (fun a => ‖w₀ a‖) (axisClockBlock Φ J z L ℓ k n) volume ∧
      (∫ a in axisClockBlock Φ J z L ℓ k n, ‖w₀ a‖) ≤
        M * ((2 : ℝ)^k) ^ ((α : ℝ) + 2) * J.val ^ (3 * (α : ℝ) + 6) *
          ((2 : ℝ)^n) ^ ((α : ℝ) + 3) := by
  obtain ⟨H, hH⟩ := h.norm_vorticity_le_radius_rpow haxis 0 ⟨le_rfl, h.1⟩
  refine ⟨64 * H * (2 : ℝ) ^ (α : ℝ) + 1, by positivity, fun Φ J z L ℓ k n => ?_⟩
  intro w₀
  have hJ := J.property
  have hvol := volume_axisClockBlock_le Φ J z L ℓ k n
  have hpoint : ∀ a ∈ axisClockBlock Φ J z L ℓ k n,
      ‖w₀ a‖ ≤ (H : ℝ) * (2 * ((2 : ℝ)^k * J.val^3 * (2 : ℝ)^n)) ^ (α : ℝ) :=
    fun a ha => (hH 0 ⟨le_rfl, le_rfl⟩ a).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Real.sqrt_nonneg _) ha.1.1.2.2.2.le α.coe_nonneg) H.coe_nonneg)
  obtain ⟨W, _, hW, _⟩ := h.exists_boundedContinuous_vorticity
  refine ⟨(Measure.integrableOn_of_bounded
    (hvol.trans_lt ENNReal.ofReal_lt_top).ne
    (h.continuous_vorticity 0 ⟨le_rfl, h.1⟩).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun a => by
      change ‖w₀ a‖ ≤ ‖W 0‖
      rw [show w₀ a = W 0 a from (hW 0 ⟨le_rfl, h.1⟩ a).symm]
      exact (W 0).norm_coe_le_norm a))).norm, ?_⟩
  refine ((le_abs_self _).trans (norm_setIntegral_le_of_norm_le_const (f := fun a => ‖w₀ a‖)
    (hvol.trans_lt ENNReal.ofReal_lt_top) (fun a ha => by
      simpa only [norm_norm] using hpoint a ha))).trans ?_
  have hvolR : volume.real (axisClockBlock Φ J z L ℓ k n) ≤
      64 * ((2 : ℝ)^k * J.val^3 * (2 : ℝ)^n)^2 * (2 : ℝ)^n := by
    simpa only [Measure.real, ENNReal.toReal_ofReal (by positivity :
      0 ≤ 64 * ((2 : ℝ)^k * J.val^3 * (2 : ℝ)^n)^2 * (2 : ℝ)^n)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
  refine (mul_le_mul_of_nonneg_left hvolR (by positivity)).trans ?_
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity),
    Real.mul_rpow (by positivity : 0 ≤ (2 : ℝ)^k * J.val^3) (by positivity),
    Real.mul_rpow (by positivity : 0 ≤ (2 : ℝ)^k) (by positivity),
    ← Real.rpow_natCast_mul hJ.le,
    Real.rpow_add (by positivity : 0 < (2 : ℝ)^k),
    Real.rpow_add hJ, Real.rpow_add (by positivity : 0 < (2 : ℝ)^n)]
  norm_num only [Nat.cast_ofNat, Real.rpow_ofNat]
  ring_nf
  exact le_add_of_nonneg_right (by positivity)

end ClockBarrier.Euler
