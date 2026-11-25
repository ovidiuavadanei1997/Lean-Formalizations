/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.L2Momentum
import ClockBarrier.Analysis.ConvectiveDifference
import ClockBarrier.Analysis.EnergyUniqueness
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Module

/-! # Uniqueness of classical finite-energy Euler velocities -/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Classical finite-energy Euler velocities with the same initial data agree
throughout their common lifespan. Pressure is allowed its arbitrary time gauge. -/
theorem classical_euler_on.velocity_eq
    {α β : ℝ≥0} {T : ℝ} {u v : ℝ → E₃ →ᵇ E₃} {p q : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (hv : classical_euler_on β T v q)
    (hinit : u 0 = v 0) {b : ℝ} (hb : b ∈ Ico 0 T) : u b = v b := by
  obtain ⟨U, N, hU, hN, hUe, hUo⟩ := h.exists_l2_integrated_momentum hb
  obtain ⟨V, M, hV, hM, hVe, hVo⟩ := hv.exists_l2_integrated_momentum hb
  obtain ⟨Du, hDu, hdu, _⟩ := h.2.2.2.2.1
  obtain ⟨Dv, hDv, hdv, _⟩ := hv.2.2.2.2.1
  have hsub : Icc 0 b ⊆ Ico 0 T := fun _ ht => ⟨ht.1, ht.2.trans_lt hb.2⟩
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.1⟩
  have hbb : b ∈ Icc 0 b := ⟨hb.1, le_rfl⟩
  have hdivu (t : ℝ) (ht : t ∈ Icc 0 b) (x : E₃) :
      LinearMap.trace ℝ E₃ (Du t x).toLinearMap = 0 := by
    rw [← (hdu t (hsub ht) x).fderiv]
    exact h.velocity_regular.2.2.2.2 t (hsub ht) x
  have hdivv (t : ℝ) (ht : t ∈ Icc 0 b) (x : E₃) :
      LinearMap.trace ℝ E₃ (Dv t x).toLinearMap = 0 := by
    rw [← (hdv t (hsub ht) x).fderiv]
    exact hv.velocity_regular.2.2.2.2 t (hsub ht) x
  have hUE (s : ℝ) (hs : s ∈ Icc 0 b) :
      U s = (h.2.2.2.2.2.1 s (hsub hs)).toLp (u s) :=
    Lp.ext ((hUe s hs).1.trans (h.2.2.2.2.2.1 s (hsub hs)).coeFn_toLp.symm)
  have hVE (s : ℝ) (hs : s ∈ Icc 0 b) :
      V s = (hv.2.2.2.2.2.1 s (hsub hs)).toLp (v s) :=
    Lp.ext ((hVe s hs).1.trans (hv.2.2.2.2.2.1 s (hsub hs)).coeFn_toLp.symm)
  let W (t : ℝ) := U t - V t
  let Q (t : ℝ) := N t - M t
  have hWe (t : ℝ) (ht : t ∈ Icc 0 b) : W t =ᵐ[volume] fun x => u t x - v t x :=
    (Lp.coeFn_sub (U t) (V t)).trans ((hUe t ht).1.sub (hVe t ht).1)
  have hQe (t : ℝ) (ht : t ∈ Icc 0 b) : Q t =ᵐ[volume]
      fun x => Du t x (u t x) - Dv t x (v t x) := by
    filter_upwards [Lp.coeFn_sub (N t) (M t), (hUe t ht).2, (hVe t ht).2] with x hx hy hz
    simp only [Q, hx, Pi.sub_apply, hy, hz, (hdu t (hsub ht) x).fderiv,
      (hdv t (hsub ht) x).fderiv]
  have hW0 : W 0 = 0 := by
    apply sub_eq_zero.mpr
    apply Lp.ext
    exact (hUe 0 h0).1.trans (by simpa only [hinit] using (hVe 0 h0).1.symm)
  have hort (s : ℝ) (hs : s ∈ Icc 0 b) (t : ℝ) (ht : t ∈ Icc 0 b) :
      inner ℝ (W t - W 0 + ∫ r in 0..t, Q r) (W s) = 0 := by
    have huu := hUo (u s) (Du s) (h.2.2.2.2.2.1 s (hsub hs))
      (hdu s (hsub hs)) (hdivu s hs) t ht
    have huv := hUo (v s) (Dv s) (hv.2.2.2.2.2.1 s (hsub hs))
      (hdv s (hsub hs)) (hdivv s hs) t ht
    have hvu := hVo (u s) (Du s) (h.2.2.2.2.2.1 s (hsub hs))
      (hdu s (hsub hs)) (hdivu s hs) t ht
    have hvv := hVo (v s) (Dv s) (hv.2.2.2.2.2.1 s (hsub hs))
      (hdv s (hsub hs)) (hdivv s hs) t ht
    rw [← hUE s hs] at huu hvu
    rw [← hVE s hs] at huv hvv
    have he : W t - W 0 + ∫ r in 0..t, Q r =
        (U t - U 0 + ∫ r in 0..t, N r) - (V t - V 0 + ∫ r in 0..t, M r) := by
      dsimp only [W, Q]
      rw [intervalIntegral.integral_sub (hN.intervalIntegrable _ _) (hM.intervalIntegrable _ _)]
      module
    rw [he]
    change inner ℝ _ (U s - V s) = 0
    rw [inner_sub_left, inner_sub_right, inner_sub_right, huu, huv, hvu, hvv]
    ring
  obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) b)).exists_bound_of_continuousOn
    (f := Dv) (hDv.mono hsub)
  have hbound (t : ℝ) (ht : t ∈ Icc 0 b) : -K * ‖W t‖ ^ 2 ≤ inner ℝ (Q t) (W t) := by
    have hnorm : ‖W t‖ ^ 2 = ∫ x : E₃, ‖u t x - v t x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hWe t ht] with x hx
      rw [hx, real_inner_self_eq_norm_sq]
    have hinner : inner ℝ (Q t) (W t) =
        ∫ x : E₃, inner ℝ (Du t x (u t x) - Dv t x (v t x)) (u t x - v t x) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hWe t ht, hQe t ht] with x hx hy
      rw [hx, hy]
    calc
      -K * ‖W t‖ ^ 2 ≤ -‖Dv t‖ * ‖W t‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (neg_le_neg (hK t ht)) (sq_nonneg _)
      _ ≤ inner ℝ (Q t) (W t) := by
        rw [hnorm, hinner]
        apply Analysis.integral_inner_convective_sub_ge
          (h.2.2.2.2.2.1 t (hsub ht)) (hv.2.2.2.2.2.1 t (hsub ht))
          (hdu t (hsub ht)) (hdv t (hsub ht))
        intro x
        simpa [LinearMap.trace_eq_matrix_trace ℝ (PiLp.basisFun 2 ℝ (Fin 3)),
          Matrix.trace, LinearMap.toMatrix_apply] using hdivu t ht x
  have hz := Analysis.eq_zero_of_integrated_orthogonality
    (hU.sub hV) (hN.sub hM) hb.1 hW0 hort hbound
  have he : U b = V b := sub_eq_zero.mp hz
  have hae : (u b : E₃ → E₃) =ᵐ[volume] v b :=
    (hUe b hbb).1.symm.trans (by simpa only [he] using (hVe b hbb).1)
  apply BoundedContinuousFunction.ext
  intro x
  exact congrFun (MeasureTheory.Measure.eq_of_ae_eq hae (u b).continuous (v b).continuous) x

end ClockBarrier.Euler
