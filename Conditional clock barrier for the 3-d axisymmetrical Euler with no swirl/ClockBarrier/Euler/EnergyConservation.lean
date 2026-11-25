/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.PressureCancellation
public import ClockBarrier.Analysis.ConvectiveCancellation
public import ClockBarrier.Analysis.EnergyIncrement
import ClockBarrier.Analysis.BoundedApply
import ClockBarrier.Analysis.L2Apply

/-! # Energy conservation under the classical Euler hypotheses -/

public section

namespace ClockBarrier.Euler

open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Kinetic energy is conserved under the classical Euler interface.
No decay or integrability assumption on pressure is added. -/
theorem classical_euler_on.energy_eq_initial
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {b : ℝ} (hb : b ∈ Ico 0 T) :
    (∫ x : E₃, ‖u b x‖ ^ 2) = ∫ x : E₃, ‖u 0 x‖ ^ 2 := by
  obtain ⟨D, hD, hd, _⟩ := h.2.2.2.2.1
  have hsub : Icc 0 b ⊆ Ico 0 T := fun _ ht => ⟨ht.1, ht.2.trans_lt hb.2⟩
  let c : ℝ → Icc 0 b := projIcc 0 b hb.1
  let v (t : ℝ) := u (c t).val
  let d (t : ℝ) := D (c t).val
  have hc : Continuous (fun t => (c t).val) := continuous_subtype_val.comp continuous_projIcc
  have hv : Continuous v := h.2.2.2.1.comp_continuous hc (fun t => hsub (c t).property)
  have hdcont : Continuous d := hD.comp_continuous hc (fun t => hsub (c t).property)
  have hvlp (t : ℝ) : MemLp (v t) 2 volume := h.2.2.2.2.2.1 _ (hsub (c t).property)
  let U (t : ℝ) := (hvlp t).toLp (v t)
  have hU : Continuous U := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun s => (v s : E₃ → E₃)) hvlp (v t) (hvlp t)).mpr
    exact (h.2.2.2.2.2.2.1 _ (hsub (c t).property)).comp
      (tendsto_nhdsWithin_iff.mpr ⟨hc.continuousAt,
        Eventually.of_forall (fun s => hsub (c s).property)⟩)
  have hUe (t : ℝ) : U t =ᵐ[volume] v t := (hvlp t).coeFn_toLp
  obtain ⟨N, hN, hNe⟩ := Analysis.exists_continuous_bounded_apply d v hdcont hv
  obtain ⟨M, hM, hMe⟩ := Analysis.exists_continuous_lp_apply d U hdcont hU hUe
  have hMN (t : ℝ) : M t =ᵐ[volume] N t :=
    (hMe t).trans (Eventually.of_forall (fun x => (hNe t x).symm))
  have hve (t : ℝ) (ht : t ∈ Icc 0 b) : v t = u t := by
    simp only [v, c, projIcc_of_mem hb.1 ht]
  have hNa (t : ℝ) (ht : t ∈ Icc 0 b) (x : E₃) :
      N t x = fderiv ℝ (u t) x (u t x) := by
    simpa only [v, d, c, projIcc_of_mem hb.1 ht, (hd t (hsub ht) x).fderiv] using hNe t x
  have hfd (t : ℝ) (ht : t ∈ Icc 0 b) : fderiv ℝ (u t) = D t :=
    funext (fun x => (hd t (hsub ht) x).fderiv)
  have hdiv (t : ℝ) (ht : t ∈ Icc 0 b) (x : E₃) :
      ∑ i : Fin 3, fderiv ℝ (u t) x (EuclideanSpace.single i 1) i = 0 := by
    simpa [LinearMap.trace_eq_matrix_trace ℝ (PiLp.basisFun 2 ℝ (Fin 3)),
      Matrix.trace, LinearMap.toMatrix_apply] using h.velocity_regular.2.2.2.2 t (hsub ht) x
  have hconv (t : ℝ) (ht : t ∈ Icc 0 b) : inner ℝ (U t) (M t) = 0 := by
    rw [L2.inner_def]
    have he : (∫ x : E₃, inner ℝ (U t x) (M t x)) =
        ∫ x : E₃, inner ℝ (u t x) (fderiv ℝ (u t) x (u t x)) := by
      apply integral_congr_ae
      filter_upwards [hUe t, hMN t] with x hx hy
      simp only [hx, hy, hve t ht, hNa t ht]
    rw [he]
    exact Analysis.integral_inner_convective_eq_zero (h.2.2.2.2.2.1 t (hsub ht))
      (fun x => (hd t (hsub ht) x).differentiableAt)
      (by rw [hfd t ht]; exact (D t).continuous) (u t).norm_coe_le_norm
      (fun x => by rw [(hd t (hsub ht) x).fderiv]; exact (D t).norm_coe_le_norm x)
      (hdiv t ht)
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.1⟩
  have hort (s : ℝ) (hs : s ∈ Icc 0 b) (t : ℝ) (ht : t ∈ Icc 0 b) :
      inner ℝ (U t - U 0 + ∫ r in 0..t, M r) (U s) = 0 := by
    let G : E₃ →ᵇ E₃ := u t - u 0 + ∫ r in 0..t, N r
    let L : Lp E₃ 2 volume := U t - U 0 + ∫ r in 0..t, M r
    have hint := Analysis.ae_intervalIntegral_lp_eq_integral_bounded
      (hN.intervalIntegrable 0 t) (hM.intervalIntegrable 0 t) hMN
    have hLG : L =ᵐ[volume] G := by
      simpa only [hve t ht, hve 0 h0, G, L,
        BoundedContinuousFunction.coe_add, BoundedContinuousFunction.coe_sub] using
        (Lp.coeFn_add (U t - U 0) (∫ r in 0..t, M r)).trans
          (((Lp.coeFn_sub (U t) (U 0)).trans ((hUe t).sub (hUe 0))).add hint)
    have hpzero := (h.integrated_pressure_cancellation (hsub ht) (hsub hs)).2.2
    have hGp (x : E₃) : G x = -(∫ r in 0..t, gradient (p r) x) :=
      h.integrated_momentum_eq_neg_pressure (hsub ht) hN
        (fun r hr => hNa r ⟨hr.1, hr.2.trans ht.2⟩) x
    have hz : (∫ x : E₃, inner ℝ (G x) (u s x)) = 0 := by
      simp_rw [hGp, inner_neg_left]
      rw [integral_neg, hpzero, neg_zero]
    rw [L2.inner_def]
    apply Eq.trans ?_ hz
    apply integral_congr_ae
    filter_upwards [hLG, hUe s] with x hx hy
    change inner ℝ (L x) (U s x) = inner ℝ (G x) (u s x)
    simp only [hx, hy, hve s hs]
  have henergy := Analysis.norm_sq_eq_of_integrated_orthogonality hU hM hb.1 hconv hort
  have hnorm (t : ℝ) (ht : t ∈ Icc 0 b) :
      ‖U t‖ ^ 2 = ∫ x : E₃, ‖u t x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hUe t] with x hx
    simp only [hx, hve t ht, real_inner_self_eq_norm_sq]
  simpa only [hnorm b ⟨hb.1, le_rfl⟩, hnorm 0 h0] using henergy

end ClockBarrier.Euler
