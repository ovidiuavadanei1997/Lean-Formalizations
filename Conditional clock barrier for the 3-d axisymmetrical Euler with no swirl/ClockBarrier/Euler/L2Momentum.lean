/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.PressureCancellation
import ClockBarrier.Analysis.BoundedApply
import ClockBarrier.Analysis.L2Apply

/-! # Finite-energy integrated momentum and arbitrary solenoidal tests -/

public section

namespace ClockBarrier.Euler

open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- A continuous L² realization of velocity and convection, with integrated
momentum orthogonal to every bounded C¹ finite-energy solenoidal test field.
No instantaneous L² pressure gradient or velocity time derivative is assumed. -/
theorem classical_euler_on.exists_l2_integrated_momentum
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {b : ℝ} (hb : b ∈ Ico 0 T) :
    ∃ U N : ℝ → Lp E₃ 2 volume, Continuous U ∧ Continuous N ∧
      (∀ t ∈ Icc 0 b, U t =ᵐ[volume] u t ∧
        N t =ᵐ[volume] fun x => fderiv ℝ (u t) x (u t x)) ∧
      ∀ (g : E₃ →ᵇ E₃) (Dg : E₃ →ᵇ (E₃ →L[ℝ] E₃)) (hg : MemLp g 2 volume),
        (∀ x, HasFDerivAt g (Dg x) x) →
        (∀ x, LinearMap.trace ℝ E₃ (Dg x).toLinearMap = 0) →
        ∀ t ∈ Icc 0 b,
          inner ℝ (U t - U 0 + ∫ r in 0..t, N r) (hg.toLp g) = 0 := by
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
  refine ⟨U, M, hU, hM, ?_, ?_⟩
  · intro t ht
    exact ⟨by simpa only [hve t ht] using hUe t,
      (hMN t).trans (Eventually.of_forall (hNa t ht))⟩
  · intro g Dg hg hgd hgdiv t ht
    let G : E₃ →ᵇ E₃ := u t - u 0 + ∫ r in 0..t, N r
    let L : Lp E₃ 2 volume := U t - U 0 + ∫ r in 0..t, M r
    have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.1⟩
    have hint := Analysis.ae_intervalIntegral_lp_eq_integral_bounded
      (hN.intervalIntegrable 0 t) (hM.intervalIntegrable 0 t) hMN
    have hLG : L =ᵐ[volume] G := by
      simpa only [hve t ht, hve 0 h0, G, L,
        BoundedContinuousFunction.coe_add, BoundedContinuousFunction.coe_sub] using
        (Lp.coeFn_add (U t - U 0) (∫ r in 0..t, M r)).trans
          (((Lp.coeFn_sub (U t) (U 0)).trans ((hUe t).sub (hUe 0))).add hint)
    have hG : MemLp G 2 volume := (Lp.memLp L).ae_eq hLG
    obtain ⟨q, hq⟩ := h.exists_potential_integrated_momentum (hsub ht) hN
      (fun r hr => hNa r ⟨hr.1, hr.2.trans ht.2⟩)
    have hfd : fderiv ℝ g = Dg := funext (fun x => (hgd x).fderiv)
    have hdiv (x : E₃) :
        ∑ i : Fin 3, fderiv ℝ g x (EuclideanSpace.single i 1) i = 0 := by
      rw [hfd]
      simpa [LinearMap.trace_eq_matrix_trace ℝ (PiLp.basisFun 2 ℝ (Fin 3)),
        Matrix.trace, LinearMap.toMatrix_apply] using hgdiv x
    have hz := Analysis.integral_inner_exact_gradient_eq_zero hG hg G.continuous hq
      (fun x => (hgd x).differentiableAt) (by rw [hfd]; exact Dg.continuous)
      G.norm_coe_le_norm g.norm_coe_le_norm
      (fun x => by rw [hfd]; exact Dg.norm_coe_le_norm x) hdiv
    rw [L2.inner_def]
    apply Eq.trans ?_ hz
    apply integral_congr_ae
    filter_upwards [hLG, hg.coeFn_toLp] with x hx hy
    change inner ℝ (L x) (hg.toLp g x) = inner ℝ (G x) (g x)
    rw [hx, hy]

end ClockBarrier.Euler
