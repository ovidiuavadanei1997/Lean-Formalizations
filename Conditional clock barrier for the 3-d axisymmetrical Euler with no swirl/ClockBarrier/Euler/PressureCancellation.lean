/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.PressurePotential
public import ClockBarrier.Analysis.GradientCancellation
import ClockBarrier.Analysis.BoundedApply
import ClockBarrier.Analysis.L2Apply

/-! # Pressure cancellation in the time-integrated Euler energy identity -/

public section

namespace ClockBarrier.Euler

open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The actual time-integrated pressure gradient has finite energy and pairs
integrably to zero with the velocity at any time in the lifespan. No pressure
integrability or decay premise is imposed. -/
theorem classical_euler_on.integrated_pressure_cancellation
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {b s : ℝ} (hb : b ∈ Ico 0 T) (hs : s ∈ Ico 0 T) :
    MemLp (fun x : E₃ => ∫ t in 0..b, gradient (p t) x) 2 volume ∧
    Integrable (fun x : E₃ => inner ℝ (∫ t in 0..b, gradient (p t) x) (u s x)) volume ∧
    (∫ x : E₃, inner ℝ (∫ t in 0..b, gradient (p t) x) (u s x)) = 0 := by
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
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.1⟩
  have hbb : b ∈ Icc 0 b := ⟨hb.1, le_rfl⟩
  let G : E₃ →ᵇ E₃ := u b - u 0 + ∫ r in 0..b, N r
  let L : Lp E₃ 2 volume := U b - U 0 + ∫ r in 0..b, M r
  have hint := Analysis.ae_intervalIntegral_lp_eq_integral_bounded
    (hN.intervalIntegrable 0 b) (hM.intervalIntegrable 0 b) hMN
  have hLG : L =ᵐ[volume] G := by
    simpa only [hve b hbb, hve 0 h0, G, L,
      BoundedContinuousFunction.coe_add, BoundedContinuousFunction.coe_sub] using
      (Lp.coeFn_add (U b - U 0) (∫ r in 0..b, M r)).trans
        (((Lp.coeFn_sub (U b) (U 0)).trans ((hUe b).sub (hUe 0))).add hint)
  have hG : MemLp G 2 volume := (Lp.memLp L).ae_eq hLG
  obtain ⟨q, hq⟩ := h.exists_potential_integrated_momentum hb hN hNa
  have hfd : fderiv ℝ (u s) = D s := funext (fun x => (hd s hs x).fderiv)
  have hdiv (x : E₃) : ∑ i : Fin 3, fderiv ℝ (u s) x (EuclideanSpace.single i 1) i = 0 := by
    simpa [LinearMap.trace_eq_matrix_trace ℝ (PiLp.basisFun 2 ℝ (Fin 3)),
      Matrix.trace, LinearMap.toMatrix_apply] using h.velocity_regular.2.2.2.2 s hs x
  have hLs := h.2.2.2.2.2.1 s hs
  have hz := Analysis.integral_inner_exact_gradient_eq_zero hG hLs G.continuous hq
    (fun x => (hd s hs x).differentiableAt)
    (by rw [hfd]; exact (D s).continuous) G.norm_coe_le_norm (u s).norm_coe_le_norm
    (fun x => by rw [(hd s hs x).fderiv]; exact (D s).norm_coe_le_norm x) hdiv
  have hpG (x : E₃) : (∫ t in 0..b, gradient (p t) x) = -G x := by
    simpa only [neg_neg, G, BoundedContinuousFunction.coe_add,
      BoundedContinuousFunction.coe_sub, Pi.add_apply, Pi.sub_apply] using congrArg Neg.neg
      (h.integrated_momentum_eq_neg_pressure hb hN hNa x).symm
  simp_rw [hpG]
  refine ⟨hG.neg, ?_, ?_⟩
  · exact memLp_one_iff_integrable.mp ((innerSL ℝ (E := E₃)).memLp_of_bilin 1 hG.neg hLs)
  · simpa only [inner_neg_left, integral_neg, neg_eq_zero] using hz

end ClockBarrier.Euler
