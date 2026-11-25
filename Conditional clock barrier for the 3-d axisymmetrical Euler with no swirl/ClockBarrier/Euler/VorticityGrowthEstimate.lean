/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.VorticityIncrement
public import ClockBarrier.Analysis.HolderTransport
public import ClockBarrier.Euler.SpatialCurlData
public import ClockBarrier.Frozen.CurlHolderLogarithmic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
/-! # Vorticity growth from the actual Euler flow

The Hölder estimate consumes the homogeneous spatial curl bound. The supremum
estimate has coefficient one in the accumulated velocity gradient.
-/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped NNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
/-- The homogeneous spatial curl estimate closes Hölder growth along the actual Euler flow. -/
theorem classical_euler_on.holderWith_vorticity_realization
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p)
    {D : ℝ → E₃ →ᵇ (E₃ →L[ℝ] E₃)} {W : ℝ → E₃ →ᵇ E₃}
    (hDc : ContinuousOn D (Ico 0 T)) (hWc : ContinuousOn W (Ico 0 T))
    (hD : ∀ t ∈ Ico 0 T, ∀ x, HasFDerivAt (u t : E₃ → E₃) (D t x) x)
    (hW : ∀ t, ∀ ht : t ∈ Ico 0 T, ∀ x,
      W t x = vorticity (u t) (h.cartesian_partials t ht) x)
    (hH : ∀ b ∈ Ico 0 T, ∃ H : ℝ≥0, ∀ t ∈ Icc 0 b, HolderWith H α (W t : E₃ → E₃))
    {C : ℝ≥0} (hCZ : ∀ t ∈ Ico 0 T,
      HolderWith (C * nnHolderNorm α (W t : E₃ → E₃)) α (D t : E₃ → E₃ →L[ℝ] E₃))
    {H₀ : ℝ≥0} (hzero : HolderWith H₀ α (W 0 : E₃ → E₃))
    {b : ℝ} (hb : b ∈ Ico 0 T) :
    HolderWith (H₀ * ⟨Real.exp (((1 + α + C * ‖Geometry.curlLinearMap‖₊ : ℝ≥0) : ℝ) *
      ∫ s in 0..b, ‖D s‖), (Real.exp_pos _).le⟩) α (W b : E₃ → E₃) := by
  obtain ⟨Φ, hi, hc, ho, _⟩ := h.exists_flow_vorticity_transport
  have hs : Icc 0 b ⊆ Ico 0 T := fun s hs => ⟨hs.1, hs.2.trans_lt hb.2⟩
  obtain ⟨H, hHbound⟩ := hH b hb
  let c : ℝ := ((1 + α + C * ‖Geometry.curlLinearMap‖₊ : ℝ≥0) : ℝ)
  have hqd (a d : E₃) (had : a ≠ d) (t : ℝ) (ht : t ∈ Ioo 0 b) :
      ∃ Q' : E₃, HasDerivAt (fun s => ‖Φ s a - Φ s d‖ ^ (-(α : ℝ)) •
        (W s (Φ s a) - W s (Φ s d))) Q' t ∧
        ‖Q'‖ ≤ (c * ‖D t‖) * (nnHolderNorm α (W t : E₃ → E₃) : ℝ) := by
    obtain ⟨Q', hQ', hQbound⟩ := h.hasDerivAt_normalized_vorticity_increment hc ho hi hW
      ⟨ht.1, ht.2.trans hb.2⟩ (D t) (hD t (hs (Ioo_subset_Icc_self ht)))
      (hCZ t (hs (Ioo_subset_Icc_self ht))) (hHbound t (Ioo_subset_Icc_self ht)).memHolder had
    refine ⟨Q', hQ', hQbound.trans ?_⟩
    have hw := h.norm_vorticity_realization_le (hs (Ioo_subset_Icc_self ht)) (D t) (W t)
      (hD t (hs (Ioo_subset_Icc_self ht))) (hW t (hs (Ioo_subset_Icc_self ht)))
    calc
      _ ≤ (1 + (α : ℝ)) * ‖D t‖ * (nnHolderNorm α (W t : E₃ → E₃) : ℝ) +
          ((C * nnHolderNorm α (W t : E₃ → E₃) : ℝ≥0) : ℝ) *
            (‖Geometry.curlLinearMap‖ * ‖D t‖) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hw (NNReal.coe_nonneg _))
      _ = _ := by simp only [c, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_one, coe_nnnorm]; ring
  have hg := Analysis.holderWith_of_normalized_flow_deriv hb.1
    (fun a => (hc a).mono hs) hi
    (fun t ht => (h.contDiff_bijective_measurePreserving_flow hc ho hi (hs ht)).2.1)
    (hWc.mono hs) hHbound (continuousOn_const.mul (hDc.mono hs).norm)
    (fun t _ => mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg (D t))) hqd hzero
  simpa only [Pi.mul_apply, intervalIntegral.integral_const_mul] using hg
/-- Supremum stretching for the actual Euler vorticity, with the sharp coefficient one. -/
theorem classical_euler_on.norm_vorticity_realization_le_exp_integral
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p)
    {D : ℝ → E₃ →ᵇ (E₃ →L[ℝ] E₃)} {W : ℝ → E₃ →ᵇ E₃}
    (hDc : ContinuousOn D (Ico 0 T)) (hWc : ContinuousOn W (Ico 0 T))
    (hD : ∀ t ∈ Ico 0 T, ∀ x, HasFDerivAt (u t : E₃ → E₃) (D t x) x)
    (hW : ∀ t, ∀ ht : t ∈ Ico 0 T, ∀ x,
      W t x = vorticity (u t) (h.cartesian_partials t ht) x)
    {b : ℝ} (hb : b ∈ Ico 0 T) :
    ‖W b‖ ≤ ‖W 0‖ * Real.exp (∫ s in 0..b, ‖D s‖) := by
  obtain ⟨Φ, hi, hc, ho, _⟩ := h.exists_flow_vorticity_transport
  have hs : Icc 0 b ⊆ Ico 0 T := fun s hs => ⟨hs.1, hs.2.trans_lt hb.2⟩
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  obtain ⟨a, rfl⟩ := (h.contDiff_bijective_measurePreserving_flow hc ho hi hb).2.1.2 x
  have hd (t : ℝ) (ht : t ∈ Ioo 0 b) :
      HasDerivAt (fun s => W s (Φ s a)) (D t (Φ t a) (W t (Φ t a))) t := by
    simpa only [(hD t (hs (Ioo_subset_Icc_self ht)) (Φ t a)).fderiv] using
      (h.hasDerivWithinAt_vorticity_flow hc ho hi hW a (hs (Ioo_subset_Icc_self ht))).hasDerivAt
        (Ico_mem_nhds ht.1 (ht.2.trans hb.2))
  have hg := Analysis.norm_le_mul_exp_integral_of_norm_deriv_le hb.1
    ((continuous_eval.comp_continuousOn (hWc.prodMk (hc a))).mono hs)
    (hDc.norm.mono hs) (fun t _ => norm_nonneg (D t)) hd
    (fun t _ => ((D t (Φ t a)).le_opNorm (W t (Φ t a))).trans
      (mul_le_mul_of_nonneg_right ((D t).norm_coe_le_norm _) (norm_nonneg _)))
  exact hg.trans (mul_le_mul_of_nonneg_right (by simpa only [Function.comp_apply, hi a] using (W 0).norm_coe_le_norm a)
    (Real.exp_pos _).le)
end ClockBarrier.Euler
