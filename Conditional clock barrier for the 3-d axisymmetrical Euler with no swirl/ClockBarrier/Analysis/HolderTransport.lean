/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Analysis.HolderSeminormTime
public import ClockBarrier.Analysis.IntegralGronwall
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-! # Hölder growth from normalized material increments

The flow is assumed bijective in this reusable analytical lemma. Its Euler
applications supply that fact from the velocity regularity.
-/

public section
namespace ClockBarrier.Analysis
open Set MeasureTheory
open scoped NNReal BoundedContinuousFunction
/-- Norm of an inverse-distance weighted increment, away from a collision. -/
theorem norm_inverse_rpow_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) {r α : ℝ} (hr : 0 ≤ r) :
    ‖r ^ (-α) • v‖ = ‖v‖ / r ^ α := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hr _),
    Real.rpow_neg hr, div_eq_mul_inv, mul_comm]
/-- A bound on normalized derivatives along a bijective flow gives Hölder growth.
The actual finite seminorm is measurable; Hölder-norm time continuity is unnecessary. -/
theorem holderWith_of_normalized_flow_deriv
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : ℝ → E → E} {W : ℝ → E →ᵇ F} {k : ℝ → ℝ} {b : ℝ} {α H H₀ : ℝ≥0}
    (hb : 0 ≤ b) (hc : ∀ a, ContinuousOn (fun t => Φ t a) (Icc 0 b))
    (hi : ∀ a, Φ 0 a = a) (hbij : ∀ t ∈ Icc 0 b, Function.Bijective (Φ t))
    (hWc : ContinuousOn W (Icc 0 b)) (hH : ∀ t ∈ Icc 0 b, HolderWith H α (W t : E → F))
    (hk : ContinuousOn k (Icc 0 b)) (hk0 : ∀ t ∈ Icc 0 b, 0 ≤ k t)
    (hqd : ∀ a c, a ≠ c → ∀ t ∈ Ioo 0 b, ∃ Q' : F,
      HasDerivAt (fun s => ‖Φ s a - Φ s c‖ ^ (-(α : ℝ)) •
        (W s (Φ s a) - W s (Φ s c))) Q' t ∧
      ‖Q'‖ ≤ k t * (nnHolderNorm α (W t : E → F) : ℝ))
    (hzero : HolderWith H₀ α (W 0 : E → F)) :
    HolderWith (H₀ * ⟨Real.exp (∫ s in 0..b, k s), (Real.exp_pos _).le⟩)
      α (W b : E → F) := by
  let K (t : ℝ) : ℝ := nnHolderNorm α (W t : E → F)
  have hKi : IntegrableOn K (Icc 0 b) :=
    integrableOn_nnHolderNorm_of_uniform_bound measurableSet_Icc isCompact_Icc.measure_lt_top.ne
      hH (fun x => (ContinuousEvalConst.continuous_eval_const x).comp_continuousOn hWc)
  have hprod : IntegrableOn (fun t => k t * K t) (Icc 0 b) :=
    IntegrableOn.continuousOn_mul hk hKi isCompact_Icc
  have hbound (t : ℝ) (ht : t ∈ Icc 0 b) : K t ≤ H₀ + ∫ s in 0..t, k s * K s := by
    have htprod := (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr
      (hprod.mono_set (Icc_subset_Icc le_rfl ht.2))
    have hnonneg : 0 ≤ (H₀ : ℝ) + ∫ s in 0..t, k s * K s :=
      add_nonneg H₀.coe_nonneg (intervalIntegral.integral_nonneg ht.1
        (fun s hs => mul_nonneg (hk0 s ⟨hs.1, hs.2.trans ht.2⟩)
          (nnHolderNorm α (W s : E → F)).coe_nonneg))
    apply (nnHolderNorm_le_iff_quotient_le (hH t ht).memHolder hnonneg).mpr
    intro x y
    by_cases hxy : x = y
    · simpa only [hxy, dist_self, zero_div] using hnonneg
    obtain ⟨a, rfl⟩ := (hbij t ht).2 x
    obtain ⟨c, rfl⟩ := (hbij t ht).2 y
    have hac : a ≠ c := fun he => hxy (congrArg (Φ t) he)
    let Q (s : ℝ) := ‖Φ s a - Φ s c‖ ^ (-(α : ℝ)) • (W s (Φ s a) - W s (Φ s c))
    have hQc : ContinuousOn Q (Icc 0 b) :=
      (((hc a).sub (hc c)).norm.rpow_const (fun s hs => Or.inl
        (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (fun he => hac ((hbij s hs).1 he)))))).smul
          ((continuous_eval.comp_continuousOn (hWc.prodMk (hc a))).sub
            (continuous_eval.comp_continuousOn (hWc.prodMk (hc c))))
    have hQt (s : ℝ) (hs : s ∈ Ioo 0 t) := hqd a c hac s ⟨hs.1, hs.2.trans_le ht.2⟩
    have hinc : ‖Q t - Q 0‖ ≤ ∫ s in 0..t, k s * K s :=
      norm_sub_le_integral_of_norm_deriv_le_of_le ht.1
        (hQc.mono (Icc_subset_Icc le_rfl ht.2))
        (fun s hs => (hQt s hs).choose_spec.1.differentiableAt.differentiableWithinAt)
        (Filter.Eventually.of_forall (fun s hs => by
          rw [(hQt s hs).choose_spec.1.deriv]
          exact (hQt s hs).choose_spec.2)) htprod
    have hQ0 : ‖Q 0‖ ≤ H₀ := by
      dsimp only [Q]
      rw [hi a, hi c, norm_inverse_rpow_smul _ (norm_nonneg _)]
      exact (div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hac)) _)).mpr
        (by simpa only [dist_eq_norm] using hzero.dist_le a c)
    have hQbound : ‖Q t‖ ≤ H₀ + ∫ s in 0..t, k s * K s := by
      linarith [norm_sub_norm_le (Q t) (Q 0)]
    simpa only [Q, norm_inverse_rpow_smul _ (norm_nonneg _), dist_eq_norm] using hQbound
  have hg := le_mul_exp_integral_of_integral_le hb hk hk0 hprod hbound
  exact (hH b (right_mem_Icc.mpr hb)).memHolder.holderWith.mono
    (by exact_mod_cast hg)
end ClockBarrier.Analysis
