/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.MaterialAcceleration
public import ClockBarrier.Analysis.ExactIntegral
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-! # Weber's potential from first-order Euler regularity

The pressure is normalized before integration, so no time regularity of its
arbitrary additive gauge is required.
-/

public section

namespace ClockBarrier.Euler

open Set
open scoped Topology NNReal BoundedContinuousFunction InnerProductSpace

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- For an actual Euler flow, the difference between the pulled-back velocity
covector and its initial value is an exact spatial derivative. Spatial flow
regularity and the variational equation are derived from the trajectory ODE. -/
theorem classical_euler_on.exists_weber_potential
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x) {b : ℝ} (hb : b ∈ Ico 0 T) :
    ∃ G : E₃ → ℝ, ∀ a, HasFDerivAt G
      ((innerSL ℝ (u b (Φ b a))).comp (fderiv ℝ (Φ b) a) - innerSL ℝ (u 0 a)) a := by
  obtain ⟨hu, hdiff, hD, hbound, _⟩ := h.velocity_regular
  obtain ⟨K, hK⟩ := hbound b hb
  have hsub : Icc 0 b ⊆ Ico 0 T := fun _ hs => ⟨hs.1, hs.2.trans_lt hb.2⟩
  have hu₀ := hu.mono (prod_mono hsub (subset_refl (univ : Set E₃)))
  have hd₀ := fun s hs => hdiff s (hsub hs)
  have hD₀ := hD.mono (prod_mono hsub (subset_refl (univ : Set E₃)))
  have hc₀ := fun x => (hcont x).mono hsub
  have ho₀ := fun x s hs => hode x s (hsub (Ico_subset_Icc_self hs))
  have hΦ (s : ℝ) (hs : s ∈ Icc 0 b) : ContDiff ℝ 1 (Φ s) :=
    Dynamics.contDiff_flow hb.1 hu₀ hd₀ hD₀ hK hc₀ ho₀ hinit hs
  have hjoint : Continuous (fun q : Icc 0 b × E₃ => Φ q.1.val q.2) := by
    have hh := (Dynamics.contDiff_flow_paths hb.1 hu₀ hd₀ hD₀ hK hc₀ ho₀ hinit).continuous
    exact continuous_eval.comp ((hh.comp continuous_snd).prodMk continuous_fst)
  have hJjoint := Dynamics.continuous_fderiv_flow hb.1 hu₀ hd₀ hD₀ hK hc₀ ho₀ hinit
  have hΦc : ContinuousOn (fun q : ℝ × E₃ => Φ q.1 q.2) (Icc 0 b ×ˢ univ) := by
    apply continuousOn_iff_continuous_restrict.mpr
    exact hjoint.comp ((continuous_subtype_val.fst.subtype_mk
      (fun q => q.property.1)).prodMk continuous_subtype_val.snd)
  have hJc : ContinuousOn (fun q : ℝ × E₃ => fderiv ℝ (Φ q.1) q.2)
      (Icc 0 b ×ˢ univ) := by
    apply continuousOn_iff_continuous_restrict.mpr
    exact hJjoint.comp ((continuous_subtype_val.fst.subtype_mk
      (fun q => q.property.1)).prodMk continuous_subtype_val.snd)
  have he := h
  obtain ⟨_, _, _, _, _, _, _, hp, hgp, _, _⟩ := h
  let V : ℝ × E₃ → E₃ := fun q => u q.1 (Φ q.1 q.2)
  let U : ℝ × E₃ → E₃ →L[ℝ] E₃ := fun q => fderiv ℝ (u q.1) (Φ q.1 q.2)
  let P : ℝ × E₃ → E₃ := fun q => gradient (p q.1) (Φ q.1 q.2)
  let J : ℝ × E₃ → E₃ →L[ℝ] E₃ := fun q => fderiv ℝ (Φ q.1) q.2
  let A : ℝ → E₃ → E₃ →L[ℝ] ℝ := fun s a => (innerSL ℝ (V (s, a))).comp (J (s, a))
  let B : ℝ × E₃ → E₃ →L[ℝ] ℝ := fun q =>
    ((innerSL ℝ (V q)).comp (U q) - innerSL ℝ (P q)).comp (J q)
  let k : ℝ → E₃ → ℝ := fun s a => (1 / 2 : ℝ) * ‖V (s, a)‖ ^ 2 - p s (Φ s a)
  have hmap : Set.MapsTo (fun q : ℝ × E₃ => (q.1, Φ q.1 q.2))
      (Icc 0 b ×ˢ univ) (Ico 0 T ×ˢ univ) := fun q hq => ⟨hsub hq.1, mem_univ _⟩
  have hVc : ContinuousOn V (Icc 0 b ×ˢ univ) :=
    hu.comp (continuousOn_fst.prodMk hΦc) hmap
  have hUc : ContinuousOn U (Icc 0 b ×ˢ univ) :=
    hD.comp (continuousOn_fst.prodMk hΦc) hmap
  have hPc : ContinuousOn P (Icc 0 b ×ˢ univ) :=
    hgp.comp (continuousOn_fst.prodMk hΦc) hmap
  have hBc : ContinuousOn B (Icc 0 b ×ˢ univ) :=
    (((innerSL ℝ).continuous.comp_continuousOn hVc).clm_comp hUc |>.sub
      ((innerSL ℝ).continuous.comp_continuousOn hPc)).clm_comp hJc
  have hAc : ∀ a, ContinuousOn (fun s => A s a) (Icc 0 b) := fun a =>
    (((innerSL ℝ).continuous.comp_continuousOn hVc).clm_comp hJc).comp
      (continuousOn_id.prodMk continuousOn_const) (fun s hs => ⟨hs, mem_univ a⟩)
  have hk (s : ℝ) (hs : s ∈ Icc 0 b) (a : E₃) : HasFDerivAt (k s) (B (s, a)) a := by
    have hdΦ := ((hΦ s hs).differentiable (by decide) a).hasFDerivAt
    have hdV := (hdiff s (hsub hs) (Φ s a)).hasFDerivAt.comp a hdΦ
    have hh := (hdV.norm_sq.const_mul (1 / 2 : ℝ)).sub
      ((hp s (hsub hs) (Φ s a)).hasFDerivAt.comp a hdΦ)
    apply hh.congr_fderiv
    ext v
    simp only [B, V, U, P, J, sub_apply, ContinuousLinearMap.comp_apply,
      smul_apply, smul_eq_mul, Function.comp_apply,
      innerSL_apply_apply, inner_gradient_left]
    ring
  have hAt (a : E₃) (s : ℝ) (hs : s ∈ Ioo 0 b) :
      HasDerivAt (fun t => A t a) (B (s, a)) s := by
    have hdΦ := (Dynamics.hasDerivWithinAt_trajectory_Icc hb.1 hu₀ (hc₀ a) (ho₀ a)
      (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
    have hdV := he.hasDerivAt_material_velocity ⟨hs.1, hs.2.trans hb.2⟩ hdΦ
    have hdJ := Dynamics.hasDerivAt_fderiv_flow hb.1 hu₀ hd₀ hD₀ hK hc₀ ho₀ hinit a hs
    have hdI := (innerSL ℝ).hasFDerivAt.comp_hasDerivAt s hdV
    apply (hdI.hasFDerivAt.clm_comp hdJ.hasFDerivAt).hasDerivAt.congr_deriv
    ext v
    simp only [B, V, U, P, J, add_apply, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul, Function.comp_apply,
      map_neg, neg_apply]
    module
  obtain ⟨G, hG⟩ := Analysis.exists_potential_endpoint_sub hb.1 hBc hk hAc hAt
  refine ⟨G, fun a => ?_⟩
  simpa only [A, V, J, hinit, Dynamics.fderiv_flow_zero hinit,
    ContinuousLinearMap.comp_id] using hG a

end ClockBarrier.Euler
