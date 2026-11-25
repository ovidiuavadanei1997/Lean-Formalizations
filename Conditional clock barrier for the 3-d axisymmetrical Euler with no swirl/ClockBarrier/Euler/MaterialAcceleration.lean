/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisFlow
public import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.Module

/-! # Material acceleration at classical Euler regularity

Joint differentiability in the interior follows from continuous first partial
derivatives. Applying its chain rule cancels the convective term.
-/

public section

namespace ClockBarrier.Euler

open Set Filter
open scoped Topology NNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Along an actual trajectory the material velocity derivative is minus the
pressure gradient. Only first spatial and time derivatives are used. -/
theorem classical_euler_on.hasDerivAt_material_velocity
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {t : ℝ} (ht : t ∈ Ioo 0 T)
    {γ : ℝ → E₃} (hγ : HasDerivAt γ (u t (γ t)) t) :
    HasDerivAt (fun s => u s (γ s)) (-gradient (p t) (γ t)) t := by
  obtain ⟨hu, hdiff, hDu, _, _⟩ := h.velocity_regular
  obtain ⟨_, _, _, _, _, _, _, _, hgp, hut, _⟩ := h
  let V : ℝ × E₃ → E₃ := fun q =>
    -(fderiv ℝ (u q.1) q.2) (u q.1 q.2) - gradient (p q.1) q.2
  have hV : ContinuousOn V (Ico 0 T ×ˢ univ) := (hDu.clm_apply hu).neg.sub hgp
  have hnb : Ico 0 T ×ˢ (univ : Set E₃) ∈ 𝓝 (t, γ t) :=
    prod_mem_nhds (Ico_mem_nhds ht.1 ht.2) univ_mem
  have hev : ∀ᶠ q : ℝ × E₃ in 𝓝 (t, γ t), q.1 ∈ Ioo 0 T :=
    continuous_fst.continuousAt.eventually (Ioo_mem_nhds ht.1 ht.2)
  have hj : HasFDerivAt (fun q : ℝ × E₃ => u q.1 q.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ (V (t, γ t))).coprod
        (fderiv ℝ (u t) (γ t))) (t, γ t) := by
    apply (hasStrictFDerivAt_uncurry_coprod
      (𝕜 := ℝ) (u := (t, γ t))
      (f := fun s x => u s x)
      (f₁ := fun s x => ContinuousLinearMap.toSpanSingleton ℝ (V (s, x)))
      (f₂ := fun s x => fderiv ℝ (u s) x) ?_ ?_ ?_ ?_).hasFDerivAt
    · filter_upwards [hev] with q hq
      exact ((hut q.1 ⟨hq.1.le, hq.2⟩ q.2).hasDerivAt
        (Ico_mem_nhds hq.1 hq.2)).hasFDerivAt
    · filter_upwards [hev] with q hq
      exact (hdiff q.1 ⟨hq.1.le, hq.2⟩ q.2).hasFDerivAt
    · exact (ContinuousLinearMap.toSpanSingletonLIE ℝ E₃).continuous.continuousAt.comp
        (hV.continuousAt hnb)
    · exact hDu.continuousAt hnb
  have hc := hj.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hγ)
  simp only [Function.comp_def, id_eq, ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul, V] at hc
  exact hc.congr_deriv (by module)

end ClockBarrier.Euler
