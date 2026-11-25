/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.SpectralGap
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # Right derivatives of Rayleigh minima by the manuscript spectral-gap proof -/

public section
namespace ClockBarrier.Analysis
open Set Filter Metric
open scoped Topology InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The full-eigenspace and positive-gap cases of the paper's affine estimate. -/
theorem exists_unit_quadratic_affine_lower (A D : E →L[ℝ] E) (hA : A.IsSymmetric)
    (x₀ : sphere (0 : E) 1)
    (hmin : ∀ x : sphere (0 : E) 1, ⟪(x₀ : E), A x₀⟫_ℝ ≤ ⟪(x : E), A x⟫_ℝ)
    (hgmin : ∀ x : sphere (0 : E) 1, ⟪(x : E), A x⟫_ℝ = ⟪(x₀ : E), A x₀⟫_ℝ →
      ⟪(x₀ : E), D x₀⟫_ℝ ≤ ⟪(x : E), D x⟫_ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, 0 ≤ h → ∀ x : sphere (0 : E) 1,
      ⟪(x₀ : E), A x₀⟫_ℝ + h * ⟪(x₀ : E), D x₀⟫_ℝ - K * h ^ 2 ≤
        ⟪(x : E), A x⟫_ℝ + h * ⟪(x : E), D x⟫_ℝ := by
  let μ := ⟪(x₀ : E), A x₀⟫_ℝ
  let τ := ⟪(x₀ : E), D x₀⟫_ℝ
  let S := Module.End.eigenspace A.toLinearMap μ
  have heval (x : sphere (0 : E) 1) (hx : (x : E) ∈ S) : ⟪(x : E), A x⟫_ℝ = μ := by
    rw [show A x = μ • (x : E) from Module.End.mem_eigenspace_iff.mp hx,
      real_inner_smul_right, real_inner_self_eq_norm_sq,
      mem_sphere_zero_iff_norm.mp x.property, one_pow, mul_one]
  have hτ : ∀ x ∈ S, ‖x‖ = 1 → τ ≤ ⟪x, D x⟫_ℝ := by
    intro x hx hn
    exact hgmin ⟨x, mem_sphere_zero_iff_norm.mpr hn⟩ (heval _ hx)
  by_cases hfull : S = ⊤
  · refine ⟨0, le_rfl, fun h hh x => ?_⟩
    have hx : (x : E) ∈ S := hfull ▸ Submodule.mem_top
    have hb := mul_le_mul_of_nonneg_left (hτ x hx (mem_sphere_zero_iff_norm.mp x.property)) hh
    change μ + h * τ - 0 * h ^ 2 ≤ ⟪(x : E), A x⟫_ℝ + h * ⟪(x : E), D x⟫_ℝ
    rw [heval x hx, zero_mul, sub_zero]
    exact add_le_add le_rfl hb
  · obtain ⟨δ, hδ, hgap⟩ := exists_least_eigenspace_gap A hA μ
      (fun x hx => hmin ⟨x, mem_sphere_zero_iff_norm.mpr hx⟩)
    have hτnorm : |τ| ≤ ‖D‖ := by
      calc
        _ ≤ ‖(x₀ : E)‖ * ‖D x₀‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖(x₀ : E)‖ * (‖D‖ * ‖(x₀ : E)‖) :=
          mul_le_mul_of_nonneg_left (D.le_opNorm x₀) (norm_nonneg _)
        _ = _ := by rw [mem_sphere_zero_iff_norm.mp x₀.property, one_mul, mul_one]
    exact ⟨4 * ‖D‖ ^ 2 / δ, by positivity, fun h hh x =>
      unit_quadratic_affine_lower A D hA hδ hgap hτ hτnorm hh
        (mem_sphere_zero_iff_norm.mp x.property)⟩

/-- Right differentiation of the least Rayleigh value by the spectral-gap
lower bound and the fixed-minimizer upper bound of Lemma 4.1. -/
theorem hasDerivWithinAt_sInf_unit_inner_of_minimizer
    {A : ℝ → E →L[ℝ] E} {D : E →L[ℝ] E} {t₀ : ℝ}
    (hA : HasDerivWithinAt A D (Ici t₀) t₀) (hsym : (A t₀).IsSymmetric)
    (x₀ : sphere (0 : E) 1)
    (hmin : ∀ x : sphere (0 : E) 1, ⟪(x₀ : E), A t₀ x₀⟫_ℝ ≤ ⟪(x : E), A t₀ x⟫_ℝ)
    (hgmin : ∀ x : sphere (0 : E) 1, ⟪(x : E), A t₀ x⟫_ℝ = ⟪(x₀ : E), A t₀ x₀⟫_ℝ →
      ⟪(x₀ : E), D x₀⟫_ℝ ≤ ⟪(x : E), D x⟫_ℝ) :
    HasDerivWithinAt
      (fun t => sInf (range (fun x : sphere (0 : E) 1 => ⟪(x : E), A t x⟫_ℝ)))
      ⟪(x₀ : E), D x₀⟫_ℝ (Ici t₀) t₀ := by
  let q : ℝ → C(sphere (0 : E) 1, ℝ) := fun t => ⟨fun x => ⟪(x : E), A t x⟫_ℝ, by fun_prop⟩
  let g : C(sphere (0 : E) 1, ℝ) := ⟨fun x => ⟪(x : E), D x⟫_ℝ, by fun_prop⟩
  haveI : Nonempty (sphere (0 : E) 1) := ⟨x₀⟩
  have hq : HasDerivWithinAt q g (Ici t₀) t₀ := hasDerivWithinAt_unit_inner hA
  have hm : sInf (range (q t₀)) = q t₀ x₀ :=
    (show IsLeast (range (q t₀)) (q t₀ x₀) from
      ⟨mem_range_self x₀, fun _ ⟨x, hx⟩ => hx ▸ hmin x⟩).csInf_eq
  have hs : Tendsto (slope q t₀) (𝓝[>] t₀) (𝓝 g) :=
    (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp hq.Ioi_of_Ici
  have herr : Tendsto (fun t => ‖slope q t₀ t - g‖) (𝓝[>] t₀) (𝓝 0) := by
    simpa using (hs.sub_const g).norm
  obtain ⟨K, _, hK⟩ := exists_unit_quadratic_affine_lower (A t₀) D hsym x₀ hmin hgmin
  have hlo : Tendsto (fun t => g x₀ - K * (t - t₀) - ‖slope q t₀ t - g‖)
      (𝓝[>] t₀) (𝓝 (g x₀)) := by
    simpa only [id_eq, sub_self, mul_zero, sub_zero] using
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul
        ((tendsto_id.mono_left nhdsWithin_le_nhds).sub_const t₀))).sub herr
  have heval (t : ℝ) (x : sphere (0 : E) 1) :
      slope q t₀ t x = (q t x - q t₀ x) / (t - t₀) := by
    simp [slope_def_module, div_eq_mul_inv, mul_comm]
  apply HasDerivWithinAt.Ici_of_Ioi
  refine (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mpr (tendsto_order.mpr ⟨?_, ?_⟩)
  · intro b hb
    filter_upwards [hlo.eventually (lt_mem_nhds hb), self_mem_nhdsWithin] with t ht hpos
    obtain ⟨x, hx⟩ := (isLeast_sInf_range_continuousMap (q t)).1
    have hh : 0 < t - t₀ := sub_pos.mpr hpos
    have ha := hK (t - t₀) hh.le x
    have hdiv : g x₀ - K * (t - t₀) ≤
        (q t₀ x - q t₀ x₀) / (t - t₀) + g x := by
      rw [← sub_le_iff_le_add, le_div_iff₀ hh]
      change (g x₀ - K * (t - t₀) - g x) * (t - t₀) ≤ q t₀ x - q t₀ x₀
      dsimp only [q, g, ContinuousMap.coe_mk]
      nlinarith only [ha]
    have herrx : -‖slope q t₀ t - g‖ ≤ slope q t₀ t x - g x :=
      (slope q t₀ t - g).neg_norm_le_apply x
    change b < slope (fun t => sInf (range (q t))) t₀ t
    rw [slope_def_field, hm, ← hx]
    have halgebra : (q t x - q t₀ x₀) / (t - t₀) =
        (q t₀ x - q t₀ x₀) / (t - t₀) + slope q t₀ t x := by
      rw [heval, ← add_div, add_comm (q t₀ x - q t₀ x₀), sub_add_sub_cancel]
    rw [halgebra]
    linarith only [ht, hdiv, herrx]
  · intro b hb
    have hev : Tendsto (fun t => slope q t₀ t x₀) (𝓝[>] t₀) (𝓝 (g x₀)) :=
      ((ContinuousMap.evalCLM ℝ x₀).continuous.tendsto g).comp hs
    filter_upwards [hev.eventually (gt_mem_nhds hb), self_mem_nhdsWithin] with t ht hpos
    change slope (fun t => sInf (range (q t))) t₀ t < b
    rw [slope_def_field, hm]
    exact (div_le_div_of_nonneg_right
      (sub_le_sub_right ((isLeast_sInf_range_continuousMap (q t)).2 (mem_range_self x₀)) _)
      (sub_nonneg.mpr hpos.le)).trans_lt ((heval t x₀) ▸ ht)
end ClockBarrier.Analysis
