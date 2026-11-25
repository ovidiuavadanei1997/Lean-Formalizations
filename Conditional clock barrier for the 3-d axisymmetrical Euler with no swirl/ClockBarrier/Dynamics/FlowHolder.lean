/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Dynamics.FlowPerturbation
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # Compact-time spatial Hölder bounds for the actual flow derivative

Comparing the two variational equations gives the estimate used for the
averaged Dini condition in Proposition 3.1.
-/

public section
namespace ClockBarrier.Dynamics
open Set
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Separate variation of a coefficient from variation of the evolved operator. -/
theorem norm_comp_sub_comp_le (A B F G : E →L[ℝ] E) :
    ‖A.comp F - B.comp G‖ ≤ ‖A‖ * ‖F - G‖ + ‖A - B‖ * ‖G‖ := by
  have he : A.comp F - B.comp G = A.comp (F - G) + (A - B).comp G := by
    simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
    abel
  exact he ▸ (norm_add_le _ _).trans
    (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _))

/-- With zero initial displacement, the Grönwall bound is linear in the forcing. -/
theorem gronwallBound_zero_mul (K ε q t : ℝ) :
    gronwallBound 0 K (ε * q) t = gronwallBound 0 K ε t * q := by
  by_cases hK : K = 0 <;> simp [gronwallBound, hK] <;> ring

/-- Uniform Hölder coefficients and bounded linearized paths give one spatial
Hölder constant for the entire compact time interval. -/
theorem exists_uniform_holder_bound_linearized_paths
    {T : ℝ} {α H K M : ℝ≥0} {A J : ℝ → E → E →L[ℝ] E}
    (hc : ∀ a, ContinuousOn (fun t => J t a) (Icc 0 T))
    (hd : ∀ a, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => J s a) ((A t a).comp (J t a)) (Ici t) t)
    (hi : ∀ a, J 0 a = ContinuousLinearMap.id ℝ E)
    (hA : ∀ t ∈ Ico 0 T, ∀ a, ‖A t a‖ ≤ K)
    (hH : ∀ t ∈ Ico 0 T, ∀ a b, ‖A t a - A t b‖ ≤ H * ‖a - b‖ ^ (α : ℝ))
    (hJ : ∀ t ∈ Ico 0 T, ∀ a, ‖J t a‖ ≤ M) :
    ∃ C : ℝ≥0, ∀ t ∈ Icc 0 T, ∀ a b,
      ‖J t a - J t b‖ ≤ C * ‖a - b‖ ^ (α : ℝ) := by
  refine ⟨⟨max 0 (gronwallBound 0 K (H * M) T), le_max_left _ _⟩, ?_⟩
  intro t ht a b
  have hb : ∀ s ∈ Ico 0 T,
      ‖(A s a).comp (J s a) - (A s b).comp (J s b)‖ ≤
        K * ‖J s a - J s b‖ + (H * M) * ‖a - b‖ ^ (α : ℝ) := by
    intro s hs
    exact (norm_comp_sub_comp_le _ _ _ _).trans ((add_le_add
      (mul_le_mul_of_nonneg_right (hA s hs a) (norm_nonneg _))
      (mul_le_mul (hH s hs a b) (hJ s hs b) (norm_nonneg _) (by positivity))).trans_eq (by ring))
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le ((hc a).sub (hc b))
    (fun s hs => (hd a s hs).sub (hd b s hs)) (by simp [hi] : ‖J 0 a - J 0 b‖ ≤ (0 : ℝ)) hb t ht
  have hgT := hg.trans (gronwallBound_mono (le_refl (0 : ℝ))
    (by positivity : 0 ≤ (H : ℝ) * M * ‖a - b‖ ^ (α : ℝ)) K.coe_nonneg
      (by simpa only [sub_zero] using ht.2))
  exact (hgT.trans_eq (gronwallBound_zero_mul _ _ _ _)).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) _))

/-- The actual flow derivative is spatially Hölder with one constant on a compact
initial time interval, derived from the velocity regularity and trajectory equation. -/
theorem exists_uniform_holder_bound_fderiv_flow [CompleteSpace E] [FiniteDimensional ℝ E]
    {T : ℝ} (hT : 0 ≤ T) {u Φ : ℝ → E → E} {K H α : ℝ≥0}
    (hu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set E)))
    (hdiff : ∀ s ∈ Icc 0 T, Differentiable ℝ (u s))
    (hD : ContinuousOn (fun q : ℝ × E => fderiv ℝ (u q.1) q.2) (Icc 0 T ×ˢ univ))
    (hbound : ∀ s ∈ Ico 0 T, ∀ a, ‖fderiv ℝ (u s) a‖₊ ≤ K)
    (hholder : ∀ s ∈ Icc 0 T, HolderWith H α (fderiv ℝ (u s)))
    (hcont : ∀ a, ContinuousOn (fun s => Φ s a) (Icc 0 T))
    (hode : ∀ a, ∀ s ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s a) (u s (Φ s a)) (Ici s) s)
    (hinit : ∀ a, Φ 0 a = a) :
    ∃ C : ℝ≥0, ∀ t ∈ Icc 0 T, ∀ a b,
      ‖fderiv ℝ (Φ t) a - fderiv ℝ (Φ t) b‖ ≤ C * ‖a - b‖ ^ (α : ℝ) := by
  let L : ℝ≥0 := ⟨Real.exp (K * T), (Real.exp_pos _).le⟩
  have hpaths := lipschitzWith_flow_paths
    (fun s hs => lipschitzWith_of_nnnorm_fderiv_le (hdiff s (Ico_subset_Icc_self hs)) (hbound s hs))
    hcont hode hinit
  have hLip : ∀ s ∈ Icc 0 T, LipschitzWith L (Φ s) := fun s hs =>
    LipschitzWith.of_dist_le_mul (fun a b =>
      (ContinuousMap.dist_apply_le_dist ⟨s, hs⟩).trans (hpaths.dist_le_mul a b))
  have hcoeff : ∀ s ∈ Icc 0 T,
      HolderWith (H * L ^ (α : ℝ)) α (fun a => fderiv ℝ (u s) (Φ s a)) :=
    fun s hs => by simpa only [mul_one, Function.comp_def] using
      (hholder s hs).comp (hLip s hs).holderWith
  have hJc : ∀ a, ContinuousOn (fun s => fderiv ℝ (Φ s) a) (Icc 0 T) := fun a =>
    continuousOn_iff_continuous_restrict.mpr
      ((continuous_fderiv_flow hT hu hdiff hD hbound hcont hode hinit).comp
        (continuous_id.prodMk continuous_const))
  exact exists_uniform_holder_bound_linearized_paths (A := fun s a => fderiv ℝ (u s) (Φ s a))
    (H := H * L ^ (α : ℝ)) (K := K) (M := L) hJc
    (fun a s hs => hasDerivWithinAt_fderiv_flow_right hT hu hdiff hD hbound hcont hode hinit a hs)
    (fderiv_flow_zero hinit) (fun s hs a => hbound s hs (Φ s a))
    (fun s hs a b => by simpa only [dist_eq_norm] using
      (hcoeff s (Ico_subset_Icc_self hs)).dist_le a b)
    (fun s hs a => norm_fderiv_flow_le_exp
      (fun r hr => hdiff r (Ico_subset_Icc_self hr)) hbound hcont hode hinit (Ico_subset_Icc_self hs) a)

end ClockBarrier.Dynamics
