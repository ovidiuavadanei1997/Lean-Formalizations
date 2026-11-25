/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Dynamics.FlowRegularity

/-! # Uniform perturbation bounds for the flow derivative

The short-time estimate in Proposition 3.1 follows from the already constructed
spatial derivative and its variational equation. Bounds are uniform in the
initial label, on a fixed compact time interval.
-/

public section
namespace ClockBarrier.Dynamics
open Set
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {T : ℝ} {u Φ : ℝ → E → E} {K : ℝ≥0}

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The trajectory Lipschitz estimate bounds the actual spatial derivative. -/
theorem norm_fderiv_flow_le_exp
    (hdiff : ∀ s ∈ Ico 0 T, Differentiable ℝ (u s))
    (hbound : ∀ s ∈ Ico 0 T, ∀ x, ‖fderiv ℝ (u s) x‖₊ ≤ K)
    (hcont : ∀ x, ContinuousOn (fun s => Φ s x) (Icc 0 T))
    (hode : ∀ x, ∀ s ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u s (Φ s x)) (Ici s) s)
    (hinit : ∀ x, Φ 0 x = x) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
    ‖fderiv ℝ (Φ t) x‖ ≤ Real.exp (K * T) := by
  have hLip := lipschitzWith_flow_paths
    (fun s hs => lipschitzWith_of_nnnorm_fderiv_le (hdiff s hs) (hbound s hs))
    hcont hode hinit
  apply norm_fderiv_le_of_lipschitz ℝ
    (LipschitzWith.of_dist_le_mul (K := ⟨Real.exp (K * T), (Real.exp_pos _).le⟩)
      (fun a b => (ContinuousMap.dist_apply_le_dist ⟨t, ht⟩).trans (hLip.dist_le_mul a b)))

/-- The actual flow derivative approaches the identity uniformly in all labels.
The displayed rate uses any common bound on the velocity derivative. -/
theorem norm_fderiv_flow_sub_id_le (hT : 0 ≤ T)
    (hu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set E)))
    (hdiff : ∀ s ∈ Icc 0 T, Differentiable ℝ (u s))
    (hD : ContinuousOn (fun q : ℝ × E => fderiv ℝ (u q.1) q.2)
      (Icc 0 T ×ˢ (univ : Set E)))
    (hbound : ∀ s ∈ Ico 0 T, ∀ x, ‖fderiv ℝ (u s) x‖₊ ≤ K)
    (hcont : ∀ x, ContinuousOn (fun s => Φ s x) (Icc 0 T))
    (hode : ∀ x, ∀ s ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u s (Φ s x)) (Ici s) s)
    (hinit : ∀ x, Φ 0 x = x) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
    ‖fderiv ℝ (Φ t) x - ContinuousLinearMap.id ℝ E‖ ≤
      K * Real.exp (K * T) * t := by
  have hb (s : ℝ) (hs : s ∈ Ico 0 T) :
      ‖(fderiv ℝ (u s) (Φ s x)).comp (fderiv ℝ (Φ s) x)‖ ≤
        K * Real.exp (K * T) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hbound s hs (Φ s x))
        (norm_fderiv_flow_le_exp (fun r hr => hdiff r (Ico_subset_Icc_self hr))
          hbound hcont hode hinit (Ico_subset_Icc_self hs) x)
        (norm_nonneg _) K.coe_nonneg)
  simpa only [fderiv_flow_zero hinit x, sub_zero] using
    norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s hs => hasDerivWithinAt_fderiv_flow hT hu hdiff hD hbound hcont hode hinit x hs)
      hb t ht

end ClockBarrier.Dynamics
