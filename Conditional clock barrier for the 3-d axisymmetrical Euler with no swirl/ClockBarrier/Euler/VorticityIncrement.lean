/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.VorticityMaterialDerivative
public import ClockBarrier.Euler.FlowChangeOfVariables
public import ClockBarrier.Analysis.NormalizedIncrement
public import ClockBarrier.Analysis.HolderSeminormTime
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
/-! # Differential estimate for normalized material vorticity increments

All trajectories and vorticities in the final lemma are actual realizations
of an classical Euler solution.
-/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
/-- The stretching term splits into a vorticity increment and a derivative increment. -/
theorem norm_stretching_sub_le
    (D : E₃ →ᵇ (E₃ →L[ℝ] E₃)) (W : E₃ →ᵇ E₃) {H α : ℝ≥0}
    (hD : HolderWith H α (D : E₃ → E₃ →L[ℝ] E₃)) (x y : E₃) :
    ‖D x (W x) - D y (W y)‖ ≤ ‖D‖ * ‖W x - W y‖ +
      (H : ℝ) * ‖W‖ * ‖x - y‖ ^ (α : ℝ) := by
  have he : D x (W x) - D y (W y) = D x (W x - W y) + (D x - D y) (W y) := by
    simp only [map_sub, sub_apply]; abel
  calc
    _ ≤ ‖D x (W x - W y)‖ + ‖(D x - D y) (W y)‖ := he ▸ norm_add_le _ _
    _ ≤ ‖D‖ * ‖W x - W y‖ + (H : ℝ) * ‖x - y‖ ^ (α : ℝ) * ‖W‖ := by
      exact add_le_add ((D x).le_opNorm_of_le (le_refl ‖W x - W y‖) |>.trans
        (mul_le_mul_of_nonneg_right (D.norm_coe_le_norm x) (norm_nonneg _)))
        ((D x - D y).le_opNorm (W y) |>.trans (mul_le_mul
          (by simpa only [dist_eq_norm] using hD.dist_le x y)
          (W.norm_coe_le_norm y) (norm_nonneg _) (by positivity)))
    _ = _ := by ring
/-- A realization of actual vorticity is bounded by the actual velocity derivative. -/
theorem classical_euler_on.norm_vorticity_realization_le
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {t : ℝ} (ht : t ∈ Ico 0 T)
    (D : E₃ →ᵇ (E₃ →L[ℝ] E₃)) (W : E₃ →ᵇ E₃)
    (hD : ∀ x, HasFDerivAt (u t : E₃ → E₃) (D x) x)
    (hW : ∀ x, W x = vorticity (u t) (h.cartesian_partials t ht) x) :
    ‖W‖ ≤ ‖Geometry.curlLinearMap‖ * ‖D‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  rw [hW x, h.vorticity_eq_curlLinearMap t ht x, (hD x).fderiv]
  exact Geometry.curlLinearMap.le_opNorm_of_le (D.norm_coe_le_norm x)
/-- An initialized classical Euler trajectory has its ordinary derivative at interior times. -/
theorem classical_euler_on.hasDerivAt_flow
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hc : ∀ a, ContinuousOn (fun t => Φ t a) (Ico 0 T))
    (ho : ∀ a, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s a) (u t (Φ t a)) (Ici t) t)
    (a : E₃) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => Φ s a) (u t (Φ t a)) t := by
  obtain ⟨b, htb, hbT⟩ := exists_between ht.2
  have hs : Icc 0 b ⊆ Ico 0 T := fun s hs => ⟨hs.1, hs.2.trans_lt hbT⟩
  exact (Dynamics.hasDerivWithinAt_trajectory_Icc (ht.1.le.trans htb.le)
    (h.velocity_regular.1.mono (prod_mono hs subset_rfl)) ((hc a).mono hs)
    (fun s hs' => ho a s (hs (Ico_subset_Icc_self hs'))) ⟨ht.1.le, htb.le⟩).hasDerivAt
      (Icc_mem_nhds ht.1 htb)
/-- The actual vorticity difference along two distinct Euler trajectories, normalized
by their current distance, satisfies the Hölder-growth differential estimate. -/
theorem classical_euler_on.hasDerivAt_normalized_vorticity_increment
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hc : ∀ a, ContinuousOn (fun t => Φ t a) (Ico 0 T))
    (ho : ∀ a, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s a) (u t (Φ t a)) (Ici t) t)
    (hi : ∀ a, Φ 0 a = a) {W : ℝ → E₃ →ᵇ E₃}
    (hW : ∀ t, ∀ ht : t ∈ Ico 0 T, ∀ x,
      W t x = vorticity (u t) (h.cartesian_partials t ht) x)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (D : E₃ →ᵇ (E₃ →L[ℝ] E₃))
    (hD : ∀ x, HasFDerivAt (u t : E₃ → E₃) (D x) x)
    {H : ℝ≥0} (hH : HolderWith H α (D : E₃ → E₃ →L[ℝ] E₃))
    (hfinite : MemHolder α (W t : E₃ → E₃)) {a b : E₃} (hab : a ≠ b) :
    ∃ Q' : E₃,
      HasDerivAt (fun s => ‖Φ s a - Φ s b‖ ^ (-(α : ℝ)) •
        (W s (Φ s a) - W s (Φ s b))) Q' t ∧
      ‖Q'‖ ≤ (1 + (α : ℝ)) * ‖D‖ * (nnHolderNorm α (W t : E₃ → E₃) : ℝ) +
        (H : ℝ) * ‖W t‖ := by
  have hdW (x : E₃) : HasDerivAt (fun s => W s (Φ s x)) (D (Φ t x) (W t (Φ t x))) t := by
    simpa only [(hD (Φ t x)).fderiv] using
      (h.hasDerivWithinAt_vorticity_flow hc ho hi hW x ⟨ht.1.le, ht.2⟩).hasDerivAt
        (Ico_mem_nhds ht.1 ht.2)
  have hLip : LipschitzWith ‖D‖₊ (u t : E₃ → E₃) :=
    lipschitzWith_of_nnnorm_fderiv_le (fun x => (hD x).differentiableAt)
      (fun x => by simpa only [(hD x).fderiv] using D.nnnorm_coe_le_nnnorm x)
  exact Analysis.exists_hasDerivAt_normalized_increment_le
    ((h.hasDerivAt_flow hc ho a ht).sub (h.hasDerivAt_flow hc ho b ht))
    ((hdW a).sub (hdW b))
    (sub_ne_zero.mpr (fun he => hab
      ((h.contDiff_bijective_measurePreserving_flow hc ho hi ⟨ht.1.le, ht.2⟩).2.1.1 he)))
    α.coe_nonneg (norm_nonneg D)
    (by simpa only [dist_eq_norm, coe_nnnorm] using hLip.dist_le_mul (Φ t a) (Φ t b))
    (by simpa only [dist_eq_norm] using hfinite.holderWith.dist_le (Φ t a) (Φ t b))
    (norm_stretching_sub_le D (W t) hH (Φ t a) (Φ t b))
end ClockBarrier.Euler
