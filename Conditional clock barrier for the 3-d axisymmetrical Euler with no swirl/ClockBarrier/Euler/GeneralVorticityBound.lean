/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.GeneralClockBarrier
import ClockBarrier.Euler.SingularGeometry
import ClockBarrier.Euler.CauchyTransport
import ClockBarrier.Euler.FlowChangeOfVariables
import ClockBarrier.Geometry.SingularDeformation

/-! # Uniform deformation and vorticity bounds

Section 4 of arXiv:2605.31587v3: determinant one converts the general clock
barrier into an operator norm bound. Cauchy transport and surjectivity then
bound the actual vorticity everywhere, with a finite time integral of its
spatial supremum norm. No Euler continuation theorem is asserted here.
-/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The same positive constant bounds every smallest singular value from below
and every flow derivative from above by its inverse square. -/
theorem general_coherent_on.exists_uniform_deformation_bound
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃}
    (hα : (1 / 3 : ℝ) ≤ (α : ℝ)) (hcoh : general_coherent_on α T u) :
    ∃ c : ℝ, 0 < c ∧ ∀ Φ : ℝ → E₃ → E₃,
      (∀ x, Φ 0 x = x) →
      (∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T)) →
      (∀ x, ∀ t ∈ Ico 0 T,
        HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t) →
      ∀ a : E₃, ∀ t ∈ Ico 0 T,
        c ≤ (fderiv ℝ (Φ t) a).toLinearMap.singularValues 2 ∧
        ‖fderiv ℝ (Φ t) a‖ ≤ (c ^ 2)⁻¹ := by
  obtain ⟨c, hc, hmin⟩ := hcoh.exists_uniform_smallest_singularValue_lower_bound hα
  obtain ⟨p, h, _, Ψ, hinit, hcont, hode, V, _, hframe, _⟩ := hcoh
  refine ⟨c, hc, fun Φ hi hcΦ ho a t ht => ⟨hmin Φ hi hcΦ ho a t ht, ?_⟩⟩
  obtain ⟨_, hdiff, _, hbound, _⟩ := h.velocity_regular
  have heq : Φ t = Ψ t := funext fun x =>
    Dynamics.eqOn_trajectories_Ico_of_fderiv_bound hdiff hbound
      (hcΦ x) (ho x) (hcont x) (hode x) ((hi x).trans (hinit x).symm) ht
  obtain ⟨U, hU⟩ := hframe t ht a
  simpa only [heq] using Geometry.norm_le_inv_sq_of_singular_frame hU
    (h.prod_singularValues_fderiv_flow hcont hode hinit ht a) hc
    (hmin Ψ hinit hcont hode a t ht)

/-- Uniform deformation and actual vorticity bounds with one common constant.
The bounded continuous realization retains the exact Cartesian vorticity at
every lifespan point; its supremum norm has a finite time integral. -/
theorem general_coherent_on.exists_uniform_deformation_vorticity_bounds
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃}
    (hα : (1 / 3 : ℝ) ≤ (α : ℝ)) (hcoh : general_coherent_on α T u) :
    ∃ c : ℝ, 0 < c ∧
      (∀ Φ : ℝ → E₃ → E₃,
        (∀ x, Φ 0 x = x) →
        (∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T)) →
        (∀ x, ∀ t ∈ Ico 0 T,
          HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t) →
        ∀ a : E₃, ∀ t ∈ Ico 0 T, ‖fderiv ℝ (Φ t) a‖ ≤ (c ^ 2)⁻¹) ∧
      ∃ p : ℝ → E₃ → ℝ, ∃ h : classical_euler_on α T u p,
      ∃ W : ℝ → E₃ →ᵇ E₃,
        ContinuousOn W (Ico 0 T) ∧
        (∀ t, ∀ ht : t ∈ Ico 0 T, ∀ x,
          W t x = vorticity (u t) (h.cartesian_partials t ht) x) ∧
        (∀ t ∈ Ico 0 T, ‖W t‖ ≤ (c ^ 2)⁻¹ * ‖W 0‖) ∧
        IntegrableOn (fun t => ‖W t‖) (Ico 0 T) volume ∧
        (∫ t in Ico 0 T, ‖W t‖) ≤ T * (c ^ 2)⁻¹ * ‖W 0‖ := by
  obtain ⟨c, hc, hdef⟩ := hcoh.exists_uniform_deformation_bound hα
  obtain ⟨p, h, _, Φ, hinit, hcont, hode, _⟩ := hcoh
  obtain ⟨W, hW, heq, _⟩ := h.exists_boundedContinuous_vorticity
  have hnorm (t : ℝ) (ht : t ∈ Ico 0 T) : ‖W t‖ ≤ (c ^ 2)⁻¹ * ‖W 0‖ := by
    refine BoundedContinuousFunction.norm_le_of_nonempty.mpr (fun x => ?_)
    obtain ⟨a, rfl⟩ :=
      (h.contDiff_bijective_measurePreserving_flow hcont hode hinit ht).2.1.2 x
    calc
      ‖W t (Φ t a)‖ = ‖vorticity (u t) (h.cartesian_partials t ht) (Φ t a)‖ :=
        congrArg norm (heq t ht _)
      _ ≤ ‖fderiv ℝ (Φ t) a‖ *
          ‖vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩) a‖ :=
        h.norm_vorticity_flow_le hcont hode hinit t ht a
      _ ≤ (c ^ 2)⁻¹ * ‖W 0‖ := mul_le_mul (hdef Φ hinit hcont hode a t ht).2
        (by simpa only [heq 0 ⟨le_rfl, h.1⟩] using (W 0).norm_coe_le_norm a)
        (norm_nonneg _) (inv_nonneg.mpr (sq_nonneg c))
  have hconst : IntegrableOn (fun _ : ℝ => (c ^ 2)⁻¹ * ‖W 0‖) (Ico 0 T) volume :=
    integrableOn_const
      ((measure_mono Ico_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top).ne
  have hWi : IntegrableOn (fun t => ‖W t‖) (Ico 0 T) volume :=
    hconst.mono' (hW.norm.aestronglyMeasurable measurableSet_Ico)
      (ae_restrict_of_forall_mem measurableSet_Ico (fun t ht => by
        simpa only [norm_norm] using hnorm t ht))
  refine ⟨c, hc, fun Ψ hi hcΨ ho a t ht => (hdef Ψ hi hcΨ ho a t ht).2,
    p, h, W, hW, heq, hnorm, hWi, ?_⟩
  calc
    (∫ t in Ico 0 T, ‖W t‖) ≤ ∫ _ in Ico 0 T, (c ^ 2)⁻¹ * ‖W 0‖ :=
      setIntegral_mono_on hWi hconst measurableSet_Ico hnorm
    _ = T * (c ^ 2)⁻¹ * ‖W 0‖ := by
      rw [setIntegral_const, Real.volume_real_Ico_of_le h.1.le, sub_zero, smul_eq_mul,
        mul_assoc]

end ClockBarrier.Euler
