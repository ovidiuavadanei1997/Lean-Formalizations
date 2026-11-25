/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.AxisCoherent
public import ClockBarrier.Euler.Reflection
import ClockBarrier.Euler.AxisBarrier

/-! # Assembly from the literal axis coherence class

The source tail and two-sided geometry supply the proved barrier; trajectory
uniqueness makes its bound independent of the chosen actual flow.
-/

public section

namespace ClockBarrier.Euler

open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

/-- Supplies the exact physical axis-barrier statement from the literal coherent class. -/
theorem axis_coherent_on.uniform_physical_axis_barrier
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃}
    (hα : (1 / 3 : ℝ) ≤ (α : ℝ)) (hcoh : axis_coherent_on α T u)
    (_hreflection : ∀ t ∈ Ico 0 T, z_reflection_symmetric (u t))
    (_hmaximal : ∀ T' : ℝ, T < T' →
      ¬ ∃ v : ℝ → E₃ →ᵇ E₃,
        axis_coherent_on α T' v ∧ ∀ t ∈ Ico 0 T, v t = u t) :
    ∃ c : ℝ, 0 < c ∧ ∀ Φ : ℝ → E₃ → E₃,
      (∀ x, Φ 0 x = x) →
      (∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T)) →
      (∀ x, ∀ t ∈ Ico 0 T,
        HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t) →
      ∀ z : ℝ, ∀ t ∈ Ico 0 T, ∃ j : ℝ,
        c ≤ j ∧ Tendsto (fun r : ℝ =>
          (fderiv ℝ (fun q : E₂ =>
            (!₂[Real.sqrt ((Φ t !₂[q 0, 0, q 1] 0)^2 + (Φ t !₂[q 0, 0, q 1] 1)^2),
              Φ t !₂[q 0, 0, q 1] 2] : E₂)) !₂[r, z]).toLinearMap.det)
          (𝓝[>] 0) (𝓝 j) := by
  rcases hcoh with ⟨p, h, haxis, Φ, hi, hc, ho, L, ℓ, cr, Cr, cd, Cd, cF, CF,
    M, Tail, b, BR, hBR, hgeom, hmass, hb, htail, hoff⟩
  have hfinite (t : ℝ) (ht : t ∈ Ico 0 T) (z : ℝ) (q : Finset ℤ)
      (hq : ∀ n ∈ q, (2 : ℝ) ^ n ≤ ℓ.val) :
      ∑ n ∈ q, ((2 : ℝ) ^ n) ^ (α : ℝ) * b t z n ≤ Tail.val := by
    apply le_trans _ ((le_csSup (htail t ht).2.1 (Set.mem_range_self z)).trans
      (htail t ht).2.2.le)
    refine (Finset.sum_congr rfl (fun n hn => (if_pos (hq n hn)).symm)).trans_le
      (((htail t ht).1 z).sum_le_tsum q ?_)
    exact fun n _ => by
      split_ifs
      exact mul_nonneg (Real.rpow_nonneg (zpow_nonneg (by norm_num) n) _) (hb t ht z n)
      exact le_rfl
  obtain ⟨c, hcpos, hbarrier⟩ := h.exists_uniform_axis_clock_barrier
    hα hc ho hi haxis L ℓ Cr.property.le cd.property CF.property.le M.property.le b BR hBR
    (fun t ht z a hL hℓ => (hgeom t ht z a hL hℓ).2.2.2.1)
    (fun t ht z a hL hℓ => (hgeom t ht z a hL hℓ).1)
    (fun t ht z a hL hℓ => (hgeom t ht z a hL hℓ).2.2.2.2.2)
    hmass hb hfinite hoff
  refine ⟨c, hcpos, fun Ψ hΨi hΨc hΨo z t ht => ?_⟩
  obtain ⟨hu, hdiff, hD, hbound, hdiv⟩ := h.velocity_regular
  have hEq : Ψ t = Φ t := funext fun a =>
    Dynamics.eqOn_trajectories_Ico_of_fderiv_bound hdiff hbound
      (hΨc a) (hΨo a) (hc a) (ho a) ((hΨi a).trans (hi a).symm) ht
  rw [hEq]
  exact ⟨_, hbarrier z t ht⟩

end ClockBarrier.Euler
