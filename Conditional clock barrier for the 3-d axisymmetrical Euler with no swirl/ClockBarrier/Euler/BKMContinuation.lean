/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import ClockBarrier.Euler.UniformRestart
public import ClockBarrier.Euler.VorticityRegularity
import ClockBarrier.Frozen.VorticityHolderGrowth
import ClockBarrier.Analysis.BoundedLInfinity

/-! # BKM continuation in the Hölder and finite-energy class

Finite time integral of the essential supremum of the actual vorticity gives
uniform initial-data norms, a common restart lifespan, and an actual extension.
The bounded continuous vorticity representative is identified everywhere.
-/
public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- BKM continuation for every classical Euler solution. No symmetry,
coherence, higher Sobolev bounds, or terminal data are assumed. -/
theorem classical_euler_on.exists_extension_of_bkm
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (W : ℝ → E₃ →ᵇ E₃)
    (hW : ∀ t, ∀ ht : t ∈ Ico 0 T, ∀ x,
      W t x = vorticity (u t) (h.cartesian_partials t ht) x)
    (hBKM : IntegrableOn (fun t => (eLpNorm (W t) ∞ volume).toReal) (Ico 0 T) volume) :
    ∃ T' : ℝ, T < T' ∧ ∃ v : ℝ → E₃ →ᵇ E₃, ∃ q : ℝ → E₃ → ℝ,
      classical_euler_on α T' v q ∧ ∀ t ∈ Ico 0 T, v t = u t := by
  obtain ⟨_, _, hbound⟩ := vorticity_holder_growth_and_bkm_bounds α h.2.1 h.2.2.1
  obtain ⟨D, Z, _, _, hD, hZ, _, _, hnorm⟩ := hbound T u p h
  have heq (t : ℝ) (ht : t ∈ Ico 0 T) : W t = Z t :=
    BoundedContinuousFunction.ext (fun x => (hW t ht x).trans (hZ t ht x).symm)
  have hi : IntegrableOn (fun t => ‖Z t‖) (Ico 0 T) volume := by
    apply hBKM.congr_fun _ measurableSet_Ico
    intro t ht
    change (eLpNorm (W t) ∞ volume).toReal = ‖Z t‖
    rw [heq t ht, Analysis.eLpNorm_top_eq_enorm_bounded, toReal_enorm]
  obtain ⟨M, _, hM⟩ := hnorm hi
  apply h.exists_extension_of_uniform_bounds D M hD
  intro t ht
  obtain ⟨hu, hd, _, hH, _, hL⟩ := hM t ht
  exact ⟨hu, hd, hH, hL⟩

end ClockBarrier.Euler
