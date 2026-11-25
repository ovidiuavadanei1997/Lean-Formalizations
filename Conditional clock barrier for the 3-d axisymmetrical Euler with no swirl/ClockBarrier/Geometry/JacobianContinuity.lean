/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.Meridional
public import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Jacobian limits at the axis

For a genuinely `C¹` two-dimensional map, nearby derivative determinants converge to
the derivative determinant at the axis. Applying this to the physical meridional map
still requires its identification with the appropriate signed extension.
-/

public section

namespace ClockBarrier.Geometry

open scoped Topology

/-- `C¹` regularity identifies the right-hand limit of meridional Jacobians with the
Jacobian at the axis. Differentiability at the axis alone would not suffice. -/
theorem tendsto_det_fderiv_of_contDiffAt
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)} {z : ℝ}
    (hg : ContDiffAt ℝ 1 g !₂[0, z]) :
    Filter.Tendsto (fun r : ℝ => (fderiv ℝ g !₂[r, z]).toLinearMap.det)
      (𝓝[>] 0) (𝓝 ((fderiv ℝ g !₂[0, z]).toLinearMap.det)) := by
  have hJ : ContinuousAt (fun p => (fderiv ℝ g p).toLinearMap.det) !₂[0, z] :=
    ContinuousLinearMap.continuous_det.continuousAt.comp
      (hg.continuousAt_fderiv (by norm_num))
  have hpath : Continuous (fun r : ℝ => (!₂[r, z] : EuclideanSpace ℝ (Fin 2))) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    refine continuous_pi fun i => ?_
    fin_cases i <;> first | exact continuous_id | exact continuous_const
  exact hJ.tendsto.comp ((hpath.tendsto 0).mono_left nhdsWithin_le_nhds)

end ClockBarrier.Geometry
