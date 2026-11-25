/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Normed.Operator.Asymptotics

/-! # Differentiating a bilinear product when one factor vanishes

The second factor only needs continuity. This is the cancellation used when
recovering curl from a pullback by a C¹ map, without differentiating that map twice.
-/

public section

namespace ClockBarrier.Analysis

open Filter Asymptotics
open scoped Topology

/-- If the differentiable factor vanishes, continuity of the other factor suffices. -/
theorem hasFDerivAt_bilinear_of_zero
    {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g : E → G}
    {f' : E →L[ℝ] F} {x : E}
    (hf : HasFDerivAt f f' x) (hf0 : f x = 0) (hg : ContinuousAt g x) :
    HasFDerivAt (fun y => B (f y) (g y)) ((B.flip (g x)).comp f') x := by
  have hfO : f =O[𝓝 x] (fun y => y - x) := by
    simpa only [hf0, sub_zero] using hf.isBigO_sub
  have hgO : (fun y => g y - g x) =o[𝓝 x] (fun _ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).mpr (tendsto_sub_nhds_zero_iff.mpr hg)
  have heO : (fun y => B (f y) (g y - g x)) =o[𝓝 x] (fun y => y - x) := by
    exact B.isBoundedBilinearMap.isBigO_comp.trans_isLittleO
      (by simpa only [mul_one, isLittleO_norm_right] using hfO.norm_norm.mul_isLittleO hgO.norm_left)
  have he : HasFDerivAt (fun y => B (f y) (g y - g x)) (0 : E →L[ℝ] H) x := by
    simpa only [hasFDerivAt_iff_isLittleO, sub_self, map_zero,
      zero_apply, sub_zero] using heO
  have hc := (B.flip (g x)).hasFDerivAt.comp x hf
  simpa only [Pi.add_def, ContinuousLinearMap.flip_apply, Function.comp_def, map_sub,
    ← add_sub_assoc, add_sub_cancel_left, add_zero] using hc.add he

end ClockBarrier.Analysis
