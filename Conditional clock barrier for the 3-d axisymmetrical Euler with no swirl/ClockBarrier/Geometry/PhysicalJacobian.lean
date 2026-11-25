/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.CylindricalRadius
public import ClockBarrier.Geometry.JacobianContinuity
import ClockBarrier.Analysis.AxisLimits
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Physical meridional Jacobians and their axis limit

Positive-radius points are compared on full two-dimensional neighborhoods, so their
actual derivative determinants agree with those of a signed extension. The resulting
right-hand Jacobian limit uses `C¹` regularity, not merely differentiability at the axis.
-/

public section

namespace ClockBarrier.Geometry

open Filter Set
open scoped Topology

/-- Taking the absolute value of the first output coordinate does not change the derivative
at a point where that coordinate is positive and continuous. -/
theorem fderiv_abs_first_eq
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {p : EuclideanSpace ℝ (Fin 2)}
    (hcont : ContinuousAt (fun q => g q 0) p) (hpos : 0 < g p 0) :
    fderiv ℝ (fun q => (!₂[|g q 0|, g q 1] : EuclideanSpace ℝ (Fin 2))) p =
      fderiv ℝ g p := by
  apply Filter.EventuallyEq.fderiv_eq
  refine (hcont.eventually (Ioi_mem_nhds hpos)).mono fun q hq => ?_
  ext i
  fin_cases i <;> simp [abs_of_pos hq]

/-- The Jacobians of the physical map obtained from a signed `C¹` extension converge
to the signed Jacobian at the axis, when the initial radial derivative is positive. -/
theorem tendsto_det_fderiv_abs_first
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)} {z a : ℝ}
    (hg : ContDiffAt ℝ 1 g !₂[0, z])
    (hrad : HasDerivAt (fun r : ℝ => g !₂[r, z] 0) a 0)
    (hzero : g !₂[0, z] 0 = 0) (ha : 0 < a) :
    Tendsto (fun r : ℝ =>
      (fderiv ℝ (fun p => (!₂[|g p 0|, g p 1] : EuclideanSpace ℝ (Fin 2)))
        !₂[r, z]).toLinearMap.det) (𝓝[>] 0)
      (𝓝 ((fderiv ℝ g !₂[0, z]).toLinearMap.det)) := by
  have hratio : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < g !₂[r, z] 0 / r :=
    (ClockBarrier.Analysis.tendsto_div_self_of_hasDerivAt_zero hrad hzero).eventually
      (Ioi_mem_nhds ha)
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < g !₂[r, z] 0 :=
    (hratio.and self_mem_nhdsWithin).mono fun _ hr =>
      (div_pos_iff_of_pos_right hr.2).mp hr.1
  have hpath : Continuous (fun r : ℝ => (!₂[r, z] : EuclideanSpace ℝ (Fin 2))) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    refine continuous_pi fun i => ?_
    fin_cases i <;> first | exact continuous_id | exact continuous_const
  have hnear : ∀ᶠ r : ℝ in 𝓝[>] 0, ContDiffAt ℝ 1 g !₂[r, z] :=
    ((hpath.tendsto 0).mono_left nhdsWithin_le_nhds).eventually (hg.eventually (by norm_num))
  refine (tendsto_det_fderiv_of_contDiffAt hg).congr' ?_
  exact (hpos.and hnear).mono fun r hr =>
    congrArg (fun L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) =>
      L.toLinearMap.det)
      (fderiv_abs_first_eq
        ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous.continuousAt.comp
          hr.2.continuousAt) hr.1).symm

/-- A Cartesian `C¹` map induces a signed meridional `C¹` restriction. -/
theorem contDiffAt_meridional_restriction
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {r z : ℝ}
    (hf : ContDiffAt ℝ 1 f !₂[r, 0, z]) :
    ContDiffAt ℝ 1
      (fun p : EuclideanSpace ℝ (Fin 2) =>
        (!₂[f !₂[p 0, 0, p 1] 0, f !₂[p 0, 0, p 1] 2] : EuclideanSpace ℝ (Fin 2)))
      !₂[r, z] := by
  let E := (Matrix.toEuclideanLin
    (!![1, 0; 0, 0; 0, 1] : Matrix (Fin 3) (Fin 2) ℝ)).toContinuousLinearMap
  let P := (Matrix.toEuclideanLin
    (!![1, 0, 0; 0, 0, 1] : Matrix (Fin 2) (Fin 3) ℝ)).toContinuousLinearMap
  have hE (p : EuclideanSpace ℝ (Fin 2)) : E p = !₂[p 0, 0, p 1] := by
    ext i
    fin_cases i <;> simp [E, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      dotProduct, Fin.sum_univ_succ]
  have hP (p : EuclideanSpace ℝ (Fin 3)) : P p = !₂[p 0, p 2] := by
    ext i
    fin_cases i <;> simp [P, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      dotProduct, Fin.sum_univ_succ]
  have hfE : ContDiffAt ℝ 1 f (E !₂[r, z]) := by simpa [hE] using hf
  simpa only [Function.comp_def, hE, hP] using
    P.contDiff.contDiffAt.comp !₂[r, z] (hfE.comp !₂[r, z] E.contDiff.contDiffAt)

/-- The right-hand limit of the actual physical meridional Jacobians is the reciprocal
transverse stretch. The nonnegative radius itself need not be differentiable at the axis. -/
theorem tendsto_det_fderiv_physical_meridional
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {A : Matrix (Fin 3) (Fin 3) ℝ} {z : ℝ}
    (hC1 : ContDiffAt ℝ 1 f !₂[0, 0, z])
    (hf : HasFDerivAt f (Matrix.toEuclideanLin A).toContinuousLinearMap !₂[0, 0, z])
    (hx : Function.Semiconj f
      (Matrix.toEuclideanLin (Matrix.diagonal ![-1, 1, 1]))
      (Matrix.toEuclideanLin (Matrix.diagonal ![-1, 1, 1])))
    (hy : Function.Semiconj f
      (Matrix.toEuclideanLin (Matrix.diagonal ![1, -1, 1]))
      (Matrix.toEuclideanLin (Matrix.diagonal ![1, -1, 1])))
    (hq : Function.Semiconj f
      (Matrix.toEuclideanLin !![0, -1, 0; 1, 0, 0; 0, 0, 1])
      (Matrix.toEuclideanLin !![0, -1, 0; 1, 0, 0; 0, 0, 1]))
    (hdet : A.det = 1) (ha : 0 < A 0 0) :
    let φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun p =>
      !₂[Real.sqrt ((f !₂[p 0, 0, p 1] 0) ^ 2 + (f !₂[p 0, 0, p 1] 1) ^ 2),
        f !₂[p 0, 0, p 1] 2]
    Tendsto (fun r : ℝ => (fderiv ℝ φ !₂[r, z]).toLinearMap.det)
      (𝓝[>] 0) (𝓝 (A 0 0)⁻¹) := by
  let g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun p =>
    !₂[f !₂[p 0, 0, p 1] 0, f !₂[p 0, 0, p 1] 2]
  have hlim := tendsto_det_fderiv_abs_first (g := g)
    (contDiffAt_meridional_restriction hC1) (hasDerivAt_radial_coordinate hf)
    (radial_coordinate_eq_zero_of_reflection hx) ha
  have hdetg : (fderiv ℝ g !₂[0, z]).toLinearMap.det = (A 0 0)⁻¹ :=
    det_fderiv_meridional_eq_inv hf (eq_diagonal_of_hasFDerivAt_axis hf hx hy hq) hdet
  have heq :
      (fun p : EuclideanSpace ℝ (Fin 2) =>
        (!₂[Real.sqrt ((f !₂[p 0, 0, p 1] 0) ^ 2 + (f !₂[p 0, 0, p 1] 1) ^ 2),
          f !₂[p 0, 0, p 1] 2] : EuclideanSpace ℝ (Fin 2))) =
        (fun p => (!₂[|g p 0|, g p 1] : EuclideanSpace ℝ (Fin 2))) := by
    funext p
    ext i
    fin_cases i <;> simp [g, second_coordinate_eq_zero_of_reflection hy, Real.sqrt_sq_eq_abs]
  simpa only [heq, hdetg] using hlim

end ClockBarrier.Geometry
