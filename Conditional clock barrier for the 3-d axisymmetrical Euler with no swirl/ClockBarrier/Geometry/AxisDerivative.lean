/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import ClockBarrier.Analysis.AxisLimits
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Derivatives at an axis fixed by transverse symmetries

These are general geometry lemmas for the axis calculations in Section 6 of
arXiv:2605.31587v3 and Lemma 4.1 of arXiv:2603.10945v3. Covariance of an actual Euler
flow and volume preservation are separate obligations. Transverse coordinate reflections
must not be confused with the reflection in the plane `z = 0`.
-/

public section

namespace ClockBarrier.Geometry

open scoped Topology

/-- Differentiate covariance under linear maps at a fixed point of the domain map. -/
theorem comp_eq_comp_of_semiconj
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {F R S : E →L[ℝ] E} {x : E}
    (hf : HasFDerivAt f F x) (hx : R x = x) (heq : Function.Semiconj f R S) :
    F.comp R = S.comp F := by
  have hleft := (hx.symm ▸ hf).comp x R.hasFDerivAt
  exact hleft.unique ((S.hasFDerivAt.comp x hf).congr_of_eventuallyEq
    (Filter.Eventually.of_forall heq))

/-- A matrix commuting with transverse coordinate reflections and a quarter-turn has equal
transverse diagonal entries and no off-diagonal entries. -/
theorem eq_diagonal_of_transverse_symmetries (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hx : A * Matrix.diagonal ![-1, 1, 1] = Matrix.diagonal ![-1, 1, 1] * A)
    (hy : A * Matrix.diagonal ![1, -1, 1] = Matrix.diagonal ![1, -1, 1] * A)
    (hq : A * !![0, -1, 0; 1, 0, 0; 0, 0, 1] =
      !![0, -1, 0; 1, 0, 0; 0, 0, 1] * A) :
    A = Matrix.diagonal ![A 0 0, A 0 0, A 2 2] := by
  have hdiag := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 1) hq
  norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at hdiag
  ext i j
  have hxy := And.intro (congrArg (fun M => M i j) hx) (congrArg (fun M => M i j) hy)
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_succ, hdiag] at hxy ⊢ <;>
    first | rfl | linarith only [hxy, hdiag]

/-- Matrix form of the differentiated covariance identity in Euclidean coordinates. -/
theorem matrix_mul_eq_mul_of_semiconj
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {A R : Matrix (Fin 3) (Fin 3) ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (hf : HasFDerivAt f (Matrix.toEuclideanLin A).toContinuousLinearMap x)
    (hx : Matrix.toEuclideanLin R x = x)
    (heq : Function.Semiconj f (Matrix.toEuclideanLin R) (Matrix.toEuclideanLin R)) :
    A * R = R * A := by
  have hcomm := comp_eq_comp_of_semiconj hf
    (R := (Matrix.toEuclideanLin R).toContinuousLinearMap)
    (S := (Matrix.toEuclideanLin R).toContinuousLinearMap) hx heq
  have hlin := congrArg ContinuousLinearMap.toLinearMap hcomm
  exact (Matrix.toLpLin 2 2).injective
    ((Matrix.toLpLin_mul_same 2 A R).trans (hlin.trans (Matrix.toLpLin_mul_same 2 R A).symm))

/-- At any point on the axis, transverse covariance forces the derivative to be
`diag(a,a,c)`. Differentiability at that point suffices. -/
theorem eq_diagonal_of_hasFDerivAt_axis
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {A : Matrix (Fin 3) (Fin 3) ℝ} {z : ℝ}
    (hf : HasFDerivAt f (Matrix.toEuclideanLin A).toContinuousLinearMap !₂[0, 0, z])
    (hx : Function.Semiconj f
      (Matrix.toEuclideanLin (Matrix.diagonal ![-1, 1, 1]))
      (Matrix.toEuclideanLin (Matrix.diagonal ![-1, 1, 1])))
    (hy : Function.Semiconj f
      (Matrix.toEuclideanLin (Matrix.diagonal ![1, -1, 1]))
      (Matrix.toEuclideanLin (Matrix.diagonal ![1, -1, 1])))
    (hq : Function.Semiconj f
      (Matrix.toEuclideanLin !![0, -1, 0; 1, 0, 0; 0, 0, 1])
      (Matrix.toEuclideanLin !![0, -1, 0; 1, 0, 0; 0, 0, 1])) :
    A = Matrix.diagonal ![A 0 0, A 0 0, A 2 2] := by
  refine eq_diagonal_of_transverse_symmetries A
    (matrix_mul_eq_mul_of_semiconj hf ?_ hx)
    (matrix_mul_eq_mul_of_semiconj hf ?_ hy)
    (matrix_mul_eq_mul_of_semiconj hf ?_ hq)
  all_goals
    apply (WithLp.ext_iff 2).mpr
    change Matrix.mulVec _ ![0, 0, z] = ![0, 0, z]
    ext i
    fin_cases i <;> norm_num [Matrix.mulVec_diagonal, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.diagonal, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Fin.isValue]

/-- The algebraic consequences of unit determinant for an axis-shaped matrix. This does
not assert positivity of the transverse stretch or identify a cylindrical Jacobian. -/
theorem axis_entries_of_det_eq_one {A : Matrix (Fin 3) (Fin 3) ℝ} {a c : ℝ}
    (hdiag : A = Matrix.diagonal ![a, a, c]) (hdet : A.det = 1) :
    a ≠ 0 ∧ c = (a⁻¹) ^ 2 ∧ a * c = a⁻¹ := by
  have hmul : a ^ 2 * c = 1 := by
    simpa [hdiag, Matrix.det_diagonal, Fin.prod_univ_succ, pow_two, mul_assoc] using hdet
  have ha : a ≠ 0 := fun h => by simp [h] at hmul
  exact ⟨ha,
    by simpa only [inv_pow] using
      ((mul_eq_one_iff_inv_eq₀ (pow_ne_zero 2 ha)).mp hmul).symm,
    ((mul_eq_one_iff_inv_eq₀ ha).mp
      (by simpa only [pow_two, mul_assoc] using hmul)).symm⟩

/-- Along a continuous family of axis-shaped matrices with unit determinant, the transverse
stretch remains positive if it starts at one. The endpoint can be any time before blowup. -/
theorem axis_stretch_pos_of_det_eq_one {A : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {s t : ℝ}
    (hst : s ≤ t) (hcont : ContinuousOn (fun r => A r 0 0) (Set.Icc s t))
    (hstart : A s 0 0 = 1)
    (hdiag : ∀ r ∈ Set.Icc s t, A r = Matrix.diagonal ![A r 0 0, A r 0 0, A r 2 2])
    (hdet : ∀ r ∈ Set.Icc s t, (A r).det = 1) : 0 < A t 0 0 := by
  exact ClockBarrier.Analysis.pos_of_continuousOn_of_ne_zero hst hcont
    (by simp only [hstart, zero_lt_one])
    (fun r hr => (axis_entries_of_det_eq_one (hdiag r hr) (hdet r hr)).1)

/-- The transverse coordinate derivative along a Cartesian radial line is the corresponding
entry of the actual Fréchet derivative. -/
theorem hasDerivAt_radial_coordinate
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {A : Matrix (Fin 3) (Fin 3) ℝ} {z : ℝ}
    (hf : HasFDerivAt f (Matrix.toEuclideanLin A).toContinuousLinearMap !₂[0, 0, z]) :
    HasDerivAt (fun r : ℝ => f !₂[r, 0, z] 0) (A 0 0) 0 := by
  have hline : HasDerivAt (fun r : ℝ => (!₂[r, 0, z] : EuclideanSpace ℝ (Fin 3)))
      !₂[1, 0, 0] 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const
      (!₂[1, 0, 0] : EuclideanSpace ℝ (Fin 3))).add_const !₂[0, 0, z] using 1
    all_goals simp [funext_iff, WithLp.ext_iff]
  convert! ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).hasFDerivAt.comp
    !₂[0, 0, z] hf).comp_hasDerivAt 0 hline using 1
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]

/-- Covariance under reflection in `x = 0` makes the first coordinate vanish on the axis. -/
theorem radial_coordinate_eq_zero_of_reflection
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {z : ℝ}
    (hx : Function.Semiconj f
      (Matrix.toEuclideanLin (Matrix.diagonal ![-1, 1, 1]))
      (Matrix.toEuclideanLin (Matrix.diagonal ![-1, 1, 1]))) :
    f !₂[0, 0, z] 0 = 0 := by
  have hfix : Matrix.toEuclideanLin (Matrix.diagonal ![-1, 1, 1]) !₂[0, 0, z] =
      (!₂[0, 0, z] : EuclideanSpace ℝ (Fin 3)) := by
    ext i
    fin_cases i <;> norm_num [Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      Matrix.mulVec_diagonal, Matrix.cons_val_two]
  have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) (hx !₂[0, 0, z])
  norm_num [hfix, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_diagonal] at hcoord
  linarith only [hcoord]

/-- First-order radial and reciprocal limits along a Cartesian radial line. The zero value
at the axis and nonzero transverse derivative are explicit; no higher Taylor remainder is used.
Identifying the signed coordinate here with the cylindrical radius is a separate step. -/
theorem tendsto_radial_ratios_of_hasFDerivAt
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {A : Matrix (Fin 3) (Fin 3) ℝ} {z : ℝ}
    (hf : HasFDerivAt f (Matrix.toEuclideanLin A).toContinuousLinearMap !₂[0, 0, z])
    (hzero : f !₂[0, 0, z] 0 = 0) (ha : A 0 0 ≠ 0) :
    Filter.Tendsto (fun r : ℝ => f !₂[r, 0, z] 0 / r) (𝓝[>] 0) (𝓝 (A 0 0)) ∧
      Filter.Tendsto (fun r : ℝ => r / f !₂[r, 0, z] 0) (𝓝[>] 0) (𝓝 (A 0 0)⁻¹) := by
  exact ⟨ClockBarrier.Analysis.tendsto_div_self_of_hasDerivAt_zero
    (hasDerivAt_radial_coordinate hf) hzero,
    ClockBarrier.Analysis.tendsto_self_div_of_hasDerivAt_zero
      (hasDerivAt_radial_coordinate hf) hzero ha⟩

end ClockBarrier.Geometry
