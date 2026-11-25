/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Tactic.FinCases

/-! # The linear algebra of Cartesian curl

The antisymmetric entries of a derivative form a continuous linear map from
operators to vectors. This construction is independent of a velocity field.
-/

public section

namespace ClockBarrier.Geometry

open scoped NNReal

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Extract the three right-handed curl components of a Cartesian derivative. -/
@[expose] noncomputable def curlLinearMap : (E₃ →L[ℝ] E₃) →L[ℝ] E₃ :=
  ({ toFun := fun A =>
       !₂[A !₂[0, 1, 0] 2 - A !₂[0, 0, 1] 1,
          A !₂[0, 0, 1] 0 - A !₂[1, 0, 0] 2,
          A !₂[1, 0, 0] 1 - A !₂[0, 1, 0] 0]
     map_add' := by
       intros A B
       ext i
       fin_cases i <;> simp [sub_add_sub_comm]
     map_smul' := by
       intros c A
       ext i
       fin_cases i <;> simp [mul_sub] } : (E₃ →L[ℝ] E₃) →ₗ[ℝ] E₃).toContinuousLinearMap

/-- Evaluation is the usual right-handed Cartesian component formula. -/
theorem curlLinearMap_apply (A : E₃ →L[ℝ] E₃) :
    curlLinearMap A =
      !₂[A !₂[0, 1, 0] 2 - A !₂[0, 0, 1] 1,
         A !₂[0, 0, 1] 0 - A !₂[1, 0, 0] 2,
         A !₂[1, 0, 0] 1 - A !₂[0, 1, 0] 0] := rfl

/-- The same formula in the standard matrix representation. -/
theorem curlLinearMap_toEuclideanLin (A : Matrix (Fin 3) (Fin 3) ℝ) :
    curlLinearMap (Matrix.toEuclideanLin A).toContinuousLinearMap =
      !₂[A 2 1 - A 1 2, A 0 2 - A 2 0, A 1 0 - A 0 1] := by
  ext i
  fin_cases i <;> simp [curlLinearMap_apply, Matrix.toEuclideanLin,
    Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- A diagonal derivative has zero curl, without any determinant assumption. -/
theorem curlLinearMap_diagonal (d : Fin 3 → ℝ) :
    curlLinearMap (Matrix.toEuclideanLin (Matrix.diagonal d)).toContinuousLinearMap = 0 := by
  rw [curlLinearMap_toEuclideanLin]
  ext i
  fin_cases i <;> simp

/-- Passing from a derivative field to its curl preserves its Hölder exponent.
The multiplier is the fixed operator norm of the Cartesian curl extraction map. -/
theorem holderWith_curlLinearMap
    {X : Type*} [PseudoEMetricSpace X] {D : X → E₃ →L[ℝ] E₃} {H α : ℝ≥0}
    (hD : HolderWith H α D) :
    HolderWith (‖curlLinearMap‖₊ * H) α (fun x => curlLinearMap (D x)) := by
  simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul, Function.comp_def] using
    curlLinearMap.lipschitz.holderWith.comp hD

end ClockBarrier.Geometry
