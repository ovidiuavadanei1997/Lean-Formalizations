/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.CurlLinear
public import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Tactic.FinCases

/-! # Cartesian partial derivatives of a differentiable vector field

These lemmas identify genuine scalar partial derivatives with entries of the
Fréchet derivative; they do not infer total differentiability from partial derivatives.
-/

public section

namespace ClockBarrier.Geometry

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Restrict an actual Fréchet derivative to a line and a scalar component. -/
theorem hasDerivAt_component_line
    {u : E₃ → E₃} {A : E₃ →L[ℝ] E₃} {x : E₃}
    (hu : HasFDerivAt u A x) (v : E₃) (j : Fin 3) :
    HasDerivAt (fun s : ℝ => u (x + s • v) j) (A v j) 0 := by
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hx : HasFDerivAt u A (x + (0 : ℝ) • v) := by simpa only [zero_smul, add_zero] using hu
  exact (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp_hasDerivAt 0
    (hx.comp_hasDerivAt 0 hline)

/-- Every scalar directional derivative agrees with the actual Fréchet derivative. -/
theorem deriv_component_line_eq
    {u : E₃ → E₃} {x : E₃} (hu : DifferentiableAt ℝ u x) (v : E₃) (j : Fin 3) :
    deriv (fun s : ℝ => u (x + s • v) j) 0 = fderiv ℝ u x v j :=
  (hasDerivAt_component_line hu.hasFDerivAt v j).deriv

/-- On a differentiable field, the six Cartesian partials give exactly the
antisymmetric components of the Fréchet derivative. -/
theorem cartesian_curl_eq_curlLinearMap
    {u : E₃ → E₃} {x : E₃} (hu : DifferentiableAt ℝ u x) :
    (let D := fun i j : Fin 3 =>
      deriv (fun s : ℝ => u (x + s • EuclideanSpace.single i 1) j) 0
    !₂[D 1 2 - D 2 1, D 2 0 - D 0 2, D 0 1 - D 1 0]) =
      curlLinearMap (fderiv ℝ u x) := by
  have h0 : EuclideanSpace.single (0 : Fin 3) (1 : ℝ) = (!₂[1, 0, 0] : E₃) := by
    ext i
    fin_cases i <;> simp
  have h1 : EuclideanSpace.single (1 : Fin 3) (1 : ℝ) = (!₂[0, 1, 0] : E₃) := by
    ext i
    fin_cases i <;> simp
  have h2 : EuclideanSpace.single (2 : Fin 3) (1 : ℝ) = (!₂[0, 0, 1] : E₃) := by
    ext i
    fin_cases i <;> simp
  simp only [deriv_component_line_eq hu, h0, h1, h2, curlLinearMap_apply]

end ClockBarrier.Geometry
