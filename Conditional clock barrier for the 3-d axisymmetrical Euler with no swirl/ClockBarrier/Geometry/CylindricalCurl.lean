/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.CurlAxis
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! # Rotational invariance of the signed on-axis curl kernel

Only first spatial derivatives are used. The scalar azimuthal component on the
positive meridional ray is the second Cartesian component of the curl.
-/

public section

namespace ClockBarrier.Geometry

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- A proper transverse rotation adds its angle to cylindrical coordinates. -/
theorem rotation_apply_cylindrical (β r θ z : ℝ) :
    Matrix.toEuclideanLin
      !![Real.cos β, -Real.sin β, 0; Real.sin β, Real.cos β, 0; 0, 0, 1]
        (!₂[r * Real.cos θ, r * Real.sin θ, z] : E₃) =
      !₂[r * Real.cos (θ + β), r * Real.sin (θ + β), z] := by
  ext i
  fin_cases i <;> simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Real.cos_add, Real.sin_add] <;> ring

/-- The cylindrical velocity formula gives every proper transverse rotation. -/
theorem rotation_semiconj_of_cylindrical_representation
    {f : E₃ → E₃} {v w : ℝ → ℝ → ℝ}
    (hf : ∀ r : ℝ, 0 ≤ r → ∀ θ z : ℝ,
      f !₂[r * Real.cos θ, r * Real.sin θ, z] =
        !₂[v r z * Real.cos θ, v r z * Real.sin θ, w r z]) (β : ℝ) :
    Function.Semiconj f
      (Matrix.toEuclideanLin
        !![Real.cos β, -Real.sin β, 0; Real.sin β, Real.cos β, 0; 0, 0, 1])
      (Matrix.toEuclideanLin
        !![Real.cos β, -Real.sin β, 0; Real.sin β, Real.cos β, 0; 0, 0, 1]) := by
  exact semiconj_of_cylindrical_representation hf (rotation_apply_cylindrical β)

/-- Differentiate linear covariance at two possibly distinct points. -/
theorem matrix_mul_eq_mul_of_semiconj_at
    {f : E₃ → E₃} {A B R : Matrix (Fin 3) (Fin 3) ℝ} {x : E₃}
    (hx : HasFDerivAt f (Matrix.toEuclideanLin A).toContinuousLinearMap x)
    (hRx : HasFDerivAt f (Matrix.toEuclideanLin B).toContinuousLinearMap
      (Matrix.toEuclideanLin R x))
    (hcov : Function.Semiconj f (Matrix.toEuclideanLin R) (Matrix.toEuclideanLin R)) :
    B * R = R * A := by
  have he := (hRx.comp x (Matrix.toEuclideanLin R).toContinuousLinearMap.hasFDerivAt).unique
    (((Matrix.toEuclideanLin R).toContinuousLinearMap.hasFDerivAt.comp x hx).congr_of_eventuallyEq
      (Filter.Eventually.of_forall hcov))
  exact (Matrix.toLpLin 2 2).injective
    ((Matrix.toLpLin_mul_same 2 B R).trans
      ((congrArg ContinuousLinearMap.toLinearMap he).trans (Matrix.toLpLin_mul_same 2 R A).symm))

/-- The azimuthal projection of curl transforms correctly under a proper
transverse rotation. This needs only three entries of differentiated covariance. -/
theorem rotated_azimuthal_curl_eq
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (c s : ℝ) (hcs : c^2 + s^2 = 1)
    (he : B * !![c, -s, 0; s, c, 0; 0, 0, 1] =
      !![c, -s, 0; s, c, 0; 0, 0, 1] * A) :
    c * (B 0 2 - B 2 0) - s * (B 2 1 - B 1 2) = A 0 2 - A 2 0 := by
  have hp := And.intro (congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 2) he)
    (And.intro (congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 2) he)
      (congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 2 0) he))
  norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hp
  linear_combination c * hp.1 + s * hp.2.1 - hp.2.2 + A 0 2 * hcs

/-- The azimuthal curl component at any angle is its second Cartesian component
at angle zero. No second derivative of the field is assumed. -/
theorem azimuthal_curl_fderiv_cylindrical
    {f : E₃ → E₃} {v w : ℝ → ℝ → ℝ} (hd : Differentiable ℝ f)
    (hf : ∀ r : ℝ, 0 ≤ r → ∀ θ z : ℝ,
      f !₂[r * Real.cos θ, r * Real.sin θ, z] =
        !₂[v r z * Real.cos θ, v r z * Real.sin θ, w r z]) (r θ z : ℝ) :
    Real.cos θ * curlLinearMap (fderiv ℝ f !₂[r * Real.cos θ, r * Real.sin θ, z]) 1 -
      Real.sin θ * curlLinearMap (fderiv ℝ f !₂[r * Real.cos θ, r * Real.sin θ, z]) 0 =
        curlLinearMap (fderiv ℝ f !₂[r, 0, z]) 1 := by
  have hr : Matrix.toEuclideanLin
      !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1]
        (!₂[r, 0, z] : E₃) = !₂[r * Real.cos θ, r * Real.sin θ, z] := by
    simpa using rotation_apply_cylindrical θ r 0 z
  have hm := matrix_mul_eq_mul_of_semiconj_at
    (hasFDerivAt_euclideanMatrix_fderiv (hd !₂[r, 0, z]))
    (hr.symm ▸ hasFDerivAt_euclideanMatrix_fderiv
      (hd !₂[r * Real.cos θ, r * Real.sin θ, z]))
    (rotation_semiconj_of_cylindrical_representation hf θ)
  simpa only [hr, curlLinearMap_euclideanMatrix, Matrix.cons_val_zero, Matrix.cons_val_one]
    using rotated_azimuthal_curl_eq _ _ _ _ (Real.cos_sq_add_sin_sq θ) hm

/-- Distance from an axis observation point is independent of the polar angle. -/
theorem norm_cylindrical_sub_axis (r θ z ξ : ℝ) :
    ‖(!₂[r * Real.cos θ, r * Real.sin θ, z] : E₃) - !₂[0, 0, ξ]‖ =
      ‖(!₂[r, 0, z] : E₃) - !₂[0, 0, ξ]‖ := by
  simp only [EuclideanSpace.norm_eq, Fin.sum_univ_three, PiLp.sub_apply,
    Real.norm_eq_abs, sq_abs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, sub_zero,
    zero_pow (by decide : 2 ≠ 0), add_zero]
  congr 1
  linear_combination r ^ 2 * Real.cos_sq_add_sin_sq θ

/-- The signed Cartesian curl numerator reduces to radius times the azimuthal
component on the meridional ray. -/
theorem axis_curl_numerator_cylindrical
    {f : E₃ → E₃} {v w : ℝ → ℝ → ℝ} (hd : Differentiable ℝ f)
    (hf : ∀ r : ℝ, 0 ≤ r → ∀ θ z : ℝ,
      f !₂[r * Real.cos θ, r * Real.sin θ, z] =
        !₂[v r z * Real.cos θ, v r z * Real.sin θ, w r z]) (r θ z : ℝ) :
    (r * Real.cos θ) * curlLinearMap (fderiv ℝ f !₂[r * Real.cos θ, r * Real.sin θ, z]) 1 -
      (r * Real.sin θ) * curlLinearMap (fderiv ℝ f !₂[r * Real.cos θ, r * Real.sin θ, z]) 0 =
        r * curlLinearMap (fderiv ℝ f !₂[r, 0, z]) 1 := by
  linear_combination r * azimuthal_curl_fderiv_cylindrical hd hf r θ z

/-- Angular invariance in cylindrical coordinates is invariance under the
corresponding Cartesian rotation at every point, including the axis. -/
theorem comp_rotation_eq_of_cylindrical {F : Type*} {f : E₃ → F}
    (hf : ∀ r θ z : ℝ, f !₂[r * Real.cos θ, r * Real.sin θ, z] = f !₂[r, 0, z])
    (β : ℝ) (x : E₃) :
    f (Matrix.toEuclideanLin
      !![Real.cos β, -Real.sin β, 0; Real.sin β, Real.cos β, 0; 0, 0, 1] x) = f x := by
  obtain ⟨r, θ, z, _, rfl⟩ := exists_cylindrical_coordinates x
  rw [rotation_apply_cylindrical, hf, hf]

/-- Composition with a rotation-covariant map preserves scalar angular invariance. -/
theorem cylindrical_invariant_comp_of_semiconj {F : Type*} {f : E₃ → F} {g : E₃ → E₃}
    (hf : ∀ r θ z : ℝ, f !₂[r * Real.cos θ, r * Real.sin θ, z] = f !₂[r, 0, z])
    (hg : ∀ β : ℝ, Function.Semiconj g
      (Matrix.toEuclideanLin
        !![Real.cos β, -Real.sin β, 0; Real.sin β, Real.cos β, 0; 0, 0, 1])
      (Matrix.toEuclideanLin
        !![Real.cos β, -Real.sin β, 0; Real.sin β, Real.cos β, 0; 0, 0, 1]))
    (r θ z : ℝ) :
    f (g !₂[r * Real.cos θ, r * Real.sin θ, z]) = f (g !₂[r, 0, z]) := by
  have hr : Matrix.toEuclideanLin
      !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1]
        (!₂[r, 0, z] : E₃) = !₂[r * Real.cos θ, r * Real.sin θ, z] := by
    simpa using rotation_apply_cylindrical θ r 0 z
  rw [← hr, hg θ !₂[r, 0, z], comp_rotation_eq_of_cylindrical hf]

end ClockBarrier.Geometry
