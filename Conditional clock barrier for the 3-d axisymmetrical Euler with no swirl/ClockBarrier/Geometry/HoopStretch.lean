/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Geometry.CylindricalCurl
public import ClockBarrier.Geometry.NearIdentity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
/-! # The angular derivative and hoop stretch of a rotation-equivariant flow -/

public section
namespace ClockBarrier.Geometry
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
open Set

/-- Angular differentiation of a rotation orbit gives the azimuthal generator. -/
theorem hasDerivAt_rotation_orbit_zero (a : E₃) :
    HasDerivAt (fun θ : ℝ => Matrix.toEuclideanLin
      !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1] a)
      (!₂[-a 1, a 0, 0] : E₃) 0 := by
  have hc := (Real.hasDerivAt_cos 0).smul_const (!₂[a 0, a 1, 0] : E₃)
  have hs := (Real.hasDerivAt_sin 0).smul_const (!₂[-a 1, a 0, 0] : E₃)
  have hh := (hc.add hs).add_const (!₂[0, 0, a 2] : E₃)
  convert! hh using 1
  · ext θ i
    fin_cases i <;> simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail]
    ring
  · simp

/-- Differentiate rotation covariance to obtain the undivided hoop-stretch identity. -/
theorem fderiv_angular_generator_of_rotation {f : E₃ → E₃} {a : E₃}
    (hf : DifferentiableAt ℝ f a)
    (hrot : ∀ θ : ℝ, Function.Semiconj f
      (Matrix.toEuclideanLin
        !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1])
      (Matrix.toEuclideanLin
        !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1])) :
    fderiv ℝ f a !₂[-a 1, a 0, 0] = !₂[-f a 1, f a 0, 0] := by
  have hz : Matrix.toEuclideanLin
      !![Real.cos (0 : ℝ), -Real.sin 0, 0; Real.sin 0, Real.cos 0, 0; 0, 0, 1] a = a := by
    ext i
    fin_cases i <;> simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail]
  have hcomp := (hz.symm ▸ hf.hasFDerivAt).comp_hasDerivAt 0 (hasDerivAt_rotation_orbit_zero a)
  have heq : (fun θ : ℝ => f (Matrix.toEuclideanLin
      !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1] a)) =
      (fun θ : ℝ => Matrix.toEuclideanLin
      !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1] (f a)) :=
    funext (fun θ => hrot θ a)
  simp only [Function.comp_def] at hcomp
  rw [heq, hz] at hcomp
  exact hcomp.unique (hasDerivAt_rotation_orbit_zero (f a))

/-- The angular generator has norm equal to cylindrical radius. -/
theorem norm_angular_generator (a : E₃) :
    ‖(!₂[-a 1, a 0, 0] : E₃)‖ = Real.sqrt ((a 0)^2 + (a 1)^2) := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_three, add_comm]

/-- The hoop-stretch entry controls radius near the identity. The undivided
identity `DΦ(R eθ) = r eθ` also handles the axis without division by zero. -/
theorem radius_bounds_of_hoop_stretch {f : E₃ → E₃} {a : E₃}
    (hf : DifferentiableAt ℝ f a)
    (hrot : ∀ θ : ℝ, Function.Semiconj f
      (Matrix.toEuclideanLin
        !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1])
      (Matrix.toEuclideanLin
        !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1]))
    (hF : ‖fderiv ℝ f a - ContinuousLinearMap.id ℝ E₃‖ ≤ 1 / 2) :
    (1 / 2 : ℝ) * Real.sqrt ((a 0)^2 + (a 1)^2) ≤
        Real.sqrt ((f a 0)^2 + (f a 1)^2) ∧
    Real.sqrt ((f a 0)^2 + (f a 1)^2) ≤
      (3 / 2 : ℝ) * Real.sqrt ((a 0)^2 + (a 1)^2) := by
  have hb := norm_bounds_of_norm_sub_id_le hF (!₂[-a 1, a 0, 0] : E₃)
  rw [fderiv_angular_generator_of_rotation hf hrot, norm_angular_generator,
    norm_angular_generator] at hb
  norm_num only at hb
  exact hb
end ClockBarrier.Geometry
