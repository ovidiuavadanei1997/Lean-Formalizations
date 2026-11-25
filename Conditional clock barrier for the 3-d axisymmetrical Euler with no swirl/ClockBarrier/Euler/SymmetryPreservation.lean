/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.Uniqueness
public import ClockBarrier.Euler.OrthogonalTransform
import ClockBarrier.Geometry.CylindricalIsometries
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-! # Preservation of axisymmetry and absence of swirl by Euler uniqueness -/

public section
namespace ClockBarrier.Euler
open Set
open scoped NNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Every orthogonal symmetry of the initial velocity persists. The pressure
need not have an invariant gauge. -/
theorem classical_euler_on.preserves_orthogonal_symmetry
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (R : E₃ ≃ₗᵢ[ℝ] E₃)
    (hR : Function.Semiconj (u 0) R R) {t : ℝ} (ht : t ∈ Ico 0 T) :
    Function.Semiconj (u t) R R := by
  obtain ⟨v, hv, heuler⟩ := h.exists_orthogonal_transform R
  have h0 : v 0 = u 0 := by
    apply BoundedContinuousFunction.ext
    intro x
    rw [hv, ← hR (R.symm x), R.apply_symm_apply]
  have he := heuler.velocity_eq h h0 ht
  intro x
  simpa only [he, R.symm_apply_apply] using hv t (R x)

/-- Transferring the rotations and meridional reflection of a cylindrical
no-swirl field reconstructs the exact cylindrical formula, including the axis. -/
theorem axisymmetric_no_swirl_of_symmetry_transfer {f g : E₃ → E₃}
    (hf : axisymmetric_no_swirl f)
    (htransfer : ∀ R : E₃ ≃ₗᵢ[ℝ] E₃,
      Function.Semiconj f R R → Function.Semiconj g R R) :
    axisymmetric_no_swirl g := by
  obtain ⟨v, w, hf⟩ := hf
  have hsem (R : E₃ ≃ₗᵢ[ℝ] E₃) (τ : ℝ → ℝ)
      (ha : ∀ r θ z : ℝ, R !₂[r * Real.cos θ, r * Real.sin θ, z] =
        !₂[r * Real.cos (τ θ), r * Real.sin (τ θ), z]) : Function.Semiconj f R R := by
    intro x
    obtain ⟨r, θ, z, hr, rfl⟩ := Geometry.exists_cylindrical_coordinates x
    rw [ha, hf r hr, hf r hr, ha]
  obtain ⟨S, hS⟩ := Geometry.exists_meridional_reflection
  have hs : Function.Semiconj g S S := htransfer S (hsem S (fun θ => -θ) (by
    intro r θ z
    rw [hS]
    simp))
  have hz (r z : ℝ) : g !₂[r, 0, z] 1 = 0 := by
    have he := congrArg (fun x : E₃ => x 1) (hs !₂[r, 0, z])
    simp [hS] at he
    linarith
  refine ⟨fun r z => g !₂[r, 0, z] 0, fun r z => g !₂[r, 0, z] 2, ?_⟩
  intro r _ θ z
  obtain ⟨R, hR⟩ := Geometry.exists_cylindrical_rotation θ
  have hrot : Function.Semiconj g R R := htransfer R (hsem R (fun φ => φ + θ) (by
    intro a φ b
    rw [hR]
    ext i
    fin_cases i <;> simp [Real.cos_add, Real.sin_add] <;> ring))
  have he := hrot !₂[r, 0, z]
  rw [hR, hR] at he
  simpa [hz, mul_comm] using he

/-- Initial axisymmetry and no swirl persist throughout the classical lifespan.
This is derived from orthogonal covariance and finite-energy uniqueness. -/
theorem classical_euler_on.axisymmetric_no_swirl
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (haxis : axisymmetric_no_swirl (u 0))
    {t : ℝ} (ht : t ∈ Ico 0 T) : axisymmetric_no_swirl (u t) :=
  axisymmetric_no_swirl_of_symmetry_transfer haxis
    (fun R hR => h.preserves_orthogonal_symmetry R hR ht)

end ClockBarrier.Euler
