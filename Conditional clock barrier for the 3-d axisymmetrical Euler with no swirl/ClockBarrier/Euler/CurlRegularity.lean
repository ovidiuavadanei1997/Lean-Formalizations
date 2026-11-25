/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.Classical
public import ClockBarrier.Euler.Axisymmetry
public import ClockBarrier.Geometry.CurlAxis
public import ClockBarrier.Analysis.AxisHolder
import ClockBarrier.Dynamics.VelocityRegularity

/-! # Regularity of the Cartesian curl of a classical Euler velocity

These ordinary helper theorems use the literal curl extraction map applied to
the actual spatial derivative. They use only the spatial and temporal
regularity and, for axis vanishing, the cylindrical symmetry.
No vorticity evolution equation or Cauchy transport is assumed or concluded.
-/

public section

namespace ClockBarrier.Euler

open Set Geometry
open scoped NNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The actual curl has a bounded continuous spatial realization, continuous in
time in the supremum norm, with uniform Hölder bounds on each compact time interval. -/
theorem classical_euler_on.exists_boundedContinuous_curl
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) :
    ∃ W : ℝ → E₃ →ᵇ E₃,
      ContinuousOn W (Ico 0 T) ∧
      (∀ t ∈ Ico 0 T, ∀ x, W t x = curlLinearMap (fderiv ℝ (u t) x)) ∧
      ∀ b ∈ Ico 0 T, ∃ H : ℝ≥0, ∀ t ∈ Icc 0 b, HolderWith H α (W t) := by
  obtain ⟨D, hD, hd, hHolder⟩ := h.2.2.2.2.1
  refine ⟨fun t => curlLinearMap.compLeftContinuousBounded E₃ (D t),
    (curlLinearMap.compLeftContinuousBounded E₃).continuous.comp_continuousOn hD, ?_, ?_⟩
  · intro t ht x
    simp only [ContinuousLinearMap.compLeftContinuousBounded_apply, (hd t ht x).fderiv]
  · intro b hb
    obtain ⟨H, hH⟩ := hHolder b hb
    exact ⟨‖curlLinearMap‖₊ * H, fun t ht => holderWith_curlLinearMap (hH t ht)⟩

/-- The actual Cartesian curl is jointly continuous in time and space. -/
theorem classical_euler_on.continuousOn_curl
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) :
    ContinuousOn (fun q : ℝ × E₃ => curlLinearMap (fderiv ℝ (u q.1) q.2))
      (Ico 0 T ×ˢ univ) := by
  obtain ⟨W, hW, heq, _⟩ := h.exists_boundedContinuous_curl
  exact (Dynamics.continuousOn_uncurry_of_boundedContinuousFunction hW).congr
    (fun q hq => (heq q.1 hq.1 q.2).symm)

/-- The spatial curl is uniformly Hölder on each compact time interval before T. -/
theorem classical_euler_on.holderWith_curl
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) :
    ∀ b ∈ Ico 0 T, ∃ H : ℝ≥0, ∀ t ∈ Icc 0 b,
      HolderWith H α (fun x => curlLinearMap (fderiv ℝ (u t) x)) := by
  obtain ⟨W, _, heq, hHolder⟩ := h.exists_boundedContinuous_curl
  intro b hb
  obtain ⟨H, hH⟩ := hHolder b hb
  refine ⟨H, fun t ht => ?_⟩
  have hfun : (fun x => curlLinearMap (fderiv ℝ (u t) x)) = W t :=
    funext (fun x => (heq t ⟨ht.1, ht.2.trans_lt hb.2⟩ x).symm)
  rw [hfun]
  exact hH t ht

/-- No-swirl axisymmetry makes the actual curl vanish at every axis point. -/
theorem classical_euler_on.curl_axis_eq_zero
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {t : ℝ} (ht : t ∈ Ico 0 T)
    (haxis : axisymmetric_no_swirl (u t)) (z : ℝ) :
    curlLinearMap (fderiv ℝ (u t) !₂[0, 0, z]) = 0 := by
  obtain ⟨D, _, hd, _⟩ := h.2.2.2.2.1
  obtain ⟨v, w, hvw⟩ := haxis
  exact curlLinearMap_fderiv_axis_eq_zero (hd t ht _).differentiableAt hvw

/-- A single compact-time constant controls the curl by radius to the power α,
uniformly over every spatial point and every axis height. -/
theorem classical_euler_on.norm_curl_le_radius_rpow
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p)
    (haxis : ∀ t ∈ Ico 0 T, axisymmetric_no_swirl (u t)) :
    ∀ b ∈ Ico 0 T, ∃ H : ℝ≥0, ∀ t ∈ Icc 0 b, ∀ x : E₃,
      ‖curlLinearMap (fderiv ℝ (u t) x)‖ ≤
        H * (Real.sqrt ((x 0)^2 + (x 1)^2)) ^ (α : ℝ) := by
  intro b hb
  obtain ⟨H, hH⟩ := h.holderWith_curl b hb
  refine ⟨H, fun t ht x => ?_⟩
  have htT : t ∈ Ico 0 T := ⟨ht.1, ht.2.trans_lt hb.2⟩
  exact Analysis.norm_le_radius_rpow_of_holderWith_axis_zero (hH t ht)
    (h.curl_axis_eq_zero htT (haxis t htT)) x

end ClockBarrier.Euler
