/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.Vorticity
public import ClockBarrier.Euler.CurlRegularity
public import ClockBarrier.Geometry.CartesianDerivative

/-! # Regularity of the Cartesian vorticity

The definition needs only scalar Cartesian partial derivatives.
The classical Euler interface supplies these and identifies their curl with
the already controlled antisymmetric spatial derivative. No second derivatives
or vorticity evolution law are used.
-/

public section

namespace ClockBarrier.Euler

open Set Geometry
open scoped NNReal BoundedContinuousFunction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Actual differentiability identifies the partial-derivative curl
with the continuous linear curl extraction map. -/
theorem vorticity_eq_curlLinearMap {u : E₃ → E₃}
    (hp : ∀ x : E₃, ∀ i j : Fin 3,
      DifferentiableAt ℝ (fun s : ℝ => u (x + s • EuclideanSpace.single i 1) j) 0)
    {x : E₃} (hu : DifferentiableAt ℝ u x) :
    vorticity u hp x = curlLinearMap (fderiv ℝ u x) :=
  cartesian_curl_eq_curlLinearMap hu

/-- The Euler regularity supplies every Cartesian scalar partial. -/
theorem classical_euler_on.cartesian_partials
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (t : ℝ) (ht : t ∈ Ico 0 T) :
    ∀ x : E₃, ∀ i j : Fin 3,
      DifferentiableAt ℝ (fun s : ℝ => u t (x + s • EuclideanSpace.single i 1) j) 0 := by
  obtain ⟨D, _, hd, _⟩ := h.2.2.2.2.1
  exact fun x i j =>
    (hasDerivAt_component_line (hd t ht x) (EuclideanSpace.single i 1) j).differentiableAt

/-- The actual Euler vorticity is the curl of its actual spatial derivative. -/
theorem classical_euler_on.vorticity_eq_curlLinearMap
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (t : ℝ) (ht : t ∈ Ico 0 T) (x : E₃) :
    vorticity (u t) (h.cartesian_partials t ht) x = curlLinearMap (fderiv ℝ (u t) x) := by
  obtain ⟨D, _, hd, _⟩ := h.2.2.2.2.1
  exact Euler.vorticity_eq_curlLinearMap _ (hd t ht x).differentiableAt

/-- Vorticity has a bounded continuous spatial realization continuous in time
in the supremum norm, with the same compact-time Hölder exponent. -/
theorem classical_euler_on.exists_boundedContinuous_vorticity
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) :
    ∃ W : ℝ → E₃ →ᵇ E₃,
      ContinuousOn W (Ico 0 T) ∧
      (∀ t, ∀ ht : t ∈ Ico 0 T, ∀ x, W t x = vorticity (u t) (h.cartesian_partials t ht) x) ∧
      ∀ b ∈ Ico 0 T, ∃ H : ℝ≥0, ∀ t ∈ Icc 0 b, HolderWith H α (W t) := by
  obtain ⟨W, hW, heq, hHolder⟩ := h.exists_boundedContinuous_curl
  exact ⟨W, hW, fun t ht x => (heq t ht x).trans
    (h.vorticity_eq_curlLinearMap t ht x).symm, hHolder⟩

/-- At every lifespan time, the actual vorticity is spatially continuous. -/
theorem classical_euler_on.continuous_vorticity
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (t : ℝ) (ht : t ∈ Ico 0 T) :
    Continuous (vorticity (u t) (h.cartesian_partials t ht)) := by
  obtain ⟨W, _, heq, _⟩ := h.exists_boundedContinuous_vorticity
  exact (W t).continuous.congr (heq t ht)

/-- Joint continuity uses the lifespan as a subtype, so no vorticity value is
invented at times where Cartesian partial derivatives have not been supplied. -/
theorem classical_euler_on.continuous_vorticity_lifespan
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) :
    Continuous (fun q : {t : ℝ // t ∈ Ico 0 T} × E₃ =>
      vorticity (u q.1.val) (h.cartesian_partials q.1.val q.1.property) q.2) := by
  obtain ⟨W, hW, heq, _⟩ := h.exists_boundedContinuous_vorticity
  have hc : Continuous (fun q : {t : ℝ // t ∈ Ico 0 T} × E₃ => W q.1.val q.2) :=
    continuous_eval.comp ((hW.restrict.comp continuous_fst).prodMk continuous_snd)
  exact hc.congr (fun q => heq q.1.val q.1.property q.2)

/-- The named vorticity has compact-time uniform spatial Hölder bounds. -/
theorem classical_euler_on.holderWith_vorticity
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) :
    ∀ b, ∀ hb : b ∈ Ico 0 T, ∃ H : ℝ≥0, ∀ t, ∀ ht : t ∈ Icc 0 b,
      HolderWith H α (vorticity (u t) (h.cartesian_partials t ⟨ht.1, ht.2.trans_lt hb.2⟩)) := by
  intro b hb
  obtain ⟨H, hH⟩ := h.holderWith_curl b hb
  refine ⟨H, fun t ht => ?_⟩
  have heq : vorticity (u t) (h.cartesian_partials t ⟨ht.1, ht.2.trans_lt hb.2⟩) =
      fun x => curlLinearMap (fderiv ℝ (u t) x) :=
    funext (h.vorticity_eq_curlLinearMap t ⟨ht.1, ht.2.trans_lt hb.2⟩)
  rw [heq]
  exact hH t ht

/-- The vorticity vanishes at all axis points of a no-swirl field. -/
theorem classical_euler_on.vorticity_axis_eq_zero
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (t : ℝ) (ht : t ∈ Ico 0 T)
    (haxis : axisymmetric_no_swirl (u t)) (z : ℝ) :
    vorticity (u t) (h.cartesian_partials t ht) !₂[0, 0, z] = 0 := by
  rw [h.vorticity_eq_curlLinearMap t ht]
  exact h.curl_axis_eq_zero ht haxis z

/-- One compact-time constant bounds the actual vorticity by radius to α. -/
theorem classical_euler_on.norm_vorticity_le_radius_rpow
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p)
    (haxis : ∀ t ∈ Ico 0 T, axisymmetric_no_swirl (u t)) :
    ∀ b, ∀ hb : b ∈ Ico 0 T, ∃ H : ℝ≥0, ∀ t, ∀ ht : t ∈ Icc 0 b, ∀ x : E₃,
      ‖vorticity (u t) (h.cartesian_partials t ⟨ht.1, ht.2.trans_lt hb.2⟩) x‖ ≤
        H * (Real.sqrt ((x 0)^2 + (x 1)^2)) ^ (α : ℝ) := by
  intro b hb
  obtain ⟨H, hH⟩ := h.norm_curl_le_radius_rpow haxis b hb
  refine ⟨H, fun t ht x => ?_⟩
  rw [h.vorticity_eq_curlLinearMap t ⟨ht.1, ht.2.trans_lt hb.2⟩]
  exact hH t ht x

end ClockBarrier.Euler
