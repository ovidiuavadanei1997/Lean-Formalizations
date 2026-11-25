import ClockBarrier
open Set Filter MeasureTheory
open scoped NNReal Topology InnerProductSpace BoundedContinuousFunction
open ClockBarrier ClockBarrier.Euler ClockBarrier.Analysis
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)
-- Exact public type: ClockBarrier.Euler.axis_clock_barrier
example : ∀ {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃}
    (_hα : (1 / 3 : ℝ) ≤ (α : ℝ)) (_hcoh : axis_coherent_on α T u)
    (_hreflection : ∀ t ∈ Ico 0 T, z_reflection_symmetric (u t))
    (_hmaximal : ∀ T' : ℝ, T < T' →
      ¬ ∃ v : ℝ → E₃ →ᵇ E₃,
        axis_coherent_on α T' v ∧ ∀ t ∈ Ico 0 T, v t = u t),
    ∃ c : ℝ, 0 < c ∧ ∀ Φ : ℝ → E₃ → E₃,
      (∀ x, Φ 0 x = x) →
      (∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T)) →
      (∀ x, ∀ t ∈ Ico 0 T,
        HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t) →
      ∀ z : ℝ, ∀ t ∈ Ico 0 T, ∃ j : ℝ,
        c ≤ j ∧ Tendsto (fun r : ℝ =>
          (fderiv ℝ (fun q : E₂ =>
            (!₂[Real.sqrt ((Φ t !₂[q 0, 0, q 1] 0)^2 + (Φ t !₂[q 0, 0, q 1] 1)^2),
              Φ t !₂[q 0, 0, q 1] 2] : E₂)) !₂[r, z]).toLinearMap.det)
          (𝓝[>] 0) (𝓝 j) := by exact @ClockBarrier.Euler.axis_clock_barrier

-- Exact public type: ClockBarrier.Euler.general_clock_continuation
example : ∀ {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃},
    (1 / 3 : ℝ) ≤ (α : ℝ) → general_coherent_on α T u →
    ∃ T' : ℝ, T < T' ∧ ∃ v : ℝ → E₃ →ᵇ E₃, ∃ p : ℝ → E₃ → ℝ,
      classical_euler_on α T' v p ∧
      (∀ t ∈ Ico 0 T', axisymmetric_no_swirl (v t)) ∧
      ∀ t ∈ Ico 0 T, v t = u t := by exact @ClockBarrier.Euler.general_clock_continuation

-- Exact public type: ClockBarrier.Euler.smallest_singularValue_evolution
example : ∀ {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (_h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (_hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (_hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (_hinit : ∀ x, Φ 0 x = x) (a : E₃) {t : ℝ} (_ht : t ∈ Ico 0 T),
  let F := fun s => fderiv ℝ (Φ s) a
    let ν := fun s => (F s).toLinearMap.singularValues 2
    let L := fderiv ℝ (u t) (Φ t a)
    let S := (1 / 2 : ℝ) • (L + L.adjoint)
    let G := {r : ℝ | ∃ e : E₃, ‖e‖ = 1 ∧
      F t ((F t).adjoint e) = ν t ^ 2 • e ∧ r = ⟪e, S e⟫_ℝ}
    IsLeast G (sInf G) ∧ HasDerivWithinAt ν (ν t * sInf G) (Ici t) t := by exact @ClockBarrier.Euler.smallest_singularValue_evolution

-- Exact public type: ClockBarrier.Euler.general_driver_bound
example : ∀ {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃},
    (1 / 3 : ℝ) ≤ (α : ℝ) → general_coherent_on α T u →
    ∃ B : ℝ → ℝ, ∃ C : ℝ,
      IntegrableOn B (Ico 0 T) volume ∧
      (∀ t ∈ Ico 0 T, 0 < B t) ∧ 0 < C ∧
      ∀ Φ : ℝ → E₃ → E₃,
        (∀ x, Φ 0 x = x) →
        (∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T)) →
        (∀ x, ∀ t ∈ Ico 0 T,
          HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t) →
        ∀ a : E₃, ∀ t ∈ Ico 0 T,
          let F := fderiv ℝ (Φ t) a
          let ν := F.toLinearMap.singularValues 2
          let L := fderiv ℝ (u t) (Φ t a)
          let S := (1 / 2 : ℝ) • (L + L.adjoint)
          ∀ e : E₃, ‖e‖ = 1 → F (F.adjoint e) = ν ^ 2 • e →
            |⟪e, S e⟫_ℝ| ≤ B t + C * ν ^ ((3 * (α : ℝ) - 1) / 2) := by exact @ClockBarrier.Euler.general_driver_bound

-- Exact public type: ClockBarrier.Euler.local_general_coherence
example : ∀ {α : ℝ≥0} {T : ℝ} {u : ℝ → EuclideanSpace ℝ (Fin 3) →ᵇ EuclideanSpace ℝ (Fin 3)} {p : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ} (_h : ClockBarrier.Euler.classical_euler_on α T u p) (_haxis : ClockBarrier.Euler.axisymmetric_no_swirl (u 0)),
  ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ < T ∧ ClockBarrier.Euler.general_coherent_on α T₀ u := by exact @ClockBarrier.Euler.local_general_coherence

-- Exact public type: ClockBarrier.Euler.local_axis_coherence
example : ∀ {α : ℝ≥0} {T : ℝ}
    {u : ℝ → EuclideanSpace ℝ (Fin 3) →ᵇ EuclideanSpace ℝ (Fin 3)}
    {p : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ}
    (_h : ClockBarrier.Euler.classical_euler_on α T u p)
    (_haxis : ClockBarrier.Euler.axisymmetric_no_swirl (u 0))
    (_hreflection : ClockBarrier.Euler.z_reflection_symmetric (u 0)),
  ∃ T₀ : ℝ, 0 < T₀ ∧ T₀ < T ∧
      ClockBarrier.Euler.axis_coherent_on α T₀ u := by exact @ClockBarrier.Euler.local_axis_coherence

-- Exact public type: ClockBarrier.Analysis.exists_curl_holder_logarithmic_constant
example : ∀ (α : ℝ≥0), 0 < α → α < 1 →
  ∃ C : ℝ≥0, 0 < C ∧
    ∀ (u : E₃ →ᵇ E₃) (D : E₃ →ᵇ (E₃ →L[ℝ] E₃)),
      (∀ x, HasFDerivAt (u : E₃ → E₃) (D x) x) →
      (∃ K : ℝ≥0, HolderWith K α (D : E₃ → E₃ →L[ℝ] E₃)) →
      MemLp (u : E₃ → E₃) 2 volume →
      (∀ x, LinearMap.trace ℝ E₃ (D x).toLinearMap = 0) →
      let ω : E₃ →ᵇ E₃ := Geometry.curlLinearMap.compLeftContinuousBounded E₃ D
      ∀ H : ℝ≥0, HolderWith H α (ω : E₃ → E₃) →
        HolderWith (C * H) α (D : E₃ → E₃ →L[ℝ] E₃) ∧
        ‖D‖ ≤ (C : ℝ) *
          (1 + (eLpNorm (u : E₃ → E₃) 2 volume).toReal +
            ‖ω‖ * Real.log (Real.exp 1 + (H : ℝ))) := by exact @ClockBarrier.Analysis.exists_curl_holder_logarithmic_constant

-- Exact public type: ClockBarrier.Euler.vorticity_holder_growth_and_bkm_bounds
example : ∀ (α : ℝ≥0), 0 < α → α < 1 →
  ∃ C : ℝ≥0, 0 < C ∧
    ∀ (T : ℝ) (u : ℝ → E₃ →ᵇ E₃) (p : ℝ → E₃ → ℝ)
      (_h : classical_euler_on α T u p),
    ∃ D : ℝ → E₃ →ᵇ (E₃ →L[ℝ] E₃), ∃ W : ℝ → E₃ →ᵇ E₃,
      ContinuousOn D (Ico 0 T) ∧ ContinuousOn W (Ico 0 T) ∧
      (∀ t ∈ Ico 0 T, ∀ x, HasFDerivAt (u t : E₃ → E₃) (D t x) x) ∧
      (∀ t, ∀ _ht : t ∈ Ico 0 T, ∀ x,
        W t x = vorticity (u t) (_h.cartesian_partials t _ht) x) ∧
      (∀ H₀ : ℝ≥0, HolderWith H₀ α (W 0 : E₃ → E₃) →
        ∀ t ∈ Ico 0 T,
          HolderWith (H₀ * ⟨Real.exp ((C : ℝ) * ∫ s in 0..t, ‖D s‖),
            (Real.exp_pos _).le⟩) α (W t : E₃ → E₃)) ∧
      (∀ t ∈ Ico 0 T,
        ‖W t‖ ≤ ‖W 0‖ * Real.exp (∫ s in 0..t, ‖D s‖)) ∧
      (IntegrableOn (fun t => ‖W t‖) (Ico 0 T) volume →
        ∃ M : ℝ≥0, 0 < M ∧ ∀ t ∈ Ico 0 T,
          ‖u t‖ ≤ M ∧ ‖D t‖ ≤ M ∧ ‖W t‖ ≤ M ∧
          HolderWith M α (D t : E₃ → E₃ →L[ℝ] E₃) ∧
          HolderWith M α (W t : E₃ → E₃) ∧
          (eLpNorm (u t : E₃ → E₃) 2 volume).toReal ≤ M) := by exact @ClockBarrier.Euler.vorticity_holder_growth_and_bkm_bounds

-- Exact public type: ClockBarrier.Euler.uniform_local_classical_euler
example : ∀ (α : ℝ≥0), 0 < α → α < 1 →
  ∀ M : ℝ≥0, ∃ τ : ℝ, 0 < τ ∧
    ∀ (u₀ : E₃ →ᵇ E₃) (D₀ : E₃ →ᵇ (E₃ →L[ℝ] E₃)),
      (∀ x, HasFDerivAt (u₀ : E₃ → E₃) (D₀ x) x) →
      ‖u₀‖ ≤ (M : ℝ) → ‖D₀‖ ≤ (M : ℝ) →
      HolderWith M α (D₀ : E₃ → E₃ →L[ℝ] E₃) →
      MemLp (u₀ : E₃ → E₃) 2 volume →
      (eLpNorm (u₀ : E₃ → E₃) 2 volume).toReal ≤ (M : ℝ) →
      (∀ x, LinearMap.trace ℝ E₃ (D₀ x).toLinearMap = 0) →
      ∃ v : ℝ → E₃ →ᵇ E₃, ∃ p : ℝ → E₃ → ℝ,
        classical_euler_on α τ v p ∧ v 0 = u₀ := by exact @ClockBarrier.Euler.uniform_local_classical_euler

#print axioms ClockBarrier.Euler.axis_clock_barrier
#print axioms ClockBarrier.Euler.general_clock_continuation
#print axioms ClockBarrier.Euler.smallest_singularValue_evolution
#print axioms ClockBarrier.Euler.general_driver_bound
#print axioms ClockBarrier.Euler.local_general_coherence
#print axioms ClockBarrier.Euler.local_axis_coherence
#print axioms ClockBarrier.Analysis.exists_curl_holder_logarithmic_constant
#print axioms ClockBarrier.Euler.vorticity_holder_growth_and_bkm_bounds
#print axioms ClockBarrier.Euler.uniform_local_classical_euler
#print axioms ClockBarrier.Analysis.ac_comp_of_dist_le
#print axioms ClockBarrier.Analysis.ac_exp
#print axioms ClockBarrier.Analysis.ac_le_of_ae_deriv_nonpos
#print axioms ClockBarrier.Analysis.le_mul_exp_integral_of_ac_deriv_le
#print axioms ClockBarrier.Analysis.ac_rpow_of_one_le
#print axioms ClockBarrier.Analysis.directional_strain_kernel_add
#print axioms ClockBarrier.Analysis.integral_abs_add_le_of_bounds
#print axioms ClockBarrier.Analysis.abs_directional_cutoff_apply_le
#print axioms ClockBarrier.Analysis.le_linear_solution_of_right_deriv
#print axioms ClockBarrier.Analysis.exists_ac_linear_comparison
#print axioms ClockBarrier.Analysis.negative_power_derivative_bound
#print axioms ClockBarrier.Analysis.inverse_power_linear_derivative
#print axioms ClockBarrier.Analysis.exists_positive_power_comparison
#print axioms ClockBarrier.Analysis.quadratic_lower_of_unit_lower
#print axioms ClockBarrier.Analysis.exists_least_eigenspace_gap
#print axioms ClockBarrier.Analysis.eigenspace_quadratic_decomposition
#print axioms ClockBarrier.Analysis.quadratic_derivative_lower_of_split
#print axioms ClockBarrier.Analysis.spectral_gap_square_completion
#print axioms ClockBarrier.Analysis.unit_quadratic_affine_lower
#print axioms ClockBarrier.Analysis.exists_unit_quadratic_affine_lower
#print axioms ClockBarrier.Analysis.hasDerivWithinAt_sInf_unit_inner_of_minimizer
#print axioms ClockBarrier.Euler.classical_euler_on.deriv_axis_eq_biot_savart_of_cylindrical_cauchy
#print axioms ClockBarrier.Euler.classical_euler_on.deriv_axis_eq_smooth_near_add_far_of_cylindrical
#print axioms ClockBarrier.Euler.classical_euler_on.directional_initial_increment_bound
#print axioms ClockBarrier.Geometry.hasDerivAt_rotation_orbit_zero
#print axioms ClockBarrier.Geometry.fderiv_angular_generator_of_rotation
#print axioms ClockBarrier.Geometry.norm_angular_generator
#print axioms ClockBarrier.Geometry.radius_bounds_of_hoop_stretch
