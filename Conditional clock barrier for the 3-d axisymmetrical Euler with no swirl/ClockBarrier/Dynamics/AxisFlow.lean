/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Dynamics.AxisClockWithin
public import ClockBarrier.Dynamics.FlowDerivativeWithin
public import ClockBarrier.Dynamics.FlowVolume
public import ClockBarrier.Dynamics.FlowSymmetry
public import ClockBarrier.Geometry.AxisEvaluation
public import ClockBarrier.Geometry.CylindricalSymmetry
public import ClockBarrier.Geometry.PhysicalJacobian

/-!
# The physical axis clock of a constructed incompressible cylindrical flow

The clock is the actual signed meridional derivative determinant. Its physical
right-hand limit, positivity, and evolution are derived from velocity regularity,
the cylindrical no-swirl formula, and zero divergence.
-/

public section

namespace ClockBarrier.Dynamics

open ClockBarrier.Geometry Filter Set
open scoped Topology NNReal

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

variable {u Φ : ℝ → E₃ → E₃} {T : ℝ}
  (hu : ContinuousOn (Function.uncurry u) (Ico 0 T ×ˢ univ))
  (hdiff : ∀ t ∈ Ico 0 T, Differentiable ℝ (u t))
  (hD : ContinuousOn (fun p : ℝ × E₃ => fderiv ℝ (u p.1) p.2) (Ico 0 T ×ˢ univ))
  (hbound : ∀ b ∈ Ico 0 T, ∃ K : ℝ≥0,
    ∀ t ∈ Ico 0 b, ∀ x, ‖fderiv ℝ (u t) x‖₊ ≤ K)
  (haxis : ∀ t ∈ Ico 0 T, ∃ v w : ℝ → ℝ → ℝ,
    ∀ r : ℝ, 0 ≤ r → ∀ θ z : ℝ,
      u t !₂[r * Real.cos θ, r * Real.sin θ, z] =
        !₂[v r z * Real.cos θ, v r z * Real.sin θ, w r z])
  (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
  (hode : ∀ x, ∀ t ∈ Ico 0 T,
    HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
  (hinit : ∀ x, Φ 0 x = x)

include hdiff hbound haxis hcont hode hinit

/-- The flow inherits the three transverse symmetries from the full cylindrical velocity formula. -/
theorem transverse_symmetries_flow_of_cylindrical_velocity {t : ℝ} (ht : t ∈ Ico 0 T) :
    Function.Semiconj (Φ t)
      (Matrix.toEuclideanLin (Matrix.diagonal ![-1, 1, 1]))
      (Matrix.toEuclideanLin (Matrix.diagonal ![-1, 1, 1])) ∧
    Function.Semiconj (Φ t)
      (Matrix.toEuclideanLin (Matrix.diagonal ![1, -1, 1]))
      (Matrix.toEuclideanLin (Matrix.diagonal ![1, -1, 1])) ∧
    Function.Semiconj (Φ t)
      (Matrix.toEuclideanLin !![0, -1, 0; 1, 0, 0; 0, 0, 1])
      (Matrix.toEuclideanLin !![0, -1, 0; 1, 0, 0; 0, 0, 1]) := by
  choose v w hv using haxis
  exact ⟨semiconj_flow_Ico_of_fderiv_bound
      (Matrix.toEuclideanLin (Matrix.diagonal ![-1, 1, 1])).toContinuousLinearMap hdiff hbound
      (fun s hs => (transverse_symmetries_of_cylindrical_representation (hv s hs)).1)
      hcont hode hinit t ht,
    semiconj_flow_Ico_of_fderiv_bound
      (Matrix.toEuclideanLin (Matrix.diagonal ![1, -1, 1])).toContinuousLinearMap hdiff hbound
      (fun s hs => (transverse_symmetries_of_cylindrical_representation (hv s hs)).2.1)
      hcont hode hinit t ht,
    semiconj_flow_Ico_of_fderiv_bound
      (Matrix.toEuclideanLin !![0, -1, 0; 1, 0, 0; 0, 0, 1]).toContinuousLinearMap hdiff hbound
      (fun s hs => (transverse_symmetries_of_cylindrical_representation (hv s hs)).2.2)
      hcont hode hinit t ht⟩

variable (hdiv : ∀ t ∈ Ico 0 T, ∀ x,
  LinearMap.trace ℝ E₃ (fderiv ℝ (u t) x).toLinearMap = 0)

include hu hD hdiv

/-- The actual meridional Jacobian is a positive normalized axis clock, is the
physical Jacobian limit, and evolves by the transported axial scalar strain. -/
theorem axis_clock_of_cylindrical_velocity (hT : 0 < T) (z : ℝ) :
    let J : ℝ → ℝ := fun t =>
      (fderiv ℝ (fun p : E₂ =>
        (!₂[Φ t !₂[p 0, 0, p 1] 0, Φ t !₂[p 0, 0, p 1] 2] : E₂)) !₂[0, z]).toLinearMap.det
    J 0 = 1 ∧ ∀ t ∈ Ico 0 T,
      Φ t !₂[0, 0, z] = !₂[0, 0, Φ t !₂[0, 0, z] 2] ∧
      0 < J t ∧
      euclideanMatrix (fderiv ℝ (Φ t) !₂[0, 0, z]) =
        Matrix.diagonal ![(J t)⁻¹, (J t)⁻¹, (J t)^2] ∧
      Tendsto (fun r : ℝ =>
        (fderiv ℝ (fun p : E₂ =>
          (!₂[Real.sqrt ((Φ t !₂[p 0, 0, p 1] 0)^2 + (Φ t !₂[p 0, 0, p 1] 1)^2),
            Φ t !₂[p 0, 0, p 1] 2] : E₂)) !₂[r, z]).toLinearMap.det)
        (𝓝[>] 0) (𝓝 (J t)) ∧
      HasDerivWithinAt J
        ((1 / 2 : ℝ) * J t *
          deriv (fun ζ : ℝ => u t !₂[0, 0, ζ] 2) (Φ t !₂[0, 0, z] 2)) (Ico 0 T) t := by
  let A : ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun t =>
    euclideanMatrix (fderiv ℝ (Φ t) !₂[0, 0, z])
  intro J
  have hC1 (s : ℝ) (hs : s ∈ Ico 0 T) : ContDiff ℝ 1 (Φ s) :=
    (flow_spatial_regularity_Ico hu hdiff hD hbound hcont hode hinit s hs).1
  have hfd (s : ℝ) (hs : s ∈ Ico 0 T) :
      HasFDerivAt (Φ s) (Matrix.toEuclideanLin (A s)).toContinuousLinearMap !₂[0, 0, z] :=
    hasFDerivAt_euclideanMatrix_fderiv ((hC1 s hs).differentiable (by decide) _)
  have hsym (s : ℝ) (hs : s ∈ Ico 0 T) :=
    transverse_symmetries_flow_of_cylindrical_velocity hdiff hbound haxis hcont hode hinit hs
  have hdiag (s : ℝ) (hs : s ∈ Ico 0 T) :
      A s = Matrix.diagonal ![A s 0 0, A s 0 0, A s 2 2] :=
    eq_diagonal_of_hasFDerivAt_axis (hfd s hs) (hsym s hs).1 (hsym s hs).2.1 (hsym s hs).2.2
  have hdet (s : ℝ) (hs : s ∈ Ico 0 T) : (A s).det = 1 :=
    (det_euclideanMatrix _).trans
      (det_fderiv_flow_eq_one_Ico hu hdiff hD hbound hcont hode hinit hdiv _ hs)
  have hJ (s : ℝ) (hs : s ∈ Ico 0 T) : J s = (A s 0 0)⁻¹ :=
    det_fderiv_meridional_eq_inv (hfd s hs) (hdiag s hs) (hdet s hs)
  have hA0 : A 0 = 1 := by simp only [A, fderiv_flow_zero hinit, euclideanMatrix_id]
  refine ⟨by simpa only [hA0, Matrix.one_apply_eq, inv_one] using hJ 0 ⟨le_rfl, hT⟩,
    fun t ht => ?_⟩
  have hAc : ContinuousOn A (Icc 0 t) :=
    euclideanMatrix.continuous.comp_continuousOn
      (continuousOn_fderiv_flow_Icc hu hdiff hD hbound hcont hode hinit _ ht)
  have ha : 0 < A t 0 0 := axis_stretch_pos_of_det_eq_one ht.1
    ((continuous_apply 0).comp_continuousOn ((continuous_apply 0).comp_continuousOn hAc))
    (by simp only [hA0, Matrix.one_apply_eq])
    (fun s hs => hdiag s ⟨hs.1, hs.2.trans_lt ht.2⟩)
    (fun s hs => hdet s ⟨hs.1, hs.2.trans_lt ht.2⟩)
  have hmap : Φ t !₂[0, 0, z] = !₂[0, 0, Φ t !₂[0, 0, z] 2] :=
    map_axis_of_transverse_reflections (hsym t ht).1 (hsym t ht).2.1
  refine ⟨hmap, by simpa only [hJ t ht] using inv_pos.mpr ha,
    ?_, ?_, ?_⟩
  · simpa only [hJ t ht, inv_inv, (axis_entries_of_det_eq_one (hdiag t ht) (hdet t ht)).2.1]
      using hdiag t ht
  · simpa only [hJ t ht] using
      tendsto_det_fderiv_physical_meridional (hC1 t ht).contDiffAt (hfd t ht)
        (hsym t ht).1 (hsym t ht).2.1 (hsym t ht).2.2 (hdet t ht) ha
  · let M := euclideanMatrix (fderiv ℝ (u t) (Φ t !₂[0, 0, z]))
    have hfM : HasFDerivAt (u t) (Matrix.toEuclideanLin M).toContinuousLinearMap
        !₂[0, 0, Φ t !₂[0, 0, z] 2] := by
      simpa only [← hmap] using
        hasFDerivAt_euclideanMatrix_fderiv (hdiff t ht (Φ t !₂[0, 0, z]))
    obtain ⟨v, w, hv⟩ := haxis t ht
    have hvSym := transverse_symmetries_of_cylindrical_representation hv
    have hMdiag := eq_diagonal_of_hasFDerivAt_axis hfM hvSym.1 hvSym.2.1 hvSym.2.2
    have htransverse : M 0 0 = M 1 1 := by
      simpa using (congrArg (fun N : Matrix (Fin 3) (Fin 3) ℝ => N 1 1) hMdiag).symm
    have htime : HasDerivWithinAt A (M * A t) (Ico 0 T) t :=
      hasDerivWithinAt_euclideanMatrix_of_operator_ode
        (hasDerivWithinAt_fderiv_flow_Ico hu hdiff hD hbound hcont hode hinit _ ht)
    simpa only [(hasDerivAt_axial_coordinate hfM).deriv] using
      hasDerivWithinAt_det_fderiv_meridional_of_matrix_ode ht hfd htime (hdiag t ht)
        htransverse ((trace_euclideanMatrix _).trans (hdiv t ht _))

omit hcont hode hinit in
/-- Construct the flow and its physical axis clocks directly from cylindrical velocity data. -/
theorem exists_flow_axis_clock_Ico (hT : 0 < T) :
    ∃ Φ : ℝ → E₃ → E₃,
      (∀ x, Φ 0 x = x) ∧ (∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T)) ∧
      (∀ x, ∀ t ∈ Ico 0 T,
        HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t) ∧
      (∀ t ∈ Ico 0 T, ContDiff ℝ 1 (Φ t) ∧ Function.Injective (Φ t) ∧
        ∀ s : Set E₃, MeasurableSet s → MeasureTheory.volume (Φ t '' s) = MeasureTheory.volume s) ∧
      ∀ z : ℝ,
        let J : ℝ → ℝ := fun t =>
          (fderiv ℝ (fun p : E₂ =>
            (!₂[Φ t !₂[p 0, 0, p 1] 0, Φ t !₂[p 0, 0, p 1] 2] : E₂)) !₂[0, z]).toLinearMap.det
        J 0 = 1 ∧ ∀ t ∈ Ico 0 T,
          Φ t !₂[0, 0, z] = !₂[0, 0, Φ t !₂[0, 0, z] 2] ∧
          0 < J t ∧
          euclideanMatrix (fderiv ℝ (Φ t) !₂[0, 0, z]) =
            Matrix.diagonal ![(J t)⁻¹, (J t)⁻¹, (J t)^2] ∧
          Tendsto (fun r : ℝ =>
            (fderiv ℝ (fun p : E₂ =>
              (!₂[Real.sqrt ((Φ t !₂[p 0, 0, p 1] 0)^2 + (Φ t !₂[p 0, 0, p 1] 1)^2),
                Φ t !₂[p 0, 0, p 1] 2] : E₂)) !₂[r, z]).toLinearMap.det)
            (𝓝[>] 0) (𝓝 (J t)) ∧
          HasDerivWithinAt J
            ((1 / 2 : ℝ) * J t *
              deriv (fun ζ : ℝ => u t !₂[0, 0, ζ] 2) (Φ t !₂[0, 0, z] 2)) (Ico 0 T) t := by
  obtain ⟨Φ, hi, hc, ho, hr⟩ := exists_flow_volume_image_eq_Ico hT hu hdiff hD hbound hdiv
  exact ⟨Φ, hi, hc, ho, fun t ht => ⟨(hr t ht).1, (hr t ht).2.1, (hr t ht).2.2.2⟩,
    axis_clock_of_cylindrical_velocity hu hdiff hD hbound haxis hc ho hi hdiv hT⟩

end ClockBarrier.Dynamics
