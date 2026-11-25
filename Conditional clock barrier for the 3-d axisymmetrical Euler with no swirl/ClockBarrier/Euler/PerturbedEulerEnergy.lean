/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd.
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: direct projected L² equation, without an auxiliary pressure representative.
-/
module
public import ClockBarrier.Euler.RegularizationError
public import ClockBarrier.Analysis.SmoothEnergyControl

/-! # L² stability of the projected Euler equation with an additive defect -/
@[expose] public noncomputable section
namespace ClockBarrier.Euler.Regularized
open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap ClockBarrier.Analysis
  Solenoidal SmoothL2Field Sobolev Finset
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem projected_difference_energy (A B : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) (hB : B.toLp ∈ solenoidalSpace)
    (K : ℝ) (hK : ∀ x, ‖fderiv ℝ A.field x‖ ≤ K) :
    2*⟪B.toLp-A.toLp, projectedRhsL2 B-projectedRhsL2 A⟫_ℝ ≤
      2*K*‖B.toLp-A.toLp‖^2 := by
  let W := fieldSub B A
  have hw : solenoidalProjection W.toLp = W.toLp := by
    apply solenoidalSpace.starProjection_eq_self_iff.mpr
    rw [toLp_fieldSub]
    exact solenoidalSpace.sub_mem hB hA
  have he : fieldSub (advectionField B B) (advectionField A A) =
      addField (advectionField W A) (advectionField B W) := by
    apply field_ext
    funext x
    have hwf : W.field = B.field-A.field := funext (fieldSub_field B A)
    simp only [fieldSub_field, addField_field, advectionField_field, hwf, Pi.sub_apply]
    rw [fderiv_sub (B.smooth.differentiable (by simp) x) (A.smooth.differentiable (by simp) x)]
    simp only [sub_apply, map_sub]
    abel
  have hz := advection_inner_zero B W
    (solenoidal_representative_divergence B.toLp hB B.field B.smooth B.toLp_ae)
  have hz' : ⟪W.toLp, (advectionField B W).toLp⟫_ℝ = 0 := by
    exact (real_inner_comm _ _).trans hz
  have hp : ⟪B.toLp-A.toLp, projectedRhsL2 B-projectedRhsL2 A⟫_ℝ =
      -⟪W.toLp, (advectionField W A).toLp⟫_ℝ := by
    change ⟪W.toLp, -solenoidalProjection (advectionField B B).toLp -
      -solenoidalProjection (advectionField A A).toLp⟫_ℝ = _
    rw [show -solenoidalProjection (advectionField B B).toLp -
        -solenoidalProjection (advectionField A A).toLp =
        -solenoidalProjection ((fieldSub (advectionField B B) (advectionField A A)).toLp) by
          rw [toLp_fieldSub, map_sub]; abel,
      inner_neg_right, ← projection_inner, hw, he, toLp_addField, inner_add_right,
      hz', add_zero]
  rw [hp]
  have hb : |⟪W.toLp, (advectionField W A).toLp⟫_ℝ| ≤ K*‖W.toLp‖^2 := by
    exact (abs_real_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_left (advection_norm_gradient W A K hK) (norm_nonneg _)).trans_eq (by ring))
  have h := (neg_le_abs ⟪W.toLp, (advectionField W A).toLp⟫_ℝ).trans hb
  simpa only [W, toLp_fieldSub, mul_assoc] using mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)

theorem perturbed_difference_energy (A B : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) (hB : B.toLp ∈ solenoidalSpace)
    (RA RB : L2) (K ea eb : ℝ) (hK : ∀ x, ‖fderiv ℝ A.field x‖ ≤ K)
    (ha : ‖RA-projectedRhsL2 A‖ ≤ ea)
    (hb : ‖RB-projectedRhsL2 B‖ ≤ eb) :
    2*⟪B.toLp-A.toLp,RB-RA⟫_ℝ ≤ (2*K+1)*‖B.toLp-A.toLp‖^2+(ea+eb)^2 := by
  let W := B.toLp-A.toLp
  let e := (RB-projectedRhsL2 B)-(RA-projectedRhsL2 A)
  have he : RB-RA=(projectedRhsL2 B-projectedRhsL2 A)+e := by dsimp [e]; abel
  have hn : ‖e‖ ≤ ea+eb := by
    exact (norm_sub_le _ _).trans ((add_le_add hb ha).trans_eq (add_comm eb ea))
  have hpair : 2*⟪W,e⟫_ℝ ≤ ‖W‖^2+(ea+eb)^2 := by
    have hi : ⟪W,e⟫_ℝ ≤ ‖W‖*(ea+eb) :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg W))
    nlinarith [sq_nonneg (‖W‖-(ea+eb))]
  rw [he,inner_add_right,mul_add]
  exact (add_le_add (projected_difference_energy A B hA hB K hK) hpair).trans_eq (by dsimp [W]; ring)

theorem forced_linear_zero_bound (T C E : ℝ) (hC : 1 ≤ C)
    (X X' : ℝ → ℝ) (hX : ContinuousOn X (Icc 0 T)) (hX0 : X 0=0)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt X (X' t) (Icc 0 T) t)
    (hb : ∀ t ∈ Icc 0 T, X' t ≤ C*X t+E^2)
    (t : ℝ) (ht : t ∈ Icc 0 T) : X t ≤ E^2*Real.exp (C*T) := by
  have hh := linear_stability_within (fun r => X r+E^2) X' C T
    (hX.add continuousOn_const)
    (fun r hr => (hd r ⟨hr.1,hr.2.le⟩).add_const _)
    (fun r hr => (hb r ⟨hr.1,hr.2.le⟩).trans (by nlinarith [sq_nonneg E])) t ht
  rw [hX0,zero_add] at hh
  have he : E^2*Real.exp (C*t) ≤ E^2*Real.exp (C*T) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg E)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (by linarith))
  linarith [sq_nonneg E]

end ClockBarrier.Euler.Regularized
