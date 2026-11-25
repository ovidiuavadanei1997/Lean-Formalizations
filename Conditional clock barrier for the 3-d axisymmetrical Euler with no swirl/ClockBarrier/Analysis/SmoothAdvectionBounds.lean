/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd.
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: focused spatial estimates and direct coordinate Sobolev gradient bound.
-/
module
public import ClockBarrier.Analysis.SmoothH3Commutator
public import ClockBarrier.Analysis.SmoothWordTime

/-! # L² continuity of the actual advection and uniform gradient bounds -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.Sobolev
open MeasureTheory ContinuousLinearMap SmoothL2Field SmoothSobolev Finset DirectionalWords
open scoped ContDiff
local notation "Space" => EuclideanSpace ℝ (Fin 3)
theorem advection_norm_gradient (W U : SmoothL2Field Space) (K : ℝ)
    (hK : ∀ x, ‖fderiv ℝ U.field x‖ ≤ K) :
    ‖(advectionField W U).toLp‖ ≤ K*‖W.toLp‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(advectionField W U).toLp_ae,W.toLp_ae] with x ha hw
  rw [ha,hw,advectionField_field]
  exact ((fderiv ℝ U.field x).le_opNorm (W.field x)).trans
    (mul_le_mul_of_nonneg_right (hK x) (norm_nonneg _))

theorem jetLp_fieldSub {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A B : SmoothL2Field V) (n : ℕ) :
    (fieldSub A B).jetLp n=A.jetLp n-B.jetLp n := by
  have he : (fieldSub A B).field=A.field-B.field := funext (fieldSub_field A B)
  apply Lp.ext
  filter_upwards [(fieldSub A B).jetLp_ae n,A.jetLp_ae n,B.jetLp_ae n,
    Lp.coeFn_sub (A.jetLp n) (B.jetLp n)] with x ha hb hc hd
  rw [ha,he]
  have hh := iteratedFDeriv_sub_apply (i := n) (x := x)
    (A.smooth.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) (B.smooth.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
  exact hh.trans ((congrArg₂ (fun u v : Space [×n]→L[ℝ] V => u-v) hb hc).symm.trans hd.symm)

theorem advection_difference (A B : SmoothL2Field Space) :
    fieldSub (advectionField A A) (advectionField B B)=
      addField (advectionField (fieldSub A B) A) (advectionField B (fieldSub A B)) := by
  apply field_ext
  funext x
  have he : (fieldSub A B).field=A.field-B.field := funext (fieldSub_field A B)
  simp only [fieldSub_field,addField_field,advectionField_field]
  rw [he,fderiv_sub (A.smooth.differentiable (by simp) x) (B.smooth.differentiable (by simp) x)]
  simp only [map_sub,sub_apply]
  abel

theorem advection_norm_velocity (U W : SmoothL2Field Space) (K : ℝ)
    (hK : ∀ x, ‖U.field x‖ ≤ K) :
    ‖(advectionField U W).toLp‖ ≤ K*‖W.derivative.toLp‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(advectionField U W).toLp_ae,W.derivative.toLp_ae] with x ha hw
  rw [ha,hw,advectionField_field]
  exact ((fderiv ℝ W.field x).le_opNorm (U.field x)).trans
    ((mul_le_mul_of_nonneg_left (hK x) (norm_nonneg _)).trans_eq (mul_comm _ _))

theorem advection_sub_norm (A B : SmoothL2Field Space) (G K : ℝ)
    (hG : ∀ x, ‖fderiv ℝ A.field x‖ ≤ G) (hK : ∀ x, ‖B.field x‖ ≤ K) :
    ‖(advectionField A A).toLp-(advectionField B B).toLp‖ ≤
      G*‖A.toLp-B.toLp‖+K*‖A.jetLp 1-B.jetLp 1‖ := by
  rw [← toLp_fieldSub,advection_difference,toLp_addField]
  apply (norm_add_le _ _).trans
  have h := add_le_add (advection_norm_gradient (fieldSub A B) A G hG)
    (advection_norm_velocity B (fieldSub A B) K hK)
  simpa only [toLp_fieldSub,← norm_jetLp_zero (fieldSub A B).derivative,
    norm_derivative_jetLp,jetLp_fieldSub] using h


theorem wordBound_gradient {A : SmoothL2Field Space} {M : ℝ} (hM : WordBound 3 M A)
    (x : Space) : ‖fderiv ℝ A.field x‖ ≤ (39*smoothEmbeddingConstant)*M := by
  rw [← norm_iteratedFDeriv_one]
  apply (multilinear_norm_le_coordinate_sum 3 1 (iteratedFDeriv ℝ 1 A.field x)).trans
  calc
    _ ≤ ∑ _w : Fin 1 → Fin 3, (13*smoothEmbeddingConstant)*M := by
      apply sum_le_sum
      intro w _
      have h := wordBound_pointwise (wordBound_wordField (s := 2) (k := 1) hM w) x
      simpa only [wordField_field, wordDerivative, axis] using h
    _ = _ := by simp; ring

end ClockBarrier.Analysis.Sobolev
