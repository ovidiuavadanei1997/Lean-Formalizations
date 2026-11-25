/-
Adapted from openai/NavierStokesAndEuler, commit
f9e8bc5b38b6e212696e8a30e3e91517af887bbd, Euler/HilbertQuadraticFlow.lean.
Released under Apache 2.0 license; see licenses/NavierStokesAndEuler-Apache-2.0.txt.
Adaptations copyright (c) 2026 Ovidiu-Neculai Avadanei.
-/
module
public import ClockBarrier.Dynamics.FlowExistence
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # Norm-preserving quadratic evolution on Hilbert spaces

The radial normalization argument is adapted from the upstream source.
Trajectory existence is supplied by this project's Picard construction.
This is an ODE construction ingredient, not an Euler PDE existence theorem.
-/

@[expose] public section
namespace ClockBarrier.Dynamics.QuadraticFlow
open Set ContinuousLinearMap
open scoped Topology NNReal

section Normed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial normalization into the unit ball. -/
noncomputable def radial (x : E) : E := (1 + ‖x‖)⁻¹ • x

theorem radial_norm (x : E) : ‖radial x‖ ≤ 1 := by
  rw [radial, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (by positivity)),
    ← div_eq_inv_mul]
  exact (div_le_one (by positivity)).mpr (by linarith [norm_nonneg x])

theorem radial_sub_norm (x y : E) : ‖radial x-radial y‖ ≤ 2*‖x-y‖ := by
  have hx : 0 < 1+‖x‖ := by positivity
  have hy : 0 < 1+‖y‖ := by positivity
  have ha : 0 ≤ (1+‖x‖)⁻¹ := (inv_pos.mpr hx).le
  have ha1 : (1+‖x‖)⁻¹ ≤ 1 := (inv_le_one₀ hx).mpr (by linarith [norm_nonneg x])
  have he : (1+‖x‖)⁻¹-(1+‖y‖)⁻¹ =
      ((1+‖x‖)⁻¹*(‖y‖-‖x‖))*(1+‖y‖)⁻¹ := by
    field_simp
    ring
  have hv : radial x-radial y = (1+‖x‖)⁻¹ • (x-y)+
      ((1+‖x‖)⁻¹*(‖y‖-‖x‖)) • radial y := by
    calc
      _ = (1+‖x‖)⁻¹ • (x-y)+((1+‖x‖)⁻¹-(1+‖y‖)⁻¹) • y := by
        dsimp [radial]
        module
      _ = _ := by rw [he,radial,smul_smul]
  have hd : |‖y‖-‖x‖| ≤ ‖x-y‖ := by
    simpa only [norm_sub_rev] using abs_norm_sub_norm_le y x
  rw [hv]
  apply (norm_add_le _ _).trans
  rw [norm_smul,norm_smul,Real.norm_of_nonneg ha,norm_mul,
    Real.norm_of_nonneg ha,Real.norm_eq_abs]
  have h1 : (1+‖x‖)⁻¹*‖x-y‖ ≤ ‖x-y‖ :=
    mul_le_of_le_one_left (norm_nonneg _) ha1
  have h2 : ((1+‖x‖)⁻¹*|‖y‖-‖x‖|)*‖radial y‖ ≤ ‖x-y‖ := by
    calc
      _ ≤ ((1+‖x‖)⁻¹*‖x-y‖)*1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hd ha) (radial_norm y)
          (norm_nonneg _) (mul_nonneg ha (norm_nonneg _))
      _ ≤ _ := by simpa only [mul_one] using h1
  linarith

theorem radial_lipschitz : LipschitzWith 2 (radial : E → E) :=
  lipschitzWith_iff_norm_sub_le.mpr radial_sub_norm

noncomputable def normalized (B : E →L[ℝ] E →L[ℝ] E) (x : E) : E := B (radial x) (radial x)

theorem bilinear_bound (B : E →L[ℝ] E →L[ℝ] E) (x y : E) :
    ‖B x y‖ ≤ ‖B‖*‖x‖*‖y‖ :=
  ((B x).le_opNorm y).trans (mul_le_mul_of_nonneg_right (B.le_opNorm x) (norm_nonneg y))

theorem normalized_lipschitz (B : E →L[ℝ] E →L[ℝ] E) :
    LipschitzWith (4*‖B‖₊) (normalized B) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro x y
  have he : normalized B x-normalized B y =
      B (radial x-radial y) (radial x)+B (radial y) (radial x-radial y) := by
    simp only [normalized,map_sub,sub_apply]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  have h1 : ‖B (radial x-radial y) (radial x)‖ ≤ ‖B‖*(2*‖x-y‖) := by
    apply (bilinear_bound B _ _).trans
    exact (mul_le_mul (mul_le_mul_of_nonneg_left (radial_sub_norm x y) (norm_nonneg B))
      (radial_norm x) (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have h2 : ‖B (radial y) (radial x-radial y)‖ ≤ ‖B‖*(2*‖x-y‖) := by
    apply (bilinear_bound B _ _).trans
    exact (mul_le_mul (mul_le_mul_of_nonneg_left (radial_norm y) (norm_nonneg B))
      (radial_sub_norm x y) (norm_nonneg _) (by positivity)).trans_eq (by ring)
  exact (add_le_add h1 h2).trans_eq (by simp only [NNReal.coe_mul,NNReal.coe_ofNat,coe_nnnorm]; ring)

theorem normalized_eq (B : E →L[ℝ] E →L[ℝ] E) (x : E) :
    normalized B x=((1+‖x‖)⁻¹)^2 • B x x := by
  simp only [normalized,radial,map_smul,smul_apply,smul_smul,pow_two]

end Normed

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Every norm-preserving bounded bilinear ODE has trajectories on any prescribed
compact positive time interval. No existence hypothesis is supplied. -/
theorem exists_quadratic_solution_Icc (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x, inner ℝ x (B x x) = 0) (x : E) {T : ℝ} (hT : 0 ≤ T) :
    ∃ u : ℝ → E, u 0 = x ∧ ContinuousOn u (Icc 0 T) ∧
      (∀ t ∈ Ico 0 T, HasDerivWithinAt u (B (u t) (u t)) (Ici t) t) ∧
      ∀ t ∈ Icc 0 T, ‖u t‖ = ‖x‖ := by
  let c : ℝ := (1 + ‖x‖) ^ 2
  have hc : 0 < c := by dsimp only [c]; positivity
  obtain ⟨Φ, hinit, hcont, hode⟩ := exists_flow_Icc (mul_nonneg hc.le hT)
    (u := fun _ : ℝ => normalized B)
    ((normalized_lipschitz B).continuous.comp continuous_snd).continuousOn
    (fun _ _ => normalized_lipschitz B)
  have hd (t : ℝ) (ht : t ∈ Ico 0 (c * T)) :
      HasDerivWithinAt (fun s => ‖Φ s x‖ ^ 2) 0 (Ici t) t := by
    simpa only [normalized_eq, real_inner_smul_right, hB, mul_zero] using
      (hode x t ht).norm_sq
  have hn (t : ℝ) (ht : t ∈ Icc 0 (c * T)) : ‖Φ t x‖ = ‖x‖ := by
    have he := constant_of_has_deriv_right_zero ((hcont x).norm.pow 2) hd t ht
    simp only [Pi.pow_apply, hinit] at he
    nlinarith only [he, norm_nonneg (Φ t x), norm_nonneg x]
  have hmap : MapsTo (fun t => c * t) (Icc 0 T) (Icc 0 (c * T)) :=
    fun _ ht => ⟨mul_nonneg hc.le ht.1, mul_le_mul_of_nonneg_left ht.2 hc.le⟩
  refine ⟨fun t => Φ (c * t) x, by simpa only [mul_zero] using hinit x,
    (hcont x).comp (continuous_const.mul continuous_id).continuousOn hmap, ?_,
    fun t ht => hn _ (hmap ht)⟩
  intro t ht
  have hi : HasDerivAt (fun r : ℝ => c * r) c t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul c
  have hderiv := (hode x (c * t)
    ⟨mul_nonneg hc.le ht.1, mul_lt_mul_of_pos_left ht.2 hc⟩).scomp t
      (hi.hasDerivWithinAt (s := Ici t))
      (fun r (hr : r ∈ Ici t) => mul_le_mul_of_nonneg_left hr hc.le)
  have he : c * ((1 + ‖x‖)⁻¹) ^ 2 = 1 := by
    simpa only [c, inv_pow] using mul_inv_cancel₀ hc.ne'
  simpa only [normalized_eq, hn _ (hmap (Ico_subset_Icc_self ht)), smul_smul,
    he, one_smul, Function.comp_def] using hderiv

end Hilbert

end ClockBarrier.Dynamics.QuadraticFlow
