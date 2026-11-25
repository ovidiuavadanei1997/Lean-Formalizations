/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.GeneralCoherent
import ClockBarrier.Analysis.StrainComponents
import ClockBarrier.Analysis.DirectionalFarTranslation
import ClockBarrier.Analysis.RadialFarCutoff
import ClockBarrier.Analysis.DirectionalCancellation
import ClockBarrier.Analysis.DirectionalStrainKernel
import ClockBarrier.Analysis.DirectionalNewtonianLimit
import ClockBarrier.Analysis.DirectionalNewtonianScaling
import ClockBarrier.Euler.DirectionalLagrangian
import ClockBarrier.Euler.DirectionalSmoothFar
import ClockBarrier.Euler.DirectionalNearBound
import ClockBarrier.Euler.GeneralDini
import ClockBarrier.Euler.GeneralOffClock
import ClockBarrier.Euler.GeneralLongitudinal
import ClockBarrier.Euler.GeneralTransverseBlock
import ClockBarrier.Analysis.GeneralClockSeries
import ClockBarrier.Euler.GeneralSignedInitial
import ClockBarrier.Analysis.DirectionalAssembly

/-! # General driver assembly

The literal coherence budgets control the signed Lagrangian near term. Separate
cone and off-cone sums share one transverse constant; the complete smooth far
term is absorbed into a positive integrable envelope. Trajectory uniqueness
makes the same constants work for every initialized Euler flow.
-/

public section
namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped Topology NNReal ENNReal InnerProductSpace BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Uniform driver control from the general coherence class. -/
theorem general_coherent_on.exists_uniform_general_driver_bound :
  ∀ {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃},
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
            |⟪e, S e⟫_ℝ| ≤ B t + C * ν ^ ((3 * (α : ℝ) - 1) / 2) :=
by
  intro α T u hα hcoh
  rcases hcoh with ⟨p, h, haxis, Φ, hinit, hcont, hode, V, hVmeas, hframe,
    L, ℓ, c₁, c₂, M, Tail, K, b, BF, BP, BR, hBF, hBP, hBR, hnonneg,
    hnear, hDini, hcusp, hb, htail, hlong, hoff, hdist⟩
  obtain ⟨χ, hχ, hzero, hχ₀, hχ₁, _, houter, hradial⟩ := Analysis.exists_radial_far_cutoff
  obtain ⟨Cfar, hCfar, hfar⟩ := exists_directional_smooth_far_initial_energy_bound
    hχ hzero hχ₀ hχ₁ houter
  let w := fun j : ℤ × ℤ =>
    (Real.sqrt (((2 : ℝ) ^ j.1) ^ 2 + ((2 : ℝ) ^ j.2) ^ 2)) ^ (α : ℝ) *
      (2 : ℝ) ^ j.1 * (2 : ℝ) ^ j.2 /
    (Real.sqrt (1 + ((2 : ℝ) ^ j.1) ^ 2 + ((2 : ℝ) ^ j.2) ^ 2)) ^ 3
  let N : ℝ := 3 / (4 * Real.pi)
  let C0 := 2 * (M.val / c₁.val ^ 3) * K.val ^ (((α : ℝ) + 1) / 2) *
    (∑' j, w j) * Tail.val
  let F0 := Cfar * L.val ^ (-(5 : ℝ) / 2) * Real.sqrt (∫ x : E₃, ‖u 0 x‖ ^ 2)
  let B := fun t => 1 + N * (BF t + BP t + BR t) + F0
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hw₀ (j : ℤ × ℤ) : 0 ≤ w j := by dsimp only [w]; positivity
  have hC0 : 0 ≤ C0 := mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (div_nonneg M.property.le (pow_nonneg c₁.property.le 3)))
        (Real.rpow_nonneg K.property.le _)) (tsum_nonneg hw₀)) Tail.property.le
  have hF0 : 0 ≤ F0 := mul_nonneg
    (mul_nonneg hCfar (Real.rpow_nonneg L.property.le _)) (Real.sqrt_nonneg _)
  have hfinite : volume (Ico (0 : ℝ) T) ≠ ⊤ :=
    ((measure_mono Ico_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top).ne
  refine ⟨B, 1 + N * C0, ?_, ?_, by positivity, ?_⟩
  · exact ((integrableOn_const hfinite).add
      (((hBF.add hBP).add hBR).const_mul N)).add (integrableOn_const hfinite)
  · intro t ht
    have hn := hnonneg t ht
    have hn' := mul_nonneg hN (add_nonneg (add_nonneg hn.1 hn.2.1) hn.2.2)
    dsimp only [B]
    linarith only [hn', hF0]
  · intro Ψ hΨinit hΨcont hΨode a t ht
    obtain ⟨_, hdiff, _, hbound, _⟩ := h.velocity_regular
    have hEq : Ψ t = Φ t := funext fun x =>
      Dynamics.eqOn_trajectories_Ico_of_fderiv_bound hdiff hbound
        (hΨcont x) (hΨode x) (hcont x) (hode x) ((hΨinit x).trans (hinit x).symm) ht
    rw [hEq]
    intro F ν D S e he _
    obtain ⟨U, hU⟩ := hframe t ht a
    have hn := hnonneg t ht
    have hν : 0 < ν := h.singularValues_fderiv_flow_pos hcont hode hinit ht a 2
    have hpow : 0 ≤ ν ^ ((3 * (α : ℝ) - 1) / 2) := Real.rpow_nonneg hν.le _
    have hinc := h.directional_initial_increment_bound hcont hode hinit ht a U (V t a)
      L.val ℓ.val c₁.property M.property.le Tail.property.le K.property (b t a)
      (hb t ht a) hn.2.1 hn.2.2 hχ.continuous hχ₀ hχ₁ e he hU (fun x hx => (hnear t ht a x hx).1)
      (hcusp t ht a) ((le_iSup_of_le a le_rfl).trans (htail t ht)) (hdist t ht a)
      ((le_iSup_of_le a le_rfl).trans (hlong t ht))
      ((le_iSup_of_le a le_rfl).trans (hoff t ht))
    let FF := fderiv ℝ (Φ t)
    let w₀ := vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩)
    let d := fun x => Φ t x - Φ t a
    let z := fun x => (FF x - FF a) (w₀ x)
    let v := fun x => w₀ x - w₀ a
    let η := fun x => 1 - χ (L.val⁻¹ • d x)
    let s := {x : E₃ | ‖d x‖ ≤ L.val}
    have hdini := h.integrableOn_deformation_of_dini hcont hode hinit ht a (V t a)
      L.val hn.1 ((le_iSup_of_le a le_rfl).trans (hDini t ht))
    have hD : (∫⁻ x in s, ENNReal.ofReal (‖z x‖ / ‖d x‖ ^ 3)) ≤ ENNReal.ofReal (BF t) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hdini.1
        (Filter.Eventually.of_forall (fun x =>
          div_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) 3)))]
      exact ENNReal.ofReal_le_ofReal hdini.2
    have hreg := (h.contDiff_bijective_measurePreserving_flow hcont hode hinit ht).1
    have hd : Continuous d := hreg.continuous.sub continuous_const
    have hFF : Continuous FF := hreg.continuous_fderiv (by decide)
    have hw₀ : Continuous w₀ := h.continuous_vorticity 0 ⟨le_rfl, h.1⟩
    have hz : Measurable z := ((hFF.sub continuous_const).clm_apply hw₀).measurable
    have hη : Measurable η :=
      (continuous_const.sub (hχ.continuous.comp (hd.const_smul (L.val⁻¹)))).measurable
    have hII := Analysis.integrableOn_directional_cutoff_apply_of_budget
      (A := ContinuousLinearMap.id ℝ E₃) hd.measurable hz hη
      (fun x => sub_nonneg.mpr (hχ₁ _)) (fun x => sub_le_self _ (hχ₀ _))
      (by norm_num : (0 : ℝ) ≤ 1) ContinuousLinearMap.norm_id_le hn.1 e he
      (by simpa only [one_mul] using hD)
    obtain ⟨_, _, hrep⟩ := h.strain_eq_lagrangian_near_add_far hcont hode hinit t ht
      hχ hzero hχ₀ hχ₁ houter hradial L.property a e he
    have hfarBound := (hfar h t ht (Φ t a) e he L.property).2
    let ker := fun (x v : E₃) => ⟪e, x⟫_ℝ *
      ⟪e, (!₂[x 1 * v 2 - x 2 * v 1, x 2 * v 0 - x 0 * v 2,
        x 0 * v 1 - x 1 * v 0] : E₃)⟫_ℝ / ‖x‖ ^ 5
    let f := fun x => η x * ker (d x) (z x + F (v x))
    let ω := vorticity (u t) (h.cartesian_partials t ht)
    let g := fun x => χ (L.val⁻¹ • (x - Φ t a)) * ker (x - Φ t a) (ω x)
    let fII := fun x => η x * ker (d x) (z x)
    let fI := fun x => η x * ker (d x) (F (v x))
    change IntegrableOn fII s volume ∧ (∫ x in s, |fII x|) ≤ BF t at hII
    change IntegrableOn fI s volume ∧ (∫ x in s, |fI x|) ≤
      BP t + BR t + C0 * ν ^ ((3 * (α : ℝ) - 1) / 2) at hinc
    have hsplit : f = fun x => fII x + fI x := by
      funext x
      exact (congrArg (η x * ·)
        (Analysis.directional_strain_kernel_add e (d x) (z x) (F (v x)))).trans (mul_add _ _ _)
    have hsum := Analysis.integral_abs_add_le_of_bounds hII.1 hinc.1 hII.2 hinc.2
    change ⟪e, S e⟫_ℝ = N * ((∫ x in s, f x) + ∫ x, g x) at hrep
    change |N * ∫ x, g x| ≤ F0 at hfarBound
    have hnearBound : |∫ x in s, f x| ≤
        BF t + (BP t + BR t + C0 * ν ^ ((3 * (α : ℝ) - 1) / 2)) :=
      abs_integral_le_integral_abs.trans (by simpa only [hsplit] using hsum.2)
    calc
      |⟪e, S e⟫_ℝ| = |N * (∫ x in s, f x) + N * ∫ x, g x| := by rw [hrep, mul_add]
      _ ≤ |N * ∫ x in s, f x| + |N * ∫ x, g x| := abs_add_le _ _
      _ ≤ N * (BF t + (BP t + BR t + C0 * ν ^ ((3 * (α : ℝ) - 1) / 2))) + F0 := by
        apply add_le_add _ hfarBound
        rw [abs_mul, abs_of_nonneg hN]
        exact mul_le_mul_of_nonneg_left hnearBound hN
      _ ≤ B t + (1 + N * C0) * ν ^ ((3 * (α : ℝ) - 1) / 2) := by
        dsimp only [B]
        nlinarith only [hpow]

end ClockBarrier.Euler
