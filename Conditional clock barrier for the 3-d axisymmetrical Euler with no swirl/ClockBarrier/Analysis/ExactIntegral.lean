/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Analysis.PathIntegral
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Integrating continuous families of exact derivatives

Only the derivatives must be continuous in the parameter. Subtracting the value
at a fixed reference point removes arbitrary parameter-dependent additive constants.
-/

public section

namespace ClockBarrier.Analysis

open Set MeasureTheory
open scoped Topology

/-- Joint continuity of the derivatives implies joint continuity of normalized
potential differences, even if the unnormalized potentials are not measurable in the parameter. -/
theorem continuous_normalized_of_continuous_derivative
    {S E F : Type*} [TopologicalSpace S]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : S → E → F} {D : S × E → E →L[ℝ] F}
    (hD : Continuous D) (hd : ∀ s x, HasFDerivAt (f s) (D (s, x)) x) (x₀ : E) :
    Continuous (fun q : S × E => f q.1 q.2 - f q.1 x₀) := by
  let c : S × E → C(Icc (0 : ℝ) 1, F) := fun q =>
    ⟨fun r => D (q.1, x₀ + r.val • (q.2 - x₀)) (q.2 - x₀),
      (hD.comp (continuous_const.prodMk
        (continuous_const.add (continuous_subtype_val.smul continuous_const)))).clm_apply
        continuous_const⟩
  have hc : Continuous c := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (hD.comp ((continuous_fst.fst).prodMk
      (continuous_const.add (continuous_snd.subtype_val.smul
        (continuous_fst.snd.sub continuous_const))))).clm_apply
        (continuous_fst.snd.sub continuous_const)
  let L : C(Icc (0 : ℝ) 1, F) →L[ℝ] F :=
    (ContinuousMap.evalCLM ℝ ⟨1, by simp⟩).comp (pathIntegral zero_le_one)
  apply (L.continuous.comp hc).congr
  intro q
  change (∫ r in (0 : ℝ)..1,
    D (q.1, x₀ + (projIcc 0 1 zero_le_one r).val • (q.2 - x₀)) (q.2 - x₀)) = _
  rw [intervalIntegral.integral_congr (g := fun r =>
    D (q.1, x₀ + r • (q.2 - x₀)) (q.2 - x₀))
    (fun r hr => by rw [projIcc_of_mem zero_le_one (by simpa only [uIcc_of_le zero_le_one] using hr)])]
  have hline (r : ℝ) : HasDerivAt (fun s : ℝ => x₀ + s • (q.2 - x₀)) (q.2 - x₀) r := by
    simpa only [one_smul, id_eq] using
      ((hasDerivAt_id r).smul_const (q.2 - x₀)).const_add x₀
  have hcont : Continuous (fun r : ℝ => D (q.1, x₀ + r • (q.2 - x₀)) (q.2 - x₀)) :=
    (hD.comp (continuous_const.prodMk
      (continuous_const.add (continuous_id.smul continuous_const)))).clm_apply continuous_const
  simpa only [Function.comp_def, one_smul, zero_smul, add_zero,
    ← add_sub_assoc, add_sub_cancel_left] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => (hd q.1 (x₀ + r • (q.2 - x₀))).comp_hasDerivAt r (hline r))
      (hcont.intervalIntegrable 0 1)

/-- A continuous family of genuine exact derivatives on a compact time interval
has an exact time integral. Arbitrary time-dependent additive constants in the
potentials are removed before integration. -/
theorem exists_potential_intervalIntegral
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {T : ℝ} (hT : 0 ≤ T) {f : ℝ → E → F} {D : ℝ × E → E →L[ℝ] F}
    (hD : ContinuousOn D (Icc 0 T ×ˢ univ))
    (hd : ∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (f t) (D (t, x)) x) :
    ∃ G : E → F, ∀ x, HasFDerivAt G (∫ t in 0..T, D (t, x)) x := by
  let D₀ : C(Icc 0 T × E, E →L[ℝ] F) :=
    ⟨fun q => D (q.1.val, q.2), hD.comp_continuous
      (continuous_fst.subtype_val.prodMk continuous_snd) (fun q => ⟨q.1.property, mem_univ _⟩)⟩
  let K : C(Icc 0 T × E, F) :=
    ⟨fun q => f q.1.val q.2 - f q.1.val 0,
      continuous_normalized_of_continuous_derivative D₀.continuous
        (fun t x => hd t.val t.property x) 0⟩
  have hK (t : Icc 0 T) (x : E) : HasFDerivAt (fun y => K (t, y)) (D₀ (t, x)) x :=
    (hd t.val t.property x).sub_const (f t.val 0)
  let C : E →L[ℝ] C(Icc 0 T, E) := ContinuousLinearMap.const ℝ (Icc 0 T)
  let L : C(Icc 0 T, F) →L[ℝ] F :=
    (ContinuousMap.evalCLM ℝ ⟨T, by exact ⟨hT, le_rfl⟩⟩).comp (pathIntegral hT)
  refine ⟨fun x => L (pathSuperposition K (C x)), fun x => ?_⟩
  have h := L.hasFDerivAt.comp x
    ((hasFDerivAt_pathSuperposition K D₀ hK (C x)).comp x C.hasFDerivAt)
  apply h.congr_fderiv
  ext v
  change (∫ t in 0..T, D ((projIcc 0 T hT t).val, x) v) = (∫ t in 0..T, D (t, x)) v
  have hi : IntervalIntegrable (fun t => D (t, x)) volume 0 T :=
    (hD.comp (continuousOn_id.prodMk continuousOn_const)
      (fun t ht => ⟨ht, mem_univ _⟩)).intervalIntegrable_of_Icc hT
  rw [ContinuousLinearMap.intervalIntegral_apply hi]
  exact intervalIntegral.integral_congr (fun t ht => by
    rw [projIcc_of_mem hT (by simpa only [uIcc_of_le hT] using ht)])

/-- If the time derivative of a family of covectors is spatially exact, its
endpoint difference is exact. The potentials need no time regularity. -/
theorem exists_potential_endpoint_sub
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {T : ℝ} (hT : 0 ≤ T) {f : ℝ → E → F}
    {D : ℝ × E → E →L[ℝ] F} {A : ℝ → E → E →L[ℝ] F}
    (hD : ContinuousOn D (Icc 0 T ×ˢ univ))
    (hd : ∀ t ∈ Icc 0 T, ∀ x, HasFDerivAt (f t) (D (t, x)) x)
    (hA : ∀ x, ContinuousOn (fun t => A t x) (Icc 0 T))
    (hAt : ∀ x, ∀ t ∈ Ioo 0 T, HasDerivAt (fun s => A s x) (D (t, x)) t) :
    ∃ G : E → F, ∀ x, HasFDerivAt G (A T x - A 0 x) x := by
  obtain ⟨G, hG⟩ := exists_potential_intervalIntegral hT hD hd
  refine ⟨G, fun x => ?_⟩
  exact (hG x).congr_fderiv
    (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT (hA x) (hAt x)
      ((hD.comp (continuousOn_id.prodMk continuousOn_const)
        (fun t ht => ⟨ht, mem_univ _⟩)).intervalIntegrable_of_Icc hT))

end ClockBarrier.Analysis
