/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd,
Euler/MeanPressurePotential.lean, CanonicalGraphPotential.lean and EulerProof.lean.
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: ordinary Euclidean carrier, focused imports and module interface.
-/
module
public import ClockBarrier.Analysis.SmoothWeakCurl
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # An actual normalized scalar pressure potential -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.SmoothPressure
open MeasureTheory Set InnerProductSpace Solenoidal
open scoped ContDiff
local notation "Space" => EuclideanSpace ℝ (Fin 3)

theorem smooth_gradient_potential (v : Space → Space) (hv : ContDiff ℝ ∞ v)
    (hsymm : ∀ x a b, ⟪fderiv ℝ v x a, b⟫_ℝ = ⟪fderiv ℝ v x b, a⟫_ℝ) :
    ∃ p : Space → ℝ, ContDiff ℝ ∞ p ∧ ∀ x, gradient p x = v x := by
  let form : Space → Space →L[ℝ] ℝ := fun x => toDual ℝ Space (v x)
  have hω : ContDiff ℝ ∞ form := (toDual ℝ Space).toContinuousLinearEquiv.contDiff.comp hv
  have hωd (x : Space) : HasFDerivAt form
      ((toDual ℝ Space).toContinuousLinearEquiv.toContinuousLinearMap.comp (fderiv ℝ v x)) x :=
    (toDual ℝ Space).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x
      ((hv.differentiable (by simp)) x).hasFDerivAt
  obtain ⟨p, hp⟩ := (convex_univ : Convex ℝ (univ : Set Space)).exists_forall_hasFDerivAt_of_fderiv_symmetric
    isOpen_univ (hω.differentiable (by simp)).differentiableOn (fun x _ a b => by
      rw [(hωd x).fderiv]
      change ⟪fderiv ℝ v x a, b⟫_ℝ = ⟪fderiv ℝ v x b, a⟫_ℝ
      exact hsymm x a b)
  have hp' (x : Space) : HasFDerivAt p (form x) x := hp x (mem_univ _)
  have hpd : Differentiable ℝ p := fun x => (hp' x).differentiableAt
  have hpf : fderiv ℝ p = form := funext (fun x => (hp' x).fderiv)
  refine ⟨p, ?_, ?_⟩
  · rw [contDiff_infty_iff_fderiv]
    exact ⟨hpd, by rwa [hpf]⟩
  · intro x
    rw [gradient, (hp' x).fderiv]
    exact (toDual ℝ Space).symm_apply_apply (v x)

/-- The scalar radial integral of a spatial vector field, based at the origin. -/
def radialPotential (V : Space → Space) (x : Space) : ℝ :=
  ∫ s in (0 : ℝ)..1, ⟪V (s • x), x⟫_ℝ

/-- The radial integral is normalized to vanish at the origin. -/
theorem radialPotential_zero (V : Space → Space) : radialPotential V 0 = 0 := by
  simp [radialPotential]

/-- The fundamental theorem of calculus identifies the radial integral with a normalized genuine potential. -/
theorem radialPotential_eq_sub (V : Space → Space) (hV : Continuous V)
    (q : Space → ℝ) (hq : ContDiff ℝ ∞ q) (hgrad : ∀ x, gradient q x = V x)
    (x : Space) : radialPotential V x = q x - q 0 := by
  have hd (s : ℝ) : HasDerivAt (fun r : ℝ => q (r • x)) ⟪V (s • x), x⟫_ℝ s := by
    have h := ((hq.differentiable (by simp)) (s • x)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).smul_const x)
    simpa only [Function.comp_def, id_eq, one_smul, ← inner_gradient_left, hgrad] using h
  have hi : IntervalIntegrable (fun s : ℝ => ⟪V (s • x), x⟫_ℝ) volume 0 1 :=
    ((hV.comp (continuous_id.smul continuous_const)).inner continuous_const).intervalIntegrable 0 1
  simpa only [radialPotential, one_smul, zero_smul] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi

/-- A radial reconstruction of a genuine smooth gradient is itself spatially smooth. -/
theorem radialPotential_smooth (V : Space → Space) (hV : Continuous V)
    (q : Space → ℝ) (hq : ContDiff ℝ ∞ q) (hgrad : ∀ x, gradient q x = V x) :
    ContDiff ℝ ∞ (radialPotential V) := by
  have he : radialPotential V = fun x => q x - q 0 :=
    funext (radialPotential_eq_sub V hV q hq hgrad)
  rw [he]
  exact hq.sub contDiff_const

/-- Radial normalization preserves the actual gradient. -/
theorem radialPotential_gradient (V : Space → Space) (hV : Continuous V)
    (q : Space → ℝ) (hq : ContDiff ℝ ∞ q) (hgrad : ∀ x, gradient q x = V x)
    (x : Space) : gradient (radialPotential V) x = V x := by
  have he : radialPotential V = fun x => q x - q 0 :=
    funext (radialPotential_eq_sub V hV q hq hgrad)
  rw [he, gradient, fderiv_sub_const]
  exact hgrad x

/-- A jointly continuous vector field has a jointly continuous radial scalar potential. -/
theorem radialPotential_joint_continuous {T : Type*} [TopologicalSpace T]
    [FirstCountableTopology T] [LocallyCompactSpace T]
    (V : T → Space → Space) (hV : Continuous V.uncurry) :
    Continuous (fun p : T × Space => radialPotential (V p.1) p.2) := by
  have hc : Continuous (fun p : (T × Space) × ℝ =>
      ⟪V p.1.1 (p.2 • p.1.2), p.1.2⟫_ℝ) := by
    exact (hV.comp ((continuous_fst.fst).prodMk
      (continuous_snd.smul continuous_fst.snd))).inner continuous_fst.snd
  have hi := continuous_parametric_integral_of_continuous
    (μ := volume)
    (f := fun p : T × Space => fun s : ℝ => ⟪V p.1 (s • p.2), p.2⟫_ℝ)
    hc (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  simpa only [radialPotential, intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc] using hi

theorem symmetry_of_coordinates (L : Space →L[ℝ] Space)
    (hL : ∀ i j, (L (EuclideanSpace.single i 1)) j = (L (EuclideanSpace.single j 1)) i)
    (a b : Space) : ⟪L a, b⟫_ℝ = ⟪L b, a⟫_ℝ := by
  let B : LinearMap.BilinForm ℝ Space := (innerₗ Space).comp L.toLinearMap
  have hB : LinearMap.BilinForm.IsSymm B :=
    (LinearMap.BilinForm.isSymm_iff_basis (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis).2 (fun i j => by
      change ⟪L ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis i),
          (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis j⟫_ℝ =
        ⟪L ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis j),
          (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis i⟫_ℝ
      simpa only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
        EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul] using hL i j)
  exact hB.eq a b

/-- Smooth representatives of the actual closed gradient space have a genuine scalar potential. -/
theorem gradientSpace_has_potential (p : L2) (hp : p ∈ gradientSpace)
    (g : Space → Space) (hrep : p =ᵐ[volume] g) (hg : ContDiff ℝ ∞ g) :
    ∃ q : Space → ℝ, ContDiff ℝ ∞ q ∧ ∀ x, gradient q x = g x := by
  apply smooth_gradient_potential g hg
  intro x a b
  exact symmetry_of_coordinates (fderiv ℝ g x)
    (gradientSpace_classical_curl_zero p hp g hrep hg x) a b

/-- The concrete radial integral gives a fixed additive normalization, not just an existential pressure. -/
theorem gradientSpace_radial_potential (p : L2) (hp : p ∈ gradientSpace)
    (g : Space → Space) (hrep : p =ᵐ[volume] g) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (radialPotential g) ∧ radialPotential g 0 = 0 ∧
      ∀ x, gradient (radialPotential g) x = g x := by
  obtain ⟨q, hq, hgrad⟩ := gradientSpace_has_potential p hp g hrep hg
  exact ⟨radialPotential_smooth g hg.continuous q hq hgrad,
    radialPotential_zero g, radialPotential_gradient g hg.continuous q hq hgrad⟩

end ClockBarrier.Analysis.SmoothPressure
