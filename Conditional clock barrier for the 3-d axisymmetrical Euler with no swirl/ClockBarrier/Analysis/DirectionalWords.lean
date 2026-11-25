/-
Released under Apache 2.0 license.
Adapted from NavierStokesAndEuler, commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd.
See licenses/NavierStokesAndEuler-Apache-2.0.txt.
Modifications: focused imports, namespaces, module interface and pinned Mathlib compatibility.
-/
module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Tactic.Ring

/-! # Actual ordered directional derivatives

Selective port of ParameterWordGevrey, ParameterWordCalculus and ParameterWordHigher.
-/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis.DirectionalWords
open ContinuousLinearMap Finset
open scoped ContDiff
variable {P E F ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [Fintype ι]
/-- The actual mixed differential evaluated on an ordered word of directions. -/
def wordDerivative (directions : ι → P) (f : P → E) {n : ℕ} (w : Fin n → ι) (x : P) : E :=
  iteratedFDeriv ℝ n f x (fun j => directions (w j))

/-- The sum of the actual norms over all ordered words. -/
def wordSum (directions : ι → P) (f : P → E) (n : ℕ) (x : P) : ℝ :=
  ∑ w : Fin n → ι, ‖wordDerivative directions f w x‖

omit [Fintype ι] in
/-- Unit directions do not enlarge the norm of the actual differential. -/
theorem wordDerivative_norm (directions : ι → P) (hd : ∀ i, ‖directions i‖ ≤ 1)
    (f : P → E) {n : ℕ} (w : Fin n → ι) (x : P) :
    ‖wordDerivative directions f w x‖ ≤ ‖iteratedFDeriv ℝ n f x‖ := by
  have hp : (∏ j : Fin n, ‖directions (w j)‖) ≤ 1 :=
    prod_le_one (fun _ _ => norm_nonneg _) (fun j _ => hd (w j))
  exact ((iteratedFDeriv ℝ n f x).le_opNorm (fun j => directions (w j))).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (norm_nonneg _))

/-- Summing the actual word norms costs precisely the number of words. -/
theorem wordSum_le (directions : ι → P) (hd : ∀ i, ‖directions i‖ ≤ 1)
    (f : P → E) (n : ℕ) (x : P) :
    wordSum directions f n x ≤ (Fintype.card ι : ℝ)^n * ‖iteratedFDeriv ℝ n f x‖ := by
  have h := sum_le_sum (fun (w : Fin n → ι) (_ : w ∈ univ) => wordDerivative_norm directions hd f w x)
  simpa only [wordSum, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow] using h


section
omit [Fintype ι]
/-- A genuine derivative in one prescribed constant direction. -/
def directional (directions : ι → P) (f : P → E) (i : ι) : P → E :=
  fun x => fderiv ℝ f x (directions i)

theorem directional_contDiff (directions : ι → P) (f : P → E) (hf : ContDiff ℝ ∞ f) (i : ι) :
    ContDiff ℝ ∞ (directional directions f i) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem wordDerivative_zero (directions : ι → P) (f : P → E)
    (w : Fin 0 → ι) (x : P) : wordDerivative directions f w x = f x :=
  iteratedFDeriv_zero_apply _

/-- Every bounded linear map commutes with the actual ordered spatial derivative. -/
theorem wordDerivative_comp_clm (directions : ι → P) (L : E →L[ℝ] F)
    (f : P → E) (hf : ContDiff ℝ ∞ f) {n : ℕ} (w : Fin n → ι) (x : P) :
    wordDerivative directions (L ∘ f) w x = L (wordDerivative directions f w x) :=
  congrArg (fun D : P [×n]→L[ℝ] F => D (fun j => directions (w j)))
    (L.iteratedFDeriv_comp_left (x := x) hf.contDiffAt (WithTop.coe_le_coe.mpr le_top))

theorem wordDerivative_add (directions : ι → P) (f g : P → E)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {n : ℕ} (w : Fin n → ι) (x : P) :
    wordDerivative directions (f+g) w x =
      wordDerivative directions f w x+wordDerivative directions g w x :=
  congrArg (fun D : P [×n]→L[ℝ] E => D (fun j => directions (w j)))
    (iteratedFDeriv_add_apply (x := x) (hf.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) (hg.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)))

theorem wordDerivative_sub (directions : ι → P) (f g : P → E)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {n : ℕ} (w : Fin n → ι) (x : P) :
    wordDerivative directions (f-g) w x =
      wordDerivative directions f w x-wordDerivative directions g w x :=
  congrArg (fun D : P [×n]→L[ℝ] E => D (fun j => directions (w j)))
    (iteratedFDeriv_sub_apply (x := x) (hf.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) (hg.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)))

/-- Removing the last word letter differentiates the function in that direction first. -/
theorem wordDerivative_snoc (directions : ι → P) (f : P → E) (hf : ContDiff ℝ ∞ f)
    {n : ℕ} (w : Fin n → ι) (i : ι) (x : P) :
    wordDerivative directions f (Fin.snoc w i) x =
      wordDerivative directions (directional directions f i) w x := by
  change iteratedFDeriv ℝ (n+1) f x (directions ∘ Fin.snoc w i) = _
  rw [Fin.comp_snoc, iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]
  exact (wordDerivative_comp_clm directions (ContinuousLinearMap.apply ℝ E (directions i))
    (fderiv ℝ f) (hf.fderiv_right (m := ∞) (by simp)) w x).symm

end

theorem wordSum_zero (directions : ι → P) (f : P → E) (x : P) :
    wordSum directions f 0 x = ‖f x‖ := by
  simp only [wordSum, wordDerivative_zero, sum_const, card_univ, Fintype.card_fun,
    Fintype.card_fin, pow_zero, one_smul]

theorem wordSum_nonneg (directions : ι → P) (f : P → E) (n : ℕ) (x : P) :
    0 ≤ wordSum directions f n x := sum_nonneg (fun _ _ => norm_nonneg _)

/-- The genuine word sum decomposes as the sum of its first directional derivatives. -/
theorem wordSum_succ (directions : ι → P) (f : P → E) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (x : P) :
    wordSum directions f (n+1) x = ∑ i, wordSum directions (directional directions f i) n x := by
  calc
    _ = ∑ z : ι × (Fin n → ι), ‖wordDerivative directions (directional directions f z.1) z.2 x‖ :=
      Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n+1) => ι)).symm
        (fun w => ‖wordDerivative directions f w x‖)
        (fun z => ‖wordDerivative directions (directional directions f z.1) z.2 x‖)
        (fun w => by
          change ‖wordDerivative directions f w x‖ =
            ‖wordDerivative directions (directional directions f (w (Fin.last n))) (Fin.init w) x‖
          have h := wordDerivative_snoc directions f hf (Fin.init w) (w (Fin.last n)) x
          simpa only [Fin.snoc_init_self] using congrArg norm h)
    _ = _ := Fintype.sum_prod_type _

/-- A fixed bounded map preserves the radius and factorial shift in the actual word sum. -/
theorem wordSum_comp_clm_le (directions : ι → P) (L : E →L[ℝ] F)
    (f : P → E) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : P) :
    wordSum directions (L ∘ f) n x ≤ ‖L‖*wordSum directions f n x := by
  unfold wordSum
  rw [mul_sum]
  apply sum_le_sum
  intro w _
  rw [wordDerivative_comp_clm directions L f hf w x]
  exact L.le_opNorm _

theorem wordSum_add_le (directions : ι → P) (f g : P → E)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (n : ℕ) (x : P) :
    wordSum directions (f+g) n x ≤ wordSum directions f n x+wordSum directions g n x := by
  unfold wordSum
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro w _
  rw [wordDerivative_add directions f g hf hg w x]
  exact norm_add_le _ _

theorem wordSum_sub_le (directions : ι → P) (f g : P → E)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (n : ℕ) (x : P) :
    wordSum directions (f-g) n x ≤ wordSum directions f n x+wordSum directions g n x := by
  unfold wordSum
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro w _
  rw [wordDerivative_sub directions f g hf hg w x]
  exact norm_sub_le _ _

/-- Subtracting a frozen coefficient has no positive-order derivative. -/
theorem wordSum_sub_const_succ (directions : ι → P) (f : P → E)
    (hf : ContDiff ℝ ∞ f) (c : E) (n : ℕ) (x : P) :
    wordSum directions (f-fun _ => c) (n+1) x = wordSum directions f (n+1) x := by
  unfold wordSum wordDerivative
  rw [iteratedFDeriv_sub_apply (hf.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) contDiffAt_const]
  simp only [iteratedFDeriv_succ_const, Pi.zero_apply, sub_zero]

omit [Fintype ι] in
theorem wordDerivative_contDiff (directions : ι → P) (f : P → E)
    (hf : ContDiff ℝ ∞ f) {n : ℕ} (w : Fin n → ι) :
    ContDiff ℝ ∞ (wordDerivative directions f w) := by
  induction n generalizing f with
  | zero =>
    have he : wordDerivative directions f w = f := funext (wordDerivative_zero directions f w)
    rwa [he]
  | succ n ih =>
    have he : wordDerivative directions f w =
        wordDerivative directions (directional directions f (w (Fin.last n))) (Fin.init w) := by
      funext x
      simpa only [Fin.snoc_init_self] using
        wordDerivative_snoc directions f hf (Fin.init w) (w (Fin.last n)) x
    rw [he]
    exact ih _ (directional_contDiff directions f hf (w (Fin.last n))) (Fin.init w)

/-- The sum over all words can be decomposed for any scalar expression on words. -/
theorem sum_words_snoc (n : ℕ) (a : (Fin (n+1) → ι) → ℝ) :
    (∑ w, a w) = ∑ i, ∑ w : Fin n → ι, a (Fin.snoc w i) := by
  calc
    _ = ∑ z : ι × (Fin n → ι), a (Fin.snoc z.2 z.1) :=
      ((Fin.snocEquiv (fun _ : Fin (n+1) => ι)).sum_comp a).symm
    _ = _ := Fintype.sum_prod_type _

end ClockBarrier.Analysis.DirectionalWords
