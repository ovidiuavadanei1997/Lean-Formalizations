/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Topology.Piecewise
import Mathlib.Tactic.Linarith

/-! # Joining actual classical trajectories at a matching endpoint -/
@[expose] public noncomputable section
namespace ClockBarrier.Analysis
open Set Filter Topology

def joinTime {X : Type*} (S : ℝ) (f g : ℝ → X) (t : ℝ) : X :=
  if t ≤ S then f t else g (t-S)

theorem joinTime_left {X : Type*} (S : ℝ) (f g : ℝ → X) {t : ℝ} (ht : t ≤ S) :
    joinTime S f g t = f t := if_pos ht

theorem joinTime_right {X : Type*} (S : ℝ) (f g : ℝ → X) (he : f S = g 0)
    {t : ℝ} (ht : S ≤ t) : joinTime S f g t = g (t-S) := by
  rcases ht.eq_or_lt with h | h
  · subst t
    simp only [joinTime, le_refl, if_true, sub_self, he]
  · exact if_neg (not_le.mpr h)

theorem joinTime_comp {X Y : Type*} (H : X → Y) (S : ℝ) (f g : ℝ → X) (t : ℝ) :
    H (joinTime S f g t) = joinTime S (H ∘ f) (H ∘ g) t := by
  unfold joinTime
  split <;> rfl

theorem continuous_joinTime {X : Type*} [TopologicalSpace X] (S : ℝ) (f g : ℝ → X)
    (hf : Continuous f) (hg : Continuous g) (he : f S = g 0) : Continuous (joinTime S f g) := by
  apply hf.if _ (hg.comp (continuous_id.sub continuous_const))
  intro t ht
  have htS : t = S := by
    change t ∈ frontier (Iic S) at ht
    simpa only [frontier_Iic, mem_singleton_iff] using ht
  subst t
  simpa only [Function.comp_def, Pi.sub_apply, id_eq, sub_self] using he

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivWithinAt_joinTime (S D : ℝ)
    (f g f' g' : ℝ → E) (he : f S = g 0) (he' : f' S = g' 0)
    (hf : ∀ t ∈ Icc 0 S, HasDerivWithinAt f (f' t) (Icc 0 S) t)
    (hg : ∀ t ∈ Icc 0 D, HasDerivWithinAt g (g' t) (Icc 0 D) t)
    (t : ℝ) :
    HasDerivWithinAt (joinTime S f g) (joinTime S f' g' t) (Icc 0 (S+D)) t := by
  have hl (r : ℝ) (hr : r ∈ Icc 0 S) :
      HasDerivWithinAt (joinTime S f g) (joinTime S f' g' r) (Icc 0 S) r := by
    rw [joinTime_left S f' g' hr.2]
    exact (hf r hr).congr_of_mem (fun s hs => joinTime_left S f g hs.2) hr
  have hr (r : ℝ) (hr : r ∈ Icc S (S+D)) :
      HasDerivWithinAt (joinTime S f g) (joinTime S f' g' r) (Icc S (S+D)) r := by
    rw [joinTime_right S f' g' he' hr.1]
    have hm : MapsTo (fun s : ℝ => s-S) (Icc S (S+D)) (Icc 0 D) := by
      intro s hs
      constructor <;> dsimp <;> linarith [hs.1, hs.2]
    have hd := (hg (r-S) (hm hr)).scomp r ((hasDerivAt_id r).sub_const S).hasDerivWithinAt hm
    have hd' : HasDerivWithinAt (fun s => g (s-S)) (g' (r-S)) (Icc S (S+D)) r := by
      simpa only [mul_one, smul_eq_mul, one_smul, Function.comp_def, id_eq] using hd
    exact hd'.congr_of_mem (fun s hs => joinTime_right S f g he hs.1) hr
  have hl' : HasDerivWithinAt (joinTime S f g) (joinTime S f' g' t) (Icc 0 S) t := by
    by_cases h : t ∈ Icc 0 S
    · exact hl t h
    · exact HasFDerivWithinAt.of_notMem_closure (by simpa only [isClosed_Icc.closure_eq] using h)
  have hr' : HasDerivWithinAt (joinTime S f g) (joinTime S f' g' t) (Icc S (S+D)) t := by
    by_cases h : t ∈ Icc S (S+D)
    · exact hr t h
    · exact HasFDerivWithinAt.of_notMem_closure (by simpa only [isClosed_Icc.closure_eq] using h)
  apply (hl'.union hr').mono
  intro s hs
  by_cases h : s ≤ S
  · exact Or.inl ⟨hs.1, h⟩
  · exact Or.inr ⟨(not_le.mp h).le, hs.2⟩

end ClockBarrier.Analysis
