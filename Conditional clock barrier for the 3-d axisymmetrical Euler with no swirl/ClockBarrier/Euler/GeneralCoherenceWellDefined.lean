/-
Copyright (c) 2026 Ovidiu-Neculai Avadanei.
See LICENSE for the terms governing original contributions.
-/
module

public import ClockBarrier.Euler.FlowChangeOfVariables
public import ClockBarrier.Euler.VorticityRegularity
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Well-definedness of general coherence

The actual Euler flow has positive singular values. Its literal clock blocks
are measurable, and the bounded initial vorticity has finite, integrable
Cartesian slices with a measurable slice average. These are proved consequences
of the Euler interface, not additional coherence assumptions.
-/

public section

namespace ClockBarrier.Euler
open Set MeasureTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

/-- Measurability of a Cartesian slice average, with the source's zero-area convention. -/
theorem stronglyMeasurable_slice_average
    {S : Set (ℝ × E₂)} (hS : MeasurableSet S)
    {g : ℝ × E₂ → E₃} (hg : StronglyMeasurable g) :
    StronglyMeasurable (fun s : ℝ =>
      if volume (Prod.mk s ⁻¹' S) = 0 then (0 : E₃) else
        (volume (Prod.mk s ⁻¹' S)).toReal⁻¹ • ∫ q in Prod.mk s ⁻¹' S, g (s, q)) := by
  have hm := measurable_measure_prodMk_left (ν := (volume : Measure E₂)) hS
  have hi := (hg.indicator hS).integral_prod_right' (ν := (volume : Measure E₂))
  simp_rw [← indicator_comp_right, integral_indicator (measurable_prodMk_left hS)] at hi
  exact StronglyMeasurable.ite (hm (measurableSet_singleton 0)) stronglyMeasurable_const
    (hm.ennreal_toReal.inv.stronglyMeasurable.smul hi)

/-- A clock cutoff gives finite area for every rotated Cartesian slice. -/
theorem clock_slice_measure_lt_top (aStar : E₃) (V : E₃ ≃ₗᵢ[ℝ] E₃)
    {S : Set E₃} {ℓ : ℝ} (hS : ∀ a ∈ S, ‖a - aStar‖ < ℓ) (s : ℝ) :
    volume {q : E₂ | aStar + V !₂[q 0, q 1, s] ∈ S} < ∞ := by
  have hp : Continuous (fun x : E₃ => (!₂[x 0, x 1] : E₂)) := by fun_prop
  refine lt_of_le_of_lt (measure_mono ?_)
    (((isCompact_closedBall (0 : E₃) ℓ).image hp).measure_lt_top)
  intro q hq
  refine ⟨!₂[q 0, q 1, s], ?_, ?_⟩
  · simpa [Metric.mem_closedBall, dist_eq_norm] using (hS _ hq).le
  · ext i
    fin_cases i <;> rfl

/-- Bounded continuous fields are Bochner integrable on every clock slice. -/
theorem integrableOn_clock_slice (aStar : E₃) (V : E₃ ≃ₗᵢ[ℝ] E₃)
    {S : Set E₃} {ℓ : ℝ} (hS : ∀ a ∈ S, ‖a - aStar‖ < ℓ)
    (W : E₃ →ᵇ E₃) (s : ℝ) :
    IntegrableOn (fun q : E₂ => W (aStar + V !₂[q 0, q 1, s]))
      {q : E₂ | aStar + V !₂[q 0, q 1, s] ∈ S} volume := by
  have hc : Continuous (fun q : E₂ => W (aStar + V !₂[q 0, q 1, s])) := by fun_prop
  exact Measure.integrableOn_of_bounded (clock_slice_measure_lt_top aStar V hS s).ne
    hc.aestronglyMeasurable (Filter.Eventually.of_forall (fun q => W.norm_coe_le_norm _))

/-- The actual Euler flow has three positive singular values at every lifespan point. -/
theorem classical_euler_on.singularValues_fderiv_flow_pos
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) {Φ : ℝ → E₃ → E₃}
    (hcont : ∀ x, ContinuousOn (fun t => Φ t x) (Ico 0 T))
    (hode : ∀ x, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => Φ s x) (u t (Φ t x)) (Ici t) t)
    (hinit : ∀ x, Φ 0 x = x) {t : ℝ} (ht : t ∈ Ico 0 T) (a : E₃) (i : Fin 3) :
    0 < (fderiv ℝ (Φ t) a).toLinearMap.singularValues i := by
  obtain ⟨hu, hdiff, hD, hbound, hdiv⟩ := h.velocity_regular
  have hd := Dynamics.det_fderiv_flow_eq_one_Ico (u := fun s x => u s x)
    hu hdiff hD hbound hcont hode hinit hdiv a ht
  have hk : (fderiv ℝ (Φ t) a).toLinearMap.ker = ⊥ := by
    simpa [hd] using (LinearMap.det_eq_zero_iff_ker_ne_bot
      (f := (fderiv ℝ (Φ t) a).toLinearMap))
  simp [LinearMap.singularValues_pos_iff_lt_finrank_range,
    LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hk)]

/-- Measurability of the rotated slice average for a measurable physical label set. -/
theorem stronglyMeasurable_clock_slice_average (aStar : E₃) (V : E₃ ≃ₗᵢ[ℝ] E₃)
    {S : Set E₃} (hS : MeasurableSet S) (W : E₃ →ᵇ E₃) :
    StronglyMeasurable (fun s : ℝ =>
      if volume {q : E₂ | aStar + V !₂[q 0, q 1, s] ∈ S} = 0 then (0 : E₃) else
        (volume {q : E₂ | aStar + V !₂[q 0, q 1, s] ∈ S}).toReal⁻¹ •
          ∫ q in {q : E₂ | aStar + V !₂[q 0, q 1, s] ∈ S},
            W (aStar + V !₂[q 0, q 1, s])) := by
  have hc : Continuous (fun x : ℝ × E₂ => aStar + V !₂[x.2 0, x.2 1, x.1]) := by fun_prop
  exact stronglyMeasurable_slice_average (hS.preimage hc.measurable)
    (W.continuous.comp hc).stronglyMeasurable

/-- Borel measurability of all three half-open singular-coordinate shells with the
strict label cutoff and closed physical cutoff. -/
theorem measurableSet_singular_clock_block {Φ : E₃ → E₃} (hΦ : Continuous Φ)
    (aStar : E₃) (V : E₃ ≃ₗᵢ[ℝ] E₃) (σ : Fin 3 → ℝ)
    (k : Fin 3 → ℤ) (ℓ L : ℝ) :
    MeasurableSet
      ({a : E₃ | let η := V.symm (a - aStar)
        (2 : ℝ) ^ (k 2) ≤ |η 2| ∧ |η 2| < 2 * (2 : ℝ) ^ (k 2) ∧
        (2 : ℝ) ^ (k 0) * σ 2 * (2 : ℝ) ^ (k 2) / σ 0 ≤ |η 0| ∧
        |η 0| < 2 * ((2 : ℝ) ^ (k 0) * σ 2 * (2 : ℝ) ^ (k 2) / σ 0) ∧
        (2 : ℝ) ^ (k 1) * σ 2 * (2 : ℝ) ^ (k 2) / σ 1 ≤ |η 1| ∧
        |η 1| < 2 * ((2 : ℝ) ^ (k 1) * σ 2 * (2 : ℝ) ^ (k 2) / σ 1)} ∩
        {a | ‖a - aStar‖ < ℓ} ∩ {a | ‖Φ a - Φ aStar‖ ≤ L}) := by
  have hη (i : Fin 3) : Continuous (fun a : E₃ => |V.symm (a - aStar) i|) := by fun_prop
  exact (((isClosed_le continuous_const (hη 2)).measurableSet.inter
    ((isOpen_lt (hη 2) continuous_const).measurableSet.inter
      ((isClosed_le continuous_const (hη 0)).measurableSet.inter
        ((isOpen_lt (hη 0) continuous_const).measurableSet.inter
          ((isClosed_le continuous_const (hη 1)).measurableSet.inter
            (isOpen_lt (hη 1) continuous_const).measurableSet))))).inter
    (isOpen_lt (by fun_prop) continuous_const).measurableSet).inter
    (isClosed_le (by fun_prop) continuous_const).measurableSet

/-- The actual initial Euler vorticity has finite, integrable slices and a measurable
Cartesian slice average on every measurable clock-local label set. -/
theorem classical_euler_on.initial_vorticity_clock_slices
    {α : ℝ≥0} {T : ℝ} {u : ℝ → E₃ →ᵇ E₃} {p : ℝ → E₃ → ℝ}
    (h : classical_euler_on α T u p) (aStar : E₃) (V : E₃ ≃ₗᵢ[ℝ] E₃)
    {S : Set E₃} (hS : MeasurableSet S) {ℓ : ℝ}
    (hclock : ∀ a ∈ S, ‖a - aStar‖ < ℓ) :
    let ω₀ := vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩)
    let A := fun s : ℝ => {q : E₂ | aStar + V !₂[q 0, q 1, s] ∈ S}
    (∀ s, volume (A s) < ∞ ∧
      IntegrableOn (fun q : E₂ => ω₀ (aStar + V !₂[q 0, q 1, s])) (A s) volume) ∧
    StronglyMeasurable (fun s : ℝ => if volume (A s) = 0 then (0 : E₃) else
      (volume (A s)).toReal⁻¹ • ∫ q in A s, ω₀ (aStar + V !₂[q 0, q 1, s])) := by
  obtain ⟨W, _, hW, _⟩ := h.exists_boundedContinuous_vorticity
  have hw : vorticity (u 0) (h.cartesian_partials 0 ⟨le_rfl, h.1⟩) = W 0 :=
    (funext (hW 0 ⟨le_rfl, h.1⟩)).symm
  simp only [hw]
  exact ⟨fun s => ⟨clock_slice_measure_lt_top aStar V hclock s,
    integrableOn_clock_slice aStar V hclock (W 0) s⟩,
    stronglyMeasurable_clock_slice_average aStar V hS (W 0)⟩

end ClockBarrier.Euler
