# Errata and deviations

This record compares the formalization with Ovidiu-Neculai Avadanei,
*A conditional Lagrangian clock barrier at the C¹,⅓ threshold for axisymmetric
Euler without swirl*, [arXiv:2605.31587v3](https://arxiv.org/abs/2605.31587v3).
Locations use that version's section and result numbers and identify the relevant
display in words. We count entries, grouping repeated occurrences; editorial
misprints are included. An erratum records a false printed assertion or formula.
An additional argument for a true assertion is recorded as a deviation, not an
erratum. The five repairs below preserve the conclusions of Theorems 1.1 and 1.2;
the precise conventions for their hypotheses are described separately. Their Lean
axiom closures contain only `propext`, `Classical.choice` and `Quot.sound`.

| Source | Errata | Deviations |
| --- | ---: | ---: |
| arXiv:2605.31587v3 | 5 | 8 |

## arXiv:2605.31587v3

### Errata

1. **Lemma 4.1, square completion in the proper least-eigenspace case.**
   The second lower bound for `v · C(t₀+h)v` prints the quadratic error
   `(2‖Ċ(t₀)‖ |v⊥| / √(γ−λ(t₀)))² h²`. The factor `|v⊥|²` must be removed.
   For example, with δ = M = 1, h = 0.1 and r = 0.2, the preceding expression
   δr² − 4Mhr is −0.04, while the incorrectly retained-factor bound is −0.0016.
   The valid lower bound is −4M²h²/δ, uniform in r. This still gives the required
   first-order remainder and does not change the evolution formula. See
   `spectral_gap_square_completion` and `unit_quadratic_affine_lower` in
   [SpectralGap.lean](../ClockBarrier/Analysis/SpectralGap.lean).
   The numerical counterexample here is explanatory, not a separate Lean theorem.

2. **Section 5, transverse angular summation after the longitudinal and Dini estimates.**
   The statement that there are at most `O(n+1)` dyadic pairs with
   `λ₁²+λ₂² ≃ 2^(2n)` is false for two-sided dyadic indices: fix λ₁ = 2ⁿ and
   let λ₂ = 2⁻ᵐ with m arbitrarily large. The weighted series is nevertheless
   summable. The proof sums over the maximum index and a nonnegative difference
   of indices, retaining geometric decay in the smaller coordinate. No theorem
   conclusion changes. See `summable_general_angular_weight` in
   [GeneralAngularSummation.lean](../ClockBarrier/Analysis/GeneralAngularSummation.lean).
   The pair-count counterexample is explanatory; Lean proves the weighted sum.

3. **Section 6, the axis expansions preceding the diagonal deformation matrix.**
   The printed remainders `φʳ = aR + O(R³)` and `φᶻ = b + O(R²)` do not follow
   from C¹,α regularity and axisymmetry. For example, the rotationally covariant
   C¹,α maps `((1+r^α)x,(1+r^α)y,z)` and `(x,y,z+r^(1+α))` have remainders of
   order R^(1+α). These are examples about regularity and symmetry, not asserted
   Euler flows. First-order differentiability, symmetry, determinant one and
   continuity suffice for the needed axis derivative and physical Jacobian limit.
   No theorem conclusion changes. See `eq_diagonal_of_hasFDerivAt_axis` in
   [AxisDerivative.lean](../ClockBarrier/Geometry/AxisDerivative.lean) and
   `tendsto_det_fderiv_physical_meridional` in
   [PhysicalJacobian.lean](../ClockBarrier/Geometry/PhysicalJacobian.lean).
   The illustrative maps above are not separately formalized counterexamples.

4. **Section 5, smooth near/far decomposition and far-field integration by parts.**
   The initial split restricts the χ_L far integral to `|x*−y| ≥ L`, omitting its
   transition annulus `L/2 < |x*−y| < L`. A subsequent displayed curl identity
   also drops the product-rule term on its left side. Keep the entire smooth
   far term and both terms in the derivative of the product. Its estimate has
   the scaling `L^(-5/2) ‖u₀‖₂`; at the fixed coherence radius this is absorbed
   into the same integrable driver coefficient. No theorem conclusion changes.
   See `directional_far_curl_expansion` in
   [DirectionalFarField.lean](../ClockBarrier/Analysis/DirectionalFarField.lean),
   `exists_scaled_directional_far_energy_constant` in
   [DirectionalFarScaling.lean](../ClockBarrier/Analysis/DirectionalFarScaling.lean),
   and the explicit annulus identity `classical_euler_on.axis_smooth_far_eq_sharp_add_annulus`
   in [AxisSmoothDecomposition.lean](../ClockBarrier/Euler/AxisSmoothDecomposition.lean).

5. **Section 4, final BKM integral bound in the proof of Theorem 1.1.**
   The factor printed as `C_T⁻²` refers to the positive clock lower bound
   introduced as `c_T`. Use `c_T⁻²`. This is a constant-name typo and does not
   change the theorem. The same lower-bound witness is used by
   `general_coherent_on.exists_uniform_deformation_vorticity_bounds` in
   [GeneralVorticityBound.lean](../ClockBarrier/Euler/GeneralVorticityBound.lean)
   and the time-integral conclusion in
   [BKMIntegrability.lean](../ClockBarrier/Euler/BKMIntegrability.lean).

### Deviations

1. **Theorem 1.2 and Proposition 3.2, “odd in z”.**
   The intended reflection symmetry is made componentwise: horizontal Cartesian
   components are even in z, and the axial component is odd. This interpretation
   is used in `z_reflection_symmetric`; it is not literal oddness of every
   Cartesian component. See [Reflection.lean](../ClockBarrier/Euler/Reflection.lean).

2. **The classical Euler class and Cartesian curl.**
   `classical_euler_on` spells out the PDE, C_t(C_b¹ ∩ L²) temporal convention and
   spatial α-Hölder derivative bounds uniform on compact time intervals. It does
   not assume time continuity in the full Hölder norm or any flow/energy theorem.
   `vorticity` is the right-handed Cartesian curl with explicit existence of all
   scalar Cartesian partial derivatives. Its definition does not require their
   continuity or total differentiability. See
   [Classical.lean](../ClockBarrier/Euler/Classical.lean) and
   [Vorticity.lean](../ClockBarrier/Euler/Vorticity.lean).

3. **Section 2, dyadic and coherence conventions; Theorem 1.2 maximality.**
   Dyadic shells are half-open, for example Λ ≤ |ΔZ| < 2Λ and
   λJ³Λ ≤ R < 2λJ³Λ. Axis label-distance cutoffs use ≤ ℓ; general label-distance
   cutoffs use < ℓ. Both physical-distance cutoffs use ≤ L. The general tail uses
   Λ ≤ ℓ; constants in both coherence classes are uniformly finite. Theorem 1.2
   maximality means no extension within that same uniformly finite coherence
   class. These choices make endpoint and quantifier conventions exact. See
   [AxisClockBlock.lean](../ClockBarrier/Euler/AxisClockBlock.lean),
   [GeneralCoherent.lean](../ClockBarrier/Euler/GeneralCoherent.lean),
   [AxisCoherent.lean](../ClockBarrier/Euler/AxisCoherent.lean) and
   [AxisBarrier.lean](../ClockBarrier/Frozen/AxisBarrier.lean).

4. **Lemma 4.1, Proposition 4.2 and the scope of the axis barrier.**
   Lemma 4.1 is proved for every classical Euler flow, with an actual right
   derivative and an attained minimum over the full least singular eigenspace.
   Proposition 4.2 makes unit-vector normalization explicit; B and C are chosen
   uniformly before the flow, label, time and direction. The public Theorem 1.2
   retains its reflection and maximality hypotheses, although the underlying
   estimate does not need them. These are explicit scope/quantifier choices,
   without stronger hidden premises. See
   [SingularValueEvolution.lean](../ClockBarrier/Frozen/SingularValueEvolution.lean),
   [GeneralDriver.lean](../ClockBarrier/Frozen/GeneralDriver.lean) and
   [AxisCoherentBarrier.lean](../ClockBarrier/Euler/AxisCoherentBarrier.lean).

5. **Propositions 3.1 and 3.2, local lifespan.**
   The public statements restrict a supplied classical solution to
   `0 < T₀ < T` and establish coherence on `[0,T₀)`. The chosen interval has room
   before the original endpoint. Uniform local existence is proved separately
   and supplies solutions from initial data. Initial symmetries are propagated
   using proved uniqueness. See
   [LocalGeneralCoherence.lean](../ClockBarrier/Frozen/LocalGeneralCoherence.lean),
   [LocalAxisCoherence.lean](../ClockBarrier/Frozen/LocalAxisCoherence.lean) and
   [UniformLocalExistence.lean](../ClockBarrier/Frozen/UniformLocalExistence.lean).

6. **Section 6, cylindrical Cauchy transport and integration.**
   The scalar cylindrical formula uses the projection of the vector Cauchy
   transport onto the azimuthal direction, with normalization −3/2. Cylindrical
   measure and the three-dimensional block mass are explicitly distinguished.
   The manuscript's notation can be retained; the subsequent block mass estimate
   returns to the Cartesian volume integral. See
   `classical_euler_on.axis_strain_cylindrical_cauchy` in
   [AxisCylindricalTransport.lean](../ClockBarrier/Euler/AxisCylindricalTransport.lean)
   and [AxisCylindricalAssembly.lean](../ClockBarrier/Euler/AxisCylindricalAssembly.lean).

7. **Sections 4 and 6, comparison ODE.**
   For integrable B, the auxiliary equality solution is absolutely continuous
   and satisfies its equation almost everywhere. For p > 1, bounding the
   negative transform `g = f^(1-p)/(1-p)` against divergence to minus infinity
   yields the lower bound for f. The printed nonvanishing assertion about g is
   true, but nonvanishing alone does not supply this implication. Lean constructs
   the same solution via the positive rescaling `G = −(p−1)g`, proves comparison,
   and obtains a uniform exponential lower bound. No absolute continuity of the
   original clock or continuity of B is added. See `exists_positive_power_comparison`
   in [PowerComparison.lean](../ClockBarrier/Analysis/PowerComparison.lean) and
   [Scalar.lean](../ClockBarrier/Analysis/Scalar.lean).

8. **Standard analytic inputs invoked by the paper.**
   Flow construction, Cauchy transport, volume preservation, pressure cancellation,
   energy conservation, Hölder/logarithmic estimates, local existence and BKM
   continuation are proved explicitly. Measurable singular-frame selection and
   null-slice handling supply details implicit in the local coherence argument.
   Theorem 1.1 constructs actual classical continuation beyond T, without requiring
   coherence after T. These are proof supplements, not extra hypotheses. See the
   [theorem guide](../THEOREM_GUIDE.md).

## Proof routes

The six numbered proofs follow the paper's mathematical mechanisms: near-identity
local coherence, the hoop-stretch identity, spectral-gap square completion,
signed deformation/initial-increment splitting and angular summation, cylindrical
axis reduction, and the auxiliary comparison ODE followed by BKM continuation.
Shared estimates implement identical final bounds in the cone and its complement.
Standard-library subproofs need not reproduce individual sentences of the paper.

The restriction to the collapse regime J < 1, clock-local upper bounds written
with ≲, and full-block cylindrical scaling shorthand are not listed as errors.

## Outside scope and reference-only sources

The Lorentz-space comparison remark is not formalized. Background literature
survey claims are not part of the certificate. Selected analytic constructions
are adapted from the pinned NavierStokesAndEuler repository; this is a code
reference, not a claim that its separate PDE results are certified here. See
[third-party attribution](THIRD-PARTY.md). The mathematical source archive is
not redistributed; its identity is recorded in
[source metadata](../verification/paper-source.json).
