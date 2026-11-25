# Theorem-to-file guide

## How to use this guide

Start with the **public statement** to see the exact hypotheses and conclusion. Its proof calls the named **implementation theorem**, where the proof is assembled from supporting modules. The reading routes below identify useful entry points; they are not an exhaustive dependency graph.

The production root [ClockBarrier.lean](ClockBarrier.lean) imports all nine public theorem exports. For use in another Lean file, start with `import ClockBarrier`; for a narrower import, use the relevant `ClockBarrier.Frozen.*` module.

## Numbered paper results

| Paper result | Public statement and public export | Proof implementation |
| --- | --- | --- |
| **Theorem 1.1** — classical continuation from general coherence | [Frozen/GeneralContinuation.lean](ClockBarrier/Frozen/GeneralContinuation.lean)<br>`ClockBarrier.Euler.general_clock_continuation` | [Euler/GeneralContinuation.lean](ClockBarrier/Euler/GeneralContinuation.lean)<br>`ClockBarrier.Euler.general_coherent_on.exists_classical_extension` |
| **Theorem 1.2** — uniform physical axis barrier | [Frozen/AxisBarrier.lean](ClockBarrier/Frozen/AxisBarrier.lean)<br>`ClockBarrier.Euler.axis_clock_barrier` | [Euler/AxisCoherentBarrier.lean](ClockBarrier/Euler/AxisCoherentBarrier.lean)<br>`ClockBarrier.Euler.axis_coherent_on.uniform_physical_axis_barrier` |
| **Proposition 3.1** — local membership in the general coherence class | [Frozen/LocalGeneralCoherence.lean](ClockBarrier/Frozen/LocalGeneralCoherence.lean)<br>`ClockBarrier.Euler.local_general_coherence` | [Euler/LocalGeneralCoherence.lean](ClockBarrier/Euler/LocalGeneralCoherence.lean)<br>`ClockBarrier.Euler.classical_euler_on.exists_local_general_coherence` |
| **Proposition 3.2** — local membership in the axis coherence class | [Frozen/LocalAxisCoherence.lean](ClockBarrier/Frozen/LocalAxisCoherence.lean)<br>`ClockBarrier.Euler.local_axis_coherence` | [Euler/LocalAxisCoherence.lean](ClockBarrier/Euler/LocalAxisCoherence.lean)<br>`ClockBarrier.Euler.classical_euler_on.exists_local_axis_coherence` |
| **Lemma 4.1** — smallest-singular-value evolution, including multiplicity | [Frozen/SingularValueEvolution.lean](ClockBarrier/Frozen/SingularValueEvolution.lean)<br>`ClockBarrier.Euler.smallest_singularValue_evolution` | [Euler/SingularValueEvolution.lean](ClockBarrier/Euler/SingularValueEvolution.lean)<br>`ClockBarrier.Euler.classical_euler_on.smallest_singularValue_evolution` |
| **Proposition 4.2** — uniform directional strain driver bound | [Frozen/GeneralDriver.lean](ClockBarrier/Frozen/GeneralDriver.lean)<br>`ClockBarrier.Euler.general_driver_bound` | [Euler/GeneralDriver.lean](ClockBarrier/Euler/GeneralDriver.lean)<br>`ClockBarrier.Euler.general_coherent_on.exists_uniform_general_driver_bound` |

The following scope details matter when comparing the manuscript with Lean:

- **Theorem 1.1:** for α ≥ 1/3, uniformly finite general coherence yields an actual classical extension with the same α. The velocity agrees on the original lifespan and remains axisymmetric without swirl. Continued coherence is not required.
- **Theorem 1.2:** for α ≥ 1/3, the physical meridional Jacobian has an on-axis limit bounded below by one positive constant, uniformly in axis label, time, and initialized flow. The public statement retains reflection and maximality within the same uniformly finite coherence class. The underlying barrier estimate is stronger and does not need those two premises.
- **Propositions 3.1 and 3.2:** these restrict a supplied classical solution to a shorter positive lifespan on which coherence holds. Both allow every 0 < α < 1. Proposition 3.1 assumes initial axisymmetry/no swirl; Proposition 3.2 additionally retains initial reflection. The separate local-existence theorem below constructs the solution itself.
- **Lemma 4.1:** the statement applies to all classical Euler flows. It gives an actual right derivative and an attained minimum of the strain quadratic form over the entire unit smallest left singular eigenspace, including repeated singular values.
- **Proposition 4.2:** directions are explicitly unit vectors in that eigenspace. The same integrable function B and constant C work before choosing the flow, label, time, or direction, in the bound with exponent (3α − 1)/2.

## Additional public supporting theorems

These three results supply the analytic and existence theory used in the BKM continuation proof; they are not additional numbered propositions in the manuscript.

| Result | Public statement and public export | Proof implementation |
| --- | --- | --- |
| Hölder Calderón–Zygmund and logarithmic supremum estimates | [Frozen/CurlHolderLogarithmic.lean](ClockBarrier/Frozen/CurlHolderLogarithmic.lean)<br>`ClockBarrier.Analysis.exists_curl_holder_logarithmic_constant` | [Analysis/CurlHolderLogarithmic.lean](ClockBarrier/Analysis/CurlHolderLogarithmic.lean)<br>`ClockBarrier.Analysis.exists_uniform_curl_holder_logarithmic_constant` |
| Vorticity Hölder growth and uniform bounds under the BKM integral condition | [Frozen/VorticityHolderGrowth.lean](ClockBarrier/Frozen/VorticityHolderGrowth.lean)<br>`ClockBarrier.Euler.vorticity_holder_growth_and_bkm_bounds` | [Euler/VorticityHolderGrowth.lean](ClockBarrier/Euler/VorticityHolderGrowth.lean)<br>`ClockBarrier.Euler.exists_vorticity_holder_growth_and_bkm_bounds` |
| Uniform local classical Euler existence | [Frozen/UniformLocalExistence.lean](ClockBarrier/Frozen/UniformLocalExistence.lean)<br>`ClockBarrier.Euler.uniform_local_classical_euler` | [Euler/UniformLocalExistence.lean](ClockBarrier/Euler/UniformLocalExistence.lean)<br>`ClockBarrier.Euler.exists_uniform_local_classical_euler` |

The exact specifications are the public Lean declarations linked above. The existence lifespan depends only on α and the common initial norm bound M, including M = 0. The growth theorem supplies a priori bounds; the actual continuation is assembled in [BKMContinuation.lean](ClockBarrier/Euler/BKMContinuation.lean).

## Reading routes through the proofs

### Theorem 1.1: general clock barrier and continuation

1. Read [GeneralCoherent.lean](ClockBarrier/Euler/GeneralCoherent.lean) for the hypotheses, then the public statements of Lemma 4.1 and Proposition 4.2 above.
2. [GeneralClockBarrier.lean](ClockBarrier/Euler/GeneralClockBarrier.lean) combines singular-value evolution with the driver bound to obtain a uniform positive lower bound for the smallest singular value.
3. [GeneralVorticityBound.lean](ClockBarrier/Euler/GeneralVorticityBound.lean) uses determinant one, Cauchy transport, and flow surjectivity to obtain uniform deformation and vorticity bounds. [BKMIntegrability.lean](ClockBarrier/Euler/BKMIntegrability.lean) converts these to a finite BKM time integral.
4. [BKMContinuation.lean](ClockBarrier/Euler/BKMContinuation.lean) applies the Hölder-growth bounds and [UniformRestart.lean](ClockBarrier/Euler/UniformRestart.lean). Restarting uses [TimeTranslation.lean](ClockBarrier/Euler/TimeTranslation.lean), [OverlapUniqueness.lean](ClockBarrier/Euler/OverlapUniqueness.lean), and [RestartGluing.lean](ClockBarrier/Euler/RestartGluing.lean).
5. [GeneralContinuation.lean](ClockBarrier/Euler/GeneralContinuation.lean) supplies the final extension and its axisymmetry/no swirl using [SymmetryPreservation.lean](ClockBarrier/Euler/SymmetryPreservation.lean).

For the longer proof of **Proposition 4.2**, start at its implementation and follow [DirectionalLagrangian.lean](ClockBarrier/Euler/DirectionalLagrangian.lean), then the coherence estimates in [GeneralDini.lean](ClockBarrier/Euler/GeneralDini.lean), [GeneralOffClock.lean](ClockBarrier/Euler/GeneralOffClock.lean), [GeneralLongitudinal.lean](ClockBarrier/Euler/GeneralLongitudinal.lean), and [GeneralTransverseBlock.lean](ClockBarrier/Euler/GeneralTransverseBlock.lean). The executed signed transverse/longitudinal/off-clock estimate is [GeneralSignedInitial.lean](ClockBarrier/Euler/GeneralSignedInitial.lean); the summation and signed I/II assembly use [GeneralClockSeries.lean](ClockBarrier/Analysis/GeneralClockSeries.lean) and [DirectionalSplit.lean](ClockBarrier/Analysis/DirectionalSplit.lean).

The spectral lower derivative now follows [SpectralGap.lean](ClockBarrier/Analysis/SpectralGap.lean) and [SpectralMinimum.lean](ClockBarrier/Analysis/SpectralMinimum.lean). The scalar supercritical comparison constructs the actual auxiliary solution in [PowerComparison.lean](ClockBarrier/Analysis/PowerComparison.lean), supported by [LinearComparison.lean](ClockBarrier/Analysis/LinearComparison.lean) and [ACComparison.lean](ClockBarrier/Analysis/ACComparison.lean).

### Theorem 1.2: physical axis barrier

1. Read [AxisCoherent.lean](ClockBarrier/Euler/AxisCoherent.lean) and the two public axis-block definitions below.
2. [AxisBiotSavart.lean](ClockBarrier/Euler/AxisBiotSavart.lean) supplies the signed on-axis representation; [AxisCylindricalTransport.lean](ClockBarrier/Euler/AxisCylindricalTransport.lean) gives the cylindrical, transported form.
3. [AxisBlockComparison.lean](ClockBarrier/Euler/AxisBlockComparison.lean), [AxisCoherentIntegral.lean](ClockBarrier/Euler/AxisCoherentIntegral.lean), and [AxisVorticityIntegral.lean](ClockBarrier/Euler/AxisVorticityIntegral.lean) connect the geometry, coherence, and transported-vorticity bounds. [AxisOffClock.lean](ClockBarrier/Euler/AxisOffClock.lean) handles the off-clock near field.
4. [AxisCylindricalAssembly.lean](ClockBarrier/Euler/AxisCylindricalAssembly.lean) and [AxisSmoothFarBound.lean](ClockBarrier/Euler/AxisSmoothFarBound.lean) handle the smooth decomposition and energy-controlled far field, including the transition annulus. [AxisUniformDriver.lean](ClockBarrier/Euler/AxisUniformDriver.lean) assembles the uniform driver.
5. [Euler/AxisBarrier.lean](ClockBarrier/Euler/AxisBarrier.lean) proves the barrier; [AxisCoherentBarrier.lean](ClockBarrier/Euler/AxisCoherentBarrier.lean) packages it as the exact physical conclusion consumed by the public theorem.

### Propositions 3.1 and 3.2: local coherence

The shared starting point is [Uniqueness.lean](ClockBarrier/Euler/Uniqueness.lean) and [SymmetryPreservation.lean](ClockBarrier/Euler/SymmetryPreservation.lean), which propagate initial axisymmetry/no swirl through the supplied classical solution.

For Proposition 3.1, [LocalCoherenceAssembly.lean](ClockBarrier/Euler/LocalCoherenceAssembly.lean) combines [LocalDini.lean](ClockBarrier/Euler/LocalDini.lean), [LocalOffClock.lean](ClockBarrier/Euler/LocalOffClock.lean), [LocalLongitudinal.lean](ClockBarrier/Euler/LocalLongitudinal.lean), [LocalCusp.lean](ClockBarrier/Euler/LocalCusp.lean), and [Euler/MeasurableSingularFrame.lean](ClockBarrier/Euler/MeasurableSingularFrame.lean). Its full-lifespan symmetry premise is supplied by the final provider. The measurable selection, including multiplicities, is constructed in [Geometry/MeasurableSingularFrame.lean](ClockBarrier/Geometry/MeasurableSingularFrame.lean).

For Proposition 3.2, start at [LocalAxisCoherence.lean](ClockBarrier/Euler/LocalAxisCoherence.lean), follow the angular derivative in [HoopStretch.lean](ClockBarrier/Geometry/HoopStretch.lean), then [LocalAxisCusp.lean](ClockBarrier/Euler/LocalAxisCusp.lean), [LocalAxisOffClock.lean](ClockBarrier/Euler/LocalAxisOffClock.lean), and the shared [HolderDyadicTail.lean](ClockBarrier/Analysis/HolderDyadicTail.lean).

### Uniform local existence: smooth solutions and the rough-data limit

1. [UniformSmoothExistence.lean](ClockBarrier/Euler/UniformSmoothExistence.lean) obtains a common lifespan using the smooth solver, gradient-controlled continuation, and the existing Hölder estimates. Its immediate inputs are [SmoothBoundedContinuation.lean](ClockBarrier/Euler/SmoothBoundedContinuation.lean), [SmoothClassical.lean](ClockBarrier/Euler/SmoothClassical.lean), and [UniformShortTimeBounds.lean](ClockBarrier/Euler/UniformShortTimeBounds.lean).
2. [ExactMollifiedFamily.lean](ClockBarrier/Euler/ExactMollifiedFamily.lean) constructs exact smooth Euler solutions from mollified initial data.
3. [ExactSpatialLimit.lean](ClockBarrier/Euler/ExactSpatialLimit.lean) and [ExactInitialLimit.lean](ClockBarrier/Euler/ExactInitialLimit.lean) construct the limit velocity and identify its initial value.
4. [SmoothPressureInterpolation.lean](ClockBarrier/Analysis/SmoothPressureInterpolation.lean) supports [ExactPressureLimit.lean](ClockBarrier/Euler/ExactPressureLimit.lean), which reconstructs the limiting pressure gradient and potential.
5. [ExactClassicalTimeLimit.lean](ClockBarrier/Euler/ExactClassicalTimeLimit.lean) passes the time equation to the limit. [UniformLocalExistence.lean](ClockBarrier/Euler/UniformLocalExistence.lean) verifies every clause of the classical interface.

## Reusable machinery: direct entry points

These are proved implementation declarations, rather than separate public manuscript anchors. Names are relative to `ClockBarrier.Euler` unless another namespace is shown.

| Ingredient | File | Entry declaration |
| --- | --- | --- |
| Whole-lifespan flow construction and spatial regularity | [Dynamics/FlowLifespan.lean](ClockBarrier/Dynamics/FlowLifespan.lean) | `ClockBarrier.Dynamics.exists_regular_flow_Ico` |
| Variational equation for the spatial derivative | [Dynamics/FlowDerivativeWithin.lean](ClockBarrier/Dynamics/FlowDerivativeWithin.lean) | `ClockBarrier.Dynamics.hasDerivWithinAt_fderiv_flow_Ico` |
| Cauchy vorticity transport | [Euler/CauchyTransport.lean](ClockBarrier/Euler/CauchyTransport.lean) | `classical_euler_on.vorticity_flow_eq_fderiv_apply` |
| Bijective, measure-preserving flow | [Euler/FlowChangeOfVariables.lean](ClockBarrier/Euler/FlowChangeOfVariables.lean) | `classical_euler_on.contDiff_bijective_measurePreserving_flow` |
| Global change of variables | [Euler/FlowChangeOfVariables.lean](ClockBarrier/Euler/FlowChangeOfVariables.lean) | `classical_euler_on.integral_comp_flow` |
| Pressure cancellation | [Euler/PressureCancellation.lean](ClockBarrier/Euler/PressureCancellation.lean) | `classical_euler_on.integrated_pressure_cancellation` |
| Energy conservation | [Euler/EnergyConservation.lean](ClockBarrier/Euler/EnergyConservation.lean) | `classical_euler_on.energy_eq_initial` |
| Classical velocity uniqueness | [Euler/Uniqueness.lean](ClockBarrier/Euler/Uniqueness.lean) | `classical_euler_on.velocity_eq` |
| Preservation of orthogonal symmetries | [Euler/SymmetryPreservation.lean](ClockBarrier/Euler/SymmetryPreservation.lean) | `classical_euler_on.preserves_orthogonal_symmetry` |
| Measurable singular frame with multiplicities | [Geometry/MeasurableSingularFrame.lean](ClockBarrier/Geometry/MeasurableSingularFrame.lean) | `ClockBarrier.Geometry.exists_measurable_singular_frame` |
| BKM continuation in the class | [Euler/BKMContinuation.lean](ClockBarrier/Euler/BKMContinuation.lean) | `classical_euler_on.exists_extension_of_bkm` |

The BKM entry point assumes integrability in time of the spatial essential supremum of the actual curl, represented by a bounded continuous field. It constructs a classical extension with the same α; it does not assume symmetry, coherence, or a terminal trace.

## Definitions and conventions

| Exact definition | File | Meaning |
| --- | --- | --- |
| `ClockBarrier.Euler.classical_euler_on` | [Classical.lean](ClockBarrier/Euler/Classical.lean) | Classical incompressible Euler on [0,T), with velocity in C_t(C_b¹ ∩ L²), 0 < α < 1, and compact-time spatial α-Hölder bounds for its derivative. |
| `ClockBarrier.Euler.axisymmetric_no_swirl` | [Axisymmetry.lean](ClockBarrier/Euler/Axisymmetry.lean) | Axisymmetry and zero azimuthal velocity. |
| `ClockBarrier.Euler.z_reflection_symmetric` | [Reflection.lean](ClockBarrier/Euler/Reflection.lean) | Horizontal Cartesian components even in z; axial component odd. |
| `ClockBarrier.Euler.axisDyadicBlock` | [AxisDyadicBlock.lean](ClockBarrier/Euler/AxisDyadicBlock.lean) | Half-open longitudinal and transverse dyadic shells, with transverse scale λJ³Λ. |
| `ClockBarrier.Euler.axisClockBlock` | [AxisClockBlock.lean](ClockBarrier/Euler/AxisClockBlock.lean) | An axis dyadic block restricted by the closed clock-local bounds. |
| `ClockBarrier.Euler.vorticity` | [Vorticity.lean](ClockBarrier/Euler/Vorticity.lean) | Right-handed Cartesian curl with explicit existence of scalar Cartesian partial derivatives. |
| `ClockBarrier.Euler.axis_coherent_on` | [AxisCoherent.lean](ClockBarrier/Euler/AxisCoherent.lean) | The axis coherence class, with uniformly finite coherence constants. |
| `ClockBarrier.Euler.general_coherent_on` | [GeneralCoherent.lean](ClockBarrier/Euler/GeneralCoherent.lean) | The general coherence class, including its measurable singular-frame and dyadic conditions. |

The classical interface requires the PDE and regularity; flow properties, energy conservation, and clock estimates are proved later. Its temporal convention does not assume continuity in the full Hölder norm. The vorticity definition itself requires neither total differentiability nor continuity of the partial derivatives.

See [Errata and deviations](docs/ERRATA-AND-DEVIATIONS.md) for reflection, shell, tail-cutoff, temporal and maximality conventions. Refer to the exact definitions for strict versus closed cutoff inequalities.

## Reproducing the certificate

The [README](README.md) lists the build and verification commands.
[Statements.lean](verification/Statements.lean) checks all nine public theorem
types and prints their axiom closures together with selected supporting results.
[Replay.lean](verification/Replay.lean) reloads each production module into its
import environment and rechecks its declarations with Lean's kernel, then checks
the selected compiled proof paths.

The `Frozen` directory name is retained for stable public imports; all nine
theorems in it are proved. No declaration there is a draft.
