# Conditional Euler clock barrier

A Lean formalization of Ovidiu-Neculai Avadanei's
[*A conditional Lagrangian clock barrier at the C¹,⅓ threshold for axisymmetric
Euler without swirl*](https://arxiv.org/abs/2605.31587v3).

This package proves Theorems 1.1 and 1.2, Propositions 3.1, 3.2 and 4.2,
and Lemma 4.1, with the explicit conventions and repairs described below.
It also proves the supporting Hölder/logarithmic estimates, vorticity-growth
bounds, uniform local Euler existence and BKM continuation. The
[theorem-to-file guide](THEOREM_GUIDE.md) maps results to exact declarations
and proof implementations.

The 405 production modules contain no admitted proofs or custom axioms.
All nine principal exported theorem statements are proved. Their checked axiom
closures use only `propext`, `Classical.choice` and `Quot.sound`.
The Lorentz-space comparison remark is outside scope.

## Build and verify

Prerequisites: Git, Python 3.10 or later, and
[elan](https://github.com/leanprover/elan) with the toolchain specified below.
Use a new directory containing this source package. Run from its root:

```sh
lake exe cache get
python3 scripts/check_release.py
python3 scripts/test_checks.py
python3 scripts/verify.py
```

The first command fetches the pinned dependency sources and obtains Mathlib's
compiled cache. Downloading dependencies requires network access. Verification
then builds every production module with warnings treated as errors, checks
the nine exact theorem types, audits 37 axiom closures, replays every production
module through Lean's kernel, and checks ten expected compiled proof paths and
six excluded alternatives. Logs and machine-readable results are written to
`.verification/`. Kernel replay takes longer than an incremental build.

The source and checksum checks use only Python's standard library. They do not
import external verification scripts. The Lean probes are shipped in
[verification/](verification). `Replay.lean` is a tool that reads compiled module
data; its `unsafe` IO and traversal code is outside the mathematical library.
It invokes the same pinned Lean kernel, not a separately implemented kernel.
Compiler-generated recursion artifacts are skipped only after checking their
safe definition parent; production unsafe or partial declarations are rejected.

For a build of the main theorem dependency closure without the additional audits:

```sh
lake --no-cache --wfail build ClockBarrier
```

The full verifier explicitly builds all 405 shipped modules, including retained
helpers outside that dependency closure. After a successful full verification
build of this exact tree, `python3 scripts/verify.py --skip-build` runs the
remaining checks. Dependency directories must be independent checkouts,
not symlinks into another project. See [verification details](docs/VERIFICATION.md).

## Pinned environment

- Lean: `leanprover/lean4:v4.32.1`, in [lean-toolchain](lean-toolchain).
- Mathlib: `520045ab14e26149ee970e2e617ca04b09bde5d6`.
- All transitive revisions: [lake-manifest.json](lake-manifest.json).
- Source inventory and hashes: [source-lock.json](verification/source-lock.json).
- Paper version and archive hashes: [paper-source.json](verification/paper-source.json).

Mathlib supplies the general mathematical library. Selected supporting analytic
constructions are adapted from NavierStokesAndEuler; they are included as source,
with attribution, and proved here. No external Euler theorem is introduced as an
axiom. See [third-party attribution](docs/THIRD-PARTY.md).

## Errata and deviations

The [complete record](docs/ERRATA-AND-DEVIATIONS.md) contains **5 errata and
8 deviations** for arXiv:2605.31587v3. The repairs cover spectral square
completion, weighted dyadic summation, first-order axis regularity, the full
smooth-cutoff transition annulus, and a constant-name typo.

The record also specifies reflection symmetry and coherence conventions,
explains the auxiliary comparison ODE, and identifies strengthened statements
and standard-theory proof supplements. These distinctions are part of the
certificate's scope; the claim is correspondence with the paper under those
explicit conventions and repairs.

## License and citation

The original code and accompanying software documentation are licensed under
the [Apache License, Version 2.0](LICENSE). Adapted third-party notices are
preserved in [NOTICE](NOTICE). The manuscript remains a separate work and is
not relicensed by this package. Citation metadata is in [CITATION.cff](CITATION.cff).
Please cite both the paper and the version of this formalization that you use.
