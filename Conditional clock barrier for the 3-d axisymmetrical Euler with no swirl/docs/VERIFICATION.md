# Verification and reproducibility

The public package contains the proof sources, pinned dependencies, complete
verification tools and source hashes. It contains no compiled project artifacts.

## What each check establishes

1. `python3 scripts/check_release.py` checks the exact file inventory, checksums,
   production module headers, source-code fingerprints, import roots, pinned
   dependencies, local documentation links and forbidden constructs/references.
   A checksum is a reproducibility check, not a proof of mathematical meaning.
2. `python3 scripts/test_checks.py` tests nested comments, string literals,
   primed identifiers, significant token changes and checksum tampering.
3. `python3 scripts/verify.py` checks dependency revisions, builds the production
   library, elaborates exact public types and audits their axioms, then runs the
   full project kernel replay and compiled proof-path checks. It removes inherited
   Lean search-path overrides from the subprocess environment.

The exact types in [Statements.lean](../verification/Statements.lean) are checked
by applying the exported proofs. All eight source-facing definitions are present
in the shipped library and covered by the immutable source inventory; they are
not replaced by additional assumptions. Proof status follows from compilation,
axiom auditing and kernel checks, together with mathematical inspection of the
statements and definitions. Tests alone cannot certify source interpretation.

## Kernel replay scope

[Replay.lean](../verification/Replay.lean) loads each of the 405 production modules
into a fresh environment containing its declared imports, obtains its actual
compiled declaration bodies, and invokes `Lean.Environment.replay`. This rechecks
project declarations using Lean's kernel. Imports retain Lean's normal trust
model; the entire upstream library is not independently replayed here. It is
also not a second independently implemented kernel.

The replay tool checks compiled proof-body dependencies for the spectral-gap,
hoop-stretch, signed-driver, cylindrical and auxiliary-ODE proof routes. Merely
importing an unused helper does not satisfy those checks.

## Fresh source-directory test

For an isolation test, extract the release archive into an empty directory and
run the README commands there. Let Lake fetch its own package source checkouts.
Mathlib's official compressed cache may be reused or downloaded; do not copy
project `.olean` files or link another project's `.lake` directory. The shared
installed Lean toolchain is specified exactly by `lean-toolchain`.

The package has no remote URL, Git history, hosted CI, or registry-specific
comparator configuration. Those are optional distribution arrangements, not
prerequisites for local verification. A public hosting destination can use the
same commands. Source archives are accompanied by a SHA-256 digest.

## Updates

This is a versioned source snapshot. Preserve the checked mathematical
declarations when making documentation changes. For any later source change,
regenerate the release inventory, review the exact statement/definition changes,
and rerun verification. Do not treat old output logs as evidence for new bytes.
