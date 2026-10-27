# Source provenance

`Steiner/` is the transitive part of the earlier Steiner matrix development, whose source credits are preserved in `provenance/Steiner-attribution.md`. `SteinerGeometry/` contains the geometric adapter proofs from the local staging project.

`OAI/` derives from the OpenAI math-main/lean source snapshot, originally using Lean 4.34.1. Its Apache-2.0 license is preserved in `OAI/LICENSE`; original and ported hashes are recorded in `OAI/PROVENANCE.json`. Existing source attributions are retained. Compatibility edits add module headers, public imports and declarations, exposed definition bodies, and proof-elaboration adjustments for the pinned Lean module system.

The root `LICENSE` is copied from the earlier Steiner package. The paper `Natural_cohomology_of_general_Steiner_bundles.pdf` is copied byte-for-byte; its digest is recorded in `SOURCE_MANIFEST.json`. It is reference material, not Lean source.

The package includes the transitive local proof-source closure, its entry and audit modules, and the independent Palomar interface. `Challenge.lean` defines the mathematical statement independently and intentionally leaves the theorem unproved. `Solution.lean` proves the matching theorem from the geometric development; `comparator.json` specifies the comparison.

The external dependency is pinned mathlib; its transitive Git dependencies remain locked in the Lake manifest. Compiled artifacts and package caches are excluded from version control. `SOURCE_MANIFEST.json` records the packaged source hashes.
