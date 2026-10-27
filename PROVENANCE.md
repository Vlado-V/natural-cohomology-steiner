# Source provenance

`Steiner/` is the transitive part of the earlier Steiner matrix development, whose source credits are preserved in `provenance/Steiner-attribution.md`. `SteinerGeometry/` contains the geometric adapter proofs from the local staging project.

`OAI/` derives from the OpenAI math-main/lean source snapshot, originally using Lean 4.34.1. Its Apache-2.0 license is preserved in `OAI/LICENSE`; the original and ported hashes and comment-only packaging notices are recorded in `OAI/PROVENANCE.json`. Existing source attributions are retained.

The root `LICENSE` is copied from the earlier Steiner package. The paper `Natural_cohomology_of_general_Steiner_bundles.pdf` is copied byte-for-byte; its digest is recorded in `SOURCE_MANIFEST.json`. It is reference material, not Lean source.

Only recursively imported local source modules are included, together with one generated import-only umbrella. The external dependency is pinned mathlib; its transitive git dependencies remain locked in the Lake manifest. No compiled artifacts or package caches are included.
