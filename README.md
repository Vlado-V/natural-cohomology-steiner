# Natural cohomology of general Steiner bundles

Lean formalization of the main theorem of the included paper.

For every characteristic-zero field `K`, `n ≥ 1`, `t ≥ 1`, and `r ≥ n`, a nonempty principal open of matrices of linear forms defines actual rank-`r` Steiner bundles

```
0 → O(-1)^t → O^(t+r) → F → 0
```

with natural cohomology in every integer twist. The formalization also proves all-degree maximal rank for the corresponding polynomial matrices.

The geometric theorem is `SteinerGeometry.genericNaturalSteiner_charZero` in `SteinerGeometry/GeometricSteinerConclusion.lean`. The matrix theorem is `Steiner.genericMatrixConclusion_charZero` in `SteinerGeometry/AllDegreeMaximalRank.lean`.

For Palomar, `Challenge.lean` states `NaturalCohomologySteinerPaper.main_result` independently and deliberately leaves its proof as a hole. `Solution.lean` proves the same theorem using the full geometric development. `comparator.json` selects these modules for comparison.

Lean is pinned to `leanprover/lean4:v4.35.0-rc3`; Mathlib is pinned to `8accc04827c389e678c3ef83e623b402e7480394`.

To build and audit the checkout, run:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Run the independent Palomar comparison on Linux:

```sh
lake comparator --config comparator.json
```

The included endpoint audit records report only `propext`, `Classical.choice`, and `Quot.sound`. `TheoremAudit.txt` records the integrated audit; `Audit.lean` reruns the main signatures and axiom checks. The intentional hole belongs to the independent Challenge statement, not the solution proof.

The paper is included as `Natural_cohomology_of_general_Steiner_bundles.pdf`. Source origins, licensing, dependency pins, and file hashes are recorded in `PROVENANCE.md`, `LICENSE`, and `SOURCE_MANIFEST.json`.
