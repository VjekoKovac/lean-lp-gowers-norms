# Verification and reproduction

The full, standalone targets are in `Challenge.lean`. This file imports Mathlib and contains the definitions specifying the meaning of all five statements. Its deliberate proof holes make it possible to review and compare the statements before any solution exists. `Solution.lean` uses the declarations proved by the separate `LpGowers` library. No Solution import reaches Challenge.

The full Lake build completed 8,004 jobs with cached dependencies. The axiom audit examined 1,017 project declarations, including the unconditional `LpGowers.theorem_1_3`. The independent Challenge specifies five full theorems and 30 additional statements. Both Comparator configurations passed with exit status zero. Lean, NanoDa and con-ron accepted the five full theorems together, and the same three kernels accepted all 35 declarations together. Con-ron checked 59,770 exported declarations for the five-theorem run and 60,107 for the 35-declaration run. Both configurations use the same standalone Challenge, whose SHA-256 is `cb60a895a3561c06a47e4c24b5f96b790f75ab052928902f3f7eeb8909a09a1e`.

## Toolchain and sources of trust

| Component | Version or revision |
| --- | --- |
| Lean | 4.36.0, Linux x86-64, release commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9` |
| Lake | 5.0.0-src+611c117 |
| Mathlib | `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, with transitive revisions in `lake-manifest.json` |
| Lean Comparator, leanexport, NanoDa, con-ron | Binaries shipped with the pinned Lean release |
| Local process isolation | bubblewrap 0.12.0 inside an offline user/network namespace |

The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. All proof-side arithmetic, including the binary exponents, uses kernel-checked terms. The development uses tactics including `norm_num`, `omega`, `positivity`, `ring`, and `linarith`. The declarations checked by Comparator are exported and replayed by Lean, NanoDa and con-ron. The axiom script examines transitive dependencies with `Lean.collectAxioms` and fails on any additional axiom. Its executable metadata check runs after the proofs have elaborated. Independent Python arithmetic spot checks in the review have no role in proof acceptance.

## Commands and evidence

Start at the repository root with elan installed. Run the following commands on Linux. The formalization uses the toolchain selected by the repository's `lean-toolchain` file.

```sh
lake exe cache get
lake build LpGowers Challenge Solution
lake env lean Axioms.lean
bash scripts/verify-comparator.sh comparator.components.json
bash scripts/verify-comparator.sh comparator.json
```

The supplementary metadata check uses Python with PyYAML 6.0.3 and jsonschema 4.26.0. The schema used for the archived result has SHA-256 `25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce`.

```sh
curl -fLsS https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/main/schema/v0.4.schema.json -o /tmp/formalization-v0.4.schema.json
python3 scripts/check-metadata.py /tmp/formalization-v0.4.schema.json
```

The review machine restricted network configuration inside nested sandboxes. The two archived Comparator runs invoked the following wrapper. The adapter creates an empty network namespace, verifies it has only loopback and no external routes, and invokes the toolchain's normal Comparator through bubblewrap. Ordinary Linux hosts and the GitHub workflow use the commands above.

```sh
scripts/with-offline-namespace.sh scripts/verify-comparator.sh comparator.components.json
scripts/with-offline-namespace.sh scripts/verify-comparator.sh comparator.json
```

| Evidence | Interpretation |
| --- | --- |
| [Lean build](checks/build.log) | Elaboration of all proof modules, Challenge and Solution |
| [Axiom audit](checks/axioms.log) | Individual printed reports for the selected results and a transitive audit of every exported declaration in the project namespace |
| [Confirmed statements](checks/components-comparator.log) | Comparison with the independent Challenge followed by external and default kernel checking |
| [All five target declarations](checks/five-target-comparator.log) | Exact five-target comparison, including both parts of Theorem 1.3 in one declaration |
| [Metadata and source checks](checks/metadata.log) | YAML schema validation, comparison-target inventory and source-level trust checks |

The metadata check reached all 175 project proof modules and all 45 vendored Brascamp–Lieb modules. The Lean source inventory has SHA-256 `5b898ff31f2f50c5325c47b8462afbf5abfe360fdf8759d8a4b0163212c2486c`. Warnings in Challenge identify its deliberate statement holes. The solution export, namespace-wide axiom audit, and external replays check the proof side. Independent mathematical reviews, including the specialized endpoint test for Theorem 1.3(b), are identified as AI reviews. [Statement and proof review](REVIEW.md) · [Young stability review](YOUNG-STABILITY-REVIEW.md)

## Source attribution

* The quantitative three-moment argument, the two adjoint degree-lowering estimates, the Euclidean exponent recursion, the leakage estimates, and the lattice energy presentation follow the manuscript with the specific variations identified in the review and source guide.
* The LCA inverse argument follows the nonnegative part of Eisner–Tao. It uses the compact-open small-difference argument and an explicit reduction to normalized indicators. The weighted Hölder and functional Loomis–Whitney stability estimates have formal proofs. The Euclidean sharp Young equality classification is proved by heat flow. Theorem 1.3(b) also proves uniform approximation at every positive tolerance. Its final diagonal Young step combines heat-flow localization, local compactness for approximate fixed points of the normalized Euler map, and the exact Gaussian classification. The proof covers the required output exponents $s=p+d-1\geq2$, including $s=2$.
* The proofs use Mathlib's `ENNReal.lintegral_prod_norm_pow_le`, `ENNReal.lintegral_Lp_add_le`, translation invariance of Haar measure, finite-product measure-preserving equivalences, finite-product Tonelli, Gaussian integration and real-power identities. Individual module imports record the exact dependencies.
* The checking script adapts the Palomar template at commit `2891de4c48955af824969a263d31b25e7a9a1406`. The workflow and comparison data are structured for the five-theorem goal. [Palomar template](https://github.com/PalomarRegistry/PalomarTemplate) · [Comparator documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#lake-comparator)

## Publication status

The included GitHub Actions workflow triggers on pushes, pull requests, and manual dispatch. The archived outputs were produced locally. A hosted Actions run requires this commit to reach GitHub. Palomar makes its own submission and editorial decisions. This archive records no hosted run, registry submission, or human mathematical review.
