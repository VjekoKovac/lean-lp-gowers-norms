# Estimates for Lᵖ variants of Gowers norms

A partial Lean 4 formalization of the five introductory theorems of Vjekoslav Kovač and Keith M. Rogers. All five full statements are transcribed in an independent Challenge. Theorems 1.1, 1.2, 1.4 and 1.5, and part (a) of 1.3, have formal proofs. Part 1.3(b) on Euclidean near-extremizers remains open in Lean. [arXiv:2609.08916v2](https://arxiv.org/abs/2609.08916v2) · [Statement-by-statement mathematical specification](docs/SOURCE.md)

| Theorem | Unconditional results in this repository | Remaining proof |
| --- | --- | --- |
| 1.1, improved log-convexity | Complete. A single positive gap for each degree works across all LCA groups without compact open subgroups and all Haar normalizations | — |
| 1.2, Lebesgue estimates | Complete. The bound includes the endpoint and every Haar normalization. Above the endpoint the uniform stability theorem gives a single compact open coset, with its exact amplitude | — |
| 1.3, Euclidean sharp estimates | Part (a) complete. The sharp inequality, optimality, and the characterization of nonzero, finite-critical-norm equality cases as Gaussians up to null sets | Part (b). Prove uniform relative closeness of near-extremizers to a Gaussian of exactly the same critical norm |
| 1.4, degree lowering | Complete. Both directions of the degree-lowering estimate, equality at p = 1, and simultaneous factorization of the joint density and every face for p ≠ 1 | — |
| 1.5, discrete cubes | Complete. Both binary critical exponents, the two logarithmic bounds as the side length grows, and the additive binomial-entropy asymptotic as the degree grows | — |

The formalization authors are Vjekoslav Kovač and Keith M. Rogers, as designated by the project maintainer. AI contributions and reviews are identified in the review records. The source matched the uploaded TeX byte for byte. [Source and proofs](docs/SOURCE.md) · [AI statement and proof review](docs/REVIEW.md) · [Euclidean proof-author checks](docs/EUCLIDEAN-REVIEW.md) · [Discrete proof details](docs/DISCRETE.md) · [Reused Brascamp–Lieb proof](docs/UPSTREAM.md)

## Verification

From the repository root on Linux with elan and bubblewrap installed, run

```sh
lake exe cache get
lake build LpGowers Challenge Solution
lake env lean Axioms.lean
bash scripts/verify-comparator.sh comparator.components.json
bash scripts/verify-comparator.sh comparator.json
```

The component configuration checks the proved statements. The five-theorem configuration is a separate completion check and currently fails. Challenge contains deliberate statement holes. Solution imports the proved library and is compiled independently of Challenge. The proof audit permits only `propext`, `Classical.choice` and `Quot.sound`. [Versions, commands and actual output](docs/VERIFICATION.md)

The GitHub workflow starts on any push, including the initial push to `main`. It builds Lean, audits axiom dependencies, and reports the two Comparator outcomes in separate jobs. The project is pending completion of the five-theorem check before submission to Palomar. [Workflow](.github/workflows/lean.yml) · [Palomar metadata](formalization.yaml) · [Reference project](https://github.com/roos-j/lean-dfr)
