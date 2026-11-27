# Estimates for Lᵖ variants of Gowers norms

This Lean 4 project proves all five introductory theorems of Vjekoslav Kovač and Keith M. Rogers. The standalone Challenge states the original five results. [arXiv:2609.08916v2](https://arxiv.org/abs/2609.08916v2) · [Statement-by-statement mathematical specification](docs/SOURCE.md)

| Theorem | Formalized result |
| --- | --- |
| 1.1, improved log-convexity | For each degree, one positive gap works for all locally compact second-countable abelian groups without a compact open subgroup and all Haar normalizations. |
| 1.2, Lebesgue estimates | The bound holds at and above the endpoint. Above the endpoint every near-extremizer is close to the indicator of one compact open coset with the specified amplitude. |
| 1.3, sharp Euclidean estimates | The constant is optimal. Nonzero finite-norm extremizers are precisely the Gaussians up to null sets. Every sufficiently near-extremizing input is close in its critical norm to a Gaussian of exactly the same norm, uniformly over the inputs. |
| 1.4, degree lowering | Both directions of the inequality, equality at $p=1$, and simultaneous near-factorization of the joint autocorrelation density and all its faces for $p\ne 1$. |
| 1.5, discrete cubes | Both critical exponents for side length two, both logarithmic bounds as the side length grows, and the additive binomial-entropy asymptotic as the degree grows. |

The formalization authors are Vjekoslav Kovač and Keith M. Rogers, as designated by the project maintainer. AI contributions and reviews are identified in the review records. The source matched the uploaded TeX byte for byte. [Source and proofs](docs/SOURCE.md) · [AI statement and proof review](docs/REVIEW.md) · [Euclidean proof details](docs/EUCLIDEAN-REVIEW.md) · [AI review of Theorem 1.3(b)](docs/YOUNG-STABILITY-REVIEW.md) · [Discrete proof details](docs/DISCRETE.md) · [Reused Brascamp–Lieb proof](docs/UPSTREAM.md)

Challenge contains deliberate statement holes. Solution imports the proved library and is compiled independently of Challenge. The proof audit permits only `propext`, `Classical.choice` and `Quot.sound`. [Versions, commands and actual output](docs/VERIFICATION.md)

The GitHub workflow starts on any push, including the initial push to `main`. It builds Lean, audits axiom dependencies, and reports the two Comparator outcomes in separate jobs. The verification records distinguish local replay, hosted Actions, and registry submission. [Workflow](.github/workflows/lean.yml)
