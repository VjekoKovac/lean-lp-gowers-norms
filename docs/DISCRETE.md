# The discrete-cube results

The declaration `LpGowers.Discrete.discreteClaim` proves all three parts of Theorem 1.5. The critical exponents are defined in §1.3 and the paper proves the theorem in §8. The dimensions $m$ below include zero. The parameter $p=k+1$ ranges over the positive integers. [Kovač and Rogers, arXiv:2609.08916v2](https://arxiv.org/abs/2609.08916v2)

| Result | Lean declaration in `LpGowers.Discrete` |
|---|---|
| $[\mathbf1_A]_{U^{d,p}}^{p2^d}=\mathcal P_{d,p}(A)$ on the counting measure | `gowers_finIndicator` |
| Energies multiply on finite Cartesian products, including general pure tensors of functions supported on the cube | `energy_piFinset`, `weightedEnergy_piFinset`, `exists_weighted_tensor_test` |
| The polynomial loss in the powered functional inequality, with any fixed degree in the ambient dimension, can be removed exactly | `functionExponent_of_polynomial_loss` |
| $\mathcal P_{d,p}(\{0,1\}^m)=(2^p+2d)^m$ | `full_binary_box_energy` |
| The minimum defining $t$ and maximum defining $q$ are both attained when $n\ge2$ | `criticalT_isLeast`, `criticalQ_isGreatest` |
| Proposition 8.1(c) and (d) are equivalent by removal of a dimension-independent constant using tensor powers | `exists_tensor_test`, `setExponent_iff_uniform_constant` |
| Proposition 8.1(b) implies (c), and $q_{d,p,n}t_{d,p,n}\le p2^d$ | `setExponent_of_functionExponent`, `criticalQ_mul_criticalT_le` |
| All four conditions of Proposition 8.1 are equivalent, and $q_{d,p,n}t_{d,p,n}=p2^d$ | `dyadic_extension`, `functionExponent_of_one_dimensional`, `critical_product` |
| For all $d\ge1$, $p\ge1$, the sharp binary scalar inequality holds with $t=\log_2(2^p+2d)$ | `binary_scalar_sharp` |
| The weighted binary energy on the interval is exactly $(f(0)^{2^d}+f(1)^{2^d})^p+2d(f(0)f(1))^{2^{d-1}p}$, yielding the full one-dimensional functional inequality at $q=2^d p/t$ | `weighted_binary_energy`, `binary_one_dimensional_bound` |
| Both sharp binary-cube critical exponents in all ambient dimensions, as in Theorem 1.5(a) | `binaryClaim` |
| The upper and lower logarithmic corrections for fixed $d,p$, as in Theorem 1.5(b) | `largeSideClaim` |
| The additive $o(1)$ asymptotic at fixed $n,p$, including the factorial correction in Theorem 1.5(c) | `largeDegreeClaim` |
| $\log_2(2^p+2d)\le t_{d,p,2}$ | `binary_criticalT_lower` |
| **Both binary critical exponents at $(d,p)=(2,2)$** are $t=3$ and $q=8/3$ | `binary_critical_two_two` |
| The same exact binary exponents hold at $(d,p)=(3,1)$ | `binary_critical_three_one` |
| The parameter pairs $(d+1,1)$ and $(d,2)$ have equal critical exponents for every side length | `critical_succ_one` |
| $t_{d,p,n}\le t_{d,1,n}+p-1$ and $t_{d,p,n}\le d+p$ | `criticalT_le_shift`, `criticalT_le_add` |
| For $d\ge2$, $t_{d,p,n}\le t_{2,1,n}+d+p-3$ | `criticalT_le_additive_energy` |
| For $n\ge 2(d+1)$, $t_{d,p,n}\ge d+p-(d+p)\log(2(d+1))/\log n$. In particular $t_{d,p,n}\to d+p$ at fixed $d,p$ | `largeSide_coarse_lower`, `criticalT_tendsto_add` |
| At fixed $p$, $t_{d,p,2}/\log_2(2d)\to1$ as $d\to\infty$ | `binary_criticalT_log_ratio` |

## How the proofs work

The energy counts shared increments in $A-A$, weighted by the $p$-th powers of the numbers of valid bases. The empty vertex forces each base to lie in $A$. The singleton vertices force every increment to lie in $A-A$. Given a base, the $d$ singleton vertices uniquely determine the increments. This gives $\mathcal P_{d,1}(A)\le |A|^{d+1}$. Multiplying the right side by $|A|^{p-1}$ gives the general coarse bound in §8. Testing the full interval with bases and nonnegative increments below $N=\lfloor n/(d+1)\rfloor$ gives the complementary large-side estimate.

The full binary interval admits either zero increments, with $2^p$ base choices, or a single increment equal to $+1$ or $-1$, with one base tuple per signed direction. Cartesian product factorization gives the exact energy in every dimension. A separate coding argument records the $p$ bases, the opposite corner of the first cube, and one vertex per binary digit of the direction index. This gives $t_{d,p,2}\le p+1+\lceil\log_2d\rceil$ for $d\ge1$ and proves the ratio limit for $n=2$.

For weighted binary inputs, the same enumeration gives the exact one-dimensional energy. The scalar inequality follows from the monotonicity established in the proof of Lemma 12 of Crmarić, Kovač and Shiraki. The Lean proof uses an exponential substitution and bounds the remaining logarithmic derivative using the tangent line to the logarithm. The $p=1$ case follows from the quadratic identity for $p=2$. [Crmarić, Kovač and Shiraki, arXiv:2507.01359](https://arxiv.org/abs/2507.01359)

For $d=p=2$, the eight vertices comprise two parallel four-vertex faces. Project a configuration to the three neighbors of any fixed vertex. Their coordinatewise majority recovers the central vertex. The resulting four points determine the configuration. This gives an injection into $A^3$. For a function $f$, apply the arithmetic–geometric mean inequality over the eight choices of center. Each vertex belongs to three neighbor triples. Injectivity bounds the sum for each triple by $(\sum f^{8/3})^3$. This specialized proof uses the mathlib theorem `NNReal.geom_mean_le_arith_mean_weighted`. The article proves the general assertion using Proposition 8.1 and a hyperbolic-cosine inequality.

To prove functional attainment, the integral marginal identity first gives admissibility of $q=1$ on the full lattice. Indicator tests give an upper bound on every admissible $q$. Finite support makes the $\ell^q$ functional continuous in $q>0$. A sequence of admissible exponents tending to the supremum proves attainment directly.

The reverse implication of Proposition 8.1 uses the triangle inequality from Appendix A. The mixed Gowers–Cauchy–Schwarz estimate proves this inequality. The dyadic proof then bounds the functional by $(K+1)2^{1/q}\lVert f\rVert_q$ on a support of at most $2^K$ points. At each induction step the strict superlevel set above $\lVert f\rVert_q/(2^K)^{1/q}$ has at most $2^K$ points. Applied on the $n$-ary cube, the loss is polynomial in the ambient dimension. Tensor powers remove that loss and give the exact critical product.

## General binary result and the critical product identity

The current proof includes Appendix A's triangle inequality for integer outer exponents on countable discrete abelian groups. Expanding the product of sums at all vertices and applying the mixed Gowers–Cauchy–Schwarz estimate to each term yields the triangle inequality. The dyadic reduction then proves the full critical product identity. The one-dimensional weighted binary energy has the exact formula in §8. The hyperbolic-cosine monotonicity argument and dimension induction give the optimal functional estimate, and the full binary cube witnesses sharpness for all parameters. See `DiscreteMixed.lean`, `DiscreteTriangle.lean`, `DiscreteTensorization.lean`, `DiscreteScalar.lean`, `DiscreteBinaryInterval.lean`, and `BinaryTheorem.lean`.

## The logarithmic correction at fixed degree

`largeSideClaim` proves both bounds in Theorem 1.5(b). For the lower bound, a compactly supported continuous approximation to the Gaussian is translated and dilated into the open unit interval. Sampling that function on the lattice of mesh $1/n$ gives convergent Riemann sums for its norm and its full configuration integral. The inequality at the attained exponent $t_{d,p,n}$ gives a lower bound for $(t_{d,p,n}-d-p)\log_2 n$. Taking test ratios arbitrarily close to the sharp continuum Gaussian ratio gives the coefficient $((d+p)\log_2(d+p)-p\log_2p-2d)/2$. The upper bound reduces to $(d,p)=(2,1)$. Quantitative stability on $\mathbb Z$ controls inputs away from sharpness. Inputs close to a point mass satisfy a stronger local bound from the expansion of the four-fold energy. The resulting positive absolute constant works for every $d,p$ and every $n\ge 2$. See `DiscreteLargeSide`, `DiscreteRiemannSamples` and `DiscreteAdditiveGap`.

## The additive entropy term at fixed side length

`entropy_largeDegree_lower` proves that for each $n\ge2$, $p\ge1$ and $\eta>0$, all sufficiently large $d$ satisfy $t_{d,p,n}\ge ((n-1)\log_2(2d)-\log_2((n-1)!))/H_{n-1}-\eta$. Here $H_{n-1}$ is the base-two entropy of the binomial distribution of parameters $n-1,1/2$. The proof tests the functional exponent against the binomial weights and uses its exact product identity with the set exponent.

The matching upper estimate uses the trial exponent $t=((n-1)\log_2(2d)-\log_2((n-1)!))/H_{n-1}+\delta$. Group the increments by the number $l$ of nonzero directions. A pattern fitting the interval has $l\le n-1$. At $l=n-1$ every step has absolute value one, and the signs fix the unique base point. At lower ranks, Hölder on the base-point sum costs at most $n^{p-1}$. For a normalized input $g$, weighted AM–GM bounds the product over vertices by $2^{-t H(Y)}$, where $Y$ is the corresponding integer-weighted sum of $l$ fair bits. The formal proof of $H(Y)\ge H_l$ applies the Lubell–Yamamoto–Meshalkin inequality to each antichain fiber, followed by Jensen's inequality. The strict decrease of $H_l/l$ follows from a one-step comparison of Hamming layer sizes, using a single atom of a binomial probability law. These arguments prove the results used from Proposition 10 and Corollary 7 of the previous discrete-cube paper. [Beker, Crmarić and Kovač, arXiv:2409.12579](https://arxiv.org/abs/2409.12579)

For diffuse inputs the lower-rank terms tend uniformly to zero and the top term is at most $2^{-H_{n-1}\delta}<1$. For a function concentrated at a single integer, two distinct vertices in every nonzero pattern contribute a product of distinct input weights. Together these contributions are bounded by $1-\sum_j g(j)^2$, while the zero pattern contributes at most $\sum_j g(j)^2$. Rescaling an arbitrary input and applying the dimension extension gives the upper bound for the actual critical set exponent. The two one-sided inequalities combine into the limit in `largeDegreeClaim`. The relevant modules are `DiscretePatternEnergy`, `DiscreteEntropyComparison`, `BinomialEntropy`, `DiscreteEntropyFactors`, `DiscreteEntropyRates`, `DiscreteConcentratedPatterns`, `DiscreteEntropyUniform`, and `DiscreteEntropyUpper`.
