# AI review of Theorem 1.3(b)

An AI reviewer compared the Euclidean stability statement with the arXiv paper and checked the mathematical steps below. The reviewer contributed `YoungKernelCompact` and `YoungUnitInput`. The review of those two modules is an author check. The heat path, Euler equation, strict derivative, local compactness argument and standalone Challenge were written by other contributors.

Two additional AI reviewers independently compared the arXiv statement with the Challenge. One coauthored the heat-path and Gaussian-orbit lemmas and checked the intermediate-value argument, affine normalization, and local compactness. The other contributed the orbit-crossing and signed power-map proofs and reviewed the uniform quantifiers, the $s=2$ endpoint, the exact-equality case of the inverse lemma, and the transfer back from the final Young exponent in §4.

## Source and scope

Kovač and Rogers normalize the input, propagate near equality to the last Young inequality, and pass from a Gaussian approximation of a power of the input back to the original function. Write $s=p+d-1$, $q=2s/(s+1)$, and $u=f^{2^{d-1}p/s}$ for the normalized input $f$. Then $u$ has unit $L^q$ norm. Equation (4.5) asserts near optimality of its autocorrelation in $L^s$. The input for (4.6) is the nonnegative diagonal case of Christ’s Theorem 1.1. Christ treats independently chosen inputs using rearrangement and an inverse Riesz–Sobolev inequality. The Lean argument below proves the specialization required here. [Kovač and Rogers, §4, equations (4.4)–(4.6)](https://arxiv.org/html/2609.08916v2#S4) · [Christ, theorem and proof method](https://arxiv.org/abs/1112.4875)

For integers $d\ge2$, $n\ge1$ and finite real $p\ge1$, the last exponent satisfies $s\ge 2$, including $s=2$ for $d=2,p=1$. The original input is nonnegative, is measurable up to null sets, and has finite, nonzero critical norm. The Gaussian family in the Challenge permits all centers and positive-definite symmetric precision matrices. For each requested relative error $\eta>0$ the threshold $\delta(d,p,n,\eta)>0$ is uniform over the eligible inputs. The Gaussian must have exactly the input norm.

## Argument checked

1. **Preservation of near equality.** The first two geometric Brascamp–Lieb rows contain the same density $u^q$. Taking their common heat flow keeps them equal. Applying the geometric inequality with Gaussian factors and integrating preserves the initial lower bound for the trilinear pairing. Testing against the evolved third density, which still has mass one, gives the same relative lower bound for the diagonal moment. See `diagonal_heat_path`. Geometric Brascamp–Lieb heat flow and direct Young heat-flow monotonicity have separate proofs in the literature. [Bennett, Carbery, Christ and Tao, §2](https://arxiv.org/abs/math/0505065) · [Bennett and Bez, Corollary 2](https://arxiv.org/abs/0806.2086)
2. **Crossing a prescribed distance.** As time tends to infinity, the heat-smoothed unit density approaches the heat kernel *at the same time* in $L^1$. Taking $q$-th roots turns this estimate into strong $L^q$ approximation, and gives continuity at time zero. Distance to the set of unit Gaussians is 1-Lipschitz. The intermediate value theorem therefore supplies an input at any positive distance between the initial distance and zero, with the original near-optimality bound. Only existence of a crossing time is used. A Gaussian arbitrarily close to the infimum suffices for affine normalization. See `crossing_unit_input` and `normalize_near_gaussian`. Christ uses this same level-crossing argument for nonnegative Young triples in his later proof of quantitative stability. The formalization uses the local compactness argument below to obtain the qualitative conclusion required by §4 of the source. [Christ, *Young’s Inequality Sharpened*, §3, p. 266, Lemma 6 and the argument following it](https://doi.org/10.1007/978-3-030-72058-2_7)
3. **Approximate Euler equation.** Let $R(t)=\int u(y)u(y+t)\,dy$, and let $K$ be the sharp bound on $\int R^s$ for unit inputs. The dual score $b(x)=K^{-1}\int R(t)^{s-1}u(x+t)\,dt$ satisfies $\|b\|_{q'}\le 1$ and $\int ub=K^{-1}\int R^s$. Stability of Hölder gives $\|u-b^{q'-1}\|_q\to0$ along a near-extremizing sequence. This uses a uniform estimate on unit inputs. See `near_youngEuler`.
4. **Compact derivative.** Extend the two power maps to real functions by $x\mapsto x|x|^{a-1}$. At $s=2$ the inner power is the identity. At all finite $s\ge2$, the outer exponent $q'-1=(s+1)/(s-1)>1$. At a centered Gaussian its derivative multiplies by a decaying Gaussian. In each term of the derivative this multiplication follows a convolution or correlation with a fixed Gaussian. Writing $r$ for the input exponent of each convolution, approximating its weighted kernel rows by simple $L^q(L^{r'})$ functions gives finite-rank operators converging in operator norm. See `gaussian_youngUpdate_precompact`.
5. **Strong compactness and contradiction.** If $T$ has compact strict derivative $L$ at a reference Gaussian, $T-L$ has Lipschitz constant at most one half on a small ball. For approximate fixed points $u_j$ there, take a subsequence on which $Lu_j$ converges. The identity $u_j=((u_j-Tu_j)+Lu_j)+(T-L)(u_j)$ makes that subsequence Cauchy. At the fixed positive crossing distance one can normalize into this same ball. A strong limit of the transformed unit extremizing subsequence is again a unit input and attains the sharp value. The exact Young equality theorem identifies it as Gaussian. Pulling it back contradicts the prescribed distance. See `exists_local_approx_fixed_precompact` and `YoungUnitInput.gaussian_of_strong_extremizing_limit`.

## Independent checks

The reviewer ran the following component build and inspected the transitive axiom lists using `#print axioms` on the six declarations below. All six reports listed exactly `propext`, `Classical.choice`, and `Quot.sound`.

```sh
lake build LpGowers.YoungEuler LpGowers.YoungOrbitPath LpGowers.YoungGaussianUpdate
```

```lean
import LpGowers.YoungEuler
import LpGowers.YoungOrbitPath
import LpGowers.YoungGaussianUpdate
#print axioms LpGowers.diagonal_heat_path
#print axioms LpGowers.crossing_unit_input
#print axioms LpGowers.near_youngEuler
#print axioms LpGowers.gaussian_youngUpdate_precompact
#print axioms LpGowers.exists_local_approx_fixed_precompact
#print axioms LpGowers.YoungUnitInput.gaussian_of_strong_extremizing_limit
```

The reviewer then built `Solution` and ran this separate check of the assembled proof.

```sh
lake build Solution
lake env lean --stdin <<'LEAN'
import Solution
#check LpGowers.theorem_1_3
example : LpGowers.EuclideanTheorem := LpGowers.theorem_1_3
#print axioms LpGowers.theorem_1_3
#print axioms LpGowers.diagonal_young_stability_above_two
LEAN
```

```text
LpGowers.theorem_1_3 : LpGowers.EuclideanTheorem
'LpGowers.theorem_1_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'LpGowers.diagonal_young_stability_above_two' depends on axioms: [propext, Classical.choice, Quot.sound]
```

A separate AI reviewer specialized the public theorem to $d=2$, $n=1$, $p=1$. Lean accepted the stability statement with critical exponent $4/3$, sharp constant $(16/27)^{1/8}$, equal Gaussian norm, and the relative error bound. The standalone Challenge matched its previously reviewed revision byte for byte (SHA-256 `cb60a895a3561c06a47e4c24b5f96b790f75ab052928902f3f7eeb8909a09a1e`). The release’s five-theorem Comparator run is recorded separately in the [verification records](VERIFICATION.md).
