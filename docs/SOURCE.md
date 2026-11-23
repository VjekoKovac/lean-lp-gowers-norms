# Mathematical source and proof correspondence

Vjekoslav Kovač and Keith M. Rogers, *Estimates for Lᵖ variants of Gowers norms*, arXiv:2609.08916v2, 14 October 2026. The versioned record lists 42 pages, the categories math.CA and math.CO, and the MSC codes 26D15, 11B30, 43A70 and 94A17. [Abstract and version history](https://arxiv.org/abs/2609.08916v2) · [Full text](https://arxiv.org/html/2609.08916v2)

The uploaded `gen_Gow_fun.tex` is byte-for-byte identical to the 117,140-byte file with that name in the v2 source archive. Its SHA-256 is `0efad7429445becdf4b8b36b834cc712a00111925659c124935fa9fa64d75b40`. The downloaded gzip archive had SHA-256 `21948d0e1d59ab547aeb35ea3d9760f6229da32d9c56dd3e257afc7e91d15e9d`. The comparison covered the whole TeX file. [Versioned source archive](https://arxiv.org/src/2609.08916v2)

## Common conventions

Let $G$ be a Hausdorff, second-countable, locally compact abelian group in additive notation, with additive Haar measure $\mu$. Allow every normalization of $\mu$. All five target statements concern measurable functions with **finite nonnegative values**, although an integral or functional may be infinite. For $d\ge1$, $h\in G^d$, and $0<p<\infty$, put

$$R_df(h)=\int_G\prod_{S\subseteq\{1,\ldots,d\}} f\!\left(x+\sum_{i\in S}h_i\right)\,d\mu(x),\qquad U_{d,p}(f)=\left(\int_{G^d}(R_df(h))^p\,d\mu^d(h)\right)^{1/(2^d p)}.$$

For these inputs $U_d(f)=U_{d,1}(f)$. Write $L_q(f)=(\int f^q\,d\mu)^{1/q}$, $D_q(f,g)=L_q(|f-g|)$, $q=2^dp/(d+p)$ and $a_d=d/(2^d-1)$. A nonzero input in a stability or equality clause means $f$ is not almost everywhere equal to zero. Near-extremiser errors are relative to the indicated norm. Specifically, for each target relative error $\eta>0$, one can choose $\delta>0$ depending only on $\eta$ and the displayed fixed parameters, so the conclusion with error at most $\eta$ holds for every $0<\varepsilon<\delta$. This expands the uniform little-$o$ convention of §1.5.

## Statements and source arguments

### 1.1. Uniform improvement of log-convexity

For each integer $d\ge2$ there is an $\varepsilon_d\in(0,1)$ such that every eligible $G$ with no compact open subgroup and every nonnegative measurable $f$ satisfy

$$U_d(f)\le (1-\varepsilon_d) U_{d-1}(f)^{\theta}U_{d+1}(f)^{1-\theta},\qquad \theta=d/(3d-2).$$

The same $\varepsilon_d$ works for every group, Haar measure and function. In §6 the two degree-lowering and interpolation arguments constrain three moments of each of $R_df$ and $R_{d-1}f$. Stability of Loomis–Whitney and a diagonal integral estimate then give a nearly closed set under addition. For $d>2$ this step uses a two-dimensional slice. Fournier’s uniform strict improvement of Young’s $L^{4/3}*L^{4/3}\to L^2$ bound contradicts this concentration. A pointwise strict inequality for each fixed $f$ would leave the uniform gap open.

### 1.2. Estimate on LCA groups and near-extremisers

For $d\ge2$ and $a_d\le p<\infty$, $U_{d,p}(f)\le L_q(f)$ for every nonnegative measurable $f$. For $p>a_d$, let $0<L_q(f)<\infty$ and suppose $U_{d,p}(f)\ge(1-\varepsilon)L_q(f)$. For $\varepsilon$ sufficiently small in terms of $d,p$, there exist a compact open subgroup $H$ and $x_0\in G$ with

$$D_q\!\left(f,\frac{L_q(f)}{\mu(H)^{1/q}}\mathbf1_{x_0+H}\right)\le o_{d,p}(1)L_q(f),\qquad \varepsilon\downarrow0.$$

Section 3 iterates the forward degree-lowering inequality to reach $p=a_d$ and interpolates to the other exponents. For stability, different powers are used for $a_d<p<1$ and for $p\ge1$. The resulting function nearly extremises the Eisner–Tao Gowers inequality. Taking absolute values removes the polynomial phase, and continuity estimates for positive powers transfer the coset approximation to $f$.

### 1.3. Sharp Euclidean constant, equality and near-equality

Take $G=\mathbb R^n$ with Lebesgue measure, integers $d\ge2$, $n\ge1$, and $1\le p<\infty$. The least constant in $U_{d,p}(f)\le K L_q(f)$ for all nonnegative measurable $f$ is

$$K=\left(\frac{2^{2d}p^p}{(d+p)^{d+p}}\right)^{n/(2^{d+1}p)}.$$

For $0<L_q(f)<\infty$, equality holds precisely when $f$ agrees almost everywhere with $g(x)=c\exp(-(x-x_0)^TM(x-x_0))$, where $c>0$, $x_0\in\mathbb R^n$ and $M$ is real symmetric positive definite. If $U_{d,p}(f)\ge(1-\varepsilon)K L_q(f)$ with $0<L_q(f)<\infty$ and sufficiently small $\varepsilon$, there exists such a $g$ with $L_q(g)=L_q(f)$ and $D_q(f,g)\le o_{d,p,n}(1)L_q(f)$ as $\varepsilon\downarrow0$.

Section 4 applies Beckner’s sharp Young inequality along each increment and telescopes its constants. Evaluation at $e^{-\pi|x|^2}$ witnesses optimality. For classification and stability, the final Young inequality is nondegenerate even at $p=1$. Christ’s stability result for sharp Young gives the Gaussian, followed by a power change and normalization.

### 1.4. Degree lowering and a simultaneous factorization

Fix $d\ge2$, finite positive $p,p_1,\ldots,p_d$, and real $\theta_i$ with $\sum_i\theta_i=1$ and

$$\frac{1-1/p}{d-1}=\theta_i(1-2/p_i)\qquad(1\le i\le d).$$

Write $U=U_{d,p}(f)$ and $P=\prod_i U_{d-1,p_i}(f)^{\theta_i}$. If $0<p\le1$ and every $\theta_i>0$, then $U\le P$. If $1<p<\infty$, $\theta_1>0$, and $\theta_i<0$ for $i>1$, then $U\ge P$ for $f$ nonzero modulo null sets with every involved functional finite. These are the two branches of part (a).

In part (b) additionally require $p\ne1$ and all functionals positive and finite. Assume $U\ge(1-\varepsilon)P$ in the forward branch, or $P\ge(1-\varepsilon)U$ in the reverse branch. Put $A=\|R_df\|_p^p$ and $B_i=\|R_{d-1}f\|_{p_i}^{p_i}$. For sufficiently small $\varepsilon$ a **single** family of nonnegative measurable $r_1,\ldots,r_d$ on $G$, each of integral one, satisfies

$$\|(R_df)^p-A\textstyle\bigotimes_j r_j\|_1\le o(1) A,\qquad \|(R_{d-1}f)^{p_i}-B_i\textstyle\bigotimes_{j\ne i}r_j\|_1\le o(1) B_i\quad(1\le i\le d).$$

The latter product uses the remaining coordinates in their original order. Both errors tend to zero uniformly for fixed $d,p,(p_i),(\theta_i)$. The proof of (a) in §2 identifies the marginals of $R_df$ with $(R_{d-1}f)^2$ and applies the two adjoint Loomis–Whitney inequalities of Bennett and Tao with $a=p$, $b_i=p_i/2$. Section 5 combines stability of Hölder with near-factorization in Loomis–Whitney to obtain (b).

### 1.5. Dimension-free exponents on discrete cubes

Fix integers $d\ge2$, $p\ge1$, $n\ge2$. For every dimension $m\ge0$ work on $\mathbb Z^m$ with counting measure and put $B_{m,n}=\{0,\ldots,n-1\}^m$. Let $q_{d,p,n}$ be the supremum of all real $s>0$ such that $U_{d,p}(f)\le\|f\|_{\ell^s}$ for all $m$ and all nonnegative $f$ supported in $B_{m,n}$. For finite $A\subseteq B_{m,n}$, its energy $E_{d,p}(A)$ counts the ordered tuples of $p$ base points and $d$ common increments whose $p$ cubes have every vertex in $A$. Let $t_{d,p,n}$ be the infimum of all $t>0$ such that $E_{d,p}(A)\le |A|^t$ for every $m,A$. All logarithms below are to base two.

1. For $n=2$, $t_{d,p,2}=\log_2(2^p+2d)$ and $q_{d,p,2}=2^dp/\log_2(2^p+2d)$.
2. There is an absolute $c>0$. For fixed $d,p$ and $n\to\infty$, with $C_{d,p}=((d+p)\log_2(d+p)-p\log_2 p-2d)/2$,

   $$d+p-(1+o_{d,p}(1))C_{d,p}/\log_2 n\le t_{d,p,n}\le d+p-c/\log_2 n.$$

3. For fixed $n,p$ and $d\to\infty$,

   $$t_{d,p,n}=\frac{(n-1)\log_2(2d)-\log_2((n-1)!)}{H_{n-1}}+o_{n,p}(1),\quad H_k=-\sum_{j=0}^k a_j\log_2 a_j,\quad a_j=2^{-k}\binom{k}{j}.$$

Proposition 8.1 separately proves attainment of both exponents and $q_{d,p,n}t_{d,p,n}=2^dp$. Section 8 reduces the problem to dimension one by tensorization. The binary case enumerates increments and uses a scalar hyperbolic-cosine inequality. Part (b) tests truncated discrete Gaussians for the lower estimate and compares to the $p=1$ energy for the upper estimate. Part (c) groups increments by the number of nonzero directions and uses the entropy of weighted sums of independent Bernoulli variables. The paper cites Beker–Crmarić–Kovač for the $p=1$ results and additional entropy estimates.

## Formal proof routes for the completed theorems

**Theorem 1.1.** The Lean proof normalizes the adjacent Gowers norms by rescaling the input and the Haar measure. It proves the two moment chains in §6. For the final contradiction it uses the upper three moments, simultaneous degree-lowering stability, and the set-to-box argument to approximate the autocorrelation in both L¹ and squared L² by an indicator of a rectangular box. Permuting increments preserves the autocorrelation. Comparing the box with its coordinate transpositions therefore gives the near-unit measure of every side. Freezing all but two increments preserves the exact slice autocorrelations. A quantitative averaging argument chooses one slice with both small error and a controlled input mass. The two-dimensional leakage estimate and near closure under addition produce a compact open subgroup by the small-difference argument mentioned in the paper after its proof. This gives the contradiction with the group hypothesis, uniformly in the group, measure and input. The unnormalized conclusion includes inputs with zero or infinite adjacent functionals.

**Theorem 1.2.** The endpoint bound is obtained from iterated symmetric degree lowering. Interpolation gives the entire range of part (a). For (b), the argument reduces both open exponent ranges to the ordinary nonnegative inverse theorem. The latter is proved using the diagonal inverse Young inequality with integer output exponent. A near-extremizing input is close to a normalized indicator, and a mixed Young estimate controls the change in its autocorrelation under that replacement. For a near-extremal indicator, the overlap argument yields a compact open coset. The proof tracks its measure, normalizes its amplitude, and transfers the result back through powers and the original normalization. The manuscript cites Eisner–Tao for the corresponding ordinary inverse theorem. The needed nonnegative statement is proved within this project.

**Theorem 1.4.** The two adjoint inequalities are obtained from the exact coordinate marginal identity, Hölder and the functional Loomis–Whitney inequality. For stability, weighted Hölder near equality compares the normalized densities in each sign regime. The proof of functional Loomis–Whitney stability contracts a chosen coordinate and glues the lower-dimensional marginals to one compatible family of one-dimensional probability factors. Tensor-product error estimates and unnormalization give the simultaneous L¹ bounds of the source.

**Theorem 1.3(a).** The iterated sharp Young inequality yields the claimed constant, and direct integration over a Gaussian proves optimality. Conversely, equality descends through the iteration to a normalized sharp diagonal Young extremizer. In the three-map Brascamp–Lieb representation, equality forces vanishing of the heat-flow defect at every positive time. Each smoothed input then has an affine logarithmic gradient. The almost-everywhere limit is an exponential quadratic, and its finite positive mass forces its quadratic part to be negative definite. This identifies every extremizer, including at $p=1$. The paper invokes sharp Young and its extremizers. The Lean proof reuses the geometric Brascamp–Lieb inequality and derives the needed Young characterization. [Euclidean proof review](EUCLIDEAN-REVIEW.md)

**Theorem 1.5.** The discrete proof counts the configuration energy, tensorizes its one-dimensional functional estimate, and proves attainment and the critical product relation. Gaussian sampling gives the logarithmic lower correction in (b), and the additive energy bound gives the upper correction. At fixed side length the binomial test gives the lower half of (c). Grouping signed increment patterns by their rank, bounding the entropy of antichain fibers, and treating concentrated and diffuse inputs gives the upper half with additive error tending to zero. [Discrete proof details](DISCRETE.md)

**Theorem 1.3(b).** Section 4 invokes the Euclidean sharp Young near-extremizer theorem of Michael Christ. The reduction to this result and the transfer of norm, powers and relative error are formalized. The uniform positive-tolerance inverse theorem for arbitrary nonnegative inputs remains open in this project. [Christ, Near-extremizers of Young’s inequality for Euclidean groups](https://doi.org/10.4171/RMI/1055)
