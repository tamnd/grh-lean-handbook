---
title: Unfolding
lean:
  - Lib/Adelic/QuotientMeasure/IwasawaUnfolding.lean
  - Lib/Adelic/QuotientMeasure/UnfoldingInStages.lean
  - Lib/Adelic/QuotientMeasure/MovingTheQuotient.lean
decls:
  - New.integral_tsum_orbit
  - New.exists_integral_comp_quotMeasure_eq_smul
  - New.integral_quotMeasure_stages
  - New.integral_cutoff_swap
  - New.lintegral_iwasawa
  - New.integral_quotMeasure_iwasawa
  - New.integral_quotMeasure_eq_zero_of_mean
  - New.integral_quotMeasure_eq_zero_of_twist
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Unfolding

Most integrals of automorphic forms in this book are computed by one method: a sum over a discrete group or an orbit is integrated over $\Gamma \backslash G$ and *unfolded* to an integral over a larger quotient. The Rankin-Selberg method and the computation of the inner product of a Poincaré series with a form are the model cases (Bump, *Automorphic Forms and Representations*, Chapter 1, treats them for $\mathrm{SL}_2(\mathbb{Z})$). This section gives the forms of unfolding that the source proves, in the language of the quotient measure of [Section 2](/chapter/reduction-theory/#integration-on-a-quotient-by-a-cutoff). It ends with two criteria for an integral over $\Gamma \backslash G$ to vanish.

Throughout, $G$ is a locally compact, second countable, Hausdorff group with the Borel structure and a left Haar measure $\mu$. For a discrete subgroup $\Gamma$, the measure $\mu_\Gamma$ is the quotient measure, and a function $F$ is *left $\Gamma$-invariant* if $F(\gamma g) = F(g)$ for all $\gamma \in \Gamma$ and $g \in G$.

### Unfolding over an orbit

The model case is a Poincaré series. Let $\Gamma_\infty \subset \Gamma$ be the stabilizer of a cusp and let $\phi$ be a function on $\Gamma_\infty \backslash G$. Then
$$\int_{\Gamma \backslash G} \sum_{\gamma \in \Gamma_\infty \backslash \Gamma} \phi(\gamma g) \, dg = \int_{\Gamma_\infty \backslash G} \phi(g) \, dg,$$
when the left side converges absolutely. The terms $\phi(\gamma g)$ are indexed by the orbit of a point under $\Gamma$, and the stabilizer of that point is $\Gamma_\infty$. The source states the identity in this form: a countable set $Y$ with an action of a group $\Lambda$, a family of functions $k_y$ on $G$ that is equivariant, and one orbit.

**Theorem (Unfolding over an orbit).** Let $\Lambda$ act on a countable set $Y$, and let $i : \Lambda \to G$ be an injective homomorphism with discrete image $\Gamma$. Let $k_z : G \to \mathbb{C}$, for $z \in Y$, be measurable functions with
$$k_{\gamma z}(i(\gamma) x) = k_z(x) \qquad (\gamma \in \Lambda, \ z \in Y, \ x \in G).$$
Fix $y \in Y$, let $S$ be the image under $i$ of the stabilizer of $y$, and let $D$ be the orbit of $y$. Then $k_y$ is left $S$-invariant. Assume that
$$\int_G \sum_{z \in Y} |k_z(x)| \, d\mu_\Gamma(x) < \infty, \quad \text{or that } k_y \text{ is integrable for } \mu_S.$$
Then $k_y$ is integrable for $\mu_S$, and
$$\int_G \sum_{z \in D} k_z \, d\mu_\Gamma = \int_G k_y \, d\mu_S = \sum_{z \in D} \int_G k_z \, d\mu_\Gamma.$$

Lean: `New.integral_tsum_orbit`, `New.integral_tsum_orbit_of_lt_top_or_integrable`, `New.integral_tsum_orbit_eq_integral_stabilizer` (Lib/Adelic/QuotientMeasure/IwasawaUnfolding.lean).

*Proof.* The invariance of $k_y$ under $S$ is the equivariance with $\gamma$ in the stabilizer. For the identity, the source proves a more general statement for a block $C \subset Y$ in place of the point $y$ (`New.integral_tsum_block`). Let $\beta$ be the chosen cutoff for $S$. For a point $z$ of the orbit, the sum of $\beta(i(\gamma) x)$ over the $\gamma$ that carry $z$ to $y$ is a sum of $\beta$ over one $S$-orbit, so it is $1$ (`New.tsum_cutoff_smul_mem_eq_one`). For a nonnegative family $g_z$, unfold $\int \beta(x) g_y(x) \, d\mu$ along $\Gamma$ and substitute $z = \gamma^{-1} y$ in the term of $\gamma$. This gives the identity for $g$ with no hypothesis (`New.lintegral_tsum_block`). Apply it to $|k_z|$. Under either hypothesis, the two sides are finite, and the identity for $k$ follows by splitting into real and imaginary parts and dominated convergence for the sum over $D$. $\square$

The two hypotheses are the two ways the argument meets this theorem. When the sum converges absolutely on $\Gamma \backslash G$, one gets the integral over $S \backslash G$. When $k_y$ is known to be integrable on $S \backslash G$, one gets the absolute convergence of the sum for free.

### Pulling back along a surjection

**Proposition.** Let $H$ be a second locally compact, second countable, Hausdorff group with a Haar measure $\nu$, let $\Lambda \subset H$ be discrete, and assume that $\mu$ and $\nu$ are right invariant. Let $\pi : H \to G$ be a continuous surjective homomorphism with $\pi(\Lambda) \subset \Gamma$. Then there is a real number $c$ such that, for every measurable left $\Gamma$-invariant $F$ with values in a real Banach space,
$$\int_H F(\pi(r)) \, d\nu_\Lambda(r) = c \int_G F \, d\mu_\Gamma.$$

Lean: `New.exists_integral_comp_quotMeasure_eq_smul` (Lib/Adelic/QuotientMeasure/UnfoldingInStages.lean).

*Proof.* Push $\nu_\Lambda \times (\text{count on } \Gamma)$ forward along $(r, \gamma) \mapsto \gamma \pi(r)$. The result $\kappa$ is right invariant, because the sum of $f$ over the orbit $\Gamma \pi(r)$ is left $\Lambda$-invariant in $r$. By the uniqueness of Haar measure for right invariant measures ([Section 2](/chapter/reduction-theory/#integration-on-a-quotient-by-a-cutoff)), $\kappa = d\mu$ with $d \in [0, \infty]$. Unfolding along $\pi$ shows that $F \circ \pi$ under $\nu_\Lambda$ has the law of $F$ under $d \mu_\Gamma$. Take $c$ to be the real number $d$, with $c = 0$ if $d = \infty$. $\square$

**Remark (Formalization).** The constant $c$ can be $0$. It is $0$ if $d = 0$, and also if $d = \infty$, since the source reads an infinite extended real as $0$. In that case the identity is true, but both sides may carry no information. A user of the proposition who needs $c \ne 0$ must prove it.

### Unfolding in stages

The next identity computes an integral over $\Gamma \backslash G$ as an integral over a family of smaller quotients. Let $i : H \to G$ be injective with $i(\Lambda) = \Gamma$, and suppose that $G$ is parametrized as $i(h) T(z)$, with $z$ in a measure space $(Z, m)$, so that the measure $m \times \nu$ goes to $\mu$.

**Theorem (Unfolding in stages).** Let $i : H \to G$ be an injective homomorphism, let $\Lambda \subset H$ be discrete with $i(\Lambda) = \Gamma$, and let $T : Z \to G$ be a map such that $(z, h) \mapsto i(h) T(z)$ carries $m \times \nu$ to $\mu$, where $m$ is s-finite. Let $F$ be measurable, left $\Gamma$-invariant and integrable for $\mu_\Gamma$. Then $z \mapsto \int_H F(i(a) T(z)) \, d\nu_\Lambda(a)$ is integrable for $m$, and
$$\int_G F \, d\mu_\Gamma = \int_Z \int_H F(i(a) T(z)) \, d\nu_\Lambda(a) \, dm(z).$$

Lean: `New.integral_quotMeasure_stages` (Lib/Adelic/QuotientMeasure/UnfoldingInStages.lean).

*Proof.* The map $((z, a), l) \mapsto i(l) i(a) T(z)$ carries $m \times \nu_\Lambda \times (\text{count})$ to $\mu$, by unfolding the second factor and then the hypothesis on $T$. So $F$ under $\mu_\Gamma$ has the law of $(z, a) \mapsto F(i(a) T(z))$ under $m \times \nu_\Lambda$. Fubini finishes. $\square$

For a closed subgroup $i(H)$, the source takes for $m$ the quotient measure of $i(H) \backslash G$, carried by $G$ (`New.cosetMeasure`, `New.integral_quotMeasure_eq_integral_cosetMeasure`). This is the textbook form $\int_{\Gamma \backslash G} = \int_{i(H) \backslash G} \int_{\Lambda \backslash H}$.

### Moving the quotient to the other variable

The seesaw and the theta correspondence integrate a function of two variables, one in a subgroup $R$ and one in $G$, which is invariant under a discrete group acting on both. The quotient can be taken in either variable.

**Theorem (Moving the quotient).** Let $R$ be a subgroup of a group $G$, with s-finite left invariant measures $\nu$ on $R$ and $\mu$ on $G$. Let $\Lambda$ be a countable group with a homomorphism $i : \Lambda \to R$. Let $\beta : G \to [0, \infty]$ be measurable with $\sum_{l \in \Lambda} \beta(i(l) x) = 1$ for every $x \in G$. Let $F$ on $R \times G$ be measurable with
$$F(i(l) s, i(l) x) = F(s, x) \qquad (l \in \Lambda, \ s \in R, \ x \in G),$$
and assume that $(s, x) \mapsto \beta(s) F(s, x)$ is integrable for $\nu \times \mu$. Then
$$\int_G \beta(x) \int_R F(s, x) \, d\nu(s) \, d\mu(x) = \int_R \beta(s) \int_G F(s, x) \, d\mu(x) \, d\nu(s).$$

Lean: `New.integral_cutoff_swap` (Lib/Adelic/QuotientMeasure/MovingTheQuotient.lean).

*Proof.* Let $\Lambda$ act on $R \times G$ diagonally through $i$. Both $(s, x) \mapsto \beta(x)$ and $(s, x) \mapsto \beta(s)$ are cutoffs for this action. The function $F$ is invariant. By the independence of the cutoff, its integrals against the two weighted product measures agree. Fubini, which the integrability hypothesis allows on both sides, gives the two iterated integrals. $\square$

The left side is the integral over $\Lambda \backslash G$ of $\int_R F(s, x) \, ds$, and the right side is the integral over $\Lambda \backslash R$ of $\int_G F(s, x) \, dx$. Note that the integrability hypothesis is on the side with the cutoff in $s$.

### Integration in Iwasawa coordinates

The constant term of an automorphic form along a parabolic subgroup $P = NM$ is an integral over $(\Gamma \cap N) \backslash N$. The classical formula $dg = \delta_P(m)^{-1} \, dn \, dm \, dk$ for $g = nmk$ reduces integrals over $\Gamma \backslash G$ of $N$-invariant functions to integrals over $M$ and $K$. The source proves a version of this for quotients, with an unknown nonzero constant in place of the normalization of measures. The Iwasawa decomposition of the unitary groups of the source is in [Witt and Iwasawa](/chapter/adeles-hermitian-spaces/#witts-theorem-and-the-iwasawa-decomposition-in-the-source).

In this subsection $G$ is a Polish, locally compact group, $\mu$ is a Haar measure on $G$ that is also right invariant, $M$ is a topological group with a Haar measure $\nu$ that is also right invariant, $K$ is a compact subgroup of $G$ with Haar measure $\kappa$, and $N$ is a subgroup of $G$ with a Haar measure $\lambda$. The map $i : M \to G$ is a continuous homomorphism and $w : M \to \mathbb{R}$ is continuous with $w > 0$.

**Theorem (Iwasawa integration).** Assume that $N$ is closed and unimodular, that every $g \in G$ is $n \, i(m) \, k$ with $n \in N$, $m \in M$ and $k \in K$, and that
$$\int_N f(i(m) n i(m)^{-1}) \, d\lambda(n) = w(m) \int_N f(n) \, d\lambda(n)$$
for every $m$ and every measurable $f \ge 0$. Then there is $d \in [0, \infty]$ with
$$\int_K \int_M \int_N f(i(m) n k) \, d\lambda(n) \, d\nu(m) \, d\kappa(k) = d \int_G f \, d\mu$$
for every measurable $f : G \to [0, \infty]$.

Lean: `New.lintegral_iwasawa` (Lib/Adelic/QuotientMeasure/IwasawaUnfolding.lean).

*Proof.* Let $J_f(y)$ be the triple integral of $f(i(m) n y k^{-1})$. Moving $y$ divides $J_f(y)$ by a value of $w$. So $J_f(1)$ is an average of the values $J_f(y)$ against a weight. After Fubini and a translation in $y$, this is $\int_G d(x) f(x) \, d\mu(x)$, where $d(x)$ is an integral of the weight that does not depend on $x$. $\square$

**Remark (Formalization).** The constant $d$ may be $\infty$, for example if $i$ has a noncompact kernel. The theorem does not identify $d$, and the argument does not need its value. The next theorem shows that $d \ne 0$ under its hypotheses, from the case $f = 1$.

**Theorem (Unfolding in Iwasawa coordinates).** Keep the hypotheses of the last theorem, except that $N$ need not be assumed unimodular. Assume also that $i(a) \in N$ only for $a = 1$. Let $D$ be countable and $\delta : D \to M$ injective. Let $\Gamma$ be a discrete subgroup of $G$ that contains every $i(\delta(e))$, such that each $g \in \Gamma$ has $g \, i(\delta(e)) \in N$ for some $e \in D$, and such that $\Gamma \cap N$ is cocompact in $N$. Let $\alpha$ be an s-finite measure on $M$ with
$$\int_M f \, d\nu = \int_M \sum_{e \in D} f(\delta(e) m) \, d\alpha(m)$$
for measurable $f \ge 0$. Then there is a real $c \ne 0$ with the following property. Let $F : G \to \mathbb{C}$ be measurable, left invariant under $N$ and under $\Gamma$, and such that $(m, k) \mapsto w(m) F(i(m) k)$ is integrable for $\alpha \times \kappa$. Then $F$ is integrable for $\mu_\Gamma$, and
$$\int_G F \, d\mu_\Gamma = c \int_{M \times K} w(m) F(i(m) k) \, d(\alpha \times \kappa)(m, k).$$

Lean: `New.integral_quotMeasure_iwasawa`, `New.exists_equiv_prod_subgroupOf` (Lib/Adelic/QuotientMeasure/IwasawaUnfolding.lean).

*Proof.* The group $\Gamma \cap N$ is cocompact in $N$, so its quotient has finite volume ([Section 2](/chapter/reduction-theory/#integration-on-a-quotient-by-a-cutoff)), and $N$ is unimodular by the theorem on groups with a lattice. The last theorem gives $d$, and $d \ne 0$ because the left side is a product of nonzero masses for $f = 1$. Every element of $\Gamma$ is uniquely $i(\delta(e)) \gamma$ with $\gamma \in \Gamma \cap N$. With this, the measure $w \cdot (\alpha \times \kappa) \times \lambda_{\Gamma \cap N}$, in the coordinates $n \, i(m) k$, unfolds along $\Gamma$ to $d \mu$. Since $F$ is $N$-invariant, $F$ under $\mu_\Gamma$ has the law of $(m, k) \mapsto F(i(m) k)$ under a multiple of $w (\alpha \times \kappa)$. The constant $c$ is the ratio of the masses. $\square$

In the application to constant terms, $M$ is a Levi factor, $\alpha$ is a quotient measure for $\Gamma \cap M$, and the set $\delta(D)$ is a set of representatives.

### Two vanishing criteria

The argument often needs to show that an integral over $\Gamma \backslash G$ vanishes. The classical reason is a character: if $F(ug) = \chi(u) F(g)$ for a nontrivial character $\chi$ of a compact group of $u$, then the integral of $F$ vanishes. The source proves two criteria of this kind that need no compactness.

**Theorem (Vanishing by a mean).** Let $\Gamma \subset H \subset G$ with $\Gamma$ discrete and $H$ closed. Let $F : G \to V$ be continuous and left $\Gamma$-invariant, with $V$ a complex Banach space. Let $\kappa$ be a probability measure on a measurable space $C$, and let $t_x(b) \in H$ for $x \in G$ and $b \in C$, measurable in $b$. Let $d \ge 0$ be real with the property that right translation by $t_x(b)$ carries the Haar measure of $H$ to $d$ times itself. Assume that, for some $a \in \mathbb{C}$ with $a \ne d$,
$$\int_C F(s \, t_x(b) \, x) \, d\kappa(b) = a F(s x) \qquad (s \in H, \ x \in G).$$
Then $\int_G F \, d\mu_\Gamma = 0$.

Lean: `New.integral_quotMeasure_eq_zero_of_mean` (Lib/Adelic/QuotientMeasure/UnfoldingInStages.lean).

*Proof.* Suppose that the integral $I$ of $F$ is not $0$. Then $F$ is integrable for $\mu_\Gamma$, since the integral of a function that is not integrable is $0$. Unfold in stages along $H$: $I$ is an integral over $H \backslash G$ of the integral of $s \mapsto F(sx)$ over $\Gamma \backslash H$. So there is $x$ with $I_x = \int_H F(sx) \, d\sigma(s) \ne 0$, where $\sigma$ is the quotient measure of $\Gamma \backslash H$. Integrate $F(s \, t_x(b) \, x)$ over $s$ and $b$. In one order, the hypothesis gives $a I_x$. In the other order, the right translation by $t_x(b)$ multiplies $\sigma$ by $d$, so each inner integral is $d I_x$. So $a I_x = d I_x$ and $a = d$, a contradiction. $\square$

**Corollary (Vanishing by a twist).** Let $F : G \to V$ be continuous and left $\Gamma$-invariant, with $V$ a complex Banach space. Let $u \in G$ and $c \in \mathbb{C}$ with $|c| = 1$, $c \ne 1$ and
$$F(u y) = c F(y) \qquad \text{for all } y \in G.$$
Then $\int_G F \, d\mu_\Gamma = 0$.

Lean: `New.integral_quotMeasure_eq_zero_of_twist` (Lib/Adelic/QuotientMeasure/UnfoldingInStages.lean).

*Proof.* Let $S$ be the set of $s \in G$ such that $\|F(s t u y) - c F(s t y)\| = \|F(t u y) - c F(t y)\|$ for all $t, y$. It is a closed subgroup, since $F$ is continuous. It contains $\Gamma$, by the invariance of $F$, and it contains $u$, since $|c| = 1$. For $s \in S$, the case $t = 1$ gives $F(s u y) = c F(s y)$. Apply the theorem with $H = S$, $\kappa$ the point mass, $t_x(b) = u$ and $a = c$. Here $d$ is the factor by which right translation by $u$ scales the Haar measure of $S$, a positive real. Since $|c| = 1$ and $c \ne 1$, the number $c$ is not a positive real, so $c \ne d$. $\square$

**Remark (Formalization).** Neither criterion assumes that $F$ is integrable. If $F$ is not integrable for $\mu_\Gamma$, the conclusion holds by the convention that such an integral is $0$, and it says nothing about convergence. The proof uses this convention in its first step. A user who needs the value of a convergent integral must prove integrability separately. The climbing step of the spanning argument applies the corollary to a twisted function of the Poincaré series, in [the spanning theorem](/chapter/theorem-b-plan/), and its integrability is proved there.

### Where the argument uses this section

The unfolding over an orbit computes the periods of the Weil representation in the library. Unfolding in stages, with the cutoff of Section 2 for a closed subgroup, writes the seesaw integral as a sum over cosets in the proof of Theorem A. Moving the quotient is used in the series period of the unfolding of Theorem B, and the twist criterion is used in its climbing step. The Iwasawa form computes the constant term in the tower of Siegel-Weil integrals.
