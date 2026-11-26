---
title: Integration on a quotient by a cutoff
lean:
  - Lib/Adelic/QuotientMeasure/Basic.lean
decls:
  - New.IsCutoff
  - Subgroup.quotMeasure
  - New.IsCutoff.measurePreserving
  - New.lintegral_orbitMeasure_lintegral
  - New.identDistrib_orbitMeasure
  - New.hasCutoff_of_proper
  - New.integral_quotMeasure_tsum
  - New.isFiniteMeasure_quotMeasure_of_cocompact
  - New.isMulRightInvariant_of_finite_covolume
  - New.quotMean_tsum_eq_integral
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Integration on a quotient by a cutoff

This section builds the measure on a quotient $\Gamma \backslash X$ that the whole argument uses. It proves the unfolding formula, the independence of the choices, the existence of the measure for proper actions, Weil's formula for a discrete subgroup, the finite volume of a cocompact quotient, and the unimodularity of a group with a lattice. The later sections and the later volumes integrate over $\Gamma_V \backslash G$ only through these results.

### The classical quotient measure

Let $G$ be a locally compact group with a left Haar measure $dg$, and let $\Gamma$ be a closed subgroup with a left Haar measure $d\gamma$. If the modular functions of $G$ and $\Gamma$ agree on $\Gamma$, there is a unique $G$-invariant measure $d\dot g$ on $\Gamma \backslash G$ with
$$\int_G f(g) \, dg = \int_{\Gamma \backslash G} \int_\Gamma f(\gamma g) \, d\gamma \, d\dot g$$
for every $f \in C_c(G)$. This is Weil's integration formula. Bourbaki, *Intégration*, Chapter VII, §2, proves it, and the source compares its statements with this reference. For a discrete $\Gamma$ with counting measure, the inner integral is the sum $\sum_{\gamma \in \Gamma} f(\gamma g)$.

A second classical approach uses a *fundamental domain*: a measurable set $D \subset G$ that meets each orbit $\Gamma g$ in exactly one point. Then $\int_{\Gamma \backslash G} F \, d\dot g = \int_D F \, dg$ for every $\Gamma$-invariant $F$. Reduction theory makes such sets explicit, as finite unions of Siegel sets. A fundamental domain needs a measurable choice of one point in each orbit, and its shape depends on the group.

The source uses a third approach, which contains the second. A fundamental domain $D$ gives the function $\mathbf{1}_D$, whose sum over each orbit is $1$. Any measurable function with this property serves as well. Such a function is a smoothed fundamental domain. The source calls it a cutoff.

### Cutoffs and the quotient measure

Throughout this subsection, $H$ is a group that acts on a measurable space $X$, with a measurable inversion and a measurable action map $H \times X \to X$. The measure $\nu$ on $H$ is s-finite, and the measure $\mu$ on $X$ is s-finite and invariant under $H$.

**Definition (Cutoff).** A *cutoff* for the action of $H$, with the measure $\nu$, on $X$ is a measurable function $\beta : X \to [0, \infty]$ such that
$$\int_H \beta(h x) \, d\nu(h) = 1 \qquad \text{for every } x \in X.$$
The action *has a cutoff* if some cutoff exists.

Lean: `New.IsCutoff`, `New.HasCutoff` (Lib/Adelic/QuotientMeasure/Basic.lean).

For a subgroup $\Gamma$ of a group $G$ with the counting measure, a cutoff is a measurable $\beta \ge 0$ on $G$ with $\sum_{\gamma \in \Gamma} \beta(\gamma g) = 1$ for all $g$.

**Definition (Quotient measure).** Let $\beta_0$ be a cutoff chosen once for the action of $H$ with $\nu$ on $X$. The *orbit measure* is $\beta_0 \mu$, the measure on $X$ with density $\beta_0$ with respect to $\mu$. For a subgroup $\Gamma$ of a group $G$ and a measure $\mu$ on $G$, the *quotient measure* $\mu_{\Gamma}$ is the orbit measure for the counting measure on $\Gamma$, acting by left multiplication.

Lean: `Subgroup.quotMeasure`, `New.orbitMeasure`, `New.chosenCutoff`, `New.isCutoff_chosenCutoff` (Lib/Adelic/QuotientMeasure/Basic.lean).

The quotient measure is a measure on $G$, not on $\Gamma \backslash G$. An integral $\int F \, d\mu_\Gamma$ of a $\Gamma$-invariant function $F$ is the integral of $F$ over $\Gamma \backslash G$. For a space $V$, the measure $\mu_{\Gamma_V}$ on $G$ is the measure of $\Gamma_V \backslash G$ that the source uses, with the product of the Haar measures on $G_\infty$ and on $G_f$ and $\operatorname{vol}(K_0) = 1$.

Lean: `New.Space.quotMeasure` (Lib/Adelic/Reduction/FiniteVolume.lean).

**Remark (Formalization).** The chosen cutoff $\beta_0$ is `Classical.epsilon` of the property of being a cutoff. If no cutoff exists, $\beta_0$ is an unspecified function, and the results below assume that one exists. Even then, $\beta_0 \mu$ depends on the choice on sets that are not invariant. Only the integrals and distributions of invariant functions are canonical, by the theorem on independence below, and these are all that the source uses. Finding F-047 of the plan records this choice.

### Unfolding

**Theorem (Unfolding).** Assume that $\nu$ is invariant under $h \mapsto h^{-1}$, and let $\beta$ be a cutoff. Then the map $(x, h) \mapsto h x$ carries the product measure $(\beta\mu) \times \nu$ on $X \times H$ to $\mu$. In particular, if a cutoff exists, then $(x, h) \mapsto hx$ carries $\mu_H \times \nu$ to $\mu$, where $\mu_H$ is the orbit measure.

Lean: `New.IsCutoff.measurePreserving`, `New.measurePreserving_orbitMeasure` (Lib/Adelic/QuotientMeasure/Basic.lean).

*Proof.* Let $s \subset X$ be measurable. By Tonelli, the image of $(\beta \mu) \times \nu$ gives $s$ the mass
$$\int_H \int_X \mathbf{1}_s(h x) \beta(x) \, d\mu(x) \, d\nu(h) = \int_H \int_s \beta(h^{-1} x) \, d\mu(x) \, d\nu(h),$$
by the substitution $x \mapsto h^{-1} x$, which preserves $\mu$. Exchange the integrals again. The inner integral is $\int_H \beta(h^{-1} x) \, d\nu(h)$, which equals $\int_H \beta(h x) \, d\nu(h) = 1$ since $\nu$ is invariant under inversion. So the mass is $\mu(s)$. $\square$

**Corollary.** Assume that $\nu$ is invariant under inversion and that the action has a cutoff. For every measurable $f : X \to [0, \infty]$,
$$\int_X \int_H f(h x) \, d\nu(h) \, d\mu_H(x) = \int_X f \, d\mu.$$

Lean: `New.lintegral_orbitMeasure_lintegral` (Lib/Adelic/QuotientMeasure/Basic.lean).

*Proof.* Integrate $f$ against the image measure of the theorem, and use Tonelli on $X \times H$. $\square$

This is the classical formula $\int_G f = \int_{\Gamma \backslash G} \sum_\gamma f(\gamma g)$, with no fundamental domain. The source also proves that an $H$-stable property that holds almost everywhere for $\mu_H$ holds on a dense set, when $\mu$ is positive on open sets (`New.dense_of_ae_orbitMeasure`).

### Independence of the cutoff

**Theorem (Independence of the cutoff).** Assume that $\nu$ is invariant under inversion. Let $\beta$ be a cutoff, and let $F : X \to Y$ be a measurable function with $F(hx) = F(x)$ for all $h$ and $x$. Then $F$ has the same distribution under the orbit measure $\mu_H$ as under $\beta \mu$.

Lean: `New.identDistrib_orbitMeasure`, `New.IsCutoff.integral_orbitMeasure` (Lib/Adelic/QuotientMeasure/Basic.lean).

*Proof.* Let $\varphi \ge 0$ be measurable on $Y$. Write $\int \varphi(F) \beta_0 \, d\mu$ by unfolding along $\beta$: by the theorem on unfolding, $\mu$ is the image of $(\beta \mu) \times \nu$. Since $F$ is invariant, the integrand at $(x, h)$ is $\beta_0(hx) \varphi(F(x))$. The integral over $h$ of $\beta_0(hx)$ is $1$. So the integral is $\int \varphi(F) \beta \, d\mu$. Both laws give the same integral to every $\varphi$, so they agree. $\square$

So for an invariant integrable $f$ with values in a real normed space, $\int f \, d\mu_H = \int \beta f \, d\mu$ for every cutoff $\beta$. In particular, the volume $\mu_H(X)$ is the integral of the invariant function $1$, and it does not depend on the choice.

**Example.** Let $\Gamma = \mathbb{Z}$ act on $X = \mathbb{R}$ by translation, with $\mu$ the Lebesgue measure. The indicator of $[0, 1)$ is a cutoff, and so is $\beta(x) = \max(0, 1 - |x|)$, since $\sum_k \max(0, 1 - |x + k|) = 1$. For a $1$-periodic $F$, both give $\int_0^1 F(x) \, dx$. The volume of $\mathbb{Z} \backslash \mathbb{R}$ is $1$.

**Example.** For the trivial subgroup $\Gamma = \{1\}$, the constant function $1$ is a cutoff, and the quotient measure has the same integrals as $\mu$. The source proves $\mu_{\{1\}} = \mu$ (`New.quotMeasure_bot`).

### Existence of a cutoff

**Theorem (Existence of a cutoff).** Let $H$ be a topological group with a nonzero s-finite measure $\nu$ that is right invariant and finite on compact sets. Let $H$ act properly on a $\sigma$-compact Hausdorff space $X$, with the Borel structure. Then the action has a cutoff.

Lean: `New.hasCutoff_of_proper`, `New.hasCutoff_count` (Lib/Adelic/QuotientMeasure/Basic.lean).

*Proof.* Write $X = \bigcup_n K_n$ with $K_n$ compact. Let $t_n(x) = \nu\{h : hx \in K_n\}$. The set $\{h : hx \in K_n\}$ is compact, since the action is proper, so $t_n(x) < \infty$. Right invariance of $\nu$ gives $t_n(hx) = t_n(x)$. The sets $\{h : hx \in K_n\}$ cover $H$ and $\nu \ne 0$, so there is a least $n(x)$ with $t_{n(x)}(x) > 0$, and $n(x)$ is constant on orbits. Put
$$\beta(x) = \frac{\mathbf{1}_{K_{n(x)}}(x)}{t_{n(x)}(x)}.$$
Then $\int_H \beta(hx) \, d\nu(h) = t_{n}(x) / t_{n}(x) = 1$ with $n = n(x)$. $\square$

For a discrete subgroup $\Gamma$ of a locally compact, second countable, Hausdorff group $G$, the action of $\Gamma$ on $G$ is proper, and $\Gamma$ is countable. So the counting measure on $\Gamma$ satisfies the hypotheses, and the quotient measure $\mu_\Gamma$ is defined by a true cutoff. This applies to $\Gamma_V \subset G$ for every space $V$, since $\Gamma_V$ is discrete by [the discreteness of the rational points](/chapter/adeles-hermitian-spaces/#the-spaces-and-groups-of-the-source).

### Weil's formula for a discrete subgroup

From here on, $G$ is a locally compact, second countable, Hausdorff group with the Borel structure and a left Haar measure $\mu$, and $\Gamma$ is a discrete subgroup.

**Theorem (Weil's formula).** Let $f : G \to \mathbb{C}$ be integrable for $\mu$. Then $g \mapsto \sum_{\gamma \in \Gamma} f(\gamma g)$ is integrable for $\mu_\Gamma$, and
$$\int_G \sum_{\gamma \in \Gamma} f(\gamma g) \, d\mu_\Gamma(g) = \int_G f \, d\mu.$$

Lean: `New.integral_quotMeasure_tsum`, `New.integrable_quotMeasure_tsum`, `New.integral_quotMeasure_tsum_eq` (Lib/Adelic/QuotientMeasure/Basic.lean).

*Proof.* By the theorem on unfolding, $(g, \gamma) \mapsto \gamma g$ carries $\mu_\Gamma \times (\text{counting measure})$ to $\mu$. Fubini's theorem for this measure preserving map gives the integrability of $(g, \gamma) \mapsto f(\gamma g)$ on the product, the integrability of the inner sum, and the identity. An integral against the counting measure is a sum. $\square$

**Remark (Formalization).** The sum $\sum_\gamma f(\gamma g)$ is a sum in the sense of Mathlib, which is $0$ for a family that is not summable. Fubini gives summability for almost every $g$, so the junk value occurs only on a null set and does not change the integral.

### Finite volume and unimodularity

**Definition (Cocompact).** A subgroup $N$ of $G$ is *cocompact* if there is a compact set $C \subset G$ such that every $g \in G$ has a translate $\gamma g \in C$ with $\gamma \in N$.

Lean: `Subgroup.IsCocompact` (Lib/Adelic/QuotientMeasure/Basic.lean).

**Proposition.** If $\Gamma$ is cocompact, then $\mu_\Gamma$ is a finite measure.

Lean: `New.isFiniteMeasure_quotMeasure_of_cocompact` (Lib/Adelic/QuotientMeasure/Basic.lean).

*Proof.* Let $C$ be the compact set. For each $g$, the number of $\gamma \in \Gamma$ with $\gamma g \in C$ is at least $1$. So
$$\mu_\Gamma(G) \le \int_G \#\{\gamma : \gamma g \in C\} \, d\mu_\Gamma(g) \le \mu(C) < \infty,$$
where the middle step is the corollary on unfolding applied to $\mathbf{1}_C$. $\square$

The quotient measure is never zero: unfolding carries $\mu_\Gamma \times (\text{count})$ to $\mu \ne 0$.

**Theorem (A group with a lattice is unimodular).** If $\mu_\Gamma$ is a finite measure, then $\mu$ is right invariant.

Lean: `New.isMulRightInvariant_of_finite_covolume` (Lib/Adelic/QuotientMeasure/Basic.lean).

*Proof.* Right translation by $g$ carries $\mu$ to $\Delta(g) \mu$, where $\Delta$ is the modular function. Right translation commutes with the left action of $\Gamma$. By the independence of the cutoff, applied along this translation, the quotients for $\mu$ and for $\Delta(g)\mu$ have the same volume. The second volume is $\Delta(g)$ times the first. The first volume is finite by hypothesis and nonzero by the remark above. So $\Delta(g) = 1$. $\square$

**Remark (Formalization).** The name of the hypothesis of finite volume begins with the character `_`, which in Lean marks a hypothesis that the proof does not name. Finding F-086 of the plan lists it as an unused named hypothesis. The proof does use it. The last step divides by $\mu_\Gamma(G)$, and instance search finds the finiteness from the hypothesis in the context. Without it the theorem is false: the group of affine maps $x \mapsto ax + b$ of $\mathbb{R}$ is not unimodular, and its trivial subgroup is discrete. The source applies the theorem with $\Gamma = \{1\}$ to show that compact groups are unimodular, and it proves that a right invariant Haar measure is also invariant under inversion. The unimodularity of $G$ and of $G_f$ for spaces is in [the finiteness of classes](/chapter/reduction-theory/#finite-volume-and-the-finiteness-of-classes).

Under right invariance, the source proves that every s-finite right invariant measure $\nu$ is $d \mu$ for some $d \in [0, \infty]$ (`New.exists_eq_smul_haar`). The constant can be $0$ or $\infty$.

### The mean over a compact abelian quotient

The theta series of later volumes are sums over a lattice in a vector group. For these the source uses the Haar probability measure on the compact quotient. Let $B$ be a Polish, locally compact abelian group with a Haar measure $\mu$, and let $B_0$ be a discrete subgroup with $B / B_0$ compact. Assume that $\mu_{B_0}$ is finite. For a continuous $B_0$-periodic $F$, the *mean* $M(F)$ is the integral of $F$ over $B / B_0$ against the Haar probability measure, read at coset representatives.

Lean: `New.quotMean`, `New.IsContPeriodic`, `New.average_quotMeasure_eq_quotMean` (Lib/Adelic/QuotientMeasure/Basic.lean).

**Proposition (Mean of a periodized function).** Let $F$ be integrable on $B$, and let $G$ be continuous and $B_0$-periodic with $\sum_{\gamma \in B_0} F(\gamma + x) = G(x)$ for every $x$, the sum being convergent. Then
$$M(G) = \frac{1}{\mu_{B_0}(B)} \int_B F \, d\mu.$$

Lean: `New.quotMean_tsum_eq_integral` (Lib/Adelic/QuotientMeasure/Basic.lean).

*Proof.* The average of $G$ against $\mu_{B_0}$ is $M(G)$, since the image of $\mu_{B_0}$ in $B / B_0$ is translation invariant and hence a multiple of the Haar probability measure. The integral of $G$ against $\mu_{B_0}$ is $\int F \, d\mu$ by Weil's formula. Divide by the mass. $\square$

The covolume $\mu_{B_0}(B)$ is finite by hypothesis and positive by the remark on nonzero quotient measures. With the Poisson summation formula, this proposition gives the constant terms of theta series.
