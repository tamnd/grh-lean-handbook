---
title: Steep parameters and Laplace data
lean:
  - New/Appendix/DiscreteSeries/SteepParameters.lean
decls:
  - New.DiscreteSeries.exists_unitary_mul_posSemidef
  - New.HCParam.phase
  - New.DiscreteSeries.IsSteep
  - New.DiscreteSeries.subOnePair
  - New.HCParam.laplaceIntegrand
  - New.DiscreteSeries.IsLaplaceDatum
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Steep parameters and Laplace data

This section fixes the notation of the chapter and states the hypotheses of Laplace's method. It also proves the polar decomposition, which section 3 uses.

### Notation

Let $n$ and $m$ be finite sets, and let $\varepsilon : n \to \{\pm1\}$ and $\eta : m \to \{\pm 1\}$ be vectors of signs. Let $l$ be a parameter for $U(\varepsilon)$ and $k$ a parameter for $U(\eta)$. Write $\mu$ and $\mu'$ for the highest weights of their lowest $K$-types. In the notation of [Discrete series through one matrix coefficient](/chapter/discrete-series/) we have $\mu = \lambda + \rho - 2\rho_c$, where $\rho_c$ is the half sum of the positive compact roots. We use $\mu$ and $\mu'$ also for the diagonal matrices with these entries.

For a matrix $g \in U(\varepsilon)$ we write $a$ for its block diagonal part and $y = g - a$ for its noncompact part. So $a_{ij} = g_{ij}$ if $\varepsilon_i = \varepsilon_j$ and $a_{ij} = 0$ otherwise. The element $g$ is in $K$ if and only if $y = 0$. Unless we say otherwise, $\|\cdot\|$ is the Frobenius norm $\|A\|^2 = \sum_{ij}|A_{ij}|^2$.

### The phase

**Definition (Phase).** For a pair $(Y, Y')$ of an $n \times n$ and an $m \times m$ matrix, the phase difference is
$$ \Phi(Y, Y') = \operatorname{tr}(\mu Y) - \operatorname{tr}(\mu' Y'). $$
Lean: `New.HCParam.phase` (New/Appendix/DiscreteSeries/SteepParameters.lean).

The name comes from the Gaussian shape of section 5. Near the identity, $c_l(g)$ is close to $\exp(\operatorname{tr} \mu \log g)$ times a positive number. To first order $\log g \approx g - 1$, so $\operatorname{tr}\mu(g-1)$ is the first order phase of $c_l$ at $g$. For $g$ near $1$ in $U(\varepsilon)$ the matrix $g - 1$ is close to an element of the Lie algebra, which is anti-Hermitian on $K$. So the first order phase is close to imaginary.

### Steep parameters

**Definition (Steep parameter).** Let $X$ be a finite set, $M \geq 0$, and let $e : X \sqcup \{0, \dots, M-1\} \to n$ be a bijection. Let $B$ be real. The parameter $l$ is *steep* for $(B, e)$ if the following hold.

1. On $X$ the sign is $+1$: $\varepsilon_{e(x)} = 1$.
2. On the other indices the signs alternate and begin with $+1$: $\varepsilon_{e(i)} = (-1)^i$.
3. On $X$ the weight is zero: $\mu_{e(x)} = 0$.
4. On the other indices the weight strictly decreases in $i$.
5. On the other indices the weight lies in $[-3B, -B]$.

Lean: `New.DiscreteSeries.IsSteep` (New/Appendix/DiscreteSeries/SteepParameters.lean).

So a steep weight is zero on a compact block $U(X)$ and is strongly negative on the rest. If $B \geq 1$, then every index outside $X$ has weight at most $-B \leq -1$. Section 3 uses exactly this: the weight punishes every entry of $g - 1$ in a row outside $X$.

**Example.** Let $X = \emptyset$ and $M = 3$, so $\varepsilon = (+1, -1, +1)$ and $U(\varepsilon) \cong U(2,1)$. A weight $\mu = (-B, -2B, -3B)$ with $B$ a positive integer satisfies conditions 4 and 5. So any parameter $l$ with this lowest $K$-type is steep for $(B, e)$, where $e$ is the identity.

**Example.** Let $M = 0$ and let all signs be $+1$, so $U(\varepsilon) = U(X)$ is compact. Then $K = U(X)$ and $\rho_c = \rho$, so $\mu = \lambda - \rho$. The parameter $l = 2\rho$ (that is, entries $\#n - 1, \#n - 3, \dots, 1 - \#n$ in some order) has $\mu = 0$. It is steep for every $B$. Its representation is the trivial one, and $c_l = 1$ on $U(X)$.

### The integrand

Let $S$ be a group and let $j : S \to U(\varepsilon) \times U(\eta)$ be a homomorphism. For $s \in S$ write $j(s) = (g, g')$, and write
$$ \operatorname{sub}(s) = (g - 1, g' - 1). $$
Lean: `New.DiscreteSeries.subOnePair` (New/Appendix/DiscreteSeries/SteepParameters.lean).

**Definition (Laplace integrand).** For a function $\varphi : S \to \mathbb{C}$ the Laplace integrand is
$$ \theta(s) = c_l(g)\, \overline{c_k(g')}\, e^{-\varphi(s)}. $$
Lean: `New.HCParam.laplaceIntegrand` (New/Appendix/DiscreteSeries/SteepParameters.lean).

If $\varphi = \Phi \circ \operatorname{sub}$, then $e^{-\varphi(s)}$ removes the first order phases of both coefficients. Since $c_l(1) = c_k(1) = 1$ and $\varphi(1) = 0$, we have $\theta(1) = 1$.

### Laplace data

Let $\tau : X \to m$ be a map. Write $\iota_e$ for the $n \times X$ matrix whose column $x$ is the standard basis vector at $e(x)$, and $\iota_\tau$ for the $m \times X$ matrix whose column $x$ is the standard basis vector at $\tau(x)$.

**Definition (Laplace datum).** The tuple $(l, k, j, \tau, B, e, \varphi)$ is a *Laplace datum* if $l$ is steep for $(B, e)$ and the following hold for all $s, t \in S$.

1. (Phase.) $\Phi(\operatorname{sub}(s)) = \varphi(s)$.
2. (Traces.) $\operatorname{tr}(g - 1) = \operatorname{tr}(g' - 1)$.
3. (Additivity.) $\varphi(st) = \varphi(s) + \varphi(t)$.
4. (Imaginary.) $\operatorname{Re}\varphi(s) = 0$.
5. (Second block.) For $x \in X$, $\eta_{\tau(x)} = 1$ and $\mu'_{\tau(x)} = 0$.
6. (Second weight.) For all $i, i' \in m$, $\mu'_i \geq 0$, and $\mu'_i \leq 3B$ if $\eta_i \neq \eta_{i'}$.
7. (Diagonal.) For every unitary $u \in U(X)$ there is $s \in S$ with
$$ \operatorname{sub}(s) = \big(\iota_e (u - 1) \iota_e^*,\ \iota_\tau (u - 1)\iota_\tau^*\big). $$

Lean: `New.DiscreteSeries.IsLaplaceDatum` (New/Appendix/DiscreteSeries/SteepParameters.lean).

Condition 6 says that $\mu'_i \leq 3B$ for every $i$ as soon as $\eta$ takes both signs. If $U(\eta)$ is compact, condition 6 only asks $\mu' \geq 0$. Condition 7 says that the image of $j$ contains a copy of $U(X)$ that acts on the coordinates $e(X)$ in the first factor and on $\tau(X)$ in the second, and acts trivially on the other coordinates.

Conditions 1 and 3 together say that $\Phi \circ \operatorname{sub}$ is a homomorphism to $(\mathbb{C}, +)$. This is a strong condition, since $\operatorname{tr}\mu(g - 1)$ is not additive on all of $U(\varepsilon)$. In sections 7 and 8 the group $S$ is the stabilizer of a flag, and on this group the phase is the sum of certain matrix coefficients.

**Example.** Take the compact example above with $n = m = X$, $\varepsilon = \eta = 1$, $M = 0$, $\tau$ the identity and $l = k = 2\rho$. Let $S = U(X)$ with $j(u) = (u, u)$ and $\varphi = 0$. Then $\mu = \mu' = 0$, so $\Phi = 0$ and conditions 1 to 7 hold. The integrand is $\theta = 1$. Every unitary matrix has operator norm $1$, so the ball in the theorem of Laplace's method is all of $U(X)$. The theorem then says $\nu(U(X)) \leq \beta^{20(2\#X)^2}\nu(U(X))$, which is true.

**Remark (Formalization).** In the source a parameter is a function $n \to \mathbb{Z}$ that carries the signs $\varepsilon$ only in its type. The source stores $l = 2\lambda$, so that $\lambda$ may have half integer entries. The weight $\mu$ is computed from $l$ by integer division by $2$. The function $\varphi$ is a separate argument of the integrand; condition 1 is what ties it to the phase. The datum also contains condition 2 on the traces as a separate field, although for the groups of section 8 it follows from the same computation as condition 1.

**Remark (Formalization).** The integrand uses the conjugate $\overline{c_k}$. In the proofs the source rewrites $\overline{c_k}$ as $c_{-k}$, using the conjugation formula of the previous chapter, which needs a gap for $k$. The lowest $K$-type of $-k$ is $-\mu'$. This is why the second weight has the opposite sign convention: $\mu' \geq 0$, while the steep weight $\mu$ is $\leq 0$.

### The polar decomposition

The localization in section 3 moves a nearly unitary block to a block near $1$. For this we need the polar decomposition of an invertible matrix.

**Lemma (Polar decomposition).** Let $a$ be an invertible $X \times X$ complex matrix. Then there are a unitary $k$ and a positive semidefinite $z$ with $a = kz$.
Lean: `New.DiscreteSeries.exists_unitary_mul_posSemidef` (New/Appendix/DiscreteSeries/SteepParameters.lean).

*Proof.* Let $z = |a| = (a^* a)^{1/2}$, the positive semidefinite square root, so $z^2 = a^* a$. Since $a$ is invertible, $a^* a$ is invertible, and so $z$ is invertible. Put $k = a z^{-1}$. Then
$$ k^* k = z^{-1} a^* a z^{-1} = z^{-1} z^2 z^{-1} = 1, $$
so $k$ is unitary, and $a = kz$. $\square$

This is the polar form of Horn and Johnson, *Matrix Analysis*, Theorem 7.3.1. In section 3 the factor $z$ will satisfy $\|z^2 - 1\| \leq r$, and then $\|z - 1\| \leq r$, since the eigenvalues $t \geq 0$ of $z$ satisfy $|t - 1| \leq |t^2 - 1|$.
