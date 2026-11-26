---
title: Sieve systems
lean:
  - New/Spanning/MainTerm/SieveSystem.lean
decls:
  - New.SieveSystem
  - New.dampedPower
  - New.headWeight
  - New.SieveSystem.pi
  - New.posSemidef_prod_mul
  - New.norm_prod_mul_le_prod_mul
  - New.SieveSystem.integral_sum_update
  - New.SieveSystem.norm_integral_mul_sum_update_le
  - New.SieveSystem.sum_nonneg
  - New.SieveSystem.lowerSemicontinuousAt_sum
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Sieve systems

A sieve system is the abstract input of the sieve. It is a family of forms on pairs of lists, one form for each floor. Each form but the last is the integral of the next one over a common entry. The last form is positive semidefinite. This section states the axioms and proves the four facts that the sieve uses: products, sums over a family, nonnegativity and lower semicontinuity.

### The axioms

Let $C$ be a commutative ring with a measure. In the applications $C$ is $\mathbb C$ (one infinite place), the product of the completions at a finite set $T$ of places, or a product of both. Let $U$ be a topological space, the space of *entries*. A *head* is a sequence $p : \mathbb N \to U$. Let $u : C \to U$ give the entry of a point of $C$, and let $\iota : U \to C$ send an entry back to $C$. For a head $p$, a position $i$ and an entry $x$, write $p[i \mapsto x]$ for the head with the entry $x$ at $i$ and the entries of $p$ elsewhere.

**Definition (Sieve system).** Let $n \in \mathbb N$, let $J_i(p, q) \in \mathbb C$ be forms on pairs of heads for $i \in \mathbb N$, let $\psi : C \to \mathbb C$, let $E_n \in \mathbb R$, let $\Lambda_i(p) \in \mathbb R$ be weights and let $\beta : C \to \mathbb R$ be a decay. The forms are a *sieve system* if:

1. $\psi(0) = 1$.
2. For $i \leq n$, heads $p, q$ and $\xi \in C$, let $f(c) = \psi(\xi c)\, J_{i+1}(p[i \mapsto u(c)], q[i \mapsto u(c)])$. Then $f$ is integrable, $\int f = J_i(p, q)$ if $\xi = 0$, and $|\int f| \leq \beta(\xi)\,\Lambda_i(p)\,\Lambda_i(q)$ if $\xi$ is a unit.
3. For every finite family of heads $a_1, \dots, a_m$ with a common entry at position $n$, the matrix $(J_{n+1}(a_i, a_j))_{i,j}$ is positive semidefinite.
4. The top form $J_{n+1}$ is jointly continuous in $(p, q)$, for the product topology on heads.
5. $|J_0(p, q)| \leq E_n$ for all $p, q$.
6. For $i < n$, if $\xi = \iota(p_i) - \iota(q_i)$ is a unit, then $|J_{i+1}(p, q)| \leq \beta(\xi)\,\Lambda_{i+1}(p)\,\Lambda_{i+1}(q)$.

Lean: `New.SieveSystem` (New/Spanning/MainTerm/SieveSystem.lean).

The forms $J_i$ for $i > n + 1$ play no part. Condition 2 is the recursion. Integrability is part of it, so the Bochner integral, which is $0$ for a function that is not integrable, has no junk value here. Condition 6 is the decay at a pair of heads whose entries at position $i$ differ: there the form is small. [Local densities at the real places](/chapter/real-densities/) and [local densities at the finite places](/chapter/finite-densities/) build the systems. At $C = \mathbb C$ the entry map is $\operatorname{unitOrOne}$, which sends $c$ to $c$ as a unit if $c \neq 0$ and to $1$ if $c = 0$ (`New.unitOrOne`, a junk value at one point, a null set). The twist is $\operatorname{wave}(c) = \exp(c - \bar c)$ (`New.wave`), a character of $\mathbb C$ of modulus $1$.

Two functions give the decay and the weights at an infinite place.

**Definition (Damped power and head weight).** For $k \in \mathbb N$ and $r \in \mathbb R$, $\ell_k(r) = r^k \min(1, r)^6$. For $R \in \mathbb R$, $K, i \in \mathbb N$ and a head $p$ of nonzero complex numbers, let $\delta_l = p_0 p_1 \cdots p_l$. Then
$$\Lambda_{R, K}(i, p) = \prod_{l < i} \begin{cases} \max(1, |\delta_l|^{-1})^K & \text{if } |\delta_l| \leq R, \\ 0 & \text{otherwise.} \end{cases}$$

Lean: `New.dampedPower`, `New.headWeight` (New/Spanning/MainTerm/SieveSystem.lean).

The head weight is nonnegative. It is $0$ on heads with a large partial product. In the application $R = b^{60n^2}$ and $K = n^6$, and the decay at a real place is a constant times $\ell_{k - n^7}(|\xi|^{-1})$ ([Bessel functions at a real place](/chapter/bessel-real-place/#the-bessel-system-of-the-data)).

### Products of systems

The sieve works on the product of the places. The next theorem makes a system on a product from systems on the factors.

**Lemma (Schur's product theorem).** Let $A_v$, for $v$ in a finite set $s$, and $B$ be positive semidefinite kernels on a finite set $\kappa$. Then the kernel $(i, j) \mapsto \bigl(\prod_{v \in s} A_v(i, j)\bigr) B(i, j)$ is positive semidefinite.

Lean: `New.posSemidef_prod_mul` (New/Spanning/MainTerm/SieveSystem.lean).

*Proof.* By induction on $s$. For $s = \emptyset$ the kernel is $B$. For $s \cup \{v\}$ with $v \notin s$, the kernel is the entrywise (Hadamard) product of $A_v$ and the kernel for $s$. The Hadamard product of two positive semidefinite matrices is positive semidefinite (Schur; Horn and Johnson, *Matrix Analysis*, Section 7.5). $\square$

**Lemma (Products of bounds).** If $|f_v| \leq g_v$ for all $v$ in a finite set $\tau$ and $|a| \leq b$, then $|(\prod_v f_v)\, a| \leq (\prod_v g_v)\, b$.

Lean: `New.norm_prod_mul_le_prod_mul` (New/Spanning/MainTerm/SieveSystem.lean).

*Proof.* $|\prod_v f_v| \leq \prod_v |f_v| \leq \prod_v g_v$, since $0 \leq |f_v| \leq g_v$. Multiply by $|a| \leq b$; both factors are nonnegative. $\square$

For a head $p$ with entries in $(\tau \to \mathbb C^\times) \times U$, write $p^{(v)}$ for the head $l \mapsto (p_l)_1(v)$ of its components at $v$ and $p^{(C)}$ for the head of its components in $U$.

**Theorem (Product of sieve systems).** Let $\tau$ be a finite type. Let $J$ be a sieve system on $C$ for $u, \iota, n, \psi, E_n, \Lambda, \beta$, with an s-finite measure on $C$. For each $v \in \tau$ let $J'_v$ be a sieve system on $\mathbb C$ for $\operatorname{unitOrOne}$, a common map $\iota'$, the same $n$, the twist $\operatorname{wave}$, a bound $E'_v$, common weights $\Lambda'$ and a decay $\gamma_v$. Then the forms
$$\tilde J_i(p, q) = \Bigl(\prod_{v} J'_{v,i}(p^{(v)}, q^{(v)})\Bigr)\, J_i(p^{(C)}, q^{(C)})$$
are a sieve system on $(\tau \to \mathbb C) \times C$ with the entry map $(x, c) \mapsto (\operatorname{unitOrOne} \circ x, u(c))$, the map $(y, e) \mapsto (\iota' \circ y, \iota(e))$, the twist $(x, c) \mapsto \prod_v \operatorname{wave}(x_v)\, \psi(c)$, the bound $\prod_v E'_v \cdot E_n$, the weights $\prod_v \Lambda'_i(p^{(v)}) \cdot \Lambda_i(p^{(C)})$ and the decay $\prod_v \gamma_v(x_v) \cdot \beta(c)$.

Lean: `New.SieveSystem.pi` (New/Spanning/MainTerm/SieveSystem.lean).

*Proof.* Each condition is checked factor by factor.

Condition 1: $\operatorname{wave}(0) = \exp(0) = 1$ and $\psi(0) = 1$, so the product is $1$.

Condition 2: fix $i \leq n$, heads $p, q$ and $\xi = (\xi_\infty, \xi_C)$. For $z \in \mathbb C$ let $g_v(z) = \operatorname{wave}(\xi_v z)\, J'_{v, i+1}(p^{(v)}[i \mapsto \operatorname{unitOrOne} z], q^{(v)}[i \mapsto \operatorname{unitOrOne} z])$, and for $c \in C$ let $g_C(c) = \psi(\xi_C c)\, J_{i+1}(p^{(C)}[i \mapsto u(c)], q^{(C)}[i \mapsto u(c)])$. Since the update at position $i$ acts on each component, the integrand of the product system is $f(x, c) = \prod_v g_v(x_v) \cdot g_C(c)$. Each $g_v$ and $g_C$ is integrable by condition 2 of the factors. A product of integrable functions of independent variables is integrable for the product measure, and by Fubini's theorem
$$\int f = \Bigl(\prod_v \int_{\mathbb C} g_v\Bigr) \int_C g_C.$$
The measure on $(\tau \to \mathbb C) \times C$ is the product of the measures; this needs s-finiteness of the measure on $C$. If $\xi = 0$, every twist is $1$ and each factor integral is the form $J'_{v,i}$ or $J_i$, so $\int f = \tilde J_i(p, q)$. If $\xi$ is a unit, then each $\xi_v$ and $\xi_C$ is a unit, since a pair or a function is a unit exactly when each component is. Each factor integral is bounded by the decay of its factor times its weights. By the lemma on products of bounds, $|\int f| \leq \prod_v \gamma_v(\xi_v)\Lambda'_i(p^{(v)})\Lambda'_i(q^{(v)}) \cdot \beta(\xi_C)\Lambda_i(p^{(C)})\Lambda_i(q^{(C)})$, which is the decay of $\xi$ times the two weights after rearranging.

Condition 3: let $a_1, \dots, a_m$ have the common entry $t$ at position $n$. Then the heads $a_j^{(v)}$ have the common entry $t_1(v)$ and the heads $a_j^{(C)}$ have the common entry $t_2$. Each factor matrix is positive semidefinite, and Schur's product theorem gives the product matrix.

Condition 4: the maps $p \mapsto p^{(v)}$ and $p \mapsto p^{(C)}$ are continuous, and the top forms of the factors are continuous. A finite product of continuous functions is continuous.

Conditions 5 and 6: apply the lemma on products of bounds to the bounds of the factors. In condition 6, $\xi = \tilde\iota(p_i) - \tilde\iota(q_i)$ has the components $\iota'(p^{(v)}_i) - \iota'(q^{(v)}_i)$ and $\iota(p^{(C)}_i) - \iota(q^{(C)}_i)$, and each is a unit. $\square$

The theorem asks that the factors at the infinite places share $n$, $\iota'$ and the weights $\Lambda'$. In the application they share them: the Bessel systems of all infinite places have the same shape.

### Sums over a family of heads

The sieve adds the forms over all pairs of heads from a finite family. The axioms pass to these sums.

**Lemma (Summed recursion).** Let $J$ be a sieve system, let $i \leq n$ and let $a_p$, for $p$ in a finite type $\tau$, be heads. Let $F(c) = \sum_{p, q} J_{i+1}(a_p[i \mapsto u(c)], a_q[i \mapsto u(c)])$. Then $F$ is integrable and
$$\int_C F(c)\, dc = \sum_{p, q} J_i(a_p, a_q).$$
For a unit $\xi$,
$$\Bigl|\int_C \psi(\xi c) F(c)\, dc\Bigr| \leq \beta(\xi) \Bigl(\sum_p \Lambda_i(a_p)\Bigr)^2.$$

Lean: `New.SieveSystem.integral_sum_update`, `New.SieveSystem.norm_integral_mul_sum_update_le` (New/Spanning/MainTerm/SieveSystem.lean).

*Proof.* Each term is integrable by condition 2 with $\xi = 0$, where $\psi(0) = 1$. A finite sum of integrable functions is integrable, and the integral of the sum is the sum of the integrals, each $J_i(a_p, a_q)$ by condition 2. For a unit $\xi$, take the factor $\psi(\xi c)$ into the sum and integrate term by term. The triangle inequality and condition 2 give the bound $\sum_{p,q} \beta(\xi)\Lambda_i(a_p)\Lambda_i(a_q) = \beta(\xi)(\sum_p \Lambda_i(a_p))^2$. $\square$

**Lemma (Nonnegativity).** Let $J$ be a sieve system, let $i \leq n$, and let the heads $a_p$, $p \in \tau$, have a common entry $t$ at position $i$. Then $\sum_{p, q} J_{i+1}(a_p, a_q)$ is a nonnegative real number.

Lean: `New.SieveSystem.sum_nonneg` (New/Spanning/MainTerm/SieveSystem.lean).

*Proof.* By decreasing induction on $i$, from $i = n$ down. For $i = n$, the matrix $(J_{n+1}(a_p, a_q))$ is positive semidefinite by condition 3, and the sum is its quadratic form at the vector $(1, \dots, 1)$, which is $\geq 0$. Let $i < n$ and assume the claim for $i + 1$. By the summed recursion at $i + 1$,
$$\sum_{p,q} J_{i+1}(a_p, a_q) = \int_C \sum_{p,q} J_{i+2}(a_p[i+1 \mapsto u(z)], a_q[i+1 \mapsto u(z)])\, dz.$$
For each $z$ the heads $a_p[i+1 \mapsto u(z)]$ have the common entry $u(z)$ at $i + 1$, so the integrand is $\geq 0$ by the hypothesis of induction. The integral of a nonnegative function is $\geq 0$. $\square$

Here "nonnegative" is the order of $\mathbb C$: real and $\geq 0$. The heads at position $i$ share the entry $t$, but the proof at $i$ uses only the common entries at the positions above $i$ that the induction puts in.

**Lemma (Lower semicontinuity).** Let $C$ carry a first countable topology. Let $J$ be a sieve system, let $i \leq n$, and for $y \in C$ let the heads $b_p(y)$, $p \in \tau$, have a common entry $c(y)$ at position $i$. Let $x \in C$ be a point at which every $y \mapsto b_p(y)$ is continuous. Then
$$y \mapsto \operatorname{ofReal}\Bigl(\operatorname{Re}\sum_{p,q} J_{i+1}(b_p(y), b_q(y))\Bigr) \in [0, \infty]$$
is lower semicontinuous at $x$.

Lean: `New.SieveSystem.lowerSemicontinuousAt_sum` (New/Spanning/MainTerm/SieveSystem.lean).

*Proof.* By decreasing induction on $i$. For $i = n$, the function is continuous at $x$: $J_{n+1}$ is jointly continuous, the heads are continuous at $x$, and the real part and $\operatorname{ofReal}$ are continuous. A function continuous at $x$ is lower semicontinuous at $x$.

Let $i < n$ and assume the claim for $i + 1$. Let $G(y, z) = \sum_{p,q} J_{i+2}(b_p(y)[i+1 \mapsto u(z)], b_q(y)[i+1 \mapsto u(z)])$. For each fixed $z$ the heads $b_p(y)[i+1 \mapsto u(z)]$ are continuous in $y$ at $x$ and share the entry $u(z)$ at $i+1$. By the hypothesis of induction, $y \mapsto \operatorname{ofReal}(\operatorname{Re} G(y, z))$ is lower semicontinuous at $x$. By nonnegativity, $G(y, z)$ is real and $\geq 0$, and $G(y, \cdot)$ is integrable. Hence
$$\operatorname{ofReal}\Bigl(\operatorname{Re}\sum_{p,q} J_{i+1}(b_p(y), b_q(y))\Bigr) = \operatorname{ofReal}\Bigl(\int \operatorname{Re} G(y, z)\, dz\Bigr) = \int^- \operatorname{ofReal}(\operatorname{Re} G(y, z))\, dz.$$
The first equality is the summed recursion. The second holds because the integrand is nonnegative and integrable. Then
$$\int^- \operatorname{ofReal}\operatorname{Re} G(x, z)\, dz \leq \int^- \liminf_{y \to x} \operatorname{ofReal}\operatorname{Re} G(y, z)\, dz \leq \liminf_{y \to x} \int^- \operatorname{ofReal}\operatorname{Re} G(y, z)\, dz.$$
The first inequality is lower semicontinuity at each $z$. The second is Fatou's lemma along the filter of neighbourhoods of $x$. That filter has a countable basis because the topology is first countable, which is the case of Fatou's lemma in Mathlib (`MeasureTheory.lintegral_liminf_le'`). This is lower semicontinuity at $x$. $\square$

The global sieve uses lower semicontinuity to pass from a lattice sum to an integral by one-sided Poisson summation: the extension of a sum of top forms to the adeles must be lower semicontinuous.

### An example

Take $C = \mathbb R$ with Lebesgue measure, $U = \mathbb R$, $u(c) = c$ and $n = 0$. Let $\varphi \in L^2(\mathbb R)$ be continuous with $\int|\varphi|^2 = 1$. Put $J_1(p, q) = \varphi(p_0)\overline{\varphi(q_0)}$ and $J_0 = 1$. Condition 3 holds: the matrix $(\varphi(t)\overline{\varphi(t)})$ of a family with the common entry $t$ at $0$ has rank $1$ and is positive semidefinite. Condition 2 at $i = 0$ and $\xi = 0$ reads $\int |\varphi(c)|^2 dc = 1 = J_0$. With $\psi(x) = e^{2\pi i x}$, the twisted integral is the Fourier transform of $|\varphi|^2$ at $-\xi$, and a decay $\beta$ is any bound for it. Condition 6 is empty for $n = 0$. So any $L^2$-normalised continuous $\varphi$ gives a system of length $0$.
