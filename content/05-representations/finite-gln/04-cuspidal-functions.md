---
title: Green's cuspidal functions
lean:
  - Lib/LocalGL/Green/HallAlgebra.lean
  - Lib/LocalGL/Green/CuspidalFunctions.lean
decls:
  - New.Hall.crapo_complementation
  - New.Hall.isSemisimple_of_moebius_ne_zero
  - New.Hall.blockAverage_mulMoebius
  - New.Hall.greenCuspidal
  - New.Hall.greenCuspidal_mul_constOne
  - New.Hall.isCuspidal_greenCuspidal
  - New.Hall.IsCuspidal.exists_charpoly_eq_pow
  - New.greenCuspidal_simClassOf_eq_mul
  - New.moebius_and_greenCuspidal_lsmul
  - New.mulMoebius_greenCuspidal_lsmul
  - New.exists_conj_mulLeft_eq
  - New.rankInner_greenCuspidal_mulMoebius
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Green's cuspidal functions

This section constructs Green's cuspidal function $C_\eta$ from a function $\eta$ on the eigenvalues. It proves four facts about $C_\eta$: it is cuspidal, it vanishes off the classes whose characteristic polynomial is a power of one irreducible polynomial, its values at multiplication by a field generator are explicit, and its inner product with $B\mu$ is a mean over the units of a field. Section 5 forms Green's characters from these functions, and the four facts give their cuspidality and their orthonormality.

### The Möbius function vanishes off semisimple classes

The lattice of $g$-stable subspaces of $V$ is a sublattice of the lattice of all subspaces, so it is modular. The first lemma is a form of Crapo's complementation theorem for such a lattice.

**Lemma (Complementation).** Let $\mathcal{L}$ be a finite modular lattice with least element $\bot$ and greatest element $\top$. Let $m : \mathcal{L} \to \mathbb{C}$ satisfy $\sum_{U \leq X} m(U) = 0$ for every $X \neq \bot$. If $m(\top) \neq 0$, then every $W \in \mathcal{L}$ has a complement: an element $C$ with $W \wedge C = \bot$ and $W \vee C = \top$.

Lean: `New.Hall.crapo_complementation` (Lib/LocalGL/Green/CuspidalFunctions.lean).

*Proof.* Suppose that $W$ has no complement. Choose $C$ maximal with $W \wedge C = \bot$, and put $M = W \vee C$. Then $M \neq \top$. We show $m(U) = 0$ for every $U \not\leq M$, by induction on $U$. Let $U \not\leq M$. First, $U \wedge M \neq \bot$. If not, then $C \vee U > C$, since $U \not\leq C$, and by the modular law
$$(C \vee U) \wedge W \leq (C \vee U) \wedge M = C \vee (U \wedge M) = C,$$
so $(C \vee U) \wedge W \leq C \wedge W = \bot$. This contradicts the maximality of $C$. Now $U \neq \bot$, so $0 = \sum_{V \leq U} m(V)$. The terms with $V < U$ and $V \not\leq M$ are $0$ by induction, and the terms with $V \leq M$ are the terms with $V \leq U \wedge M$, whose sum is $0$ since $U \wedge M \neq \bot$. So $m(U) = 0$. In particular $m(\top) = 0$, since $\top \not\leq M$. $\square$

**Theorem (Support of $\mu$).** Let $g$ be an endomorphism of a space $V$. If $\mu([g]) \neq 0$, then $g$ is semisimple.

Lean: `New.Hall.isSemisimple_of_moebius_ne_zero` (Lib/LocalGL/Green/CuspidalFunctions.lean).

*Proof.* Put $m(W) = \mu([g|_W])$ on the lattice of $g$-stable subspaces. By [the defining sums of $\mu$](/decl/New.Hall.sum_moebius_simClassOf_endOnSub/), applied to $g|_X$, the sum of $m$ below $X$ is $0$ for every $X \neq 0$. By [complementation](/decl/New.Hall.crapo_complementation/), every $g$-stable subspace has a $g$-stable complement. So $V$ is a semisimple $k[X]$-module, and $g$ is semisimple. $\square$

**Theorem (Block averages of $B\mu$).** For every $B \in \mathcal{H}(k)$ and all classes $a, b$,
$$\delta(B\mu)(a, b) = \mu(a) \, \mu(b) \, B([b \oplus a]).$$

Lean: `New.Hall.blockAverage_mulMoebius` (Lib/LocalGL/Green/CuspidalFunctions.lean).

*Proof.* Let $g_x$ be the block maps of $a$ and $b$. If $\mu([g_x]) \neq 0$, then $g_x$ is semisimple by [the support of $\mu$](/decl/New.Hall.isSemisimple_of_moebius_ne_zero/). So the stable subspace $0 \times V$ has a stable complement, which is isomorphic to the quotient, and $g_x$ is similar to $b \oplus a$. So $B([g_x]) \mu([g_x]) = B([b \oplus a]) \mu([g_x])$ for every $x$, and $\delta(B\mu)(a, b) = B([b \oplus a]) \, \delta\mu(a, b)$.

It remains to prove $\delta\mu(a, \cdot) = \mu(a) \mu$, by induction on $\dim a$. For $\dim a = 0$ this is the lemma on a block of dimension $0$. Apply [Mackey's formula](/decl/New.Hall.blockAverage_mul/) to $\mu * \mathbb{1} = 1$. Since $\delta \mathbb{1}(a', \cdot) = \mathbb{1}$ and $\delta 1(a, \cdot) = 1(a) \cdot 1$,
$$\Bigl(\sum_A \delta\mu([a|_A], \cdot)\Bigr) * \mathbb{1} = 1(a) \cdot 1,$$
where $A$ runs over the stable subspaces. Multiply by $\mu$. By induction the terms with $A \neq V$ are $\mu([a|_A]) \mu$, and $\sum_{A \neq V} \mu([a|_A]) = 1(a) - \mu(a)$. So $\delta \mu(a, \cdot) + (1(a) - \mu(a)) \mu = 1(a) \mu$. $\square$

### Green's cuspidal function

Let $K$ be a field that contains $k$ and let $\eta : K \to \mathbb{C}$ be any function.

**Definition (Eigenvalue sum, Green's cuspidal function).** The *eigenvalue sum* $\beta_\eta \in \mathcal{H}(k)$ is the sum of $\eta$ over the roots in $K$ of the characteristic polynomial, with multiplicity: $\beta_\eta(c) = \sum_{\chi_c(\alpha) = 0} \eta(\alpha)$. *Green's cuspidal function* is
$$C_\eta = (\beta_\eta \mu) * \mathbb{1}.$$

Lean: `New.Hall.greenCuspidal`, `New.Hall.brauerLift` (Lib/LocalGL/Green/HallAlgebra.lean).

At an endomorphism $g$ of $V$, the definition reads $C_\eta([g]) = \sum_W \beta_\eta([g|_W]) \, \mu([g|_W])$, over the $g$-stable $W$. If $K$ does not contain all the roots of $\chi_c$, the sum runs over the roots in $K$ only. In all uses in this chapter $K$ is algebraically closed.

**Theorem ($C_\eta * \mathbb{1} = -\beta_\eta$).** For every $\eta$, $C_\eta * \mathbb{1} = -\beta_\eta$, and $C_\eta$ vanishes at the class of dimension $0$.

Lean: `New.Hall.greenCuspidal_mul_constOne`, `New.Hall.greenCuspidal_eq_zero_of_dim_lt_one` (Lib/LocalGL/Green/CuspidalFunctions.lean).

*Proof.* We show $C_\eta = -\mu * \beta_\eta$, and then multiply by $\mathbb{1}$. At $g$,
$$C_\eta([g]) + (\mu * \beta_\eta)([g]) = \sum_W \mu([g|_W]) \bigl(\beta_\eta([g|_W]) + \beta_\eta([g|_{V/W}])\bigr).$$
The characteristic polynomial of $g$ is the product of those of $g|_W$ and $g|_{V/W}$. So the bracket is $\beta_\eta([g])$, and the sum is $\beta_\eta([g]) \, 1([g])$ by the defining sums of $\mu$. This is $0$: either $V \neq 0$ and $1([g]) = 0$, or $V = 0$ and $\beta_\eta$ is an empty sum. At the class $o$ of dimension $0$, $C_\eta(o) = \beta_\eta(o) \mu(o) = 0$. $\square$

**Theorem (Cuspidality).** For every $\eta$, the function $C_\eta$ is cuspidal.

Lean: `New.Hall.isCuspidal_greenCuspidal` (Lib/LocalGL/Green/CuspidalFunctions.lean).

*Proof.* Let $\dim a \neq 0$ and $\dim b \neq 0$. By the last proof $C_\eta = -\mu * \beta_\eta$. Mackey's formula gives $\delta C_\eta(a, b) = -\sum_A (\delta\mu([a|_A], \cdot) * \delta\beta_\eta([a|_{V/A}], \cdot))(b)$. The characteristic polynomial of a block map is the product of those of its blocks, so $\delta\beta_\eta(a', \cdot) = \beta_\eta(a') \mathbb{1} + \beta_\eta$. With $\delta\mu(a'', \cdot) = \mu(a'')\mu$ from the last theorem, the term of $A$ is
$$\mu([a|_A]) \, \beta_\eta([a|_{V/A}]) \, (\mu * \mathbb{1})(b) + \mu([a|_A]) \, (\mu * \beta_\eta)(b).$$
The first part is $0$, since $\mu * \mathbb{1} = 1$ and $\dim b \neq 0$. The sum over $A$ of the second part is $1(a) \, (\mu * \beta_\eta)(b) = 0$, since $\dim a \neq 0$. $\square$

### The support of a cuspidal function

**Theorem (Support of a cuspidal function).** Let $F \in \mathcal{H}(k)$ be cuspidal and let $g$ be an endomorphism of $V$ with $F([g]) \neq 0$. Then there are an irreducible $P \in k[X]$ and $j \geq 0$ with $\chi_g = P^j$.

Lean: `New.Hall.IsCuspidal.exists_charpoly_eq_pow` (Lib/LocalGL/Green/CuspidalFunctions.lean).

*Proof.* Suppose that $\chi_g$ has an irreducible factor $P$ and is not a power of $P$. For large $N$, the Fitting decomposition gives $V = V_1 \oplus V_2$ with $V_1 = \ker P(g)^N$ and $V_2 = \operatorname{im} P(g)^N$. Both are $g$-stable and nonzero, and the characteristic polynomials of $a = g|_{V_2}$ and $b = g|_{V_1}$ are coprime. Then the Sylvester map $y \mapsto ay - yb$ of $\mathrm{Hom}(V_1, V_2)$ is injective, so it is bijective. For each $x$ choose $y$ with $ay - yb = x$. The automorphism $(w, v) \mapsto (w, v - yw)$ of $V_1 \times V_2$ conjugates the block map $g_{a,b,x}$ to $b \oplus a$, which is similar to $g$. So $\delta F([a], [b]) = F([g]) \neq 0$, with $\dim a \neq 0$ and $\dim b \neq 0$. This contradicts cuspidality. If $V = 0$, take any irreducible $P$ and $j = 0$. $\square$

So $C_\eta$ lives on the classes $c$ with $\chi_c = P^j$. On such a class, the roots of $\chi_c$ are the Frobenius orbit of one root, and the value of $C_\eta$ depends on $\eta$ only along this orbit.

**Lemma (Dependence on the orbit).** Let $g$ act on $V$ with $d = \dim V$. Let $a \in \mathbb{C}$, and let $\eta, \eta'$ satisfy $\eta'(z) = a \, \eta(z)$ for every $z \in K$ with $z^{q^d} = z$ such that the roots of $\chi_g$ in $K$, with multiplicity, are $z, z^q, \ldots, z^{q^{d-1}}$. Then $C_{\eta'}([g]) = a \, C_\eta([g])$.

Lean: `New.greenCuspidal_simClassOf_eq_mul` (Lib/LocalGL/Green/CuspidalFunctions.lean).

*Proof.* If $C_\theta([g]) = 0$ for every $\theta$, both sides are $0$. Otherwise $C_\theta([g]) \neq 0$ for some $\theta$, and $\chi_g = P^j$ for an irreducible $P$ of degree $e$, by cuspidality and the support theorem. Let $z$ be a root of $P$ in $K$. The roots of $P$ are $z, z^q, \ldots, z^{q^{e-1}}$, and $z^{q^e} = z$. So the roots of $\chi_g$, with multiplicity, are $z^{q^i}$ for $0 \leq i < d = je$, and $z^{q^d} = z$. The same holds for every root of $\chi_g$ in place of $z$. So $\eta' = a\eta$ at every root of $\chi_g$. Each term of $C_\eta([g])$ involves $\eta$ only at roots of $\chi_g$, so $C_{\eta'}([g]) = a \, C_\eta([g])$. If $P$ has no root in $K$, then $\beta_\eta$ and $\beta_{\eta'}$ vanish at every restriction of $g$, and both sides are $0$. $\square$

### Values at a field generator

Let $F = k(z)$ be a finite extension of $k$ generated by $z$, with $Q = |F|$. Let $V$ be an $F$-vector space of dimension $d$, and let $g = m_z$ be multiplication by $z$ on $V$, as a $k$-linear map. Put
$$N(X) = \prod_{i=0}^{d-1} (X - Q^i) \in \mathbb{C}[X], \qquad s_\eta(z) = \sum_{\alpha} \eta(\alpha),$$
where $\alpha$ runs over the roots in $K$ of the minimal polynomial of $z$ over $k$.

**Theorem (Values at a field generator).** In this setting, $\mu([m_z]) = N(0)$ and $C_\eta([m_z]) = -s_\eta(z) \, N'(1)$.

Lean: `New.moebius_and_greenCuspidal_lsmul`, `New.moebius_simClassOf_lsmul` (Lib/LocalGL/Green/CuspidalFunctions.lean).

*Proof.* The $k$-algebra generated by $m_z$ is $F$, so the $m_z$-stable subspaces are the $F$-subspaces of $V$, and $m_z$ restricted to an $F$-subspace $W$ is multiplication by $z$ on $W$. So $\mu([m_z|_W])$ depends only on $i = \dim_F W$. Call it $\mu_i$. The characteristic polynomial of $m_z$ on $W$ is the $i$-th power of the minimal polynomial of $z$, so $\beta_\eta([m_z|_W]) = i \, s_\eta(z)$.

Put $M(X) = \sum_W \mu_{\dim W} \, X^{d - \dim W}$. It is monic of degree $d$, from $W = 0$. For $0 \leq j < d$,
$$M(Q^j) = \sum_W \mu_{\dim W} \, |\mathrm{Hom}_F(V/W, F^j)| = \sum_{\varphi : V \to F^j} \ \sum_{W \leq \ker\varphi} \mu_{\dim W},$$
and the inner sum is $1$ if $\ker \varphi = 0$ and $0$ otherwise, by the defining sums of $\mu$ for $m_z|_{\ker\varphi}$. There is no injective $F$-linear map $V \to F^j$ for $j < d$. So $M$ vanishes at the $d$ distinct numbers $Q^0, \ldots, Q^{d-1}$, and $M = N$. At $X = 0$ only $W = V$ contributes, so $\mu([m_z]) = \mu_d = N(0)$.

For $C_\eta$, the definition gives $C_\eta([m_z]) = s_\eta(z) \, \Sigma$ with $\Sigma = \sum_W \dim_F W \cdot \mu_{\dim W}$. Differentiate $M$: $M'(1) = \sum_W (d - \dim W) \mu_{\dim W} = d M(1) - \Sigma$. Here $d M(1) = d N(1) = 0$: if $d \geq 1$, then $1 = Q^0$ is a root of $N$. So $\Sigma = -M'(1) = -N'(1)$. $\square$

**Example (Small cases).** For $d = 1$: $N = X - 1$, so $\mu([m_z]) = -1$ and $C_\eta([m_z]) = -s_\eta(z)$. For $F = k$, $d = 2$ and $z = a$: $N = (X-1)(X-q)$, so $\mu([a \cdot 1]) = q$, as in Section 2, and $C_\eta([a \cdot 1]) = (q-1) \, \eta(a)$, since $N'(1) = 1 - q$.

**Corollary (The product $C_\eta \mu$).** In the same setting, with $V \neq 0$,
$$(C_\eta\mu)([m_z]) \cdot (|V| - 1) = s_\eta(z) \cdot |\mathrm{GL}_F(V)|,$$
where $\mathrm{GL}_F(V)$ is the group of $k$-linear automorphisms of $V$ that commute with $m_z$.

Lean: `New.mulMoebius_greenCuspidal_lsmul`, `New.card_GL_eq_prod` (Lib/LocalGL/Green/CuspidalFunctions.lean).

*Proof.* By the theorem, $(C_\eta\mu)([m_z]) = -s_\eta(z) N'(1) N(0)$. Here $N(0) = (-1)^d Q^{d(d-1)/2}$ and $N'(1) = \prod_{i=1}^{d-1} (1 - Q^i)$, so $-N'(1) N(0) = Q^{d(d-1)/2} \prod_{i=1}^{d-1} (Q^i - 1)$. Multiply by $|V| - 1 = Q^d - 1$. The result is $\prod_{i<d} Q^i (Q^{i+1} - 1) = |\mathrm{GL}_d(F)|$, and the centralizer of $m_z$ is $\mathrm{GL}_d(F)$. $\square$

### The inner product as a mean over a torus

**Lemma (Semisimple classes in a field).** Let $L$ be a finite field that contains $k$, and let $g$ be a semisimple $k$-linear endomorphism of $L$ with $\chi_g = P^j$ for an irreducible $P$. Then $g$ is conjugate to a multiplication: there are a $k$-linear automorphism $e$ of $L$ and $y \in L$ with $e \circ m_y \circ e^{-1} = g$.

Lean: `New.exists_conj_mulLeft_eq` (Lib/LocalGL/Green/CuspidalFunctions.lean).

*Proof.* Since $g$ is semisimple, its minimal polynomial is squarefree, so it is $P$. So $g$ makes $L$ a vector space over the field $k[X]/(P)$. The degree of $P$ divides $[L : k]$, so $P$ has a root $y$ in $L$, and $m_y$ makes $L$ a vector space over $k[X]/(P)$ too. Both have dimension $[L:k]/\deg P$. An isomorphism of these two vector spaces is the required $e$. $\square$

**Theorem (Inner product with $B\mu$).** Let $L$ be a finite field that contains $k$, with $m = [L : k]$, let $\varphi : L \to K$ be a $k$-embedding, and let $B \in \mathcal{H}(k)$. Then
$$\langle C_\eta, B\mu \rangle_m = \frac{1}{|L^\times|} \sum_{z \in L^\times} \overline{\eta(\varphi(z))} \, B([m_z]).$$

Lean: `New.rankInner_greenCuspidal_mulMoebius` (Lib/LocalGL/Green/CuspidalFunctions.lean).

*Proof.* Identify $k^m$ with $L$. A term of the mean over $g \in \mathrm{GL}_m(k)$ is $\overline{C_\eta([g])} \, \mu([g]) \, B([g])$. It is $0$ unless $C_\eta([g]) \neq 0$ and $\mu([g]) \neq 0$. Then $\chi_g = P^j$ by [cuspidality](/decl/New.Hall.isCuspidal_greenCuspidal/) and [the support theorem](/decl/New.Hall.IsCuspidal.exists_charpoly_eq_pow/), and $g$ is semisimple by [the support of $\mu$](/decl/New.Hall.isSemisimple_of_moebius_ne_zero/). So $g$ is conjugate to $m_y$ for some $y \in L^\times$, by the last lemma. Conversely, for every $y \in L^\times$, $m_y$ is semisimple with characteristic polynomial a power of the minimal polynomial of $y$. Two such maps $m_y$, $m_{y'}$ are similar exactly when $y$ and $y'$ have the same minimal polynomial, that is, when they are conjugate under $\mathrm{Gal}(L/k)$.

Fix $y$ and put $F = k(y)$. The class of $m_y$ has $|\mathrm{GL}_m(k)| / |\mathrm{GL}_F(L)|$ elements. Since $\mu$ is real, $\overline{C_\eta} \mu = \overline{C_\eta \mu}$, and [the corollary on $C_\eta\mu$](/decl/New.mulMoebius_greenCuspidal_lsmul/) gives the value $\overline{s_\eta(y)} \, |\mathrm{GL}_F(L)| / (|L| - 1)$. So the class of $m_y$ contributes $\overline{s_\eta(y)} \, B([m_y]) / |L^\times|$ to the mean. The roots of the minimal polynomial of $y$ in $K$ are the images under $\varphi$ of the Galois orbit of $y$, each once. So $s_\eta(y)$ is the sum of $\eta \circ \varphi$ over the orbit, and the sum over the classes is the sum over $z \in L^\times$. $\square$

### The example of $\mathrm{GL}_2$

**Example (Green's function in rank $2$).** Let $\eta$ be any function on $K$, and let $g \in \mathrm{GL}_2(k)$. The values of $C_\eta$ in rank $2$ are these.

- If $g$ has eigenvalues $z, z^q$ with $z \notin k$, then $g \sim m_z$ on $F = k(z)$ with $d = 1$, and $C_\eta([g]) = -(\eta(z) + \eta(z^q))$.
- If $g = a \cdot 1$, then $C_\eta([g]) = (q-1)\eta(a)$, by the example on small cases.
- If $g = a \cdot 1 + N$ with $N \neq 0$ nilpotent, the stable subspaces are $0$, $\ker N$ and $V$, and $\mu([g]) = 0$. So $C_\eta([g]) = \beta_\eta([a]) \mu([a]) = -\eta(a)$.
- If $g$ has eigenvalues $a \neq b$ in $k$, then $\chi_g$ is not a prime power, and $C_\eta([g]) = 0$ by the support theorem. Directly: $-\eta(a) - \eta(b) + (\eta(a) + \eta(b)) \cdot 1 = 0$.

For $\eta = \theta$ a character of $\mathbb{F}_{q^2}^\times$ with $\theta \neq \theta^q$, this is the table of the cuspidal character in Section 1. Section 5 shows that this choice of $\eta$ is the one that the source makes.
