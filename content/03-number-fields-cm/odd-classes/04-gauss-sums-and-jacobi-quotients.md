---
title: Gauss sums and Jacobi quotients
lean:
  - Lib/Cyclotomic/Stickelberger.lean
decls:
  - New.OddPart.floorDiff
  - New.OddPart.sum_floorDiff
  - New.OddPart.isOfFinOrder_of_norm_eq_one
  - New.OddPart.exists_galUnitsRep_gaussSum_eq
  - New.OddPart.stickelberger
  - New.OddPart.isOfFinAddOrder_distribution
  - New.OddPart.IsJacobiFamily
  - New.OddPart.exists_isJacobiFamily
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Gauss sums and Jacobi quotients

This section builds the arithmetic input of the bound: a family $J(x)$ of algebraic numbers, indexed by the torsion points $x$ of $\mathbb{Q}/\mathbb{Z}$, with a known Galois action, a known order at one place above a prime $p$, and a distribution relation up to roots of unity. It is the Euler system of Gauss sums at one prime $p$. Section 6 takes $\ell^n$-th roots of the $J(x)$ and builds Kolyvagin's cocycles from them. The classical source is Stickelberger's factorization of Gauss sums (Washington, *Introduction to Cyclotomic Fields*, §6.2; Ireland and Rosen, *A Classical Introduction to Modern Number Theory*, Ch. 14).

### Conventions

Let $\Omega = \bar{\mathbb{Q}}$ be the fixed algebraic closure of [CM fields](/chapter/cm-fields/). A place of $\Omega$ is a valuation ring $B$ of $\Omega$. It lies above a prime $p$ if $p$ is in its maximal ideal. For such $B$ and $u \in \Omega^\times$, $\mathrm{ord}_B(u) \in \mathbb{Q}$ is the order of $u$ at $B$, normalized by $\mathrm{ord}_B(p) = 1$. For $x \in \mathbb{Q}/\mathbb{Z}$, $\langle x \rangle \in [0, 1)$ is its representative. For $\sigma \in \mathrm{Gal}(\Omega/\mathbb{Q})$ and $M \ge 1$, $\mathrm{cyc}_M(\sigma) \in (\mathbb{Z}/M)^\times$ is the unit $a$ with $\sigma(\zeta) = \zeta^a$ for every $\zeta \in \mu_M$. The group $\Omega^\times$ is written multiplicatively in this section.

### The order function

**Definition.** For $c \in \mathbb{N}$ and $x \in \mathbb{Q}/\mathbb{Z}$, put
$$m_c(x) = \lfloor c \langle x \rangle \rfloor - \lfloor c \langle -x \rangle \rfloor \in \mathbb{Z}.$$

Lean: `New.OddPart.floorDiff` (Lib/Cyclotomic/Stickelberger.lean).

As $\lfloor c\langle x \rangle \rfloor = c\langle x \rangle - \langle cx \rangle$, one has $m_c(x) = c\,D(x) - D(cx)$ with $D(x) = \langle x \rangle - \langle -x \rangle$. For $x \ne 0$, $D(x) = 2\langle x \rangle - 1 = 2 B_1(\langle x \rangle)$, and $D(0) = 0$. So $m_c$ is the Stickelberger function $(c - \sigma_c)\theta$ of Section 2 made odd. For $x = a/f$ with $0 < a < f$, the term $\lfloor ca/f \rfloor$ is the coefficient of the Stickelberger sums.

**Lemma (distribution relation).** Let $m$ be prime to $r \ge 1$, let $v$ be a unit mod $r$, and let $x \in \mathbb{Q}/\mathbb{Z}$. Then
$$\sum_{b \in \mathbb{Z}/r} m_m\Big(x + \frac{vb}{r}\Big) = m_m(rx).$$

Lean: `New.OddPart.sum_floorDiff` (Lib/Cyclotomic/Stickelberger.lean).

*Proof.* Hermite's identity $\sum_{k=0}^{r-1}\lfloor y + k/r \rfloor = \lfloor ry \rfloor$ gives $\sum_{b} \langle y + b/r \rangle = \langle ry \rangle + (r-1)/2$, so $\sum_b D(y + b/r) = D(ry)$. As $v$ and $mv$ are units mod $r$, the maps $b \mapsto vb$ and $b \mapsto mvb$ permute $\mathbb{Z}/r$. So $\sum_b m_m(x + vb/r) = m\,D(rx) - D(rmx) = m_m(rx)$. $\square$

### Gauss sums and their Galois action

Let $p$ be a prime, $\psi$ a nontrivial additive character of $\mathbb{F}_p$ with values in $\Omega$, and $\chi$ a multiplicative character of $\mathbb{F}_p$. The Gauss sum is $g(\chi) = \sum_{a \in \mathbb{F}_p} \chi(a)\psi(a)$. It divides $p$ in the algebraic integers, and $g(\chi)\overline{g(\chi)} = p$ for $\chi \ne 1$ (Ireland and Rosen, Ch. 8). The source indexes characters additively: a homomorphism $t \mapsto \chi_t$ from $\mathbb{Z}/r$ to the characters of $\mathbb{F}_p^\times$.

**Lemma (Galois action).** Let $t \mapsto \chi_t$ be a homomorphism from $\mathbb{Z}/r$ to the multiplicative characters of $\mathbb{F}_p$, let $\psi$ be an additive character, and let $g(t) = g(\chi_t)$, viewed in $\Omega^\times$. There are homomorphisms $K_\sigma : \mathbb{Z}/r \to \Omega^\times$, one for each $\sigma \in \mathrm{Gal}(\Omega/\mathbb{Q})$, such that
$$\sigma(g(t)) = K_\sigma(a t)\, g(a t), \qquad a = \mathrm{cyc}_r(\sigma).$$

Lean: `New.OddPart.exists_galUnitsRep_gaussSum_eq` (Lib/Cyclotomic/Stickelberger.lean).

*Proof.* Let $u$ be the unit mod $p$ with $\sigma(\zeta) = \zeta^u$ for $\zeta \in \mu_p$. Then $\sigma$ sends $\psi(x)$ to $\psi(ux)$ and $\chi_t(x)$ to $\chi_{at}(x)$. Substitute $x \mapsto u^{-1}x$ in the sum. The factor is $K_\sigma(s) = \chi_s(u)^{-1}$. $\square$

### A weak form of Stickelberger's theorem

**Theorem (Stickelberger's factorization; Washington, §6.2).** Let $p$ be a prime, $\mathfrak{P}$ a prime above $p$ in $\mathbb{Q}(\mu_{p(p-1)})$, and $\omega_{\mathfrak{P}}$ the Teichmüller character of $\mathfrak{P}$, the character of $\mathbb{F}_p^\times$ with $\omega_{\mathfrak{P}}(a) \equiv a \bmod \mathfrak{P}$. Then for $0 \le k < p - 1$, $\mathrm{ord}_{\mathfrak{P}}\, g(\omega_{\mathfrak{P}}^{-k}) = k/(p-1)$, normalized by $\mathrm{ord}(p) = 1$.

The source proves less. It does not compute the orders. It shows only that they are the representatives of the values of an injective homomorphism into $\mathbb{Q}/\mathbb{Z}$.

**Theorem (weak Stickelberger).** Let $B$ be a place of $\Omega$ above $p$, let $r \ge 1$ be prime to $p$, let $\psi$ be a primitive additive character of $\mathbb{F}_p$, and let $t \mapsto \chi_t$ be a primitive (so injective) homomorphism from $\mathbb{Z}/r$ to the multiplicative characters of $\mathbb{F}_p$. Let $g(t) = g(\chi_t)$. Then there is an injective homomorphism $S : \mathbb{Z}/r \to \mathbb{Q}/\mathbb{Z}$ with
$$\langle S(t) \rangle = \mathrm{ord}_B\, g(t) \quad \text{for every } t.$$

Lean: `New.OddPart.stickelberger` (Lib/Cyclotomic/Stickelberger.lean).

*Proof.* *Additivity mod $\mathbb{Z}$.* For $\sigma$ in the inertia group of $B$, $\mathrm{cyc}_r(\sigma) = 1$, as $r$ is prime to $p$. By the lemma on the Galois action, $\sigma$ fixes $g(a + b)/(g(a)g(b))$, because the factors $K_\sigma$ cancel. An element fixed by inertia has integral order at $B$. So $t \mapsto \mathrm{ord}_B\, g(t) \bmod \mathbb{Z}$ is a homomorphism $S$. *Range.* For $t \ne 0$, $\psi \equiv 1$ at $B$, so $g(t) \equiv \sum_x \chi_t(x) = 0$, and $\mathrm{ord}_B\, g(t) > 0$. As $g(t)\, g(-t) = \pm p$, the orders of $g(t)$ and $g(-t)$ are positive and add to $1$, so both are in $(0, 1)$. For $t = 0$ the Gauss sum is $-1$, of order $0$. So $\mathrm{ord}_B\, g(t) \in [0, 1)$ is the representative of $S(t)$. *Injectivity.* If $S(t) = 0$, then $\mathrm{ord}_B\, g(t) = 0$, so $\chi_t = 1$, and $t = 0$. $\square$

**Remark (Formalization).** The classical theorem gives $S(t) = t/(p-1)$ for the right choice of the generator. The source does not need the formula. It needs only to identify $\mathbb{Z}/(p-1)$ with the $(p-1)$-torsion of $\mathbb{Q}/\mathbb{Z}$ in a way that makes the orders computable. The weak form does that: it indexes the Gauss sums by $x = S(t)$, and then the order of the Gauss sum at $x$ is $\langle x \rangle$. The docstring of the file says that only prime fields $\mathbb{F}_p$ appear, and that characters are named by the valuation of their Gauss sum. The source cites Washington, 6.2 and Theorem 15.1, and Davenport and Hasse (J. Reine Angew. Math. 172 (1935)) for the product relation. The source's own list of references marks this file as one whose places were not compared with the works.

### Kronecker's theorem and the distribution relation

**Lemma (Kronecker).** Let $y \in \Omega$ lie in every valuation ring of $\Omega$ and have absolute value $1$ in every complex embedding. Then $y$ is a root of unity.

Lean: `New.OddPart.isOfFinOrder_of_norm_eq_one` (Lib/Cyclotomic/Stickelberger.lean).

The classical form is: an algebraic integer whose conjugates all have absolute value $1$ is a root of unity (Washington, Lemma 1.6). The intersection of the valuation rings of $\Omega$ is the ring of algebraic integers, so the two forms agree. $\square$

**Proposition (distribution up to roots of unity).** Let $B$ be a place above $p$, let $c, M \in \mathbb{N}$ with $M \ge 1$, and let $J : \mathbb{Q}/\mathbb{Z} \to \Omega^\times$. Suppose that for every $x$ with $Mx = 0$:

1. $\sigma(J(x)) = J(ax)$ whenever $\mathrm{cyc}_M(\sigma) = a$;
2. $J(x)$ is a unit at every place $A$ of $\Omega$ with $p$ a unit at $A$;
3. $\mathrm{ord}_B J(x) = m_c(x)$;
4. $|\tau(J(x))| = 1$ for every embedding $\tau : \Omega \to \mathbb{C}$.

Then for $Mx = 0$, $r \mid M$ and $c$ prime to $r$, the quotient $\prod_{b \in \mathbb{Z}/r} J(x + b/r) \,/\, J(rx)$ is a root of unity.

Lean: `New.OddPart.isOfFinAddOrder_distribution` (Lib/Cyclotomic/Stickelberger.lean).

*Proof.* Call the quotient $y$. By Kronecker's lemma it suffices to show that $y$ is a unit at every place and has absolute value $1$ everywhere. The absolute value follows from 4. At a place prime to $p$, $y$ is a unit by 2. All places above $p$ are conjugate to $B$, say $\sigma B$, and $\mathrm{ord}_{\sigma B}(y) = \mathrm{ord}_B(\sigma^{-1} y)$. By 1, $\sigma^{-1}y$ is the same quotient at the point $ax$, with $a = \mathrm{cyc}_M(\sigma^{-1})$. By 3 its order at $B$ is $\sum_b m_c(ax + ab/r) - m_c(rax)$, which is $0$ by the distribution relation for $m_c$. $\square$

### The Jacobi family

**Definition.** Let $p$ be a prime, $B$ a place of $\Omega$, $c \in \mathbb{N}$, and $M \ge 1$. A map $J : \mathbb{Q}/\mathbb{Z} \to \Omega^\times$ is a *Jacobi family* for $(p, B, c, M)$ if for every $x$ with $Mx = 0$:

1. for $r \mid M$ with $c$ prime to $r$, $\prod_{b \in \mathbb{Z}/r} J(x + b/r)\,/\,J(rx)$ is a root of unity;
2. $\sigma(J(x)) = J(ax)$ for every $\sigma$ and every $a \in \mathbb{N}$ with $\mathrm{cyc}_M(\sigma) = a$;
3. $J(x)$ is a unit at every place at which $p$ is a unit;
4. $\mathrm{ord}_B J(x) = m_c(x)$;
5. $|\tau(J(x))| = 1$ for every $\tau : \Omega \to \mathbb{C}$;
6. for a prime $q \mid p - 1$, a place $A$ above $q$, and $b$ with $qb = 0$, $J(x + b)/J(x) \equiv 1$ modulo the maximal ideal of $A$.

Lean: `New.OddPart.IsJacobiFamily` (Lib/Cyclotomic/Stickelberger.lean).

**Theorem.** Let $B$ be a place of $\Omega$ above $p$, and let $c \in \mathbb{N}$. There is $J : \mathbb{Q}/\mathbb{Z} \to \Omega^\times$ that is a Jacobi family for $(p, B, c, M)$ for every $M \ge 1$ with $p \equiv 1 \bmod M$.

Lean: `New.OddPart.exists_isJacobiFamily` (Lib/Cyclotomic/Stickelberger.lean).

*Proof.* Choose a primitive additive character $\psi$ of $\mathbb{F}_p$ and a generator $\chi_1$ of the characters of $\mathbb{F}_p^\times$, and put $\chi_t = \chi_1^t$ for $t \in \mathbb{Z}/(p-1)$ (Lean: `New.OddPart.exists_addChar_isPrimitive_and_mulChar_isPrimitive`). Let $G(t) = g(\chi_t)$, nonzero as it divides $p$. Let $S$ be the homomorphism of the weak Stickelberger theorem with $r = p - 1$. It identifies $\mathbb{Z}/(p-1)$ with the $(p-1)$-torsion of $\mathbb{Q}/\mathbb{Z}$. Put
$$j(t) = \frac{G(t)^c}{G(ct)}, \qquad J(S(t)) = \frac{j(t)}{j(-t)},$$
and $J(x) = 1$ at the other points. Let $M \mid p - 1$ and $Mx = 0$, and write $x = S(t)$.

*Galois action.* The factors $K_\sigma$ of the lemma on the Galois action cancel in $j(t)$, because $K_\sigma$ is a homomorphism and $j$ has degree $c - c = 0$ in it. So $\sigma(j(t)) = j(at)$, and $\sigma(J(x)) = J(ax)$.

*Order at $B$.* The order of $j(t)$ is $c\langle x \rangle - \langle cx \rangle = \lfloor c\langle x \rangle \rfloor$. So the order of $J(x)$ is $m_c(x)$.

*Units and absolute value.* Gauss sums divide $p$, so $J(x)$ is a unit away from $p$. A complex conjugation $\sigma$ for $\tau$ has $\mathrm{cyc}(\sigma) = -1$, so it sends $j(t)$ to $j(-t)$. So $\tau(J(x)) = z/\bar z$ for $z = \tau(j(t))$, of absolute value $1$.

*Distribution.* The previous proposition gives property 1 from properties 2 to 5.

*Congruence.* If $qb = 0$ with $q$ prime, the values of $\chi_b$ on $\mathbb{F}_p^\times$ are $q$-th roots of unity, so they are $\equiv 1$ at a place $A$ above $q$. So $G(t + s) \equiv G(t)$ at $A$ for the index $s$ of $b$, and both are units at $A$ as $q \ne p$. The same holds for $j$ and for $J$. $\square$

**Remark (Formalization).** The family $J$ is an existence statement. The next file takes some such $J$ and uses only the six properties. The theorem fixes $p$, $B$ and $c$ first, and $J$ works for all levels $M$ with $p \equiv 1 \bmod M$. The values of $J$ at the points that $p - 1$ does not kill are junk: the source sets them to $1$, and no property is claimed there. The docstring of the theorem says that such quotients are used to prove Stickelberger's theorem on annihilators of class groups, and that no class group appears in the statement. That is accurate: the class group is replaced, in the next sections, by modules of Galois cocycles, and $J$ acts on them through Kummer theory and Artin reciprocity.

**Remark (Formalization).** The classical distribution relation for Gauss sums is the Davenport-Hasse product relation, an exact identity. The source proves it for the quotients $J$ only up to a root of unity, and only for $r$ prime to $c$. Section 6 uses the relation only after the passage to $\ell^n$-th roots and to the exponents of roots of unity, where a root of unity of order prime to the relevant place is harmless.
