---
title: Kolyvagin systems and detecting points
lean:
  - Lib/Cyclotomic/Kolyvagin/DerivativeCocycles.lean
  - Lib/Cyclotomic/Kolyvagin/ReciprocityComponentBounds.lean
decls:
  - New.OddPart.derivativeSum
  - New.OddPart.IsKolyvaginSystem
  - New.OddPart.exists_isKolyvaginSystem
  - New.OddPart.exists_detecting_points_component
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Kolyvagin systems and detecting points

The annihilator $4X^2$ of Section 5 does not bound the length of the component $C_\nu$: a module killed by $\ell^k$ can have any length. This section proves the second bound. For $\ell > N + e + 3$, at most $v_\ell(X) + 1$ elements of $G$ detect a cocycle of $C_\nu$. The tool is Kolyvagin's method, as in the classical model of Section 5. The notation is that of Section 5: $G = \mathrm{Gal}(\Omega/\mathbb{Q})$, $G_M = \mathrm{Gal}(\Omega/\mathbb{Q}(\mu_M))$, $\Upsilon = \mathrm{cyc}^e\psi$, the modules $Z(\chi, V, s)$, the sets $I_{N,\ell}(T)$, and the Stickelberger sums of the lemma there.

The dual character $\mathrm{cyc}^{e+1}\psi = \mathrm{cyc}\cdot\Upsilon$ plays the role of the Kummer dual. Kolyvagin's cocycles are cocycles for the dual character. Reciprocity pairs their ramification at a prime $r$ with the values of the cocycles of $C_\nu$ at a Frobenius at $r$. The descent then moves from a large set of auxiliary primes down to the empty set, and at the bottom it meets the Stickelberger sum.

### Kolyvagin's derivatives

Fix $n \ge 1$. For a prime $q \equiv 1 \bmod \ell^n$, fix a surjection $L_q : (\mathbb{Z}/q)^\times \to \mathbb{Z}/\ell^n$. Kolyvagin's derivative at $q$ is the element $D_q = \sum_{u} L_q(u)\, [u/q]$ of the group ring of $\mathbb{Q}/\mathbb{Z}$, where $u$ runs over the units mod $q$ and $[u/q]$ acts on functions on $\mathbb{Q}/\mathbb{Z}$ by translation. For a finite set $S$ of such primes, $D_S = \prod_{q \in S} D_q$.

**Definition.** Let $L_q$ and $d_q \in \mathbb{Z}/\ell^n$ be given for the primes $q \in S$. For $G' : \mathbb{Q}/\mathbb{Z} \to \mathbb{Z}/\ell^n$, the *derivative sum* is
$$\Lambda_S(G') = \sum_{a \in (\mathbb{Z}/N\ell^n)^\times} \bar a^e\, \psi(\bar a)\, \Big(\prod_{q \in S} \sum_{u \in (\mathbb{Z}/q)^\times} (L_q(u) - d_q)\, [u/q]\Big) G'\Big(\frac{a}{N\ell^n}\Big) \in \mathcal{O}/\ell^n.$$

Lean: `New.OddPart.derivativeSum` (Lib/Cyclotomic/Kolyvagin/DerivativeCocycles.lean).

The source uses $d_q = 0$. The weights $\bar a^e\psi(\bar a)$ project onto the $\Upsilon$-eigenspace, in the way that $\sum_a \chi^{-1}(a)\sigma_a$ projects onto the $\chi$-part of a group ring.

**Definition.** Let $\chi : G \to \mathcal{O}^\times$ be a character, $V$ an $\mathcal{O}$-module, $\gamma \in G$, $p$ a prime and $P$ a finite set of primes. A family $\kappa_S : G \to V$, one for each $S \subseteq P$, is a *Kolyvagin system* for $(\chi, \gamma, N, \ell, p, P)$ if for every $S \subseteq P$:

1. $\kappa_S \in Z(\chi, V, I_{N,\ell}(S \cup \{p\}))$: it is a cocycle, unramified over $\mathbb{Q}(\mu_N)$ outside $\ell$, $p$ and $S$;
2. $\kappa_S(\gamma) = 0$;
3. for $q \in P \setminus S$, a place $A$ above $q$ and a Frobenius $\varphi$ at $A$, there is $\tau$ in the inertia group of $A$ with $\kappa_{S \cup \{q\}}(\tau) = \kappa_S(\varphi)$.

Lean: `New.OddPart.IsKolyvaginSystem` (Lib/Cyclotomic/Kolyvagin/DerivativeCocycles.lean).

Property 3 is the heart of the method. It says that the value of $\kappa_S$ at a Frobenius at $q$ is visible as ramification of $\kappa_{S \cup \{q\}}$ at $q$. Classically it is the finite-singular comparison map of Kolyvagin's derivative classes.

**Theorem (Kolyvagin system of Gauss sums).** Let $\mathcal{O}$ be a $\mathbb{Z}_\ell$-algebra, $e, c \in \mathbb{N}$, $\gamma \in G$ and $n \ge 0$. Let $P$ be a finite set of primes with $q \equiv 1 \bmod cN\ell^n$ for all $q \in P$. Let $p$ be a prime with $p \equiv 1 \bmod N\ell^n \prod_{q \in P} q$, and let $B$ be a place above $p$. Then there is a family $\kappa_S : G \to \mathcal{O}/\ell^n$, for finite sets $S$ of primes, such that:

1. $(\kappa_S)$ is a Kolyvagin system for $(\mathrm{cyc}^{e+1}\psi, \gamma, N, \ell, p, P)$;
2. if $\kappa_\emptyset$ vanishes on the inertia group of $B$, then
$$\big(\mathrm{cyc}^{e+1}\psi(\gamma) - 1\big) \sum_{a \in (\mathbb{Z}/N\ell^n)^\times} m_c\Big(\frac{a}{N\ell^n}\Big)\, \bar a^e\, \psi(\bar a) = 0 \quad \text{in } \mathcal{O}/\ell^n.$$

Lean: `New.OddPart.exists_isKolyvaginSystem` (Lib/Cyclotomic/Kolyvagin/DerivativeCocycles.lean).

*Proof.* Let $J$ be the Jacobi family of Section 4 for $(p, B, c)$, valid at all levels $M$ with $p \equiv 1 \bmod M$. Choose $\ell^n$-th roots $y(x)$ of $J(x)$ for every $x$, and choose the maps $L_q$. For $g \in G$ the quotient $\gamma(y(x)) / (g\gamma g^{-1})(y(x))$ is an $\ell^n$-th root of unity, because $\gamma$ and $g\gamma g^{-1}$ act in the same way on roots of unity, so in the same way on $J(x)$. Let $\lambda_g(x) \in \mathbb{Z}/\ell^n$ be its exponent for a fixed primitive root $\zeta$, and put $\kappa_S(g) = \Lambda_S(\lambda_g)$ with $d = 0$. The level $M_S = N\ell^n \prod_{q \in S} q$ divides $p - 1$ for $S \subseteq P$, so $J$ is a Jacobi family at that level. *Cocycle and ramification.* The cocycle relation for $\kappa_S$ comes from the Galois action $\sigma(J(x)) = J(ax)$ and the weights $\bar a^e\psi(\bar a)$; the extra factor $\mathrm{cyc}_\ell$ comes from the action on $\zeta$. At a place away from $\ell$, $p$ and $S$, the numbers $J(x)$ are units, and the derivative $D_S$ makes the relevant product an $\ell^n$-th power up to units, by the distribution relation. So $\kappa_S$ is unramified there. *Value at $\gamma$.* The quotient is $1$ for $g = \gamma$. *Frobenius and inertia.* Let $q \in P \setminus S$, let $v$ be a unit mod $q$ with $L_q(v) = 1$, and let $\tau$ be in inertia at $A$ above $q$ and act on the $q$-torsion of $\mathbb{Q}/\mathbb{Z}$ as multiplication by $v^{-1}$. Then $(\tau - 1) D_q = \sum_u [u/q]$, the finite form of Kolyvagin's identity $(\sigma - 1)D = (q - 1) - \sum_{\rho} \rho$. This telescoping identity, the distribution relation and the congruence property 6 of the Jacobi family give the comparison of property 3. Roots of unity of order prime to $q$ stay distinct modulo a place above $q$, so the comparison can be read modulo that place. *The bottom class.* Let $S = \emptyset$, and let $\gamma$ act on the $N\ell^n$-th roots of unity as the power $b$. Take $\tau$ in the inertia group of $B$ that moves an $\ell^n$-th root of a uniformizer at $B$ by $\zeta$. As $J(x)$ is a unit times a power with exponent $m_c(x)$ of the uniformizer, the exponent $\lambda_\tau(x)$ is $b\,m_c(x) - m_c(bx)$. Write $\Sigma$ for the Stickelberger sum. Summed against $\bar a^e\psi(\bar a)$, the substitution $a \mapsto b^{-1}a$ turns the term $m_c(bx)$ into $(b^e\psi(b))^{-1}\Sigma$. So $\kappa_\emptyset(\tau) = 0$ gives $(b^{e+1}\psi(b) - 1)\Sigma = 0$ after multiplication by $b^e\psi(b)$, and $b^{e+1}\psi(b) \equiv \mathrm{cyc}^{e+1}\psi(\gamma) \bmod \ell^n$. $\square$

**Remark (Formalization).** The family $\kappa$ is an existence statement. It depends on choices of $\ell^n$-th roots, of the maps $L_q$ and of the root $\zeta$, all made with `choose` inside the proof. The values $\kappa_S$ for $S \not\subseteq P$ are defined but no property is claimed for them. The source names Rubin's paper (Texel 1989) and, for the Tate twist, G. Banaszak and W. Gajda, Euler systems for higher K-theory of number fields, J. Number Theory 58 (1996), as the classical form. The source does not use the norm-compatible formulation of Euler systems of Rubin's book. It works at one level $N\ell^n$ with one auxiliary prime $p$.

### Detecting points

**Theorem (Kolyvagin and Rubin bound).** Let $X \ne 0$ have the Stickelberger property for $N$ and $e$, let $\Upsilon = \mathrm{cyc}^e\psi$ be odd, let $e \ne 0$, and let $\ell > N + e + 3$. Then there are $\gamma_0, \dots, \gamma_{v_\ell(X)} \in G$ such that every $x \in C_\nu$ with $x(\gamma_i) = 0$ for all $i$ is $0$.

Lean: `New.OddPart.exists_detecting_points_component` (Lib/Cyclotomic/Kolyvagin/ReciprocityComponentBounds.lean).

The source cites K. Rubin, *Euler Systems*, Princeton 2000, Ch. III, §4, Thm. 4.6, for the classical form, and its docstring says that the theorem is used in place of the main conjecture of Mazur and Wiles.

*Proof.* Let $m = v_\ell(X) + 1$ and suppose that no $m$ points detect $C_\nu$. *Units.* As $\ell > N + e + 3$, the numbers $2$ and $\varphi(N\ell)$ are units of $\mathcal{O}$, and a primitive root mod $\ell$ that is $\equiv 1 \bmod N$ gives $a$ with $a^e - 1$ and $a^{e+1} - 1$ units. Let $\gamma$ be in the inertia group of a place above $\ell$ with $\mathrm{cyc}^{e+1}\psi(\gamma) = a^{e+1}$, so $\mathrm{cyc}^{e+1}\psi(\gamma) - 1$ is a unit.

*Tight sets.* Call a finite set $T$ of primes $\equiv 1 \bmod N\ell$ *tight* if every cocycle for $\mathrm{cyc}^{e+1}\psi$ with values in $\mathcal{O}/\ell^m$, killed by $\ell$, and unramified over $\mathbb{Q}(\mu_N)$ outside $\ell$ and $T$, is unramified outside $\ell$. The empty set is tight. Reciprocity modulo $\ell$ (the theorem on Artin reciprocity, read with Kummer theory) gives the key step: if $T$ is tight, and some $z \in C_\nu$ killed by $\ell$ is trivial on the decomposition groups above every prime of $T$ but not above a prime $r$, then $T \cup \{r\}$ is tight. Here $z$ pairs with the ramification at $r$ of the dual cocycle, and the pairing is perfect enough because $2(a^e - 1)$ and $\varphi(N\ell)$ are units.

*Blindness.* As no $m$ points detect $C_\nu$, for every set $T$ of at most $m$ primes $\equiv 1 \bmod N\ell$ there is $z \ne 0$ in $C_\nu$, killed by $\ell$, that is trivial above every prime of $T$. Take $z$ nonzero at the Frobenius elements that detect triviality above the primes of $T$, and replace it by its last nonzero multiple $\ell^k z$.

*Auxiliary primes.* The modules of dual cocycles and $C_\nu$ are finite. For each pair of a dual cocycle $y$ that is nonzero on $G_{aN\ell^m}$ and a nonzero $z \in C_\nu$, Chebotarev's theorem gives a prime $r \equiv 1 \bmod aN\ell^m$ and a Frobenius $\sigma$ above $r$ with $y(\sigma) \ne 0$ and $z(\sigma) \ne 0$. Let $Q$ be the finite set of these primes. Take $z \ne 0$ from the blindness with $T = \emptyset$, and by Chebotarev a prime $p \equiv 1 \bmod N\ell^m\prod_{r \in Q} r$, a place $B$ above $p$, and a Frobenius $\tau$ at $B$ with $z(\tau) \ne 0$. Then $\{p\}$ is tight.

*Descent.* Let $\kappa$ be the Kolyvagin system of the last theorem for $c = a$, $n = m$, $P = Q$ and this $p$. By descending induction on $i$ from $m$ to $0$: for every $S \subseteq Q$ with $|S| \le i$ and $S \cup \{p\}$ tight, $\ell^i \kappa_S$ is unramified outside $\ell$. For $i = m$ this holds as $\ell^m = 0$ in $\mathcal{O}/\ell^m$. For the step, suppose that $\ell \cdot \ell^i\kappa_S \ne 0$. By induction $y = \ell^{i+1}\kappa_S$ is a nonzero dual cocycle unramified outside $\ell$, and $y(\gamma) = 0$ with $\mathrm{cyc}^{e+1}\psi(\gamma) - 1$ a unit, so $y$ is nonzero on $G_{aN\ell^m}$. Blindness gives $w \ne 0$ trivial above $p$ and the primes of $S$, as $|S| + 1 \le m$. The pair $(y, w)$ gives $r \in Q$ and $\sigma$ with $y(\sigma) \ne 0$ and $w(\sigma) \ne 0$. So $r \notin S$, and $S \cup \{p, r\}$ is tight. By induction, $\ell^{i+1}\kappa_{S \cup \{r\}}$ is unramified outside $\ell$. Property 3 gives $\iota$ in inertia above $r$ with $y(\sigma) = \ell^{i+1}\kappa_{S \cup \{r\}}(\iota) = 0$, a contradiction. So $\ell^{i+1}\kappa_S = 0$, and $\ell^i\kappa_S$ is killed by $\ell$; tightness of $S \cup \{p\}$ makes it unramified outside $\ell$.

*Conclusion.* At $i = 0$ and $S = \emptyset$, $\kappa_\emptyset$ is unramified outside $\ell$. As $p \equiv 1 \bmod N\ell$, it vanishes on the inertia group of $B$. The last theorem and the unit $\mathrm{cyc}^{e+1}\psi(\gamma) - 1$ give that the Stickelberger sum at level $N\ell^m$ is $0$ in $\mathcal{O}/\ell^m$. The lemma on the Stickelberger sum then gives $\ell^m \mid (a^{e+1} - 1)X$ in $\mathcal{O}$, so $\ell^m \mid X$. As $m = v_\ell(X) + 1$ and $X \ne 0$, this makes $\ell$ a unit of $\mathcal{O}$, and then $\ell z = 0$ forces $z = 0$, a contradiction. $\square$

**Remark (Formalization).** The last step deserves care. The divisibility $\ell^m \mid X$ is in $\mathcal{O}$, not in $\mathbb{Z}$, and $\ell$ is never a unit of $\mathcal{O}$. So the contradiction is the right one: the proof shows that the hypothesis leads to $\ell^{v_\ell(X)+1} \mid X$, which is false. The bound $\ell > N + e + 3$ is used three times: to make $2$ and $\varphi(N\ell)$ units and to find $a$ with $a^e - 1$ and $a^{e+1} - 1$ units. Section 7 treats the small primes with the annihilation theorem and a crude count of detecting points from ray classes. The theorem gives a count of points, not a bound for the length; the count is $v_\ell(X) + 1$ and not $v_\ell(X)$, because the descent needs one more prime than the exponent.
