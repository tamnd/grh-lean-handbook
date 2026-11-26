---
title: Components and annihilation
lean:
  - Lib/GaloisRep/Main/SelmerModules.lean
  - Lib/Cyclotomic/Kolyvagin/ReciprocityComponentBounds.lean
decls:
  - New.cmConj
  - New.cyclotomicPowDirichlet
  - New.OddPart.vanishingCocycles
  - New.OddPart.inertiaOff
  - New.OddPart.component
  - New.OddPart.artin_reciprocity_of_mem_component
  - New.OddPart.sum_floorDiff_dvd
  - New.OddPart.nsmul_component_eq_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Components and annihilation

This section and the next prove the two bounds on one eigenspace. Fix $N \ge 1$, a prime $\ell$, an exponent $e \ge 1$, a Dirichlet character $\psi$ mod $N$, and the integer $X$ of Section 3. The eigenspace is a module of cocycles over $\mathbb{Q}$ for the character $(\mathrm{cyc}^e\psi)^{-1}$. The first bound says that $4X^2$ kills it. It is an analogue of Stickelberger's theorem, and its proof uses one Jacobi quotient of Section 4 and Artin's reciprocity law. The second bound says that, for $\ell > N + e + 3$, at most $v_\ell(X) + 1$ elements of the Galois group detect a cocycle of the module. Its proof uses the whole Euler system of Section 4 and Kolyvagin's descent. This section defines the eigenspace and proves the first bound. Section 6 proves the second.

### The classical model

Let $p$ be an odd prime, $A$ the $p$-part of $\mathrm{Cl}(\mathbb{Q}(\mu_p))$, and $\chi = \omega^i$ an odd character with $i \ne 1$. Stickelberger's theorem (Washington, Thm. 6.10) gives an annihilator of $A(\chi)$, and its $\chi$-part is a unit multiple of $B_{1,\chi^{-1}}$ (Section 2). An annihilator does not bound the order of a module that is not cyclic. Kolyvagin's method gives the bound on the order. One takes Gauss sums at many auxiliary primes $q \equiv 1 \bmod p^n$, applies Kolyvagin's derivative operators, and gets elements whose Kummer classes are controlled at every prime. A descent on the number of auxiliary primes then bounds $|A(\chi)|$ by the $p$-part of $B_{1,\chi^{-1}}$ (V. A. Kolyvagin, Euler systems, in *The Grothendieck Festschrift*, Vol. II, Progr. Math. 87, 1990; Rubin, Texel 1989, cited in Section 2; Washington, Ch. 15). With the analytic class number formula this gives the equality of the main conjecture at the bottom level.

The source follows this method with three changes. It works with cocycles on $\mathrm{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})$ and not with class groups. It twists by $\mathrm{cyc}^e$, so the relevant L-value is $L(\psi, -e)$ and not $L(\chi^{-1}, 0)$. And it bounds the number of detecting points, not the order: the module is a module over $\mathcal{O}/\ell^\nu$, and $k$ detecting points bound its length by $k\nu$. Section 7 turns the count into a length.

### The modules

Let $\Omega = \bar{\mathbb{Q}}$, and let $G = \mathrm{Gal}(\Omega/\mathbb{Q})$ with its profinite topology. For $M \ge 1$, let $G_M = \mathrm{Gal}(\Omega/\mathbb{Q}(\mu_M))$, the kernel of $\mathrm{cyc}_M$. Places of $\Omega$ are valuation rings, as in Section 4. Every place other than $\Omega$ itself lies above one prime. Let $\mathcal{O}$ be the ring of integers of a finite extension of $\mathbb{Q}_\ell$.

**Definition.** The element $c \in G$ is a fixed complex conjugation: the restriction to $\Omega$ of complex conjugation for some embedding $\Omega \to \mathbb{C}$.

Lean: `New.cmConj` (Lib/GaloisRep/Main/SelmerModules.lean).

**Remark (Formalization).** The element is taken with `choose` from an existence lemma. So it is one fixed complex conjugation, and nothing in this chapter depends on the choice. Every complex conjugation acts as $-1$ on all roots of unity, and this is the only property the proofs use.

**Definition.** Let $\mathcal{O}$ be a $\mathbb{Z}_\ell$-algebra and $\psi$ a Dirichlet character mod $N$ with values in $\mathcal{O}$. The character $\Upsilon = \mathrm{cyc}^e\psi : G \to \mathcal{O}^\times$ is $\Upsilon(g) = \mathrm{cyc}_\ell(g)^e\, \psi(\mathrm{cyc}_N(g))$, where $\mathrm{cyc}_\ell : G \to \mathbb{Z}_\ell^\times$ is the $\ell$-adic cyclotomic character.

Lean: `New.cyclotomicPowDirichlet` (Lib/GaloisRep/Main/SelmerModules.lean).

The character is *odd* if $\Upsilon(c) = -1$. As $\mathrm{cyc}_\ell(c) = -1$ and $\mathrm{cyc}_N(c) = -1$, this says $(-1)^e\psi(-1) = -1$, the parity condition of Section 3.

**Definition.** Let $\chi : G \to \mathcal{O}^\times$ be a character, $V$ an $\mathcal{O}$-module, and $s \subseteq G$. Then $Z(\chi, V, s)$ is the $\mathcal{O}$-module of locally constant maps $x : G \to V$ with
$$x(gh) = x(g) + \chi(g)\, x(h) \quad \text{for all } g, h \in G,$$
and $x(g) = 0$ for $g \in s$.

Lean: `New.OddPart.vanishingCocycles` (Lib/GaloisRep/Main/SelmerModules.lean).

**Definition.** For a finite set $T$ of primes, $I_{N,\ell}(T)$ is the set of $g \in G_N$ that lie in the inertia group of some place $A$ of $\Omega$ above neither $\ell$ nor a prime of $T$.

Lean: `New.OddPart.inertiaOff` (Lib/GaloisRep/Main/SelmerModules.lean).

So a cocycle in $Z(\chi, V, I_{N,\ell}(T))$ is unramified over $\mathbb{Q}(\mu_N)$ at all primes outside $\{\ell\} \cup T$.

**Definition.** Let $\nu \ge 0$. The *component* $C_\nu = C_\nu(\ell, e, \psi)$ is
$$C_\nu = Z\big(\Upsilon^{-1},\ \mathcal{O}/\ell^\nu,\ \{c\} \cup \big(G_N \cap (I_{\ne \ell} \cup D_\ell^1)\big)\big).$$
Here $I_{\ne \ell}$ is the union of the inertia groups at the places of $\Omega$ above primes other than $\ell$, and $D_\ell^1$ is the set of $g$ in the decomposition group of some place $A$ above $\ell$ with $\mathrm{cyc}_\ell(g) = 1$.

Lean: `New.OddPart.component` (Lib/GaloisRep/Main/SelmerModules.lean).

The conditions have a plain meaning. On $\mathrm{Gal}(\Omega/\mathbb{Q}(\mu_{N\ell^\infty}))$ the character $\Upsilon$ is trivial, so a cocycle restricts there to a homomorphism. The conditions say that this homomorphism is unramified at all primes and that the places above $\ell$ split completely in the fixed field of its kernel. So $C_\nu$ is a twisted form of an eigenspace of the class groups of the fields $\mathbb{Q}(\mu_{N\ell^k})$, as in the last paragraph of Section 2. The condition $x(c) = 0$ is a normalization. For an odd character it costs only a factor $2$: Exercise 3 shows that a cocycle for $\Upsilon^{-1}$ with $\Upsilon(c) = -1$ differs from a cocycle that vanishes at $c$ by a coboundary, after multiplication by $2$.

**Remark (Formalization).** The modules are modules of cocycles, not of cohomology classes. The source never divides by coboundaries. The condition $x(c) = 0$ takes one representative in each class, up to the factor $2$. All bounds of this section are on modules of cocycles, and Section 7 needs only such bounds. The module $C_\nu$ is finite (Lean: `New.OddPart.finite_component`), because a cocycle is locally constant and is fixed by its values on a finite quotient of $G$.

### Reciprocity

The source proves one form of Artin's reciprocity law for the cocycles of $C_\nu$. For a prime $q$ that splits completely in $K = \mathbb{Q}(\mu_{Nm})$, it relates the value of a cocycle at a Frobenius at $q$ to the orders at $q$ of a number $y \in K^\times$.

**Theorem (Artin reciprocity for components).** Let $m \ge 1$, let $q \equiv 1 \bmod Nm$ be a prime, let $B$ be a place above $q$, and let $\varphi$ be a Frobenius at $B$. Let $x \in C_\nu$ with $m\,x(g) = 0$ for all $g$. Let $a \equiv 1 \bmod N$ be prime to $\ell$. Let $y \in \Omega^\times$ be fixed by $G_{Nm}$. Suppose that at each place $A$ at which $\ell$ and $q$ are units, either $y = u r^m$ with $u$ a unit at $A$ and $r$ fixed by the inertia group of $A$ in $G_{Nm}$, or $x$ vanishes on the decomposition group of $A$. Let $s(u) \in G$ have $\mathrm{cyc}_{Nm}(s(u)) = u$ for each unit $u$ mod $Nm$. Then there are integers $k(u) = \mathrm{ord}_B\, s(u)(y)$, with $\mathrm{ord}_B(q) = 1$, such that
$$\Big(\sum_{u \in (\mathbb{Z}/Nm)^\times} k(u)\, \bar u^e\, \psi(\bar u)\Big) \cdot 2(a^e - 1)\, x(\varphi) = 0,$$
where $\bar u \in [0, Nm)$ represents $u$.

Lean: `New.OddPart.artin_reciprocity_of_mem_component` (Lib/Cyclotomic/Kolyvagin/ReciprocityComponentBounds.lean).

*Proof.* Put $d = 2(a^e - 1)$. On $G_{Nm}$ the character $\Upsilon^{-1}$ acts trivially on a module killed by $m$, so the restriction of $x$ to $G_{Nm}$ is a homomorphism. For a homomorphism $\lambda$ from $\mathcal{O}/\ell^\nu$ to $\mathbb{Q}/\mathbb{Z}$, the map $\chi_\lambda(g) = \lambda(d\,x(g))$ is a character of $\mathrm{Gal}(\Omega/K)$. It has three local properties. It kills the complex conjugations, because $2x(\sigma) = 0$ for these and $2 \mid d$. It kills the decomposition groups above $\ell$: an element $\delta$ of inertia above $\ell$ with $\Upsilon(\delta) = a^e$ and the conditions at $\ell$ give $(a^e - 1)x(g) = 0$ there. It is unramified away from $\ell$, because $x$ vanishes on inertia over $\mathbb{Q}(\mu_N)$ there. Artin's reciprocity law over $K$ says that the sum over the places $w$ of $K$ of $\mathrm{ord}_w(y)\,\chi_\lambda(\mathrm{Frob}_w)$ is $0$. At a place away from $\ell q$, the hypothesis on $y$ or on $x$ makes the term $0$. As $q$ splits completely in $K$, the places above $q$ are the places below the conjugates $s(u)^{-1}B$, and $s(u)^{-1}\varphi\, s(u)$ is a Frobenius there. The cocycle relation and the conditions of $C_\nu$ give $x$ at this element as $\bar u^e\psi(\bar u)\,x(\varphi)$. So $\lambda$ kills the weighted sum times $d\,x(\varphi)$. As $\lambda$ is arbitrary, the weighted sum kills $d\,x(\varphi)$. $\square$

### The Stickelberger sum modulo powers of $\ell$

The next lemma turns the Stickelberger property of $X$ into a divisibility modulo $\ell^n$ for the odd sums of Section 4.

**Lemma.** Let $X$ have the Stickelberger property for $N$ and $e$, let $\Upsilon = \mathrm{cyc}^e\psi$ be odd, let $e \ne 0$ and $n \ge 0$, and let $a \equiv 1 \bmod N$ be prime to $\ell$. Then in $\mathcal{O}/\ell^n$,
$$\sum_{u \in (\mathbb{Z}/N\ell^n)^\times} m_a\Big(\frac{u}{N\ell^n}\Big)\, \bar u^e\, \psi(\bar u) \;\;\Big|\;\; (a^{e+1} - 1)\, X.$$

Lean: `New.OddPart.sum_floorDiff_dvd` (Lib/Cyclotomic/Kolyvagin/ReciprocityComponentBounds.lean).

*Proof.* For $n = 0$ the ring is $0$. Let $n \ge 1$ and write $n = k + 1$. Let $T(M) = \sum_{0 \le x < NM} \lfloor ax/(NM) \rfloor x^e \psi(x)$, and let $U$ be the part of $T(\ell^{k+1})$ over the units mod $N\ell^{k+1}$. The other terms have $\ell \mid x$, so $T(\ell^{k+1}) = U + \ell^e\psi(\ell)\, T(\ell^k)$. As $\Upsilon$ is odd, $\bar u \mapsto -\bar u$ changes the sign of $\bar u^e \psi(\bar u)$ modulo $N\ell^{k+1}$, so the sum of the lemma is $2U$ in $\mathcal{O}/\ell^{k+1}$. The Stickelberger property at the levels $\ell^{k+1}$ and $\ell^k$ gives one $w$ with $(a^{e+1}-1)X \equiv 2w\,T(\ell^{k+1}) \bmod \ell^{k+1}$ and $(a^{e+1}-1)X \equiv 2w\,T(\ell^k) \bmod \ell^k$. Multiply the second congruence by $\ell^e\psi(\ell)$. As $e \ge 1$, it becomes a congruence mod $\ell^{k+1}$. Subtract:
$$(1 - \ell^e\psi(\ell))\,(a^{e+1}-1)\,X \equiv 2wU \pmod{\ell^{k+1}}.$$
The Euler factor $1 - \ell^e\psi(\ell)$ is a unit mod $\ell^{k+1}$, because $\ell^e\psi(\ell)$ is nilpotent there. So $(a^{e+1}-1)X = 2U \cdot wG$ for its inverse $G$. $\square$

The Euler factor $1 - \ell^e\psi(\ell)$ is the one that relates $L(\psi, -e)$ to the value of the $\ell$-adic L-function. Here it is harmless, because $e \ge 1$. For $e = 0$ it can be $0$ mod $\ell$, and the lemma has the hypothesis $e \ne 0$.

### Annihilation

The classical model of the twisted case is the work of Coates and Sinnott. For a totally real abelian field $F$ and $n \ge 1$, they proved that twisted Stickelberger elements, built from the values of the partial zeta functions of $F$ at $1 - n$, annihilate the $\ell$-parts of higher K-groups of the ring of integers, for suitable $\ell$ and $n$ (J. Coates, W. Sinnott, Invent. Math. 24 (1974), cited in Section 2).

The source proves an analogue of this kind for its components. The annihilator is one integer for all $\ell$ and all characters.

**Theorem (annihilation).** Let $X$ have the Stickelberger property for $N$ and $e$, let $\Upsilon = \mathrm{cyc}^e\psi$ be odd, and let $e \ne 0$. Then $4X^2 z = 0$ for every $z \in C_\nu$.

Lean: `New.OddPart.nsmul_component_eq_zero` (Lib/Cyclotomic/Kolyvagin/ReciprocityComponentBounds.lean).

*Proof.* Suppose $4X^2 z \ne 0$. *A Frobenius.* The cocycle $2X^2 z$ vanishes at $c$, and $\Upsilon^{-1}(c) - 1 = -2$. So if $2X^2z$ vanished on $G_{N\ell^\nu}$, the cocycle relation at $c$ would give $-2 \cdot 2X^2 z = 0$. So $2X^2 z$ is not $0$ on $G_{N\ell^\nu}$. Its kernel is open, so Chebotarev's theorem gives a prime $p \equiv 1 \bmod N\ell^\nu$, a place $B$ above $p$, and a Frobenius $\sigma$ at $B$ with $2X^2 z(\sigma) \ne 0$. *The Jacobi quotient.* The Stickelberger property at $\ell$ gives $a \equiv 1 \bmod N$ prime to $\ell$ with $X = (a^e - 1)(a^{e+1}-1)b$. Let $J$ be the Jacobi family of Section 4 for $(p, B, a)$, and put $y = J(1/(N\ell^\nu))$. It is fixed by $G_{N\ell^\nu}$, and it is a unit away from $p$. Its conjugate by $s(u)$ is $J(u/(N\ell^\nu))$, of order $m_a(u/(N\ell^\nu))$ at $B$. *Reciprocity.* Apply the theorem on Artin reciprocity with $m = \ell^\nu$, $q = p$, $x = z$. With $t$ the sum of the last lemma at the level $n = \nu$, it gives $t \cdot 2(a^e - 1) z(\sigma) = 0$. *Conclusion.* The lemma gives $tk = (a^{e+1}-1)X$ for some $k$. Then
$$2X^2 z(\sigma) = 2(a^e - 1)\, b\, z(\sigma) \cdot (a^{e+1}-1)X = kb \cdot t \cdot 2(a^e-1) z(\sigma) = 0,$$
a contradiction. $\square$

**Remark (Formalization).** The theorem holds for every prime $\ell$, also for $\ell = 2$ and for $\ell \mid NX$. Then it may say nothing: if $\ell \mid 4X^2$ to a high power, the statement is empty for small $\nu$. The constant $X$ is a natural number, and the theorem itself allows $X = 0$; then it says $0 = 0$. Section 3 gives a nonzero $X$, and Section 7 uses only that one. The proof uses one Jacobi quotient, not the Euler system, and no class group appears.
