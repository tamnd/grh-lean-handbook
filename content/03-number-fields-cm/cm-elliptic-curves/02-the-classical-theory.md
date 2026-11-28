---
title: The classical theory
lean:
  - Lib/CM/Sigma/Basic.lean
  - Lib/CM/KroneckerLimit.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The classical theory

This section states the classical results on elliptic curves with complex multiplication that the rest of the chapter uses or replaces. It has no Lean lines. Sections 3 to 7 give the forms that the source proves, and each one says how it differs from the form here. The main references are Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Graduate Texts in Mathematics 151, Springer, 1994, Chapter II, and Silverman, *The Arithmetic of Elliptic Curves*, Graduate Texts in Mathematics 106, Springer, 1986, Chapters IV and VI. Below they are *Advanced Topics* and *AEC*.

Throughout, $K$ is an imaginary quadratic field, $\mathcal{O}_K$ is its ring of integers, $h = h_K$ is its class number, and $K \subset \mathbb{C}$ is fixed. In the argument $K = \mathbb{Q}(\sqrt{-d})$ for a prime $d \equiv 7 \pmod 8$, so $\mathcal{O}_K = \mathbb{Z}[\omega]$ with $\omega = (1 + \sqrt{-d})/2$, the units are $\pm 1$, and $2 = \omega \bar\omega$ splits.

### Lattices and elliptic functions

A lattice $\Lambda \subset \mathbb{C}$ has the Weierstrass function $\wp(z) = z^{-2} + \sum_{l \ne 0} ((z - l)^{-2} - l^{-2})$, the invariants $g_2 = 60 \sum_{l \ne 0} l^{-4}$ and $g_3 = 140 \sum_{l \ne 0} l^{-6}$, and the discriminant $\Delta = g_2^3 - 27 g_3^2 \ne 0$. The map $z \mapsto (\wp(z), \wp'(z))$ is an isomorphism of $\mathbb{C}/\Lambda$ with the curve $y^2 = 4x^3 - g_2 x - g_3$. Conversely, for every pair $(a, b)$ with $a^3 - 27 b^2 \ne 0$ there is a lattice with $g_2 = a$ and $g_3 = b$ (*AEC*, Chapter VI, Theorem 5.1, the uniformisation theorem). The Weierstrass sigma function is the entire function
$$\sigma_W(z) = z \prod_{l \ne 0} \Bigl(1 - \frac{z}{l}\Bigr) \exp\Bigl(\frac{z}{l} + \frac{z^2}{2 l^2}\Bigr).$$
It is odd, its zeros are simple and lie exactly on $\Lambda$, and $\wp = -(\log \sigma_W)''$. It is not periodic: $\sigma_W(z + l) = \pm \exp(\eta(l)(z + l/2)) \sigma_W(z)$, with the quasi-periods $\eta(l)$ of $\zeta_W = \sigma_W'/\sigma_W$ (*AEC*, Chapter VI, §3). The addition formula is
$$\sigma_W(u + v)\, \sigma_W(u - v) = (\wp(v) - \wp(u))\, \sigma_W(u)^2 \sigma_W(v)^2.$$

### Complex multiplication

A lattice $\Lambda$ has complex multiplication by $\mathcal{O}_K$ if $\alpha \Lambda \subseteq \Lambda$ for every $\alpha \in \mathcal{O}_K$, that is, if $\Lambda$ is an $\mathcal{O}_K$-module. Then $\mathrm{End}(\mathbb{C}/\Lambda) \supseteq \mathcal{O}_K$, with equality when $\Lambda$ is not stable under a larger order.

**Theorem (Lattices with CM).** A lattice $\Lambda \subset \mathbb{C}$ is an $\mathcal{O}_K$-module if and only if $\Lambda = c\,\mathfrak{a}$ for a number $c \in \mathbb{C}^\times$ and a nonzero fractional ideal $\mathfrak{a}$ of $K$. Two such lattices $c\,\mathfrak{a}$ and $c'\mathfrak{a}'$ are homothetic if and only if $\mathfrak{a}$ and $\mathfrak{a}'$ have the same class. So the elliptic curves over $\mathbb{C}$ with endomorphism ring $\mathcal{O}_K$, up to isomorphism, are in bijection with the class group of $K$.

Not in the source. The source proves the first part for its CM lattices, [Theorem](/decl/New.CMLattice.exists_latticeModule_eq_scaledIdeal/), and does not use the bijection with the class group.

This is *Advanced Topics*, Chapter II, §1. The class group acts on these curves by $\mathfrak{b} \ast (\mathbb{C}/\mathfrak{a}) = \mathbb{C}/\mathfrak{b}^{-1}\mathfrak{a}$. For an integral ideal $\mathfrak{b}$, the map $\mathbb{C}/\mathfrak{a} \to \mathbb{C}/\mathfrak{b}^{-1}\mathfrak{a}$ induced by the identity of $\mathbb{C}$ is an isogeny of degree $N(\mathfrak{b})$.

**Theorem (Algebraicity and integrality).** Let $E$ have endomorphism ring $\mathcal{O}_K$. Then $j(E)$ is an algebraic integer, $K(j(E))$ is the Hilbert class field $H$ of $K$, and $[K(j(E)) : K] = [\mathbb{Q}(j(E)) : \mathbb{Q}] = h_K$. The $h_K$ numbers $j(\mathfrak{a})$, one for each class, are conjugate over $K$.

Not in the source. The source does not use $j(E)$ or the Hilbert class field. It proves that its normalised curves have a unit discriminant at every prime, [Theorem](/decl/New.CMLattice.norm_disc_eq_one/).

See *Advanced Topics*, Chapter II, Theorem 4.3 for the Hilbert class field, and Chapter II, §6 for integrality. Since $j(E)$ is integral, $E$ has potentially good reduction at every prime (*AEC*, Chapter VII, Proposition 5.5). So over a suitable number field, $E$ has good reduction at each finite place. The source proves a statement of this kind for its normalised curves (Section 4).

### The main theorem of complex multiplication

Let $\mathbb{A}_{K,f}^\times$ be the finite ideles of $K$ and let $[\,\cdot\,, K] : \mathbb{A}_K^\times \to \mathrm{Gal}(K^{\mathrm{ab}}/K)$ be the Artin map. For an idele $s$ and a fractional ideal $\mathfrak{a}$, $s\mathfrak{a}$ is the fractional ideal with the local components $s_v \mathfrak{a}_v$, and multiplication by $s$ gives an isomorphism $K/\mathfrak{a} \to K/s\mathfrak{a}$, componentwise on $\bigoplus_v K_v/\mathfrak{a}_v$.

**Theorem (Main theorem of complex multiplication).** Let $E/\mathbb{C}$ have complex multiplication by $\mathcal{O}_K$, let $\sigma \in \mathrm{Aut}(\mathbb{C}/K)$, and let $s \in \mathbb{A}_K^\times$ with $[s, K] = \sigma|_{K^{\mathrm{ab}}}$. Fix a complex analytic isomorphism $f : \mathbb{C}/\mathfrak{a} \to E(\mathbb{C})$. Then there is a unique complex analytic isomorphism $f' : \mathbb{C}/s^{-1}\mathfrak{a} \to E^\sigma(\mathbb{C})$ such that $f(x)^\sigma = f'(s^{-1}x)$ for every $x \in K/\mathfrak{a}$.

Not in the source. The source proves a soft form with some finite adele, [Theorem](/decl/New.CMLattice.complex_multiplication_theta/).

This is *Advanced Topics*, Chapter II, Theorem 8.2, and G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton, 1971, Theorem 5.4. The theorem has two parts. The first says that $E^\sigma$ has the lattice class of $s^{-1}\mathfrak{a}$. The second says that the action of $\sigma$ on torsion points is multiplication by the idele $s^{-1}$, and the reciprocity law of class field theory identifies $s$ through the Artin map. Section 6 gives the form that the source proves: the first part with an explicit lattice, and the second part with some finite adele that the source does not relate to the Artin map.

### The Hecke character of a CM curve

Let $F \supseteq K$ be a number field and let $E/F$ have complex multiplication by $\mathcal{O}_K$, defined over $F$. Deuring attached to $E$ a Hecke character $\psi_{E/F} : \mathbb{A}_F^\times \to \mathbb{C}^\times$. At a prime $\mathfrak{P}$ of $F$ where $E$ has good reduction, $\psi_{E/F}(\mathfrak{P})$ is the element of $\mathcal{O}_K$ that reduces to the Frobenius endomorphism of the reduced curve. The theorem of Deuring says
$$L(E/F, s) = L(s, \psi_{E/F})\, L(s, \bar\psi_{E/F}).$$
See *Advanced Topics*, Chapter II, §9 for the character and §10 for the L-series. For $F = \mathbb{Q}$ and $h_K = 1$ the form is $L(E/\mathbb{Q}, s) = L(s, \psi)$ for a character $\psi$ of $K$.

The source does not define this character and does not use it. The Hecke characters of the argument are characters of the CM fields $E$ of the argument, in [class field theory](/chapter/class-field-theory/). This chapter uses the Frobenius of a CM curve in one weak form only: the height bound of the formal group in Section 5, a case of Deuring's criterion.

### Kronecker's first limit formula

For $\tau = x + iy$ in the upper half plane let $E(\tau, s) = \sum_{(m, n) \ne (0, 0)} y^s |m\tau + n|^{-2s}$, for $\operatorname{Re} s > 1$, and let $\eta(\tau) = e^{\pi i \tau/12} \prod_{n \ge 1} (1 - e^{2\pi i n\tau})$ be the Dedekind eta function.

**Theorem (Kronecker's first limit formula).** As $s \to 1$,
$$E(\tau, s) = \frac{\pi}{s - 1} + 2\pi\bigl(\gamma - \log 2 - \log(\sqrt{y}\, |\eta(\tau)|^2)\bigr) + O(s - 1).$$

Not in the source. The source proves the form for every lattice, with real $s \to 1$, [Theorem](/decl/New.kronecker_limit/).

See C. L. Siegel, *Lectures on Advanced Analytic Number Theory*, Tata Institute, Bombay, 1961, Chapter I, Theorem 1. The lattice $\Lambda = \mathbb{Z}\tau + \mathbb{Z}$ has the area $A = y$ and the discriminant $\Delta(\tau) = (2\pi)^{12} \eta(\tau)^{24}$. So $\log(A |\Delta|^{1/6} / \pi^2) = \log y + 2\log 2 + 4 \log|\eta(\tau)|$, and the formula reads
$$\sum_{l \in \Lambda,\ l \ne 0} \Bigl(\frac{|l|^2}{A}\Bigr)^{-s} = \frac{\pi}{s - 1} + \pi\Bigl(2\gamma - \log\frac{A\,|\Delta|^{1/6}}{\pi^2}\Bigr) + O(s - 1).$$
Both sides are invariant under $\Lambda \mapsto c\Lambda$, since $A$ scales by $|c|^2$ and $|\Delta|^{1/6}$ by $|c|^{-2}$. So this form holds for every lattice. It is the form that the source proves (Section 7).

### The formula of Chowla and Selberg

For an ideal class $\mathcal{C}$ of $K$ the partial zeta function is $\zeta(s, \mathcal{C}) = \sum_{\mathfrak{b} \in \mathcal{C}} N(\mathfrak{b})^{-s}$, a sum over the integral ideals. If $\mathfrak{a} \in \mathcal{C}^{-1}$, then $\mathfrak{b} = (y)\mathfrak{a}^{-1}$ runs through $\mathcal{C}$ as $y$ runs through $\mathfrak{a} \setminus \{0\}$ modulo units, and $N(\mathfrak{b}) = |y|^2/N(\mathfrak{a})$. The lattice $\mathfrak{a} \subset \mathbb{C}$ has the area $N(\mathfrak{a}) \sqrt{|D_K|}/2$. So
$$w_K\, \zeta(s, \mathcal{C}) = \Bigl(\frac{2}{\sqrt{|D_K|}}\Bigr)^{s} \sum_{y \in \mathfrak{a},\ y \ne 0} \Bigl(\frac{|y|^2}{A(\mathfrak{a})}\Bigr)^{-s},$$
with $w_K = \#\mathcal{O}_K^\times$. The sum of these over the classes is $w_K \zeta_K(s) = w_K \zeta(s) L(s, \chi_K)$ (J. Neukirch, *Algebraic Number Theory*, Springer, 1999, Chapter VII, §5 and §10). Kronecker's formula for each class and the class number formula give the mean of $\log(A |\Delta|^{1/6})$ over the classes in terms of $L'/L(1, \chi_K)$. Lerch's formula for $L'/L(0, \chi_K)$ and the functional equation then give the Gamma values.

**Theorem (Chowla and Selberg).** Let $d > 3$ be a prime with $d \equiv 3 \pmod 4$, let $K = \mathbb{Q}(\sqrt{-d})$, and let $\Lambda_{\mathcal{C}}$ be a lattice homothetic to an ideal of the class $\mathcal{C}$, for each class $\mathcal{C}$. Then
$$\prod_{\mathcal{C}} \bigl(A(\Lambda_{\mathcal{C}})\, |\Delta(\Lambda_{\mathcal{C}})|^{1/6}\bigr)^{1/h} = \pi e^{C_d} \cdot \frac{2\pi}{\sqrt d} = \frac{\pi}{\sqrt d} \prod_{a = 1}^{d - 1} \Gamma\Bigl(\frac{a}{d}\Bigr)^{\chi_K(a)/h},$$
where $C_d = \gamma - L'/L(1, \chi_K)$.

Not in the source. The source proves the first equality in a form with a unit and without the Gamma values, [Theorem](/decl/New.CMLattice.chowla_selberg/).

The original is A. Selberg and S. Chowla, *On Epstein's zeta-function*, J. reine angew. Math. 227 (1967), 86 to 110. The first equality is the sum of Kronecker's formula over the classes; Section 7 gives its proof in the form of the source. The second equality is the computation of [the Chowla-Selberg constant](/chapter/weighted-prime-remainder/) in Volume 1, which uses Lerch's formula. For $d = 7$, with $h = 1$ and $\Lambda = \mathcal{O}_K$, both sides are $13.08193$ to seven digits. For $d = 23$, with $h = 3$ and the forms $(1, 1, 6)$, $(2, 1, 3)$ and $(2, -1, 3)$, both sides are $11.18078$.

The point of the formula for an arithmetic argument is this. If $E$ is defined over a number field and has a model with unit discriminant, then $|\Delta|$ is fixed by that model, and the formula gives the size of the period lattice of $E$ and of all its conjugates. The source proves exactly this consequence, without the Gamma values and without a model over a number field (Section 7).

### Formal groups and integrality

Let $E$ be given by a Weierstrass equation with coefficients in a complete discrete valuation ring $R$. Its formal group $\hat E$ is a one parameter formal group law over $R$ in the parameter $w = -x/y$ near the origin (*AEC*, Chapter IV, §1 and §2). The law has coefficients in $R$ because the equation has. If $E$ has good reduction and complex multiplication by $\mathcal{O}_K$, then the reduction of $\hat E$ has height $1$ at primes $p$ that split in $K$ and height $2$ at primes that are inert or ramified (Deuring's criterion: M. Deuring, *Die Typen der Multiplikatorenringe elliptischer Funktionenkörper*, Abh. Math. Sem. Hansischen Univ. 14 (1941), 197 to 272; see *AEC*, Chapter V, §3 for the height). For the theory of formal groups with complex multiplication by a local ring, see J. Lubin and J. Tate, *Formal complex multiplication in local fields*, Ann. of Math. 81 (1965), 380 to 387. Section 5 gives the forms of these facts that the source proves, at a $p$-adic place of $\mathbb{C}$ in place of a valuation of a number field.
