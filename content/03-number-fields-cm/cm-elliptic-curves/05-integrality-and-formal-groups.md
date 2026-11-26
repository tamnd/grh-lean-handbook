---
title: Integrality and the formal group
lean:
  - Lib/CM/Integrality/TorsionValues.lean
  - Lib/CM/Integrality/IntegralSections.lean
  - Lib/CM/Integrality/IsogenyIntegrality.lean
  - Lib/CM/Integrality/LogTheta.lean
  - Lib/CM/FormalGroup/FormalParameter.lean
  - Lib/CM/FormalGroup/InseparableDegree.lean
decls:
  - New.CMLattice.torsionValue
  - New.CMLattice.HasIntegralValues
  - New.CMLattice.norm_a₁_le_one
  - New.CMLattice.max_norm_torsionValue
  - New.CMLattice.hasIntegralValues_monomialSection
  - New.CMLattice.integralSeriesRing
  - New.CMLattice.mem_span_monomialSection
  - New.CMLattice.exists_taylorVia_eq_theta_pow_mul
  - New.CMLattice.exists_rescale_theta_eq_theta_pow_mul
  - New.CMLattice.rescale_translatedY_mem_integralSeriesRing
  - New.CMLattice.norm_le_one_of_mapsTo_lattice
  - New.CMLattice.derivative_derivative_negLogTheta
  - New.CMLattice.translatedY_add_mem_multiSeriesRing
  - New.CMLattice.insepDegree_le
  - New.CMLattice.insepDegree_piPrime_le
  - New.CMLattice.exists_scaled_formalParam
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Integrality and the formal group

Classically, a CM curve $E$ over a number field has potential good reduction, its torsion points have integral coordinates in a suitable model away from a finite set of primes, and its formal group at a prime of good reduction is a Lubin-Tate group of height $1$ or $2$ (Silverman, *The Arithmetic of Elliptic Curves*, Chapter IV, §1 and §2, Chapter VII, §3 and §5; Lubin and Tate, Ann. of Math. 81 (1965), 380 to 387). The source proves the analytic forms of these facts that it needs, for the model $y^2 + a_1xy = x^3 + x$ of [Section 3](/decl/New.CMLattice.weierstrass_equation/), at every $p$-adic place of $\mathbb{C}$. The results feed [the CM formal group](/chapter/cm-formal-group/) of Volume 9. The good reduction of [Section 4](/decl/New.CMLattice.norm_disc_eq_one/) is the input.

Throughout, $d$ is a prime with $d \equiv 7 \pmod 8$, $p$ is a prime, and $\iota_p : \mathbb{C} \to \mathbb{C}_p$ is a ring homomorphism. In Lean, $\iota_p$ is the field of an instance of the class `New.PadicPlace p`. Let $\mathfrak{o}$ be the valuation ring of $\mathbb{C}_p$. "Integral" means of norm at most $1$ in $\mathbb{C}_p$ after $\iota_p$.

### Torsion values

A section $G$ of degree $n$ is not a function on $\mathbb{C}/\Lambda$, so its value at a torsion point is defined with the twisted translate of [Section 3](/decl/New.CMLattice.θ/).

**Definition (Torsion values).** A point $u \in \mathbb{C}$ is *torsion* if $nu \in \Lambda$ for some $n \ne 0$. For a function $G$ and $n \in \mathbb{N}$, the torsion value of degree $n$ is $G[u] = (T^n_u G)(0) = \exp(-n\pi|u|^2/2A)\, G(u)$. The function $G$ *has integral values* in degree $n$ if $|\iota_p(G[u])| \le 1$ for every torsion point $u$.

Lean: `New.CMLattice.torsionValue`, `New.CMLattice.HasIntegralValues` (Lib/CM/Integrality/TorsionValues.lean), with `New.CMLattice.IsTorsion`.

The values $\sigma[u]$ and $\theta[u]$ are, up to a root of unity, the values at $u$ of Siegel functions, in the sense of Kubert and Lang, *Modular Units*. The file cites that book and Birch for the integrality of Weber's invariants.

**Lemma.** For every CM lattice, $|\iota_p(a_1)| \le 1$.

Lean: `New.CMLattice.norm_a₁_le_one` (Lib/CM/Integrality/TorsionValues.lean).

*Proof.* $a_1^4 = (a_1^4 - 64) + 64$, and $|\iota_p(a_1^4 - 64)| = 1$ by [good reduction](/decl/New.CMLattice.norm_disc_eq_one/). So $|\iota_p(a_1)|^4 \le 1$. $\square$

**Theorem (Torsion values of sigma and theta).** For every torsion point $u$,
$$\max\bigl(|\iota_p\, \sigma[u]|, |\iota_p\, \theta[u]|\bigr) = 1.$$

Lean: `New.CMLattice.max_norm_torsionValue` (Lib/CM/Integrality/TorsionValues.lean).

*Proof.* Put $w(u) = (\theta[u]^2, \sigma[u]^2)$, read in $\mathbb{C}_p^2$ with the max norm. It is not $0$, since $\theta$ and $\sigma$ have no common zero. Its norm depends only on $u$ modulo $\Lambda$, by the transformation laws. The duplication formulas of $\theta$ and $\sigma$ give $w(2u) = F(w(u))$, with the quartic forms
$$F(w_0, w_1) = \bigl((w_0^2 - w_1^2)^2,\ w_0w_1(4w_0^2 + a_1^2w_0w_1 + 4w_1^2)\bigr)$$
(`New.CMLattice.squarePair_two_mul`, `New.doublingForms`). If $a_1$ is integral and $a_1^4 - 64$ is a unit, the reduced forms have no common zero except $0$ over the residue field. So $|F(w)| = |w|^4$ for every $w$ (`New.norm_doublingForms`). Now $u$ is torsion, so $2^iu \equiv 2^ju \pmod\Lambda$ for some $i < j$. Then $|w(u)|^{4^i} = |w(u)|^{4^j}$, and $|w(u)| = 1$. $\square$

**Theorem (Monomials).** For every $(a, b, c)$, the monomial $\theta^a(\sigma^2)^bG^c$, with $G = y\theta^3$, has integral values in degree $a + 2b + 3c$.

Lean: `New.CMLattice.hasIntegralValues_monomialSection` (Lib/CM/Integrality/TorsionValues.lean).

*Proof.* Torsion values are multiplicative in the degree (`New.CMLattice.torsionValue_mul`). The values $\theta[u]$ and $\sigma[u]$ are integral by the previous theorem. Off $t + \Lambda$, $\sigma^2 = x\theta^2$, so the cubic gives $G^2 + a_1\theta\sigma^2 G = \sigma^6 + \theta^4\sigma^2$. For torsion values this is a monic quadratic equation for $G[u]$ with integral coefficients (`New.CMLattice.torsionValue_translatedYThetaCube_sq_add`). Its roots are integral. $\square$

### The integrality principle

**Definition.** $\mathfrak{o}[[y]]$ is the ring of power series $g(y)$ with $g \in \mathfrak{o}[[T]]$, where $y$ is the Taylor series at $0$ of the coordinate $y(z)$, with $\iota_p$ applied to the coefficients. Since $y = z + \cdots$, this is a subring of $\mathbb{C}_p[[z]]$.

Lean: `New.CMLattice.integralSeriesRing` (Lib/CM/FormalGroup/IntegralParameter.lean), with `New.taylorVia` and `New.IsSeriesGenerator`.

The ring contains the series of $x$, by Hensel's lemma applied to the cubic, and it is stable under $d/dz$ (`New.CMLattice.taylorVia_translatedX_mem_integralSeriesRing`, `New.CMLattice.derivative_mem_integralSeriesRing`).

**Theorem (Integrality principle).** Let $f$ be a section of degree $m$ with integral values in degree $m$. Then:

1. $f$ is a combination of the monomials $\theta^a(\sigma^2)^bG^c$ with $c \le 1$ and $a + 2b + 3c = m$, with coefficients $\lambda \in \mathbb{C}$ such that $|\iota_p\lambda| \le 1$;
2. the Taylor series of $f$ at $0$, with $\iota_p$ applied, is $\theta^m u$ with $u \in \mathfrak{o}[[y]]$.

Lean: `New.CMLattice.mem_span_monomialSection`, `New.CMLattice.exists_taylorVia_eq_theta_pow_mul` (Lib/CM/Integrality/IntegralSections.lean).

*Proof.* By [the basis of sections](/decl/New.CMLattice.sections_le_span_monomialSection/), $f = \theta^m(P_0(x) + yP_1(x))$ with polynomials $P_0$, $P_1$. The coefficients are found by interpolation at the nodes $x(t_i)$, $t_i = t/2^i$ for $i \ge 1$. The file proves that $\theta[t_i]$, $x'(t_i)$ and $x(t_i) - x(t_j)$ for $i \ne j$ are units, by doubling from $t$. So the interpolation does not divide by non-units, and the coefficients are integral. This is (1). For (2), off $t + \Lambda$ each monomial is $\theta^m x^by^c$, and $x \in \mathfrak{o}[[y]]$. $\square$

The file compares the result with Bannai and Kobayashi, Duke Math. J. 153 (2010), 229 to 295, who prove integral expansions of theta functions of CM curves at ordinary primes $p \ge 5$. The source has no condition on $p$, but it needs $d \equiv 7 \pmod 8$.

### Isogenies

Recall `PeriodPair.IsIsogeny`: multiplication by $a$ is an isogeny of degree $N$ from $\Lambda$ to $\Lambda'$ if $a\Lambda \subseteq \Lambda'$ and $a\bar a\, A(\Lambda) = N A(\Lambda')$.

**Theorem (Isogenies are integral).** Let $C$ and $C'$ be CM lattices, and let multiplication by $a$ be an isogeny of degree $N$ from $\Lambda_C$ to $\Lambda_{C'}$. Then:

1. there is $v \in \mathfrak{o}[[y_C]]$ with $\theta_{C'}(az) = \theta_C(z)^N v$ as series;
2. the series $y_{C'}(az)$ lies in $\mathfrak{o}[[y_C]]$;
3. if only $a\Lambda_C \subseteq \Lambda_{C'}$ is known, then $|\iota_p(a)| \le 1$.

Lean: `New.CMLattice.exists_rescale_theta_eq_theta_pow_mul`, `New.CMLattice.rescale_translatedY_mem_integralSeriesRing`, `New.CMLattice.norm_le_one_of_mapsTo_lattice` (Lib/CM/Integrality/IsogenyIntegrality.lean).

*Proof.* (1) The function $z \mapsto \theta_{C'}(az)$ is a section of degree $N$ for $C$, and its torsion values are torsion values of $\theta_{C'}$, so they are integral. Apply the integrality principle. (2) In the same way, $G_{C'}(az) = \theta_C^{3N}R_3$ and $\theta_{C'}(az) = \theta_C^NR_1$ with $R_1, R_3 \in \mathfrak{o}[[y_C]]$. Both theta series have the constant term $1$, so $R_1$ is a unit of the ring. Then $y_{C'}(az) = R_3R_1^{-3}$. (3) Some $N$ makes $a$ an isogeny of degree $N$ (`New.exists_isIsogeny_of_mul_mem_lattice`). The coefficient of $z$ in $y_{C'}(az)$ is $\iota_p(a)$. An element of $\mathfrak{o}[[y_C]]$ has an integral coefficient of $z$, since $y_C = z + \cdots$. $\square$

Part (3) is used in [Section 7](/decl/New.CMLattice.chowla_selberg/): the scalings between the CM lattices of the classes are integral, and the products of these scalings are $p$-adic units.

### The group law

**Lemma (Logarithm of theta).** Let $g = -\log\theta$, the series with $g(0) = 0$, read in $\mathbb{C}_p$. Then
$$g'' = g''(0) + x$$
as power series, where $g''(0) = 2\,\mathrm{coeff}_2(g)$.

Lean: `New.CMLattice.derivative_derivative_negLogTheta` (Lib/CM/Integrality/LogTheta.lean).

*Proof.* Differentiate [the addition formula for theta](/decl/New.CMLattice.theta_add_mul_theta_sub/) twice in $w$ at $w = 0$. With $\theta(0) = 1$, $\theta'(0) = 0$, $\sigma(0) = 0$ and $\sigma'(0) = 1$, this gives $\theta'^2 = \theta\theta'' + (c + x)\theta^2$ with $c = -\theta''(0)$. Divide by $\theta^2$. $\square$

Classically, $-\log\sigma_W$ has the second derivative $\wp$, and the lemma is the same fact for the translate by $t$.

**Theorem (Integral group law).** Let $y(z_0 + z_1)$ be the series of $y$ at $z_0 + z_1$ in two variables. Then $y(z_0 + z_1)$ is an integral power series in $y(z_0)$ and $y(z_1)$.

Lean: `New.CMLattice.translatedY_add_mem_multiSeriesRing` (Lib/CM/Integrality/LogTheta.lean), with `New.CMLattice.multiSeriesRing`.

*Proof.* Euler's addition formula on the cubic expresses the third point of a line through two points in terms of their coordinates. It gives an integral series in $y(z_0)$ and $y(z_1)$, since $x \in \mathfrak{o}[[y]]$ and $a_1$ is integral. This series and $y(z_0 + z_1)$ are both killed by $\partial_0 - \partial_1$, and both equal $y(z_1)$ at $z_0 = 0$. So they are equal. $\square$

The docstring cites *AEC*, Chapter IV, §1 and §2, for the classical form: the formal group law of a Weierstrass equation with integral coefficients is integral.

### The height and the formal parameter

Let $\pi_p = \sqrt{-d}$ if $p = d$, and $\pi_p = p$ otherwise (`New.piPrime`). Let $q_p$ be the norm of a prime of $K$ above $p$, so $q_p = p^2$ if $p$ is inert and $q_p = p$ otherwise (`New.primeNorm`). For $\alpha \in \mathcal{O}_K$, the series $y(\alpha z)$ lies in $\mathfrak{o}[[y]]$ by the theorem on isogenies. Let $o(\alpha)$ be its order in $y$ modulo the maximal ideal of $\mathfrak{o}$ (`New.CMLattice.insepDegree`).

**Theorem (Height bound).** If $\alpha \in \mathcal{O}_K$, $\alpha \ne 0$ and $\alpha\bar\alpha = \nu$, then $o(\alpha) \le \nu$. For every prime $p$, $o(\pi_p) \le q_p$.

Lean: `New.CMLattice.insepDegree_le`, `New.CMLattice.insepDegree_piPrime_le` (Lib/CM/FormalGroup/InseparableDegree.lean).

*Proof.* Write $x(\alpha z)v^2 = R(x)$ with $v = \theta(\alpha z)/\theta^\nu$ a unit of $\mathfrak{o}[[y]]$ and $R$ an integral polynomial. The polynomial $R$ has a unit coefficient in some degree $i \le \nu$. Since $x$ has order $2$ in $y$, the order of $x(\alpha z)$ modulo the maximal ideal is at most $2\nu$, and $o(\alpha) \le \nu$. For $p$ not split, $\pi_p\bar\pi_p = q_p$, and the first part applies. For $p$ split, $\pi_p = q_p = p$. The source writes $p^h = \alpha\bar\alpha$ with $\iota_p(\bar\alpha)$ a unit, and compares the orders of $y(p^hz)$, $y(\alpha z)$ and $y(\bar\alpha z)$. $\square$

The file calls this a case of Deuring's criterion: the formal group of the reduction has height at most $1$ at split primes and at most $2$ at the others. It cites Deuring's paper of 1941, Blake (arXiv 1311.5454, Theorem 1.1) and Bluher (ANTS-III, LNCS 1423, 1998).

**Theorem (Formal parameter).** Let $T$ be the part of the series $y$ in the degrees $\equiv 1 \pmod{q_p - 1}$ (`New.CMLattice.formalParam`). There are $\varpi \in \mathbb{C}_p$ and $Y \in \mathfrak{o}[[z]]$ such that:

1. $|\varpi| = p^{-\rho_p}$, with $\rho_p = 1/(p - 1)$ for $p$ split, $1/(p^2 - 1)$ for $p$ inert, and $1/(2d - 2)$ for $p = d$;
2. $T(\varpi z) = \varpi\, Y(z)$;
3. $Y - Y^{q_p} \equiv z$ modulo $\iota_p(\pi_p)$;
4. for every $n$, the coefficient of $z^n$ in $Y$ is $\equiv 1$ modulo $\iota_p(\pi_p)$ if $n$ is a power of $q_p$, and $\equiv 0$ otherwise.

Lean: `New.CMLattice.exists_scaled_formalParam` (Lib/CM/FormalGroup/FormalParameter.lean).

*Proof.* The series $T$ generates $\mathfrak{o}[[y]]$ (`New.CMLattice.isSeriesGenerator_formalParam`). Write $T(\pi_p z) = \pi_p T + b_1T^{q_p} + \cdots$. By the height bound, $b_1$ is a unit. Take $\varpi^{q_p - 1} = -\pi_p/b_1$. Then $Y = T(\varpi z)/\varpi$ satisfies a functional equation $Y(\pi_pz)/\pi_p = Y - Y^{q_p} + \pi_pE(Y)$, and the solutions of this equation are integral, by induction on the degree, in the manner of Lubin and Tate (`New.exists_seriesToCp_eq_of_rescale_eq`). The congruences follow from the equation. $\square$

**Remark (Formalization).** The statements of this section hold for every ring homomorphism $\iota_p : \mathbb{C} \to \mathbb{C}_p$, provided as an instance of `New.PadicPlace p`. The source does not choose a canonical one, and the results do not depend on a choice. The source does not define the reduction of the curve, its formal group as a formal group law over a ring of integers, or the height. "Height at most $1$" is the bound $o(\pi_p) \le q_p$ on the order of a power series modulo the maximal ideal of $\mathfrak{o}$. The formal parameter $T$ and the number $\varpi$ are obtained by existence statements, so later uses get them through `choose` or `obtain`, and only the listed properties are known.
