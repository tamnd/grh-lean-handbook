---
title: Siegel sets and convergence
lean:
  - Lib/SiegelWeil/Formula/WeilRange.lean
  - Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean
decls:
  - New.SiegelWeil.normalisedTorus
  - New.SiegelWeil.normalisedTorus_zero
  - New.SiegelWeil.norm_mixedValue_normalisedTorus
  - New.SiegelWeil.theta_normalisedTorus_le
  - New.SiegelWeil.exists_compact_parabolic_normal_form
  - New.SiegelWeil.exists_siegel_set
  - New.SiegelWeil.tsum_div_two_pow_lt_top
  - New.SiegelWeil.exists_summable_zeroTerm_bound
  - New.SiegelWeil.exists_zeroTerm_normalisedTorus_le
  - New.SiegelWeil.integrable_theta_splitWeil
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Siegel sets and convergence

This section proves that both sides of the formula converge when $2p < m$. The tool is the torus of the Levi subgroup of a complete splitting, normalized so that the zero term of the splitting has constant size along it. Along the torus the other zero terms decay, and Siegel sets put every point in the torus up to a rational point and a compact set.

Fix a complete splitting $P$ of $S$ into $p$ hyperbolic planes, with frames $l$ and $k$. Let $d$ be the number of infinite places of $E$, which is the degree of $E^+$ over $\mathbb{Q}$. For $x \in \mathbb{N}^p$ let $\delta(x)$ be the diagonal adelic matrix with entries $2^{x_i}$ at the infinite places and $1$ at the finite places, and let $a_x = P.\mathrm{levi}(\delta(x), 1)$. The idele $\det \delta(x)$ has norm $(2^d)^{2\sum_i x_i}$, since each infinite place of the CM field is complex and the norm there is the square of the absolute value.

### The normalized torus

**Definition (Normalized torus).** For $x \in \mathbb{N}^p$, the normalized torus operator on $\mathcal{S}(\mathrm{Hom}(S, T))$ is
$$A_x = \big((2^d)^{\sum_i x_i}\big)^{-m}\, \omega(a_x, 1).$$

Lean: `New.SiegelWeil.normalisedTorus`, `New.Core.dyadicDiag`, `New.Core.numInfPlaces` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

**Theorem (Values along the torus).** The operator $A_0$ is the identity. For every adelic $m \times p$ matrix $y$ and every $f$,
$$\big\| (A_x f)[y] \big\| = \big\| f[y\, \delta(x)] \big\|.$$

Lean: `New.SiegelWeil.normalisedTorus_zero`, `New.SiegelWeil.norm_mixedValue_normalisedTorus` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

*Proof.* This is the Levi law of Section 2: the character has norm $1$, and the normalizing factor cancels $\sqrt{|\det \delta(x)|}^{\,m} = ((2^d)^{\sum x_i})^m$. $\square$

### An integrable majorant of theta

**Theorem (Integrable majorant).** Suppose that $2p < m$. There is a measurable function $N : G_T \to [0, \infty]$ with $\int N\, d\mu_T < \infty$ for the quotient measure $\mu_T$ of $[U(T)]$, such that
$$\big\|\theta\big(\omega(1, h) A_x f\big)\big\| \le N(h)\, \|f\|$$
for all $h \in G_T$, all $x \in \mathbb{N}^p$ and all $f$.

Lean: `New.SiegelWeil.theta_normalisedTorus_le`, `New.Space.quotMeasure`, `New.Space.lintegral_encard_ne_top` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean; Lib/Adelic/Reduction/FiniteVolume.lean).

*Proof.* By the theorem on theta in the Schrödinger model and the theorem above, the theta function is a sum over rational $\xi$ of terms of norm $\|f[h^{-1}\xi\delta(x)]\|$. The slice estimate `exists_tsum_slice_le` bounds this sum by a constant times $\|f\|$ times the number of $\xi$ with $h^{-1}\xi$ in one compact set $B$, which does not depend on $x$ since the entries of $\delta(x)^{-1}$ lie in the unit box. By `New.Space.lintegral_encard_ne_top` of [reduction theory](/chapter/reduction-theory/), this count has a finite integral over $[U(T)]$ when $2p < m$. $\square$

**Remark (Formalization).** The docstring of the theorem says that the hypothesis $2p < m$ is stronger than Weil's condition on the Witt index of $T$. For anisotropic $T$, where $[U(T)]$ is compact, the source still asks for $2p < m$. The applications of the chapter satisfy it.

**Theorem (The theta integral converges).** Suppose that $2p < m$. For every $f$ the function $h \mapsto \theta(\omega(1, h) f)$ is integrable on $G_T$ for the quotient measure $\mu_T$.

Lean: `New.SiegelWeil.integrable_theta_splitWeil` (Lib/SiegelWeil/Formula/WeilRange.lean).

*Proof.* Take $x = 0$ in the majorant; the function is continuous. $\square$

### Siegel sets

For the Eisenstein series, each Lagrangian is $\gamma L_P$ for a rational $\gamma$, by Witt's theorem, and the size of its zero term at $g$ depends on where $\gamma^{-1} g$ lies in the cusp of $P$. Write $n(\nu) = P.\mathrm{radicalElement}(0, \nu)$ for the unipotent element with $k \mapsto k$ and $l \mapsto l - k(\tfrac12 \jmath^{-1}(\nu + \nu^*))$.

**Theorem (Normal form along a Lagrangian).** There is a compact set $\Omega$ of pairs $(\nu, \kappa)$, with $\nu$ an adelic $p \times p$ matrix and $\kappa \in G_S$, with the following property. For every $g \in G_S$ and every rational $\gamma \in U(S)(E)$ there are a rational $\delta \in U(S)(E)$, integers $x \in \mathbb{Z}^p$, a rational $y \in \mathrm{GL}_p(E)$ and a matrix $\nu$ such that

1. $\big(\nu,\ a_x\, n(\nu)^{-1}\, \delta^{-1} g\big) \in \Omega$, where now $x \in \mathbb{Z}^p$ in $a_x$, and
2. $\delta^{-1}\gamma$ acts on the frame $k$ by $k \mapsto k y$.

In particular $\delta k$ and $\gamma k$ span the same Lagrangian.

Lean: `New.SiegelWeil.exists_compact_parabolic_normal_form`, `New.Space.Splitting.radicalElement`, `New.Space.Splitting.levi` (Lib/SiegelWeil/Formula/WeilRange.lean).

*Proof.* Write $\gamma^{-1} g \kappa = n(z)\, \mathrm{levi}(a, 1)$ by the Iwasawa decomposition. Reduction theory for $\mathrm{GL}_p$ gives a rational $y$ and integers $x$ with $a^{-1} y\, \delta(x)^{-1}$ in a compact set, and since the rational $p \times p$ matrices are a lattice of covolume one, a rational $r$ moves the unipotent part into a compact set. Put $\delta = \gamma\, (n(r)\, \mathrm{levi}(y^{-1}, 1))^{-1}$. Conjugation by $a_x$, by `New.SiegelWeil.radicalElement_eq_conj_levi`, moves the unipotent factor to the left. $\square$

**Theorem (Siegel sets).** There is a compact set $\Omega \subseteq G_S$ such that every $g \in G_S$ has the form
$$g = \gamma\, a_x\, \kappa, \qquad \gamma \in U(S)(E),\ x \in \mathbb{N}^p,\ \kappa \in \Omega.$$

Lean: `New.SiegelWeil.exists_siegel_set`, `New.Space.mahler_criterion` (Lib/SiegelWeil/Formula/WeilRange.lean).

*Proof.* The normal form gives $g = \delta\, n(\nu)\, a_x^{-1} \kappa'$ with $x \in \mathbb{Z}^p$; the point is that $x$ is bounded above. By [Mahler's criterion](/chapter/reduction-theory/) there is a rational isotropic frame $WDR$, from a finite list of Gram matrices, with $(x_S g)^{-1} WDR$ in a compact set. By Witt's theorem it is $\alpha k$ for a rational isometry $\alpha$, and the normal form for $\gamma = \alpha$ makes it $\delta k y$ with $y$ rational. The entries $2^{x_i} y_{ij}$ lie in a compact set, and each row of $y$ is a nonzero rational vector, so $x_i \le -c_i$ for a constant $c_i$. Shift by $a_{-c}$ into the compact set. $\square$

This is the adelic form of the classical Siegel set: a fundamental set for $U(S)(E)\backslash G_S$ is the product of a compact set and the positive cone of the torus of one Siegel parabolic subgroup.

### Uniform summability of the zero terms

**Theorem (A summable majorant of the zero terms).** Suppose that $2p < m$. There is a summable function $c$ on the Lagrangians of $S$ such that
$$\big\|\mathrm{ev}_L \circ A_x\big\| \le c(L)$$
for every $x \in \mathbb{N}^p$ and every Lagrangian $L$, where $\|\cdot\|$ is the operator norm.

Lean: `New.SiegelWeil.exists_summable_zeroTerm_bound`, `New.SiegelWeil.tsum_div_two_pow_lt_top`, `New.SiegelWeil.lagrangian_isometrySplitting_comp_eq` (Lib/SiegelWeil/Formula/WeilRange.lean).

*Proof.* Write $q = 2^d$. The normal form at $g = 1$ writes each Lagrangian as $L = \delta_L L_P$, by `lagrangian_isometrySplitting_comp_eq`, with $\kappa_L = n(b_L)\, a_{t_L}\, \delta_L^{-1}$ in a fixed compact set $K$, $b_L$ rational and $t_L \in \mathbb{N}^p$; the exponents are bounded below because the columns of $\delta_L k$ are nonzero rational vectors. The theorem on rational isometries, the parabolic scaling and the theorem on a second splitting below (for $P' = P$, $u = x$) give
$$\big\|\mathrm{ev}_L \circ A_x\big\| \le \frac{R}{\big(q^{\sum_i t_{L,i}}\big)^{m}}$$
uniformly in $x$. For the count, the map $L \mapsto (b_L + b_L^*,\ \epsilon_L \delta_L^{-1})$ is injective on the Lagrangians with $t_L = t$. Its second entry is one of finitely many rational points of $K^{-1}K$, and its first is a rational hermitian matrix in a compact set scaled by $\delta(t)$, with at most $C q^{2p\sum_i t_i}$ choices. By `tsum_div_two_pow_lt_top` the sum of the bounds is at most a constant times
$$\prod_{i \in p} \sum_{a \ge 0} \Big(\frac{2^{2p}}{2^{m}}\Big)^{d a},$$
which is finite since $2p < m$. Put $c(L) = R/(q^{\sum t_{L,i}})^m$. $\square$

So the number of Lagrangians of height $t$ grows like $q^{2p\sum t_i}$, and each zero term decays like $q^{-m\sum t_i}$. This is the classical absolute convergence of the Siegel Eisenstein series on $U(p, p)$ of weight $m > 2p$. At $x = 0$ the sum $\sum_L \mathrm{ev}_L(f)$ converges absolutely and is a bounded functional of $f$.

### Zero terms of a second splitting

**Theorem (A second splitting along the torus).** Let $P$ and $P'$ be complete splittings of $S$ into $p$ and $r$ planes, with frames $k$ and $k'$. Let $Z$ be an adelic $r \times n$ matrix with $Z k' = 1$ in adelic coordinates, and let $K \subseteq G_S$ be compact. There is a constant $R \ge 0$ with the following property. For all $g \in K$, all $x, u \in \mathbb{N}^p$ with $Z g k \delta(x) = Z g k \delta(u)$ and all $f$,
$$\big\|\mathrm{ev}_{L_{P'}}\big(\omega(g, 1) A_x f\big)\big\| \le R\, \|f\|\, 2^{d(\sum u - \sum x)m}.$$

Lean: `New.SiegelWeil.exists_zeroTerm_normalisedTorus_le`, `New.SiegelWeil.exists_ideleAbs_le_of_isCompact` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

*Proof.* Write $g a_x \kappa k' = k' a$ by the Iwasawa decomposition and read off $a$ with $Z$ as a Schur complement. Then $\det a / \det \delta(u)$ is a determinant that stays in a compact set, and `exists_ideleAbs_le_of_isCompact` bounds its idele norm. The parabolic scaling moves $a$ out of the zero term, and the normalizing factor of $A_x$ accounts for $\sum x$. $\square$

**Remark (Formalization).** The source does not define the Eisenstein series as a function on $G_S$. It works with the bounded functional $f \mapsto \sum_L \mathrm{ev}_L(f)$ and with its translates $f \mapsto \sum_L \mathrm{ev}_L(\omega(g, 1) f)$. These are the values $E(g, f)$ of the classical series at $g$. The torus estimates replace the theory of the constant term.
