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

Both sides of the Siegel-Weil formula are limits: the left side is an integral of a function that is not bounded, and the right side is a sum over infinitely many Lagrangians. This section proves that both converge when $2p < m$. The tool is the torus of the Levi subgroup of a complete splitting, normalized so that the zero term of the splitting has constant size along it. Along the torus the other zero terms decay, and Siegel sets show that every point is in the torus up to a rational point and a compact set.

Fix a complete splitting $P$ of $S$ into $p$ hyperbolic planes, with frames $l$ and $k$. Let $d$ be the number of infinite places of $E$, which is the degree of $E^+$ over $\mathbb{Q}$. For $x \in \mathbb{N}^p$ let $\delta(x)$ be the diagonal adelic matrix with entries $2^{x_i}$ at the infinite places and $1$ at the finite places, and let $a_x = P.\mathrm{levi}(\delta(x), 1)$. The idele $\det \delta(x)$ has norm $(2^d)^{2\sum_i x_i}$, since each infinite place of the CM field is complex and the norm there is the square of the absolute value.

### The normalized torus

**Definition (Normalized torus).** For $x \in \mathbb{N}^p$, the normalized torus operator on $\mathcal{S}(\mathrm{Hom}(S, T))$ is
$$A_x = \big((2^d)^{\sum_i x_i}\big)^{-m}\, \omega(a_x, 1).$$

Lean: `New.SiegelWeil.normalisedTorus`, `New.Core.dyadicDiag`, `New.Core.numInfPlaces` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

**Theorem (Values along the torus).** The operator $A_0$ is the identity. For every adelic $m \times p$ matrix $y$ and every $f$,
$$\big\| (A_x f)[y] \big\| = \big\| f[y\, \delta(x)] \big\|.$$

Lean: `New.SiegelWeil.normalisedTorus_zero`, `New.SiegelWeil.norm_mixedValue_normalisedTorus` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

*Proof.* By the Levi law of Section 2, $(\omega(a_x, 1) f)[y]$ is $\chi(\det \delta(x))^{-1} \sqrt{|\det \delta(x)|}^{\,m} f[y \delta(x)]$. The character has norm $1$, and $\sqrt{|\det \delta(x)|}^{\,m} = ((2^d)^{\sum x_i})^m$. The normalizing factor cancels this. At $x = 0$ the matrix $\delta(0)$ is $1$. $\square$

So $A_x$ keeps the size of the zero term of $L_P$ and moves the other values of $f$ outward. The term $x \mapsto f[y\delta(x)]$ is a value of $f$ far from $0$ when $y$ has a nonzero entry, and such values decay.

### An integrable majorant of theta

**Theorem (Integrable majorant).** Suppose that $2p < m$. There is a measurable function $N : G_T \to [0, \infty]$ with $\int N\, d\mu_T < \infty$ for the quotient measure $\mu_T$ of $[U(T)]$, such that
$$\big\|\theta\big(\omega(1, h) A_x f\big)\big\| \le N(h)\, \|f\|$$
for all $h \in G_T$, all $x \in \mathbb{N}^p$ and all $f$.

Lean: `New.SiegelWeil.theta_normalisedTorus_le`, `New.Space.quotMeasure`, `New.Space.lintegral_encard_ne_top` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean; Lib/Adelic/Reduction/FiniteVolume.lean).

*Proof.* Expand the theta function as the sum over the rational $m \times p$ matrices $\xi$ of the values $(A_x f)[h^{-1}\xi]$, by the theorem on theta in the Schrödinger model. By the theorem above, the term of $\xi$ has the norm of $f[h^{-1}\xi\delta(x)]$. The estimate `exists_tsum_slice_le` of the slices bounds such a sum by a constant times $\|f\|$ times the number of $\xi$ whose point $h^{-1}\xi\delta(x)$ lies in a fixed compact set. Since the entries of $\delta(x)^{-1}$ lie in the unit box, these $\xi$ have $h^{-1}\xi$ in a compact set that does not depend on $x$. So $N(h)$ can be a constant times the number of rational $\xi$ with $h^{-1}\xi$ in one compact set $B$. This is a counting function of a lattice in $\mathbb{A}^{m \times p}$ moved by $h$. By the theorem `New.Space.lintegral_encard_ne_top` of [reduction theory](/chapter/reduction-theory/), the count of rational $m \times p$ matrices $\xi$ with $h^{-1}\xi \in B$ has a finite integral over $[U(T)]$ when $2p < m$. This is the only place where the proof of the majorant uses the rank condition. $\square$

**Remark (Formalization).** The docstring of the theorem says that the hypothesis $2p < m$ is stronger than Weil's condition on the Witt index of $T$. For anisotropic $T$, where $[U(T)]$ is compact, the source still asks for $2p < m$. The applications of the chapter satisfy it.

**Theorem (The theta integral converges).** Suppose that $2p < m$. For every $f$ the function $h \mapsto \theta(\omega(1, h) f)$ is integrable on $G_T$ for the quotient measure $\mu_T$.

Lean: `New.SiegelWeil.integrable_theta_splitWeil` (Lib/SiegelWeil/Formula/WeilRange.lean).

*Proof.* The function is continuous, so it is measurable. At $x = 0$ the majorant gives $\|\theta(\omega(1, h) f)\| \le N(h)\|f\|$, and $\int N\|f\| < \infty$. $\square$

### Siegel sets

The second half of the convergence concerns the Eisenstein series. Each Lagrangian has the form $\gamma L_P$ for a rational $\gamma$, by Witt's theorem, and the size of its zero term at a point $g$ depends on where $\gamma^{-1} g$ lies in the cusp of $P$. The following normal form makes this exact. Write $n(\nu) = P.\mathrm{radicalElement}(0, \nu)$ for the unipotent element with $k \mapsto k$ and $l \mapsto l - k(\tfrac12 \jmath^{-1}(\nu + \nu^*))$.

**Theorem (Normal form along a Lagrangian).** There is a compact set $\Omega$ of pairs $(\nu, \kappa)$, with $\nu$ an adelic $p \times p$ matrix and $\kappa \in G_S$, with the following property. For every $g \in G_S$ and every rational $\gamma \in U(S)(E)$ there are a rational $\delta \in U(S)(E)$, integers $x \in \mathbb{Z}^p$, a rational $y \in \mathrm{GL}_p(E)$ and a matrix $\nu$ such that

1. $\big(\nu,\ a_x\, n(\nu)^{-1}\, \delta^{-1} g\big) \in \Omega$, where now $x \in \mathbb{Z}^p$ in $a_x$, and
2. $\delta^{-1}\gamma$ acts on the frame $k$ by $k \mapsto k y$.

In particular $\delta k$ and $\gamma k$ span the same Lagrangian.

Lean: `New.SiegelWeil.exists_compact_parabolic_normal_form`, `New.Space.Splitting.radicalElement`, `New.Space.Splitting.levi` (Lib/SiegelWeil/Formula/WeilRange.lean).

*Proof.* Choose $\kappa$ in the maximal compact subgroup with $\gamma^{-1} g \kappa = n(z)\, \mathrm{levi}(a, 1)$, by the Iwasawa decomposition. Reduction theory for $\mathrm{GL}_p$ gives a rational $y$ and integers $x$ such that $a^{-1} y\, \delta(x)^{-1}$ lies in a compact set. The rational $p \times p$ matrices form a lattice of covolume one in the adelic matrices, so a rational $r$ moves the conjugate of $z$ into a compact set. Put $\delta = \gamma\, (n(r)\, \mathrm{levi}(y^{-1}, 1))^{-1}$. Then $\delta^{-1}\gamma = n(r)\,\mathrm{levi}(y^{-1}, 1)$ acts on $k$ by $k \mapsto k y^{-1}$, which is (2) for the rational matrix $y^{-1}$. The compact set is a product of the compact sets above with the maximal compact subgroup. Conjugation by $a_x$ sends $n(b)$ to $n(\delta(x)\, b\, \delta(x)^*)$, by `New.SiegelWeil.radicalElement_eq_conj_levi`, which moves the unipotent factor to the left. $\square$

**Theorem (Siegel sets).** There is a compact set $\Omega \subseteq G_S$ such that every $g \in G_S$ has the form
$$g = \gamma\, a_x\, \kappa, \qquad \gamma \in U(S)(E),\ x \in \mathbb{N}^p,\ \kappa \in \Omega.$$

Lean: `New.SiegelWeil.exists_siegel_set`, `New.Space.mahler_criterion` (Lib/SiegelWeil/Formula/WeilRange.lean).

*Proof.* The normal form gives $g = \delta\, n(\nu)\, a_x^{-1} \kappa'$ with $x \in \mathbb{Z}^p$ and $(\nu, \kappa')$ in a compact set. The point is to show that the exponents can be taken $\ge 0$ after a shift by a fixed vector. By [Mahler's criterion](/chapter/reduction-theory/), there are a rational basis $W$ of $E^n$ and a set $I$ of its columns such that the matrix $(x_S g)^{-1} W D$, for the projection $D$ onto the columns in $I$, lies in a compact set, and the Gram matrix of $WD$ lies in a finite set. For each $I$ and each Gram matrix in the finite set, fix once an isotropic frame $R$ adapted to it. The columns of $WD$ in $I$ span an isotropic space, so by Witt's theorem $WDR = \alpha k$ for a rational isometry $\alpha$. In the normal form for $\gamma = \alpha$, the frame $\delta^{-1} WDR$ is $k y$ with $y$ rational. The entries $2^{x_i} y_{ij}$ lie in a compact set, and a rational entry that is small enough at the infinite places, with this bound at the finite places, is zero. Each row $i$ of $y$ is nonzero, so $x_i$ is at most a constant $-c_i$. Write $x_i + t_i = -c_i$ with $t_i \ge 0$. Then $g = \delta\, a_t\, \kappa$ with $\kappa$ in a compact set that contains the fixed factor $a_{-c}$. $\square$

This is the adelic form of the classical Siegel set: a fundamental set for $U(S)(E)\backslash G_S$ is the product of a compact set and the positive cone of the torus of one Siegel parabolic subgroup.

### Uniform summability of the zero terms

**Theorem (A summable majorant of the zero terms).** Suppose that $2p < m$. There is a summable function $c$ on the Lagrangians of $S$ such that
$$\big\|\mathrm{ev}_L \circ A_x\big\| \le c(L)$$
for every $x \in \mathbb{N}^p$ and every Lagrangian $L$, where $\|\cdot\|$ is the operator norm.

Lean: `New.SiegelWeil.exists_summable_zeroTerm_bound`, `New.SiegelWeil.tsum_div_two_pow_lt_top`, `New.SiegelWeil.lagrangian_isometrySplitting_comp_eq` (Lib/SiegelWeil/Formula/WeilRange.lean).

*Proof.* Write $q = 2^d$. For each Lagrangian $L$ choose a rational $\gamma_L$ such that the columns of $\gamma_L k$ are orthogonal to $L$, and apply the normal form at $g = 1$ to $\gamma_L$. This gives a rational $\delta_L$ with $L = \delta_L L_P$, by `lagrangian_isometrySplitting_comp_eq`, and exponents $x_L \in \mathbb{Z}^p$. Column $j$ of $\delta_L k$ is rational and not zero, and it is $2^{x_{L,j}}$ times a bounded vector. So $x_{L,j}$ is at least a constant $c_j$, and $x_L = c + t_L$ with $t_L \in \mathbb{N}^p$. Then
$$\kappa_L = n(b_L)\, a_{t_L}\, \delta_L^{-1}$$
lies in a fixed compact set $K$, for a rational $p \times p$ matrix $b_L$.

*The bound for one term.* The zero term of $L$ is the zero term of $L_P$ after $\omega(\delta_L^{-1}, 1)$, by the theorem on rational isometries. The unipotent factor $n(b_L)$ keeps the frame $k$, and $a_{t_L}$ acts on it by $\delta(t_L)$. The theorem on the parabolic scaling gives
$$\big\|\mathrm{ev}_{L_P}\big(\omega(\kappa_L, 1)\, \varphi\big)\big\| = \big(q^{\sum_i t_{L,i}}\big)^{m}\, \|\mathrm{ev}_L(\varphi)\|.$$
The theorem on a second splitting along the torus, for $P' = P$, with $u = x$ and with $\kappa_L \in K$, bounds the left side for $\varphi = A_x f$ by $R\|f\|$, uniformly in $x$. So
$$\big\|\mathrm{ev}_L \circ A_x\big\| \le \frac{R}{\big(q^{\sum_i t_{L,i}}\big)^{m}}.$$

*The count.* Fix $t \in \mathbb{N}^p$. On the Lagrangians with $t_L = t$, the map $L \mapsto (b_L + b_L^*,\ \epsilon_L \delta_L^{-1})$ is injective, where $\epsilon_L$ is a point chosen with the same property as $\delta_L$. Its second entry is a rational point of the compact set $K^{-1}K$, and there are finitely many of these, say $F$. Its first entry is a rational hermitian matrix in a compact set scaled by $\delta(t)$, and there are at most $C q^{\sum_{i,j}(t_i + t_j)} = C q^{2p\sum_i t_i}$ of these. So at most $C F q^{2p \sum t_i}$ Lagrangians have $t_L = t$. The lemma `tsum_div_two_pow_lt_top` sums over the fibres: the sum of the bounds is at most a constant times
$$\prod_{i \in p} \sum_{a \ge 0} \Big(\frac{2^{2p}}{2^{m}}\Big)^{d a},$$
which is finite since $2p < m$. Put $c(L) = R/(q^{\sum t_{L,i}})^m$. $\square$

This is where the range $2p < m$ enters on the side of the Eisenstein series. The number of Lagrangians of height $t$ grows like $q^{2p\sum t_i}$, and each zero term decays like $q^{-m\sum t_i}$. This is the classical fact that the Siegel Eisenstein series on $U(p, p)$ of weight $m$ converges absolutely for $m > 2p$.

At $x = 0$ the theorem gives that $\sum_L \|\mathrm{ev}_L\|$ is finite. So the sum $\sum_L \mathrm{ev}_L(f)$ converges absolutely for every $f$, and it is a bounded functional of $f$.

### Zero terms of a second splitting

The proof of Section 5 needs the size of the zero term of a second complete splitting along the torus of the first.

**Theorem (A second splitting along the torus).** Let $P$ and $P'$ be complete splittings of $S$ into $p$ and $r$ planes, with frames $k$ and $k'$. Let $Z$ be an adelic $r \times n$ matrix with $Z k' = 1$ in adelic coordinates, and let $K \subseteq G_S$ be compact. There is a constant $R \ge 0$ with the following property. For all $g \in K$, all $x, u \in \mathbb{N}^p$ with $Z g k \delta(x) = Z g k \delta(u)$ and all $f$,
$$\big\|\mathrm{ev}_{L_{P'}}\big(\omega(g, 1) A_x f\big)\big\| \le R\, \|f\|\, 2^{d(\sum u - \sum x)m}.$$

Lean: `New.SiegelWeil.exists_zeroTerm_normalisedTorus_le`, `New.SiegelWeil.exists_ideleAbs_le_of_isCompact` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

*Proof.* Write $g a_x \kappa k' = k' a$ by the Iwasawa decomposition with $\kappa$ in the maximal compact subgroup. Multiply by $Z$ to read off $a$ as a Schur complement. Then $\det a / \det \delta(u)$ is the determinant of a block matrix that stays in a compact set, and the idele norm is bounded on the ideles in a compact set of adeles, by `exists_ideleAbs_le_of_isCompact`. The parabolic scaling moves $a$ out of the zero term. The maximal compact subgroup acts by operators of bounded norm. The normalizing factor of $A_x$ accounts for $\sum x$. $\square$

**Remark (Formalization).** The source does not define the Eisenstein series as a function on $G_S$. It works with the bounded functional $f \mapsto \sum_L \mathrm{ev}_L(f)$ and with its translates $f \mapsto \sum_L \mathrm{ev}_L(\omega(g, 1) f)$. These are the values $E(g, f)$ of the classical series at $g$. The torus estimates replace the theory of the constant term.
