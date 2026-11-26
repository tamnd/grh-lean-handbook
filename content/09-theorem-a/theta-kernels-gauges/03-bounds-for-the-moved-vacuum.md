---
title: Bounds for the moved vacuum
lean:
  - New/UpperBound/Kernels/JetConjugatesAndBounds.lean
  - Lib/General/Analysis/PackingAndSobolev.lean
decls:
  - New.Parameters.norm_vacuumFn_vecAtPoint_le
  - New.Parameters.exists_intCast_eq_norm_archCoords_sq
  - New.Parameters.one_le_norm_archCoords_sub
  - New.tsum_le_of_separated
  - New.exp_neg_pi_div_mul_sq_le
  - New.sqrt_mul_sq_add_le_of_le
  - New.Parameters.norm_omega_vac_le
  - New.Parameters.IsJetConjugation.norm_map_intVacuum_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Bounds for the moved vacuum

The jets of Section 4 are integrals of the values of a datum against Gaussians. So the first need is a bound for the values. The data in question are the images under $L$ of $\varrho(\mathrm{fin}(x))\,\omega(1, g)\,\theta^\circ$, for all finite $x$ and all finite unitary $g$. The bound must be uniform in $x$, in $g$ and in the point, since later chapters sum over many $g$ and $x$. This section proves
$$\bigl|L\bigl(\varrho(\mathrm{fin}(x))\,\omega(1,g)\,\theta^\circ\bigr)(y)\bigr| \le \exp\bigl(C_P\,(q_1 n + 1)^2\bigr)$$
for all $x$, $g$ and adelic $y$, where $n$ is the rank.

### The idea

There are two steps. First, $L$ maps $\theta^\circ$ to a multiple $a\,\omega(1,u)\,\mathrm{vac}$ of a moved vacuum, by the theorem on the image of the vacuum, and the laws of $L$ move $\varrho$ and $\omega$ through it. So the datum is $a$ times a unit vector of the form $\varrho(y')\,\omega(g')\,\mathrm{vac}$, up to a factor of modulus one. The size of $a$ comes from the conjugate values of $\theta^\circ$, which [the integral vacuum and tight frames](/chapter/integral-vacuum/) bounds by $\exp(C_{\mathrm{vac}} q_1^2)^n$.

Second, a value of $f = \varrho(y)\,\omega(g)\,\mathrm{vac}$ is $\theta(f)$, and $|\theta(f)|^2$ is a theta series of matrix coefficients of $f$:
$$|\theta(f)|^2 = \sum_{\gamma \in E^n} \langle f, \varrho(\gamma) f \rangle.$$
Each coefficient has the modulus of a value of the vacuum on the moved lattice: a Gaussian $\exp(-\pi|\gamma|^2/\sqrt d)$ on a set of vectors whose squared lengths are integers, and $0$ off it. Points with integer squared distances are $1$-separated, so a packing count bounds the series by a constant that depends only on the dimension. This is the uniformity in $g$: the lattice moves, but its separation does not change.

### The model case

Take $E$ replaced by $\mathbb{Q}(i)$ for a moment, rank one, and the lattice $\Lambda = \mathbb{Z}[i] \subset \mathbb{C}$. Then $\sum_{\gamma \in \Lambda} e^{-\pi|\gamma|^2/\sqrt d}$ is at most $\bigl(\sum_{k \in \mathbb{Z}} e^{-\pi k^2/\sqrt d}\bigr)^2 \le (1 + d^{1/4})^2$. For a moved lattice $g\Lambda$ with $g$ unitary over the finite adeles, the set of $\gamma$ changes, but all squared lengths are still integers. The packing bound gives a constant that does not see $g$ at all. In the general case the dimension is $2fn$, and the constant is $e^{O(d\,q_1^2 n^2)}$.

### The vacuum at rational points

Recall the vacuum function of [the Weil representation](/chapter/weil-representation/) in one line: for an adelic vector $x$,
$$\mathrm{vac}(x) = \exp\Bigl(-\sum_{i}\sum_{w \in \Phi} \pi\,\mathrm{Im}(\Phi_w(j))\,|x_{i,w}|^2\Bigr)\cdot\begin{cases}\psi_f\bigl(\tfrac12 \mathrm{tr}_1\, j\, \bar x_f \cdot x_f\bigr) & \text{if } \alpha^{-1} x_{i,f} \in \hat{\mathcal{O}} \text{ for all } i,\\ 0 & \text{else,}\end{cases}$$
where $j \in E$ is the element of the Weil data with $\mathrm{Im}(\Phi_w(j)) = 1/\sqrt d$ at every place, and $\psi_f$ has values of modulus one. For a definite space $W$ (all signs $+1$) with point $x_W$, and $\gamma \in E^n$, write $W.\gamma = x_W^{-1}\gamma$ for the coordinates of $\gamma$ at the point, and $|\gamma|_W$ for the euclidean length of the vector of its archimedean components in $\mathbb{C}^{\Phi \times n}$.

**Lemma (The vacuum at rational points).** For a definite space $W$ over $E$ and $\gamma \in E^n$,
$$|\mathrm{vac}(W.\gamma)| \le \exp\bigl(-\pi |\gamma|_W^2/\sqrt d\bigr).$$

Lean: `New.Parameters.norm_vacuumFn_vecAtPoint_le` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Proof.* Since $\mathrm{Im}(\Phi_w(j)) = 1/\sqrt d$ for all $w$, the exponent is $-\pi/\sqrt d \cdot \sum_{i,w} |(W.\gamma)_{i,w}|^2 = -\pi|\gamma|_W^2/\sqrt d$. The second factor has modulus $1$ or $0$. $\square$

**Lemma (Integral squared lengths).** Let $W$ be a definite space over $E$ given by a hermitian matrix $J$ over $E$ and a point $x_W \in \mathrm{GL}_n(\mathbb{A}_E)$ with $x_W^* J x_W = 1$. Let $\gamma \in E^n$, and suppose that the finite parts of the coordinates of $W.\gamma$, divided by $\alpha$, lie in $\hat{\mathcal{O}}_E$. Then $|\gamma|_W^2$ is an integer.

Lean: `New.Parameters.exists_intCast_eq_norm_archCoords_sq` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Proof.* Put $h = \bar\gamma^{\,T} J \gamma \in E$. Since $x_W^* J x_W = 1$, the image of $h$ at each place is $\sum_i |(W.\gamma)_i|^2$ in the hermitian sense. At an infinite place $w$ this is $\Phi_w(h) = \sum_i |(W.\gamma)_{i,w}|^2$, a real number, and at the finite places it is $\sum_i \overline{(W.\gamma)_{i,f}}\,(W.\gamma)_{i,f}$.

Let $\delta$ be the fixed generator of the relative different of $E/K$ at the places of the Weil data. By the definition of $\alpha$ the idele $\alpha\bar\alpha\delta$ is integral at every finite place. Write
$$\bar z z\,\delta = \alpha\bar\alpha\delta\cdot\overline{(\alpha^{-1}z)}\,(\alpha^{-1}z)$$
for each finite coordinate $z$. By hypothesis $\alpha^{-1}z$ is integral, so the finite part of $h\delta$ is integral, and $h\delta$ is an algebraic integer. So $h$ lies in the inverse different of $E/K$, and its trace $c = \mathrm{tr}_{E/K}(h)$ lies in $\mathcal{O}_K$. The trace is the sum of the conjugates over $K$, so its image in $\mathbb{C}$ is
$$c = \sum_{w \in \Phi} \Phi_w(h) = \sum_{w, i} |(W.\gamma)_{i,w}|^2 = |\gamma|_W^2.$$
This is real. An element of $\mathcal{O}_K$ with $\bar c = c$ lies in $\mathbb{Z}$, since $K$ is imaginary quadratic. $\square$

**Corollary (Separation).** Under the same assumptions on $W$, let $\gamma \ne \delta$ be two vectors of $E^n$ such that both satisfy the integrality condition of the lemma. Then $|\gamma - \delta|_W \ge 1$.

Lean: `New.Parameters.one_le_norm_archCoords_sub` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Proof.* The condition is additive, so $\gamma - \delta$ satisfies it, and $|\gamma - \delta|_W^2 = m$ is an integer. The archimedean component of $W.(\gamma - \delta)$ at one place determines $\gamma - \delta$, so it is not $0$, and $m > 0$. So $m \ge 1$. $\square$

### A packing bound

**Lemma (Packing).** Let $X$ be a real normed space of finite dimension $D_0$, and let $(f_i)_{i \in I}$ be points of $X$ with $\|f_i - f_j\| \ge m > 0$ for $i \ne j$. Let $u_i \ge 1$ and $R \ge 0$ with $\|f_i\| \le R\,u_i$. If $A > D_0$ and $A \le c\,(A - D_0)$, then $\sum_i u_i^{-A}$ converges and
$$\sum_{i \in I} u_i^{-A} \le \Bigl(1 + \frac{2R}{m}\Bigr)^{D_0} c.$$

Lean: `New.tsum_le_of_separated` (Lib/General/Analysis/PackingAndSobolev.lean).

*Proof.* For $r \ge 1$ let $N(r)$ be the number of $i$ with $u_i \le r$. These $f_i$ lie in the ball of radius $Rr$. The balls of radius $m/2$ around them are disjoint and lie in the ball of radius $Rr + m/2$. Comparing Haar measures gives
$$N(r) \le \Bigl(\frac{Rr + m/2}{m/2}\Bigr)^{D_0} = \Bigl(1 + \frac{2Rr}{m}\Bigr)^{D_0} \le \Bigl(1 + \frac{2R}{m}\Bigr)^{D_0} r^{D_0}.$$
By layer cake, since all $u_i \ge 1$,
$$\sum_i u_i^{-A} = \int_1^\infty A\,r^{-A-1} N(r)\,dr \le \Bigl(1 + \frac{2R}{m}\Bigr)^{D_0} A\int_1^\infty r^{D_0 - A - 1}\,dr = \Bigl(1 + \frac{2R}{m}\Bigr)^{D_0}\frac{A}{A - D_0},$$
and $A/(A - D_0) \le c$. $\square$

We use it with $m = R = 1$, $u_\gamma = \exp|\gamma|_W$, $A = D_0 + 1$ and $c = e^{D_0}$. The condition $\|f\| \le e^{\|f\|}$ holds since $e^t \ge 1 + t$, and $D_0 + 1 \le e^{D_0}$ for the same reason. The result is
$$\sum_\gamma \exp(|\gamma|_W)^{-(D_0+1)} \le 3^{D_0} e^{D_0} \le e^{3D_0}. \tag{3.1}$$

### Two inequalities

**Lemma (Completing the square).** For $a > 0$ and real $t, D$,
$$\exp\bigl(-\pi t^2/a\bigr) \le \exp(a D^2)\,(e^t)^{-D}.$$

Lean: `New.exp_neg_pi_div_mul_sq_le` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Proof.* The claim is $tD \le \pi t^2/a + aD^2$. The difference is
$$\frac{1}{a}\Bigl(\bigl(\pi - \tfrac14\bigr)t^2 + \bigl(\tfrac t2 - aD\bigr)^2\Bigr) \ge 0,$$
since $\pi \ge 2 > 1/4$. $\square$

**Lemma (Comparison of exponents).** For natural numbers $d$, $M$, $\delta$ with $\delta \le 2M$,
$$\sqrt d\,(\delta + 1)^2 + 3\delta \le 2\,(2d + 6)\,(M + 1)^2.$$

Lean: `New.sqrt_mul_sq_add_le_of_le` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Proof.* Use $\sqrt d \le d$ and $\delta \le 2M$. The left side is at most $d(2M+1)^2 + 6M = 4dM^2 + 4dM + d + 6M$. The right side is $(4d + 12)(M^2 + 2M + 1) = 4dM^2 + 8dM + 4d + 12M^2 + 24M + 12$. Each term on the left is at most a term on the right. $\square$

### The moved vacuum

**Lemma (Values of the moved vacuum).** Let $V$ be a definite space of rank $n$ over $E$, all signs $+1$. For every point $g$ of the adelic unitary group of $V$ and every adelic vector $y$,
$$\bigl|(\omega(g)\,\mathrm{vac})(y)\bigr| \le \exp\bigl((2d + 6)\,(q_1 n + 1)^2\bigr).$$

Lean: `New.Parameters.norm_omega_vac_le` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Proof.* Let $W$ be the space $V$ moved by $g$: the same hermitian matrix with the point multiplied by $g$. Let $S$ be the set of $\gamma \in E^n$ such that the finite coordinates of $W.\gamma$, divided by $\alpha$, are integral. Let $D_0 = 2fn$ be the real dimension of $\mathbb{C}^{\Phi\times n}$, and put $D = D_0 + 1$.

Put $G = \varrho(y)\,\omega(g)\,\mathrm{vac}$. By the definition of values, $(\omega(g)\mathrm{vac})(y) = \theta(G)$. By the summation formula of [the Weil representation](/chapter/weil-representation/), [`New.Space.hasSum_dataInner`](/decl/New.Space.hasSum_dataInner/),
$$\sum_{\gamma \in E^n} \langle G, \varrho(V.\gamma)\,G\rangle = \theta(G)\,\overline{\theta(G)} = |\theta(G)|^2.$$
Now bound each term. The Heisenberg operator $\varrho(y)$ changes the matrix coefficient only by a factor of modulus one. The matrix coefficient of $\omega(g)\mathrm{vac}$ at $V.\gamma$ is $\mathrm{vac}(g^{-1}V.\gamma) = \mathrm{vac}(W.\gamma)$, by the formula for matrix coefficients of the moved vacuum. So the term at $\gamma$ has modulus $|\mathrm{vac}(W.\gamma)|$. It is $0$ for $\gamma \notin S$, by the definition of $\mathrm{vac}$. For $\gamma \in S$, the lemma on rational points and completing the square with $a = \sqrt d$ and $t = |\gamma|_W$ give
$$|\mathrm{vac}(W.\gamma)| \le \exp(-\pi|\gamma|_W^2/\sqrt d) \le \exp(\sqrt d\,D^2)\,\exp(|\gamma|_W)^{-D}.$$
The points $\gamma \in S$ are $1$-separated in $\mathbb{C}^{\Phi\times n}$, by the corollary on separation. So (3.1) gives
$$|\theta(G)|^2 \le \exp(\sqrt d\,D^2)\,e^{2D_0}e^{D_0} = \exp\bigl(\sqrt d\,(D_0+1)^2 + 3D_0\bigr).$$
It remains to compare exponents. The number $f = |\Phi|$ of infinite places of $E$ is $[E:K] \le \varphi(q_1) \le q_1$, so $D_0 = 2fn \le 2q_1 n$. The comparison lemma with $\delta = D_0$ and $M = q_1 n$ gives $|\theta(G)|^2 \le \exp((2d+6)(q_1n+1)^2)^2$. Take square roots. $\square$

The bound is wasteful, and it does not matter: the exponent $(q_1 n + 1)^2$ is of the same order as the exponents that later chapters gain from divisibility.

### The image of the integral vacuum

Recall from [the integral vacuum and tight frames](/chapter/integral-vacuum/) in one line: $\theta^\circ = c_s^{\,n}\,\mathrm{vac}$ for a fixed number $c_s$, and $|\sigma(\theta^\circ(\mathrm{fin}(x)))| \le \exp(C_{\mathrm{vac}}\,q_1^2)^n$ for all $\sigma \in \mathrm{Gal}(\mathbb{C}/K)$ and all finite $x$. The same chapter shows that $|\langle F, F\rangle| \le M^2$ for a datum $F$ with $|F(\mathrm{fin}(x))| \le M$ at all finite $x$. Recall also that $C_P = C_{\mathrm{vac}} + (2d+6) + C'$, with $C' = q_0 + |C_d| + \sum_w |\log|\Phi_{q_0}'(w)||$ over the primitive $q_0$-th roots of unity $w$, a nonnegative number.

**Theorem (Values of the conjugated vacuum).** Let $V$ be a standard space of rank $n$, and let $L$ be a jet conjugation for $(\sigma, t, b)$ on $V$. Then for every finite adelic vector $x$, every finite unitary matrix $g$ and every adelic vector $y$,
$$\Bigl|L\bigl(\varrho(\mathrm{fin}(x))\,\omega(1, g)\,\theta^\circ\bigr)(y)\Bigr| \le \exp\bigl(C_P\,(q_1 n + 1)^2\bigr).$$

Lean: `New.Parameters.IsJetConjugation.norm_map_intVacuum_le` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Proof.* By the theorem on the image of the vacuum with $R = \emptyset$, $L\,\mathrm{vac} = c\,\omega(1, u)\,\mathrm{vac}$ for some $c$ and a finite unitary scalar $u$. Since $L$ is $\sigma$-semilinear,
$$L\,\theta^\circ = a\,\omega(1,u)\,\mathrm{vac}, \qquad a = \sigma(c_s^{\,n})\,c.$$

*The size of $a$.* Let $w$ be a finite adelic vector. Since $b$ is a unit (it scales translations bijectively), $w = b w'$ for some $w'$. By the lemma on conjugate values,
$$|(L\theta^\circ)(\mathrm{fin}(w))| = |\sigma(\theta^\circ(\mathrm{fin}(w')))| \le \exp(C_{\mathrm{vac}}q_1^2)^n.$$
So $|\langle L\theta^\circ, L\theta^\circ\rangle| \le \exp(C_{\mathrm{vac}}q_1^2)^{2n}$. The datum $\omega(1,u)\,\mathrm{vac}$ is a unit vector, so the left side is $|a|^2$, and $|a| \le \exp(C_{\mathrm{vac}}q_1^2)^n$.

*The datum.* The datum $\omega(1,g)\theta^\circ$ lies in $V^{\mathrm{fin}}$. By the law for translations, the law for $\omega$ and the image of $\theta^\circ$,
$$L\,\varrho(\mathrm{fin}(x))\,\omega(1,g)\,\theta^\circ = \varrho(\mathrm{fin}(bx))\,\mu_\sigma(g)\,\omega(1,g)\,a\,\omega(1,u)\,\mathrm{vac}.$$
The multiplier ratio has modulus one. The value of $\varrho(\mathrm{fin}(bx))F$ at $y$ is a number of modulus one times $F(y + \mathrm{fin}(bx))$. So the value in the claim has modulus $|a|\,|(\omega(1, gu)\,\mathrm{vac})(y + \mathrm{fin}(bx))|$. By the lemma on the moved vacuum it is at most
$$\exp(C_{\mathrm{vac}}q_1^2)^n\,\exp\bigl((2d+6)(q_1n+1)^2\bigr) \le \exp\bigl((C_{\mathrm{vac}} + 2d + 6)(q_1n+1)^2\bigr),$$
because $n q_1^2 \le (q_1 n)^2 \le (q_1 n + 1)^2$. Finally $C_{\mathrm{vac}} + 2d + 6 \le C_P$, since $C' \ge 0$. $\square$

**Remark (Formalization).** The constant $C_{\mathrm{vac}}$ and the number $c_s$ come from a chosen object of [the integral vacuum and tight frames](/chapter/integral-vacuum/), and the source names them through `choose`. The theorem holds for every choice with the stated properties, and only these properties enter the proof. The constant $C_P$ is a fixed real number that depends only on $q_0$ and $d$. The term $C'$ is not used in this chapter. It is part of $C_P$ so that one constant serves the bounds of other chapters too.

**Remark.** The theorem has a symmetry that later chapters use. The bound does not depend on $\sigma$, on $L$, on $x$ or on $g$. So a sum over the conjugates of a jet, over Hecke translates and over chains has a bound that is a product of this exponential with counts. All the dependence on the size of the data sits in $(q_1 n + 1)^2$.
