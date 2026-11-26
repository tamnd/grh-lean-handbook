---
title: The model case
lean:
  - New/Spanning/Unfolding/PoincareSeries.lean
  - New/Spanning/Unfolding/Setup.lean
decls:
  - New.Filling.Fits.petersson_poincare
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The model case

The proof of Theorem B is a large version of a classical argument for cusp forms on $\mathrm{SL}_2(\mathbb{Z})$: unfolding, the Petersson formula, and a bound for its terms. This section works out the classical case as a guide. Nothing in this section is in the Lean source.

### Poincaré series and unfolding

Let $\Gamma = \mathrm{SL}_2(\mathbb{Z})$, let $k \geq 4$ be even, and let $S_k$ be the space of cusp forms of weight $k$ for $\Gamma$. For $\gamma = \begin{pmatrix} a & b \\ c & d \end{pmatrix}$ write $j(\gamma, z) = cz + d$, and write $e(x) = e^{2\pi i x}$. Let $\Gamma_\infty$ be the stabilizer of the cusp $\infty$, the group of the matrices $\pm\begin{pmatrix} 1 & n \\ 0 & 1\end{pmatrix}$. For an integer $m \geq 1$ the Poincaré series is

$$P_m(z) = \sum_{\gamma \in \Gamma_\infty\backslash\Gamma} j(\gamma, z)^{-k}\, e(m\gamma z).$$

For $k > 2$ the series converges absolutely and uniformly on compact sets, and $P_m \in S_k$. The Petersson inner product is $\langle f, g\rangle = \int_{\Gamma\backslash\mathbb{H}} f(z)\overline{g(z)}\, y^k\, d\mu(z)$ with $d\mu = dx\,dy/y^2$.

Let $f(z) = \sum_{n \geq 1} a_f(n) e(nz)$ be in $S_k$. The sum over $\Gamma_\infty\backslash\Gamma$ and the integral over $\Gamma\backslash\mathbb{H}$ combine into one integral over $\Gamma_\infty\backslash\mathbb{H}$, the strip $0 \leq x \leq 1$, $y > 0$. This is the unfolding:

$$\langle f, P_m\rangle = \int_0^\infty\!\!\int_0^1 f(z)\,\overline{e(mz)}\, y^{k - 2}\, dx\, dy = a_f(m)\int_0^\infty e^{-4\pi m y} y^{k - 2}\, dy = \frac{\Gamma(k - 1)}{(4\pi m)^{k - 1}}\, a_f(m).$$

The integral over $x$ keeps only the coefficient of index $m$. So the inner product with $P_m$ reads off one Fourier coefficient.

This gives the spanning theorem of Petersson at once. If $f$ is orthogonal to every $P_m$, then every $a_f(m)$ is $0$, so $f = 0$. Thus the $P_m$ span $S_k$. The argument does not say which $P_m$ to take, or how many.

### The Petersson formula

To count, one needs the inner products of the Poincaré series with each other. Apply the unfolding to $f = P_n$. The coefficient of index $m$ of $P_n$ is computed by a second unfolding, now over the double cosets $\Gamma_\infty\backslash\Gamma/\Gamma_\infty$. The identity coset gives a Kronecker delta. A coset with lower left entry $c > 0$ gives a Kloosterman sum

$$S(m, n; c) = \sum_{\substack{d \bmod c \\ (d, c) = 1}} e\Bigl(\frac{m d + n\bar d}{c}\Bigr), \qquad d\bar d \equiv 1 \pmod c,$$

times an integral over the real line, which is a $J$-Bessel function. Normalize $Q_m = \bigl((4\pi m)^{k - 1}/\Gamma(k - 1)\bigr)^{1/2} P_m$. The result is the Petersson formula:

$$\langle Q_n, Q_m\rangle = \delta(m, n) + 2\pi i^{-k}\sum_{c \geq 1} \frac{S(m, n; c)}{c}\, J_{k - 1}\Bigl(\frac{4\pi\sqrt{mn}}{c}\Bigr).$$

Written with an orthonormal basis of $S_k$, this is Proposition 14.5 of Iwaniec and Kowalski.

The formula has the shape of every computation in this volume. A Gram matrix of Poincaré series equals a sum over double cosets. The identity coset gives the diagonal. Each other coset gives a finite exponential sum, which is a local factor at the finite places, times an oscillatory integral, which is a local factor at the real place.

### A bound and its limit

Use two bounds. The Kloosterman sum has at most $c$ terms, so $|S(m, n; c)| \leq c$. For real $x \geq 0$ and $\nu \geq 0$, $|J_\nu(x)| \leq (x/2)^\nu/\Gamma(\nu + 1)$ (DLMF 10.14.4). Then for $m, n \leq L$,

$$\Bigl|\langle Q_n, Q_m\rangle - \delta(m, n)\Bigr| \leq 2\pi\sum_{c \geq 1}\frac{(2\pi L/c)^{k - 1}}{\Gamma(k)} = \frac{2\pi\,\zeta(k - 1)\,(2\pi L)^{k - 1}}{\Gamma(k)}.$$

As $\Gamma(k) \geq ((k - 1)/e)^{k - 1}$, the right side is at most $2\pi\zeta(3)\,2^{-(k - 1)}$ when $L \leq (k - 1)/(4\pi e)$. Then the Gram matrix of $Q_1, \dots, Q_L$ is $1 + E$ with entries of $E$ at most $\delta = 2\pi\zeta(3)2^{1 - k}$. So $\|E\| \leq L\delta < 1$ for large $k$, and $Q_1, \dots, Q_L$ are almost orthonormal.

Compare with the dimension. For even $k \geq 4$, $\dim S_k$ is $\lfloor k/12\rfloor - 1$ if $k \equiv 2 \pmod{12}$ and $\lfloor k/12\rfloor$ otherwise (Serre, *A Course in Arithmetic*, Chapter VII, §3). The almost orthonormal block has $L \approx k/(4\pi e) \approx k/34$ elements. So it spans only about a third of $S_k$. Beyond $L$, the Bessel factor $J_{k - 1}(4\pi\sqrt{mn}/c)$ with $c = 1$ is no longer small, and the Kloosterman terms are of the same size as the diagonal.

This is the central difficulty, and the source meets it in the same form. A diagonal argument gives a share of the target, not almost all of it. To reach the share $1 - 4/b^2$ the source uses the off-diagonal terms through a second moment: they are not small one by one, but their squares add up to the value that random subspaces would give.

### The dimension as a volume

The leading term $k/12$ has a meaning that the source uses. The holomorphic discrete series of weight $k$ has formal degree $(k - 1)/(4\pi)$ for the measure $\mu$, and $\Gamma\backslash\mathbb{H}$ has volume $\pi/3$ for $\mu$. Their product is $(k - 1)/12$: the dimension is, to first order, the formal degree times the volume. In the source the volume becomes the mass of a genus of hermitian lattices times $\#\bar G$, and the formal degree a product over the real places. [The section on the four layers](/chapter/theorem-b-plan/#the-four-layers-of-the-proof) states the result.

### The source form of the Petersson formula

In the source the role of $\Gamma_\infty$ is played by a Bessel subgroup $R = U \rtimes H$ at each real place, and the role of $e(mz)$ by a vector-valued Bessel function $W$ that transforms on the left under $R$ and generates a discrete series. A cutoff $\beta_c$ for each class $c$ replaces the strip $0 \leq x \leq 1$. The source has coordinates $(c, i)$, a class and a coordinate of $W$.

**Theorem (Petersson formula for the filling).** Let $S$ be admissible filling data over a CM field $E$ that contains a primitive $5040$-th root of unity, and let the hermitian space $V$ fit $S$. For coordinates $a = (c, i)$ and $a' = (c', i')$ let $\mathcal{P}a$ be the Poincaré series of the basis vector at $a$. Let $k$ lie in the stabilizer of the standard lattice, with reduction $s$ at the chosen places. Then

$$\langle k\,\mathcal{P}a', \mathcal{P}a\rangle = \mathrm{vol}(K_{\mathrm{pr}})\, \mathcal{A}(c, s, c')_{i, i'}, \qquad \mathcal{A}(c, s, c') = \sum_{\gamma}\int \beta_c(y)\,\beta_{c'}(\gamma^{-1}y)\, W(y) \otimes \overline{W(\gamma^{-1}y)}\, dy.$$

Here $K_{\mathrm{pr}}$ is the principal level at the chosen places, $\gamma$ runs over the rational points such that $h_c^{-1}\gamma h_{c'}$ lies in the lattice stabilizer and has reduction $s$, and $y$ runs over the product of the real unitary groups.

Lean: `New.Filling.Fits.petersson_poincare` (New/Spanning/Unfolding/PoincareSeries.lean).

The dictionary is direct. The pair $(m, n)$ becomes the pair of coordinates $(a, a')$. The double coset of $\gamma$ becomes the block $(c, s, c')$ with its terms $\gamma$. The integral $\int W(y) \otimes \overline{W(\gamma^{-1}y)}\, dy$ is the amplitude of $\gamma$, the counterpart of $J_{k - 1}$. The sum over $\gamma$ in a block with fixed finite data is the counterpart of the Kloosterman sum. [The chapter on the anatomy of a term](/chapter/anatomy-of-a-term/) sorts the terms $\gamma$ into the identity terms, the main terms and the remaining terms.

**Remark (Formalization).** The amplitude sum is a sum `tsum` of Bochner integrals. In Lean both are $0$ when they do not converge. The left side of the formula is an inner product of forms, so the formula has a meaning in any case. Bounds for the right side mean what they say only where the sums converge. [The section on conventions](/chapter/theorem-b-plan/#conventions-that-change-the-meaning) gives the theorems that prove this.

**Remark.** In the model, the diagonal term dominates for small $m$. In the source, the translates are indexed by the elements $s$ of the finite group $\bar G$, and a hypothesis of the admissible filling data makes the main second moment at least $b^{11kf}$ times the identity second moment, with $k$ the rank of $X_0$ and $f$ the number of infinite places. So the source has no diagonal regime, and almost all of the second moment is in the main term.
