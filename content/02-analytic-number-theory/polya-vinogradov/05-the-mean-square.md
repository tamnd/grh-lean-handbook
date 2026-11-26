---
title: The mean square over twists
lean:
  - Lib/Analytic/QuadraticTwist.lean
decls:
  - New.exists_abs_gaussianMonomial_le_rpow
  - New.exists_mul_abs_gaussianMonomial_mul_le
  - New.exists_summable_ge_of_isSquare
  - New.exists_summable_ge_of_isSquare_ordCompl
  - New.exists_summable_mul_norm_sum_jacobiSym_le
  - New.sum_sq_thetaSeries_jacobiSym_le
  - New.sum_integral_norm_thetaSeries_div_le
  - New.sum_thetaTailIntegral_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The mean square over twists

Section 4 turned a zero into a large theta tail. This section shows that large theta tails are rare in a family of twists. The family is indexed by $v \leq T^2$, and the coefficients are $\alpha_n(-v/n^\circ)$ with fixed $|\alpha_n| \leq 1$. By the reciprocity lemma of [Section 3](/decl/New.legendreSym_eq_jacobiSym_ordCompl/), at a prime $v = d \equiv 7 \bmod 8$ these are the coefficients $\alpha_n(n/d)$ of a quadratic twist. The mean is over all $v$, prime or not, so it is a sum of short character sums in $v$, and Pólya-Vinogradov bounds them.

### The classical estimates

The classical tool for mean values over real characters is the large sieve for real characters. Heath-Brown (*A mean value estimate for real character sums*, Acta Arith. 72 (1995)) proved that for every $\varepsilon > 0$ and all complex $a_n$,
$$\sum_{m \leq M}{}^{\flat}\,\Bigl|\sum_{n \leq N}{}^{\flat}\, a_n\Bigl(\frac nm\Bigr)\Bigr|^2 \ll_\varepsilon (MN)^{\varepsilon}(M + N)\sum_{n \leq N}{}^{\flat}|a_n|^2,$$
where $\flat$ restricts to odd squarefree integers. The proof of the criterion does not need this. It needs a much weaker statement: the sums $\sum_n\alpha_n(-v/n^\circ)w_j(nu)$ have effective length $1/u \leq T$, and the range of $v$ is $T^2$, the square of the length. In this range the diagonal and the trivial treatment of the off-diagonal already balance, up to the power $u^{-2\delta}$. The source calls the result "a form of an estimate of Elliott". I could not identify the paper of Elliott that it means, so this chapter gives no reference for that attribution.

### The model computation

Fix $u \geq 1/T$ and write $\theta_v(u) = u^{1/2}\sum_{n \geq 1}\alpha_n(-v/n^\circ)w_j(nu)$. Expand the square:
$$\sum_{v \leq T^2}|\theta_v(u)|^2 = \sum_{n, m \geq 1}\alpha_n\bar\alpha_m\,u\,w_j(nu)w_j(mu)\sum_{v \leq T^2}\Bigl(\frac{-v}{(nm)^\circ}\Bigr).$$
Here $(-v/n^\circ)(-v/m^\circ) = (-v/(nm)^\circ)$, since the odd part is multiplicative and the Jacobi symbol is multiplicative in the lower argument. There are two kinds of pairs.

1. The *square* pairs, with $(nm)^\circ$ a square. Then the inner sum is at most $T^2$. These are the pairs $nm = l^2$ or $nm = 2l^2$. Their weight $u\,w_j(nu)w_j(mu)$ is of size $u$ for $n, m \leq 1/u$, and the number of such pairs with $n, m \leq 1/u$ is of the order $(1/u)\log(1/u)$. So these pairs give about $T^2\log(1/u)$.
2. The other pairs. Then $(-v/(nm)^\circ)$ is a non-principal character in $v$, and Pólya-Vinogradov bounds the inner sum by about $\sqrt{nm}$. These pairs give about $u\cdot(1/u)^2\cdot(1/u) = u^{-2} \leq T^2$.

So the mean square is about $T^2\log T$, and the expected size of $|\theta_v(u)|$ is $1$. The source pays a power $u^{-2\delta}$ in place of the logarithms, so that every sum over pairs is absolutely convergent.

### The weights

**Lemma (Decay of the weight).** Let $A > 0$. Then for every $x > 0$,
$$|w_j(x)| \leq 3A^A\,x^{-A}.$$

Lean: `New.exists_abs_gaussianMonomial_le_rpow` (Lib/Analytic/QuadraticTwist.lean).

*Proof.* For $x \geq 0$ the source proves $|w_j(x)| \leq 3(e^{-x})^2$ (`New.norm_gaussianMonomial_le`). From $\log t \leq t$ with $t = x/A$ we get $(x/A)^A \leq e^x$, so $e^{-2x} \leq e^{-x} \leq A^Ax^{-A}$. $\square$

**Lemma (Products of weights).** Let $A > 0$. Then for $u > 0$ and positive integers $n, m$,
$$u\,|w_j(nu)|\,|w_j(mu)| \leq 9A^{2A}\,u^{1 - 2A}(nm)^{-A}.$$

Lean: `New.exists_mul_abs_gaussianMonomial_mul_le` (Lib/Analytic/QuadraticTwist.lean).

*Proof.* Apply the last lemma to $nu$ and to $mu$. $\square$

The Lean statements say only that a constant $C > 0$ exists. The constants $3A^A$ and $(3A^A)^2$ are the witnesses in their proofs.

### The square pairs

**Lemma (Square pairs).** Let $\sigma > 1/2$ and let $k$ be a positive integer. There is a function $W_k \geq 0$ on pairs of positive integers with $\sum_{n, m}W_k(n, m) < \infty$ such that $(knm)^{-\sigma} \leq W_k(n, m)$ whenever $knm$ is a square.

Lean: `New.exists_summable_ge_of_isSquare` (Lib/Analytic/QuadraticTwist.lean).

*Proof.* Let $knm = r^2$. With $g = \gcd(kn, r)$, write $kn = bg$ and $r = cg$ with $\gcd(b, c) = 1$. Then $bm = c^2g$, so $b \mid g$; write $g = ab$. This gives $kn = ab^2$ and $m = ac^2$, and $knm = (abc)^2$. Let $W_k(n, m)$ be the sum of $(abc)^{-2\sigma}$ over the triples $(a, b, c)$ with $ab^2/k = n$ and $ac^2 = m$. Every triple lies over one pair, so $\sum_{n, m}W_k(n, m) \leq \zeta(2\sigma)^3$. $\square$

**Lemma (Square odd parts).** Let $\sigma > 1/2$. There is a function $W \geq 0$ on pairs of positive integers with $\sum W < \infty$ such that $(nm)^{-\sigma} \leq W(n, m)$ whenever $(nm)^\circ$ is a square.

Lean: `New.exists_summable_ge_of_isSquare_ordCompl` (Lib/Analytic/QuadraticTwist.lean).

*Proof.* Write $nm = 2^ef^2$ with $f$ odd. If $e$ is even, $nm$ is a square. If $e$ is odd, $2nm$ is a square. Put $W = W_1 + 2^\sigma W_2$. $\square$

**Remark (Formalization).** The proof obtains $W_1$ and $W_2$ with Lean's `choose` from the existence statement of the last lemma. So the function $W$ is not named in the statement, and its sum is not a value that Lean exports. The construction gives $\sum W \leq (1 + 2^\sigma)\zeta(2\sigma)^3$. The sum over triples runs over $a, b, c \in \mathbb{N}$ including $0$; Lean's $0^{-2\sigma}$ is $0$, so these terms are harmless.

### The pair bound and the mean square

**Lemma (One pair).** Let $\delta > 0$. There is a summable function $M \geq 0$ on pairs of positive integers, depending only on $j$ and $\delta$, such that for every $T > 0$, every $u \geq 1/T$ and all positive integers $n, m$,
$$u\,|w_j(nu)|\,|w_j(mu)|\,\Bigl|\sum_{v = 1}^{\lfloor T^2\rfloor}\Bigl(\frac{-v}{(nm)^\circ}\Bigr)\Bigr| \leq M(n, m)\,T^2u^{-2\delta}.$$

Lean: `New.exists_summable_mul_norm_sum_jacobiSym_le` (Lib/Analytic/QuadraticTwist.lean).

*Proof.* Let $C_1 = 9(1/2 + \delta)^{1 + 2\delta}$ and $C_2 = 9(3/2 + \delta)^{3 + 2\delta}$ be the constants of the product lemma for $A = 1/2 + \delta$ and $A = 3/2 + \delta$. Let $W$ be the function of the last lemma for $\sigma = 1/2 + \delta$, and put $C_3 = 2(1 + 2/\delta)C_2$. Define
$$M(n, m) = C_1W(n, m) + C_3\,(nm)^{-1 - \delta/2}.$$
It is summable, since $\sum_n n^{-1 - \delta/2} < \infty$.

If $(nm)^\circ$ is a square, bound the sum over $v$ by $\lfloor T^2\rfloor \leq T^2$. The product lemma with $A = 1/2 + \delta$ gives $u^{-2\delta}(nm)^{-1/2 - \delta}$, and this is at most $u^{-2\delta}W(n, m)$.

If $(nm)^\circ$ is not a square, the [lemma on odd parts](/decl/New.norm_sum_jacobiSym_ordCompl_le/) bounds the sum over $v$ by $2(1 + 2/\delta)(nm)^{1/2 + \delta/2}$. The product lemma with $A = 3/2 + \delta$ gives $u^{-2 - 2\delta}(nm)^{-3/2 - \delta}$. The product is $C_3u^{-2}u^{-2\delta}(nm)^{-1 - \delta/2}$. Since $u \geq 1/T$, $u^{-2} \leq T^2$. $\square$

The choice $A = 3/2 + \delta$ is the point of the proof. Pólya-Vinogradov costs $(nm)^{1/2 + \delta/2}$, and the weight must pay this and leave a convergent sum. The weight pays with powers of $1/u$, and the bound $u^{-2} \leq T^2$ converts them into the length of the range of $v$. This is the step that uses $u \geq 1/T$, and so the reason that $J(c, T)$ starts at $1/T$.

**Theorem (Mean square).** Let $\delta > 0$. There is a constant $C$ such that for every $T > 0$, every $u \geq 1/T$ and every $\alpha : \mathbb{N} \to \mathbb{C}$ with $|\alpha_n| \leq 1$,
$$\sum_{v = 1}^{\lfloor T^2\rfloor}\Bigl|\theta_{c_v}(u)\Bigr|^2 \leq C\,T^2u^{-2\delta}, \qquad c_v(n) = \alpha_n\Bigl(\frac{-v}{n^\circ}\Bigr).$$

Lean: `New.sum_sq_thetaSeries_jacobiSym_le` (Lib/Analytic/QuadraticTwist.lean).

*Proof.* Take $C = \sum_{n, m}M(n, m)$. Write $\theta_{c_v}(u) = \sum_n a_v(n)$ with $a_v(n) = u^{1/2}c_v(n)w_j(nu)$. The double series $\sum_{n, m}a_v(n)\overline{a_v(m)}$ converges absolutely to $|\theta_{c_v}(u)|^2$. Sum over $v$ and take the sum over $v$ inside. The term of the pair $(n, m)$ is $\alpha_n\bar\alpha_m\,u\,w_j(nu)w_j(mu)\sum_v(-v/(nm)^\circ)$, since $w_j$ is real. By the last lemma its absolute value is at most $M(n, m)T^2u^{-2\delta}$. $\square$

The constant depends only on $j$ and $\delta$. It does not depend on $T$, $u$ or $\alpha$. The witness in the proof is
$$C = C_1\sum W + C_3\,\zeta(1 + \delta/2)^2 \leq C_1(1 + 2^{1/2 + \delta})\,\zeta(1 + 2\delta)^3 + C_3\,\zeta(1 + \delta/2)^2,$$
with $C_1$ and $C_3$ as in the proof of the pair lemma. As $\delta \to 0$ this is of order $\delta^{-3}$, since $\zeta(1 + \varepsilon) \sim 1/\varepsilon$.

### Integration in $u$

**Lemma (Sum of tails).** Let $\delta > 0$. There is a constant $C'$ such that for every $T > 0$ and every $\alpha$ with $|\alpha_n| \leq 1$,
$$\sum_{v = 1}^{\lfloor T^2\rfloor}\int_{1/T}^\infty|\theta_{c_v}(u)|\,\frac{du}{u} \leq C'\,T^{2 + \delta}.$$

Lean: `New.sum_integral_norm_thetaSeries_div_le` (Lib/Analytic/QuadraticTwist.lean).

*Proof.* Let $C$ be the constant of the theorem, and put $C' = \sqrt C/\delta$. For $u > 1/T$, Cauchy-Schwarz over at most $T^2$ values of $v$ and the theorem give
$$\sum_v|\theta_{c_v}(u)| \leq \sqrt{T^2\cdot CT^2u^{-2\delta}} = \sqrt C\,T^2u^{-\delta}.$$
Each integral converges, so the finite sum and the integral commute. Then $\int_{1/T}^\infty\sqrt CT^2u^{-\delta - 1}du = \sqrt CT^2T^{\delta}/\delta$. $\square$

**Corollary (Sum of theta tails).** Let $\delta > 0$. There is a constant $C''$ such that for every $T > 0$ and every $\alpha$ with $|\alpha_n| \leq 1$,
$$\sum_{v = 1}^{\lfloor T^2\rfloor}J(c_v, T) \leq C''\,T^{2 + \delta}.$$

Lean: `New.sum_thetaTailIntegral_le` (Lib/Analytic/QuadraticTwist.lean).

*Proof.* The coefficients of $\theta_{\mu c_v}$ are $\alpha_n\mu(n)(-v/n^\circ)$, which have the same form with $\alpha\mu$ in place of $\alpha$. Apply the lemma to $\alpha$ and to $\alpha\mu$, and take $C'' = 2C'$. $\square$

So the average of $J(c_v, T)$ over $v \leq T^2$ is $O(T^{\delta})$, while Section 4 needs $J > T^{2\delta}$ at a zero. By Markov's inequality, at most $C''T^{2 - \delta}$ values of $v$ have $J(c_v, T) > T^{2\delta}$. This is the count of Section 6.

**Remark (Formalization).** All the bounds of this section are existential in Lean (`∃ C, ...`). The proofs construct explicit witnesses, which this section gives. The witness for $W$ comes through `choose` and is not visible in the statement, so the value of $C$ above is the value that the natural construction gives, not a value that a later statement can use. The sum over $v$ is over the integers $1 \leq v \leq \lfloor T^2\rfloor$ (`Ioc 0 ⌊T ^ 2⌋₊`), with $\lfloor\cdot\rfloor$ the floor into $\mathbb{N}$, which is $0$ for $T^2 < 1$. The coefficient at $n = 0$ is irrelevant, since the theta series starts at $n = 1$.
