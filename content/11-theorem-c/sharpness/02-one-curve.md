---
title: The rate on one curve
lean:
  - New/Derivatives/Sharpness/OneCurve.lean
decls:
  - New.exists_monomial_max_norm_coeff
  - New.pow_le_of_submultiplicative
  - New.rpow_pow_le_norm_factorial_succ
  - New.CMLattice.maxDerivNorm
  - New.CMLattice.exists_isGreatest_norm_deriv
  - New.CMLattice.norm_deriv_le_one
  - New.CMLattice.maxDerivNorm_zero
  - New.CMLattice.exists_norm_coeff_subst_add_le
  - New.CMLattice.maxDerivNorm_add_le
  - New.CMLattice.norm_coeff_formalParam_of_eq_primeNorm_pow
  - New.CMLattice.pow_le_maxDerivNorm_of_eq_primeNorm_pow
  - New.CMLattice.katz_divisibility_limit
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The rate on one curve

This section works on one CM curve. It proves that for every $n$ some integral series $g$ in $y$ has $v(g^{(n)}(0)) \leq \gamma_p n$. The proof has three parts. The least valuation of $g^{(n)}(0)$ is superadditive in $n$, by the integral group law. At the powers of $q_p$ the formal parameter gives the bound directly. A form of Fekete's lemma carries the bound to every $n$.

We work with norms, not valuations. A least valuation becomes a greatest norm, and a sum of valuations becomes a product of norms.

### Notation

Let $d \equiv 7 \bmod 8$ be prime and $C$ a CM lattice for $d$ (`New.CMLattice`). Let $y$ be the Taylor series at $0$ of `C.translatedY`, carried to $\mathbb{C}_p$ by $\iota_p$. Let $\mathfrak{o}$ be the valuation ring of $\mathbb{C}_p$, and $\mathfrak{o}[[y]]$ the ring of series $G(y)$ with $G \in \mathfrak{o}[[T]]$ (`New.CMLattice.integralSeriesRing`). These objects and the facts below are in [integrality and the formal group](/chapter/cm-elliptic-curves/#integrality-and-the-formal-group):

- $\mathfrak{o}[[y]]$ is stable under $d/dz$ (`New.CMLattice.derivative_mem_integralSeriesRing`);
- $y(z_0 + z_1)$ is an integral power series in $y(z_0)$ and $y(z_1)$ (`New.CMLattice.translatedY_add_mem_multiSeriesRing`);
- the formal parameter $T$ generates $\mathfrak{o}[[y]]$, and there is $\varpi$ with $|\varpi| = p^{-\rho_p}$ and $T(\varpi z) = \varpi Y(z)$, where $Y$ is integral and its coefficient at $z^{q_p^j}$ is $\equiv 1$ modulo $\pi_p$ (`New.CMLattice.exists_scaled_formalParam`).

Here $q_p$ is the norm of a prime of $K$ above $p$ (`New.primeNorm`). The number $\rho_p$ is `New.varpiValuation`: it is $1/(p-1)$, $1/(p^2-1)$ or $1/(2p-2)$ when $p$ is split, inert or ramified. The rate is $\gamma_p = 1/(p-1) - \rho_p$ (`New.gammaPrime`). It is $0$, $p/(p^2-1)$ or $1/(2p-2)$ in the three cases, and $0 \leq \gamma_p \leq 1/(p-1)$.

### The largest monomial

**Lemma (Largest monomial).** Let $f_i$, for $i$ in a finite set $I$, be power series over $\mathbb{C}_p$ in finitely many variables, with zero constant terms. Let $s$ be a series and $\alpha$ an exponent. There is an exponent $m$ on $I$ with $|m| \leq |\alpha|$ such that
$$|\mathrm{coeff}_\alpha(G(f)\,s)| \leq \Bigl|\mathrm{coeff}_\alpha\Bigl(\prod_i f_i^{m_i}\,s\Bigr)\Bigr|$$
for every power series $G$ over $\mathfrak{o}$ in the variables $I$.

Lean: `New.exists_monomial_max_norm_coeff` (New/Derivatives/Sharpness/OneCurve.lean).

*Proof.* For an exponent $e$ on $I$ put $a_e = \mathrm{coeff}_\alpha(\prod_i f_i^{e_i}s)$. There are finitely many $e$ with $|e| \leq |\alpha|$. Take $m$ among them with $|a_m|$ largest. As the $f_i$ have no constant term, $\prod_i f_i^{e_i}$ has order at least $|e|$, so $a_e = 0$ for $|e| > |\alpha|$. Hence $\mathrm{coeff}_\alpha(G(f)s) = \sum_{|e| \leq |\alpha|} G_e a_e$, a finite sum. Each $|G_e| \leq 1$. By the ultrametric inequality the sum has norm at most $\max_e|a_e| = |a_m|$. $\square$

### A form of Fekete's lemma

**Lemma (Submultiplicative sequences).** Let $0 < b \leq 1$. Let $c : \mathbb{N} \to [0, 1]$ have $c(0) = 1$ and $c(m + n) \leq c(m)c(n)$ for all $m$, $n$. If for every $M$ there is $q \geq M$ with $b^q \leq c(q)$, then $b^n \leq c(n)$ for every $n$.

Lean: `New.pow_le_of_submultiplicative` (New/Derivatives/Sharpness/OneCurve.lean).

*Proof.* For $n = 0$ both sides are $1$. Let $n \geq 1$. By induction, $c(kn) \leq c(n)^k$ for all $k$. Let $q \geq n$ with $b^q \leq c(q)$, and write $q = n\lfloor q/n\rfloor + (q \bmod n)$. As $n(\lfloor q/n\rfloor + 1) > q$ and $b \leq 1$,
$$b^n(b^n)^{\lfloor q/n\rfloor} \leq b^q \leq c(q) \leq c(n\lfloor q/n\rfloor)\,c(q \bmod n) \leq c(n)^{\lfloor q/n\rfloor}.$$
The fourth step uses $c(q \bmod n) \leq 1$. Suppose $c(n) < b^n$. Then $\lambda = c(n)/b^n < 1$, and $b^n \leq \lambda^{\lfloor q/n\rfloor}$ for arbitrarily large $q$. The right side tends to $0$, but $b^n > 0$. This is a contradiction. $\square$

**Lemma (Legendre's bound).** For every $n$, $(p^{-1/(p-1)})^n \leq |(n+1)!|$ in $\mathbb{C}_p$.

Lean: `New.rpow_pow_le_norm_factorial_succ` (New/Derivatives/Sharpness/OneCurve.lean).

*Proof.* Legendre's formula gives $(p - 1)\,v(N!) < N$ for $N \geq 1$. With $N = n + 1$ this is $(p-1)v((n+1)!) \leq n$. Hence $|(n+1)!| = p^{-v((n+1)!)} \geq p^{-n/(p-1)}$. $\square$

### The greatest derivative

**Definition (Greatest derivative).** For $n \in \mathbb{N}$, let $D(n)$ be the supremum of $|n!\,\mathrm{coeff}_n\,g|$ over $g \in \mathfrak{o}[[y]]$. Note that $n!\,\mathrm{coeff}_n\,g = g^{(n)}(0)$.

Lean: `New.CMLattice.maxDerivNorm` (New/Derivatives/Sharpness/OneCurve.lean).

**Remark (Formalization).** The definition uses `sSup` on the reals. For a set that is empty or not bounded above, `sSup` is $0$ by convention. That junk value does not occur here. The set contains $0$, and the next lemma shows that it is bounded and that the supremum is attained.

**Lemma (A power attains the greatest derivative).** For every $n$ there is $i$ such that $|n!\,\mathrm{coeff}_n(y^i)|$ is the greatest element of the set of the $|n!\,\mathrm{coeff}_n\,g|$, $g \in \mathfrak{o}[[y]]$.

Lean: `New.CMLattice.exists_isGreatest_norm_deriv` (New/Derivatives/Sharpness/OneCurve.lean), with `New.CMLattice.exists_norm_deriv_eq_maxDerivNorm`.

*Proof.* Apply the largest monomial lemma with one series $f = y$, $s = 1$ and $\alpha = n$. The series $y$ has no constant term. So some power $y^i$ has $|\mathrm{coeff}_n\,g| \leq |\mathrm{coeff}_n(y^i)|$ for every $g = G(y)$ in $\mathfrak{o}[[y]]$. Multiply by $|n!|$. The power $y^i$ lies in $\mathfrak{o}[[y]]$. $\square$

**Lemma (Derivatives are integral).** For $g \in \mathfrak{o}[[y]]$ and every $n$, $|n!\,\mathrm{coeff}_n\,g| \leq 1$. Hence $D(n) \leq 1$, and $D(0) = 1$.

Lean: `New.CMLattice.norm_deriv_le_one`, `New.CMLattice.maxDerivNorm_zero` (New/Derivatives/Sharpness/OneCurve.lean), with `New.CMLattice.maxDerivNorm_le_one`.

*Proof.* Induction on $n$, for all $g$ at once. For $n = 0$, $g(0) = G(0)$ is in $\mathfrak{o}$, since $y(0) = 0$. For the step, $(n+1)!\,\mathrm{coeff}_{n+1}\,g = n!\,\mathrm{coeff}_n(g')$, and $g' \in \mathfrak{o}[[y]]$ because the ring is stable under $d/dz$. For $D(0)$ the series $1$ gives the value $1$. $\square$

### Superadditivity

**Lemma (Group law).** For all $j$, $m$, $n$ there are $a$, $b$ with
$$\bigl|\mathrm{coeff}_{z_0^mz_1^n}\bigl(y(z_0 + z_1)^j\bigr)\bigr| \leq |\mathrm{coeff}_m(y^a)\,\mathrm{coeff}_n(y^b)|.$$

Lean: `New.CMLattice.exists_norm_coeff_subst_add_le` (New/Derivatives/Sharpness/OneCurve.lean), with `New.CMLattice.exists_norm_coeff_le_norm_coeff_prod_pow`.

*Proof.* By the integral group law, $y(z_0 + z_1)^j$ is an integral series in $y(z_0)$ and $y(z_1)$. The largest monomial lemma, for the two series $y(z_0)$, $y(z_1)$ and $s = 1$, gives a monomial $y(z_0)^ay(z_1)^b$ whose coefficient at $z_0^mz_1^n$ is at least as large. That coefficient is $\mathrm{coeff}_m(y^a)\,\mathrm{coeff}_n(y^b)$. $\square$

**Theorem (Submultiplicativity).** $D(m + n) \leq D(m)\,D(n)$ for all $m$, $n$.

Lean: `New.CMLattice.maxDerivNorm_add_le` (New/Derivatives/Sharpness/OneCurve.lean), with `New.factorial_mul_coeff_subst_add` and `New.coeff_subst_mul_subst`.

*Proof.* Take $j$ with $D(m+n) = |(m+n)!\,\mathrm{coeff}_{m+n}(y^j)|$. Differentiating $g(z_0 + z_1)$ $m$ times in $z_0$ and $n$ times in $z_1$ at $0$ gives $g^{(m+n)}(0)$. So
$$(m+n)!\,\mathrm{coeff}_{m+n}\,g = m!\,n!\,\mathrm{coeff}_{z_0^mz_1^n}\,g(z_0 + z_1).$$
Apply this to $g = y^j$ and the group law lemma:
$$D(m+n) \leq |m!\,n!|\,|\mathrm{coeff}_m(y^a)|\,|\mathrm{coeff}_n(y^b)| = |m!\,\mathrm{coeff}_m(y^a)|\,|n!\,\mathrm{coeff}_n(y^b)| \leq D(m)D(n).$$
The last step uses $y^a, y^b \in \mathfrak{o}[[y]]$. $\square$

### The powers of $q_p$

**Lemma (Coefficients of the formal parameter).** If $n + 1 = q_p^j$, then $|\mathrm{coeff}_{n+1}\,T| = (p^{\rho_p})^n$.

Lean: `New.CMLattice.norm_coeff_formalParam_of_eq_primeNorm_pow` (New/Derivatives/Sharpness/OneCurve.lean), with `New.CMLattice.norm_eq_one_of_piPrimeInt_dvd_sub_one`.

*Proof.* Compare the coefficients of $z^{n+1}$ in $T(\varpi z) = \varpi Y(z)$: $\varpi^{n+1}\mathrm{coeff}_{n+1}\,T = \varpi\,\mathrm{coeff}_{n+1}\,Y$. As $n+1$ is a power of $q_p$, $\mathrm{coeff}_{n+1}\,Y = 1 + \pi_pc$ with $c \in \mathfrak{o}$. Since $|\pi_pc| < 1$, the ultrametric inequality gives $|1 + \pi_pc| = 1$. So $|\varpi|^n|\mathrm{coeff}_{n+1}\,T| = 1$, and $|\mathrm{coeff}_{n+1}\,T| = |\varpi|^{-n} = p^{n\rho_p}$. $\square$

**Lemma (The bound at the powers of $q_p$).** If $n + 1 = q_p^j$, then $(p^{-\gamma_p})^n \leq D(n+1)$.

Lean: `New.CMLattice.pow_le_maxDerivNorm_of_eq_primeNorm_pow` (New/Derivatives/Sharpness/OneCurve.lean).

*Proof.* By the definition of $\gamma_p$, $(p^{-\gamma_p})^n = (p^{-1/(p-1)})^n(p^{\rho_p})^n$. By Legendre's bound and the last lemma this is at most $|(n+1)!|\,|\mathrm{coeff}_{n+1}\,T|$. As $T \in \mathfrak{o}[[y]]$, this is at most $D(n+1)$. $\square$

### The theorem

**Theorem (Limit of the divisibility).** For every $n$ there is $f \in \mathfrak{o}[[y]]$ with $(p^{-\gamma_p})^n \leq |n!\,\mathrm{coeff}_n\,f|$. In valuations, $v(f^{(n)}(0)) \leq \gamma_p n$.

Lean: `New.CMLattice.katz_divisibility_limit` (New/Derivatives/Sharpness/OneCurve.lean).

*Proof.* Put $b = p^{-\gamma_p}$. Then $0 < b \leq 1$, because $\gamma_p \geq 0$. Let $q = q_p^M$, so $q \geq M$, and write $q = m + 1$. By the last lemma and $b \leq 1$, $b^q \leq b^m \leq D(q)$. So $b^q \leq D(q)$ for arbitrarily large $q$. The sequence $D$ has values in $[0, 1]$, $D(0) = 1$, and it is submultiplicative. The form of Fekete's lemma gives $b^n \leq D(n)$ for every $n$. The supremum $D(n)$ is attained by some $f \in \mathfrak{o}[[y]]$. $\square$

At a split prime $\gamma_p = 0$, and the theorem says that some $f$ has $f^{(n)}(0)$ a unit. At an inert prime the rate is $p/(p^2-1)$. The source names this rate after Katz, *Divisibilities, congruences, and Cartier duality*. This section proves only that no better rate holds for all $n$. The divisibility in the other direction is in [the CM formal group](/chapter/cm-formal-group/).

**Remark (Formalization).** The theorem gives one $f$ for each $n$, not one $f$ for all $n$. The proof never constructs $f$. It comes from the supremum, which a power $y^i$ attains, and $i$ comes from an existence statement.
