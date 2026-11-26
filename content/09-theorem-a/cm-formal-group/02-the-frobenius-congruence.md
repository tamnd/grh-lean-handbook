---
title: The Frobenius congruence
lean:
  - New/Derivatives/FormalGroup/FrobeniusCongruence.lean
  - Lib/General/Algebra/SeriesBounds.lean
decls:
  - New.ne_two_of_chiK_ne_one
  - New.norm_coeff_expSubst_sub_one_le
  - New.IsSeriesGenerator.mem_of_expSubst_smul_eq
  - New.norm_coeff_le_of_aeval
  - New.CMLattice.exists_rescale_theta_eq_pow_mul_aeval
  - New.CMLattice.norm_piPrime_mul_coeff_negLogTheta_le_one
  - New.CMLattice.norm_coeff_smul_negLogTheta_sub_rescale_le
  - New.CMLattice.exists_rescale_theta_eq_pow_mul_one_add_smul
  - New.CMLattice.exists_negLogTheta_frobenius_congruence
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The Frobenius congruence

This section proves that $\theta(\pi_p z) \equiv \theta(z)^{q_p}$ modulo $\pi_p\,\mathfrak{o}[[y]]$ at a nonsplit prime $p$. On a Lubin and Tate formal group the endomorphism $[\pi]$ is $\equiv T^{q}$ modulo $\pi$. The congruence for $\theta$ is the same fact one level up, for a section of a line bundle in place of a coordinate. Its logarithmic form, $q_p g(z) - g(\pi_p z) \in \pi_p\,\mathfrak{o}[[y]]$ for $g = -\log\theta$, is the functional equation that Section 4 solves.

Fix a prime $d \equiv 7 \bmod 8$, a CM lattice $C$ for $d$, a prime $p$ and a ring homomorphism $\iota_p : \mathbb{C} \to \mathbb{C}_p$. All series in this section are Taylor series at $0$ with coefficients mapped to $\mathbb{C}_p$ by $\iota_p$. We write $\pi$ for $\iota_p(\pi_p)$ and $q$ for $q_p$ when $p$ is fixed.

### The numbers at a nonsplit prime

**Lemma (Numbers at a nonsplit prime).** Let $p$ be a prime with $\chi_K(p) \ne 1$. Then:

1. $p \ne 2$, and $q_p$ is odd;
2. if $\chi_K(p) = -1$, then $p < q_p$;
3. $|q_p| = |\pi|^2$;
4. $|\pi| \le p^{-1/(p-1)}$.

For every prime $p$ (split or not):

5. $|\pi| \le |\iota_p(\sqrt{-d})|$;
6. $|\pi| \le |n|$ for every integer $n$ with $0 < n < q_p$;
7. $|\pi| \le |(k+2)(k+1)|$ for every $k \in \mathbb{N}$ with $k + 2 < q_p$.

Lean: `New.ne_two_of_chiK_ne_one`, `New.odd_primeNorm`, `New.lt_primeNorm_of_chiK_eq_neg_one`, `New.norm_primeNorm`, `New.norm_piPrime_le_rpow`, `New.norm_piPrime_le_norm_sqrt_neg`, `New.norm_piPrime_le_norm_natCast`, `New.norm_piPrime_le_norm_mul_succ` (New/Derivatives/FormalGroup/FrobeniusCongruence.lean).

*Proof.* (1) The prime $2$ splits, since $-d \equiv 1 \bmod 8$. So $p$ is odd, and $q_p$ is a power of $p$. (2) Then $q_p = p^2$. (3) If $p = d$, then $\pi_p^2 = -d$ and $q_p = d$. If $p$ is inert, $\pi_p = p$ and $q_p = p^2$. (4) We have $v(\pi) \ge 1/2$, and $1/2 \ge 1/(p-1)$ since $p \ge 3$. (5) If $p = d$ the two numbers are equal. Otherwise $(\sqrt{-d})^2 = -d$ is prime to $p$, so $|\iota_p(\sqrt{-d})| = 1$. (6) If $q_p = p$, then $n < p$ is a unit. If $q_p = p^2$, then $p$ is inert, $\pi = p$, and $n < p^2$ gives $v(n) \le 1 = v(\pi)$. (7) One of $k+1$ and $k+2$ is prime to $p$. The other one is less than $q_p$, so (6) applies to it. $\square$

Item 7 is the reason for the bound $q_p$ in the lemmas below. It fails at $k + 2 = q_p$ when $q_p = p^2$: then $v((k+2)(k+1)) = 2 > v(\pi)$.

### Two facts on the exponential

The exponential series $\exp X = \sum_{j \ge 0} X^j/j!$ has the radius of convergence $p^{-1/(p-1)}$ in $\mathbb{C}_p$. The reason is Legendre's formula $v(j!) = (j - s_p(j))/(p-1)$, where $s_p(j)$ is the sum of the digits of $j$ in base $p$ (see Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, Chapter IV, Section 1). For formal series we need two consequences.

**Lemma (Exponential modulo $c$).** Let $c \in \mathbb{C}_p$ with $|c| \le p^{-1/(p-1)}$, let $g \in \mathbb{C}_p[[X]]$ with $g(0) = 0$, and let $l \in \mathbb{N}$. If $|g_n| \le |c|$ for all $n < l$, then $|[X^n](\exp g - 1)| \le |c|$ for all $n < l$.

Lean: `New.norm_coeff_expSubst_sub_one_le` (Lib/General/Algebra/SeriesBounds.lean).

*Proof.* Below the degree $l$, the series $g^j$ has coefficients of norm at most $|c|^j$. The term $g^j/j!$ has coefficients of norm at most $|c|^j/|j!|$. Legendre's formula gives $v(j!) \le (j-1)/(p-1)$, so $|c|^{j-1} \le |j!|$, and $|c|^j/|j!| \le |c|$. $\square$

Let $B$ be the ring of integral series in a series $T = X + \cdots$, that is, of all $\sum_i b_i T^i$ with $b_i \in \mathfrak{o}$. In Lean this is the predicate `New.IsSeriesGenerator B T`. The ring $\mathfrak{o}[[y]]$ of [Volume 3](/decl/New.CMLattice.integralSeriesRing/) is of this kind.

**Lemma (Logarithm modulo $c$).** Let $B$ be the ring of integral series in $T$. Let $c \ne 0$ with $|c| \le p^{-1/(p-1)}$, let $g$ be a series with $g(0) = 0$, and let $H \in B$. If $\exp(cg) = 1 + cH$, then $g \in B$.

Lean: `New.IsSeriesGenerator.mem_of_expSubst_smul_eq` (Lib/General/Algebra/SeriesBounds.lean).

*Proof.* Take logarithms: $g = c^{-1}\log(1 + cH) = \sum_{j \ge 1} (-1)^{j-1} (c^{j-1}/j) H^j$. The bound $v(j) \le (j-1)/(p-1)$ holds for all $j \ge 1$, since $p^{v(j)} \le j$. So the series $\sum_j (-1)^{j-1}(c^{j-1}/j) X^j$ is integral. Its value at $H$, with $H(0) = 0$, lies in $B$. $\square$

The last tool is a triangular system. Write $R(x)$ for the value of a polynomial $R$ at a series $x$.

**Lemma (Triangular system).** Let $x = X^2 + \cdots$ be a series whose coefficients below the degree $l$ are integral. Let $R$ be a polynomial over $\mathbb{C}_p$ and $s \in \mathbb{R}$. If the coefficients of $R(x)$ below the degree $l$ have norm at most $s$, then $|R_i| \le s$ for every $i$ with $2i < l$.

Lean: `New.norm_coeff_le_of_aeval` (Lib/General/Algebra/SeriesBounds.lean).

*Proof.* By induction on $i$. The coefficient of $X^{2i}$ in $R(x)$ is $R_i + \sum_{j < i} R_j\,[X^{2i}]x^j$, since $x^j$ starts in degree $2j$ and $x^i = X^{2i} + \cdots$. The induction hypothesis and the ultrametric inequality give $|R_i| \le s$. $\square$

**Remark (Formalization).** These three lemmas are the formal series forms of the classical radius of convergence. Lean states them with norms, and the bound on $c$ is the inequality $\|c\| \le p^{-1/(p-1)}$ of real numbers. The source proves the logarithm form with the series of $\log(1 + X)$ and a substitution. It does not state the convergence of $\exp$ on $\mathbb{C}_p$, and it does not need it.

### The quotient is a polynomial in x

**Lemma (Quotient polynomial).** Let $\chi_K(p) \ne 1$. There is a polynomial $R$ over $\mathbb{C}_p$ with $2\deg R < q_p$ and
$$\theta(\pi_p z) = \theta(z)^{q_p}\, R(x(z))$$
as power series over $\mathbb{C}_p$.

Lean: `New.CMLattice.exists_rescale_theta_eq_pow_mul_aeval` (New/Derivatives/FormalGroup/FrobeniusCongruence.lean).

*Proof.* We have $\pi_p\bar\pi_p = q_p$, and $\pi_p\mathcal{O}_K \subseteq \mathcal{O}_K$, so multiplication by $\pi_p$ is an isogeny of degree $q_p$ of the lattice to itself. Hence $f(z) = \theta(\pi_p z)$ is a section of degree $q_p$, and its torsion values are integral, by the [theorem on isogenies](/decl/New.CMLattice.exists_rescale_theta_eq_theta_pow_mul/). The function $f$ is even, since $\theta$ is even. The [integrality principle](/decl/New.CMLattice.exists_taylorVia_eq_theta_pow_mul/), in its even form `New.CMLattice.exists_polynomial_of_even`, gives a polynomial $R$ with integral coefficients, $2\deg R \le q_p$ and $f = \theta^{q_p}R(x)$ as series. Since $q_p$ is odd, $2\deg R < q_p$. $\square$

The polynomial $R$ has integral coefficients, but the lemma does not state this, and the proof below does not use it. It needs more: the coefficients of $R - 1$ are divisible by $\pi$.

### The logarithm below the degree q

Recall $g = -\log\theta$ and the [lemma on the logarithm of theta](/decl/New.CMLattice.derivative_derivative_negLogTheta/): $g'' = g''(0) + x$. Write $g_n$ for the coefficient of $z^n$ in $g$. So $g_0 = g_1 = 0$, and
$$(n+2)(n+1)\,g_{n+2} = x_n \qquad (n \ge 1),$$
where $x_n$ is the coefficient of $z^n$ in $x$. The coefficients of $x$ below the degree $q_p$ are integral. Indeed $x \in \mathfrak{o}[[y]]$, every element of $\mathfrak{o}[[y]]$ is an integral series in the formal parameter $T$, and the coefficients of $T$ below the degree $q_p$ are integral (`New.CMLattice.norm_coeff_le_one_of_lt`).

**Lemma (Integrality of $\pi g$).** Let $\chi_K(p) \ne 1$. Then $|\pi|\,|g_n| \le 1$ for every $n < q_p$.

Lean: `New.CMLattice.norm_piPrime_mul_coeff_negLogTheta_le_one` (New/Derivatives/FormalGroup/FrobeniusCongruence.lean).

*Proof.* For $n = 0, 1$ the coefficient is $0$. For $n = 2$, Volume 3 proves $|\iota_p(\sqrt{-d})\cdot 2g_2| \le 1$ (`New.CMLattice.norm_sqrt_mul_coeff_two_negLogTheta_le_one`). Here $|2| = 1$ since $p$ is odd, and $|\pi| \le |\iota_p(\sqrt{-d})|$ by item 5 of the first lemma. For $n = k + 3 < q_p$, the recursion gives $(k+3)(k+2)\,g_{k+3} = x_{k+1}$, and $|x_{k+1}| \le 1$. Item 7 gives $|\pi| \le |(k+3)(k+2)|$. So $|\pi g_{k+3}| \le |x_{k+1}| \le 1$. $\square$

The coefficient $g_2$ is special. It is $g''(0)/2$, and $g''(0)$ is a constant of the lattice. It is not determined by the recursion, and it can fail to be integral. The bound with $\sqrt{-d}$ comes from the complex multiplication: Volume 3 compares the action of the generator of $\mathcal{O}_K$ and of its conjugate on $g$.

**Lemma (Difference below the degree q).** Let $\chi_K(p) \ne 1$. For every $n < q_p$, the coefficient $(q_p - \pi^n)g_n$ of $z^n$ in $q_p g(z) - g(\pi z)$ has norm at most $|\pi|$.

Lean: `New.CMLattice.norm_coeff_smul_negLogTheta_sub_rescale_le` (New/Derivatives/FormalGroup/FrobeniusCongruence.lean).

*Proof.* For $n \le 1$ the coefficient is $0$. For $n \ge 2$, $|q_p - \pi^n| \le \max(|q_p|, |\pi|^n) \le |\pi|^2$ by item 3. So $|(q_p - \pi^n)g_n| \le |\pi| \cdot |\pi g_n| \le |\pi|$. $\square$

**Example.** Take $d = 7$ and $p = 3$, as in the model case. Then $\pi = 3$ and $q = 9$, and the factor $q - \pi^2 = 0$. So the coefficient of $z^2$ in $9g(z) - g(3z)$ is $0$, whatever $g_2$ is. For $n = 3, \dots, 8$ the factor $9 - 3^n$ has valuation exactly $2$, and $3g_n$ is integral. For $p = d = 7$ we get $\pi^2 = -7$ and $q - \pi^2 = 14$, which has valuation $1 = 2v(\pi)$.

### The congruence

**Theorem (Frobenius congruence).** Let $\chi_K(p) \ne 1$. There is $H \in \mathfrak{o}[[y]]$ with
$$\theta(\pi_p z) = \theta(z)^{q_p}\bigl(1 + \pi H\bigr).$$

Lean: `New.CMLattice.exists_rescale_theta_eq_pow_mul_one_add_smul` (New/Derivatives/FormalGroup/FrobeniusCongruence.lean).

*Proof.* Take $R$ from the lemma on the quotient polynomial. From $\theta = \exp(-g)$ we get
$$R(x) = \theta(\pi z)\,\theta(z)^{-q} = \exp\bigl(q g(z) - g(\pi z)\bigr)$$
(`New.CMLattice.expSubst_smul_negLogTheta_sub_rescale_eq`). The series $q g - g(\pi z)$ has the constant term $0$, and its coefficients below the degree $q$ have norm at most $|\pi|$, by the last lemma. Item 4 gives $|\pi| \le p^{-1/(p-1)}$. So the lemma on the exponential modulo $c$ gives $|[z^n](R(x) - 1)| \le |\pi|$ for $n < q$. Now apply the triangular system to $R - 1$ and $x = z^2 + \cdots$, with $l = q$ and $s = |\pi|$. It gives $|(R-1)_i| \le |\pi|$ for every $i$ with $2i < q$. Since $2\deg R < q$, this covers all coefficients of $R - 1$. Put
$$H = \pi^{-1}(R - 1)(x) = \sum_{i \le \deg R} \pi^{-1}(R-1)_i\, x^i.$$
Each $\pi^{-1}(R-1)_i$ is integral and $x \in \mathfrak{o}[[y]]$, so $H \in \mathfrak{o}[[y]]$. Then $1 + \pi H = R(x)$. $\square$

The proof uses the degree bound in a sharp way. The congruence is checked only below the degree $q$, where item 7 controls the denominators of $g$. A polynomial in $x$ of degree less than $q/2$ is determined by these coefficients.

**Corollary (Logarithmic form).** Let $\chi_K(p) \ne 1$. There is $H \in \mathfrak{o}[[y]]$ with
$$q_p\, g(z) - g(\pi_p z) = \pi H.$$

Lean: `New.CMLattice.exists_negLogTheta_frobenius_congruence` (New/Derivatives/FormalGroup/FrobeniusCongruence.lean).

*Proof.* Let $H_0$ be the series of the theorem, and put $G = \pi^{-1}(q g - g(\pi z))$. Then $G(0) = 0$, and $\exp(\pi G) = \theta(\pi z)\theta^{-q} = 1 + \pi H_0$. The lemma on the logarithm modulo $c$, with $c = \pi$ and $B = \mathfrak{o}[[y]]$, gives $G \in \mathfrak{o}[[y]]$. $\square$

The corollary is stronger than the integrality of $\pi g$ below the degree $q$. It says that the whole series $qg - g(\pi z)$ is divisible by $\pi$ in $\mathfrak{o}[[y]]$, in all degrees. The series $g$ itself need not be integral: $g_2$ can fail to be integral, and the model case of Section 1 shows that $\theta(\varpi z)$ is not integral. The corollary controls only one combination of $g$ and its rescaling. Section 4 turns this combination into an equation for the part of $g$ that matters.

**Remark (Formalization).** The theorem and the corollary say "there is $H$". The equation determines $H$, since $\theta^{q}$ is a unit and $\pi \ne 0$. Later files obtain $H$ with `obtain`, and use only the equation and $H \in \mathfrak{o}[[y]]$. The variable $z$ of the text is the variable `X` of `PowerSeries`, and $\theta(\pi z)$ is `rescale (ιₚ (piPrime d p)) (taylorVia ιₚ C.θ)`. The results hold for every $\iota_p$.
