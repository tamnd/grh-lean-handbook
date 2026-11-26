---
title: The classical explicit formula
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The classical explicit formula

This section states the explicit formula in its classical form, and reads it as a statement about the poles of a transform. It has no Lean statements. Its purpose is to show what the source keeps from the classical theory and what it leaves out. The model case with the weight $1/n - 1/x$ is in [the weighted prime remainder](/chapter/weighted-prime-remainder/#the-model-case), and this section links to it in place of a second proof.

### Perron's formula and the residues

Let $\psi(x) = \sum_{n \leq x} \Lambda(n)$, and let $\psi_0(x)$ be $\psi(x)$ if $x$ is not a prime power and $\psi(x) - \Lambda(x)/2$ if it is. For $c > 1$ and $x > 1$, Perron's formula gives
$$\psi_0(x) = \frac{1}{2\pi i}\int_{c - i\infty}^{c + i\infty} \Bigl(-\frac{\zeta'}{\zeta}(s)\Bigr)\frac{x^s}{s}\, ds,$$
where the integral is the limit of the integrals over $[c - iT, c + iT]$ as $T \to \infty$ (Davenport, *Multiplicative Number Theory*, Chapter 17). Move the line of integration to the left. Each pole of the integrand gives its residue:

1. at $s = 1$, the pole of $\zeta$ gives $x$;
2. at a zero $\rho$ of $\zeta$ of order $m$ in the strip $0 < \operatorname{Re} s < 1$, the integrand has the residue $-m x^\rho/\rho$;
3. at $s = 0$, the kernel $1/s$ gives $-\zeta'/\zeta(0) = -\log 2\pi$;
4. at a trivial zero $s = -2k$, $k \geq 1$, the residue is $x^{-2k}/(2k)$, and the sum over $k$ is $-\frac{1}{2}\log(1 - x^{-2})$.

**Theorem (The explicit formula for ψ).** For $x > 1$,
$$\psi_0(x) = x - \sum_\rho \frac{x^\rho}{\rho} - \log 2\pi - \frac{1}{2}\log\bigl(1 - x^{-2}\bigr),$$
where $\rho$ runs over the zeros of $\zeta$ in $0 < \operatorname{Re} s < 1$ with multiplicity, and the sum is the limit as $T \to \infty$ of the sum over $|\operatorname{Im} \rho| < T$.

This is Davenport, Chapter 17. The proof is not the formal computation above. It needs the partial fraction formula of Section 2, the count $N(T + 1) - N(T) = O(\log T)$ of the zeros (Chapter 15), and a bound for $\zeta'/\zeta$ on horizontal lines that avoid the zeros, so that the integrals over the horizontal sides of the contour tend to $0$. Davenport proves a truncated form with an explicit error, and the formula is its limit. The analogue for $\psi(x, \chi) = \sum_{n \leq x}\chi(n)\Lambda(n)$ with $\chi$ primitive is Davenport, Chapter 19. Montgomery and Vaughan, *Multiplicative Number Theory I*, Chapter 12, treat the classical explicit formulae and the explicit formula of Weil. Iwaniec and Kowalski, *Analytic Number Theory*, Section 5.5, prove an explicit formula for a general L-function, with a smooth test function in place of the sharp cut-off.

The sum over $\rho$ converges only conditionally. The reason is the kernel: the residue at $\rho$ has the factor $1/\rho$, and $\sum_\rho 1/|\rho|$ diverges, since there are about $(T/2\pi)\log T$ zeros up to height $T$.

### The kernel 1/(s(s - 1))

A weight that vanishes at the end of the sum gives a kernel with more decay. For $a : \mathbb{N} \to \mathbb{C}$ with $A(s) = \sum a(n) n^{-s}$ absolutely convergent for $\operatorname{Re} s > 1$, put $S_a(y) = \sum_{n \leq y} a(n)(1/n - 1/y)$. Then
$$\int_1^\infty S_a(y)\, y^{-s}\, dy = \frac{A(s)}{s(s - 1)}, \qquad \operatorname{Re} s > 1$$
([the weighted prime remainder](/chapter/weighted-prime-remainder/#the-model-case), Lemma on the transform of the weight). Take $a = \chi\Lambda$ for a character $\chi$, so that $A(s) = \delta_\chi/(s - 1) - \tilde L'/\tilde L(s, \chi)$ by [Lemma](/decl/New.LSeriesHasSum_mul_vonMangoldt/). By [Lemma](/decl/New.tendsto_sub_mul_logDeriv_entireL_analyticOrderNatAt/), at a point $\rho \neq 0, 1$ the transform has the residue
$$\frac{-\operatorname{ord}_\rho \tilde L(\cdot, \chi)}{\rho(\rho - 1)} = \frac{\operatorname{ord}_\rho \tilde L(\cdot, \chi)}{\rho(1 - \rho)}.$$
On the critical line, $1 - \rho = \bar\rho$, so $\rho(1 - \rho) = |\rho|^2$, and the residue of a simple zero is $1/|\rho|^2 > 0$. For the first zero $\rho = 1/2 + 14.134725\,i$ of $\zeta$, $|\rho|^2 = 200.0405$, and the residue is $0.0049990$. Since $\sum_\rho |\rho|^{-2} < \infty$ (Davenport, Chapter 12), the explicit formula for $S_a$ converges absolutely. Volume 1 gives this formula for $a = \Lambda$:
$$\sum_{n \leq x}\Lambda(n)\Bigl(\frac{1}{n} - \frac{1}{x}\Bigr) = \log x - 1 - \gamma + \sum_\rho \frac{x^{\rho - 1}}{\rho(1 - \rho)} + \frac{\log 2\pi}{x} - \sum_{k \geq 1}\frac{x^{-2k - 1}}{2k(2k + 1)}, \qquad x \geq 1.$$
Each zero $\rho$ gives the term $x^{\rho - 1}/(\rho(1 - \rho))$: the residue of the transform times $x^{\rho - 1}$.

### The dictionary

The rule "a pole $c/(s - \rho)$ of the transform is a term $c\, y^{\rho - 1}$ of the function" is exact in one direction. The proposition below states it in the variable $v = \log y$, which the source uses.

**Proposition (Polar parts of an expansion).** Let $E : [0, \infty) \to \mathbb{C}$ be measurable and let $\beta$ be real. Suppose that
$$E(v) = \sum_{j = 1}^J c_j\, e^{(\rho_j - 1)v} + F(v), \qquad v \geq 0,$$
with distinct $\rho_j \in \mathbb{C}$, $c_j \in \mathbb{C}$, and $|F(v)| \leq C e^{(\beta - 1)v}$ for $v \geq 0$. Let $\sigma_0 = \max(\beta, \operatorname{Re}\rho_1, \ldots, \operatorname{Re}\rho_J)$. Then for $\operatorname{Re} s > \sigma_0$ the integral $\Phi(s) = \int_0^\infty E(v) e^{(1 - s)v}\, dv$ converges absolutely, and
$$\Phi(s) = \sum_{j = 1}^J \frac{c_j}{s - \rho_j} + \Phi_F(s),$$
where $\Phi_F(s) = \int_0^\infty F(v) e^{(1 - s)v}\, dv$ is analytic on $\operatorname{Re} s > \beta$. So $\Phi$ continues to a meromorphic function on $\operatorname{Re} s > \beta$. Its poles there are the $\rho_j$ with $\operatorname{Re}\rho_j > \beta$ and $c_j \neq 0$. They are simple, and the residue at $\rho_j$ is $c_j$.

*Proof.* For $\operatorname{Re} s > \operatorname{Re}\rho_j$, $\int_0^\infty e^{(\rho_j - s)v}\, dv = 1/(s - \rho_j)$, and the integral converges absolutely. The integrand of $\Phi_F$ is at most $C e^{(\beta - \operatorname{Re} s)v}$ in absolute value. So $\Phi_F$ converges absolutely and locally uniformly on $\operatorname{Re} s > \beta$, and it is analytic there by Morera's theorem and Fubini's theorem. Add the $J + 1$ integrals. $\square$

The proposition goes from the function to the poles. The explicit formula goes the other way: from the poles of $-L'/L$ to an expansion of the prime sum. That direction is the hard one. A pole at $\rho$ with residue $c$ says nothing about the size of the other terms, and it gives no expansion without bounds for the transform on vertical lines. The classical proof gets those bounds from the functional equation and the count of zeros.

The proposition has one consequence that needs no such bounds. If $|E(v)| \leq C e^{(\beta - 1)v}$ for all $v \geq 0$, then $\Phi$ is analytic on $\operatorname{Re} s > \beta$, so it has no pole there. For the weighted sum above this gives one half of a classical equivalence: if the remainder $\sum_{n \leq x}\Lambda(n)(1/n - 1/x) - \log x + 1 + \gamma$ is $O(x^{\beta - 1})$, then $\zeta$ has no zero in $\operatorname{Re} s > \beta$. The explicit formula gives the converse. Section 4 proves the first half in the language of the source.

### Two questions

The source needs two things that the dictionary does not give at once.

1. A *one-sided* form. The proof bounds $R_q$ from above only. Landau's theorem on transforms of positive measures gives a one-sided form of the consequence above, if the residues at the real points have the right sign ([Landau's theorem](/chapter/landau-theorem/)).
2. A form for a *combination* of L-functions. The weight of the source is $\Lambda(n)(1 - \chi_K(n))$ on the class $n \equiv 1 \bmod q$, and the transform of $R_q$ has poles at the zeros of $2\varphi(q)$ L-functions, some with a plus sign and some with a minus sign ([the weighted prime remainder](/chapter/weighted-prime-remainder/)).

The notion of a polar function in Section 4 is the frame in which the source states the poles and their residues, for any function, without an expansion.
