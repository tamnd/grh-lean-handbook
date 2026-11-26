---
title: The remainder and its poles
lean:
  - New/Reduction/Zeros/PrimeError.lean
  - Lib/Analytic/EntireLFunction.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The remainder and its poles

This chapter defines the function that the whole argument bounds, and it proves the analytic facts about it that the rest of Volume 1 uses. The function is a weighted sum over prime powers in the class $1$ modulo $q$, less its main term. We call it the weighted prime remainder $R_q(x)$. The main result is an explicit formula as a statement about poles. The Mellin transform of $R_q$ continues to a meromorphic function on $\mathbb{C}$. In $\operatorname{Re} s > 0$ its poles are at most simple, it has no pole at $s = 1$, and its residue at $\rho \neq 1$ is a count of zeros of Dirichlet L-functions at $\rho$, divided by $\varphi(q)\rho(1 - \rho)$. The sign of that count is the reason for the shape of the whole argument.

### The function

Fix a prime $d$, and let $\chi_K(n) = (n/d)$ be the Legendre symbol modulo $d$. For $d \equiv 3 \bmod 4$ it is the quadratic character of the imaginary quadratic field $K = \mathbb{Q}(\sqrt{-d})$. Fix an integer $q \geq 1$, and let $\Lambda$ be the von Mangoldt function. The weight is
$$\lambda(n) = \begin{cases} \Lambda(n)\bigl(1 - \chi_K(n)\bigr) & \text{if } n \equiv 1 \bmod q, \\ 0 & \text{otherwise,} \end{cases}$$
and the weighted prime remainder is
$$R_q(x) = \sum_{1 \leq n \leq x} \lambda(n)\Bigl(\frac{1}{n} - \frac{1}{x}\Bigr) - \frac{\log x}{\varphi(q)} - c_q,$$
where $\varphi$ is Euler's function and $c_q$ is a real constant, defined in Section 3 through logarithmic derivatives of L-functions at $s = 1$. A later theorem of the source proves that $R_q(x) \to 0$ as $x \to \infty$ when $d$ is odd and prime to $q$ (Section 5). So $c_q$ is the constant term of the asymptotic expansion of the weighted sum.

For $q = 1$ the constant is explicit. Section 4 proves that
$$c_1 = -1 - \bigl(\gamma - \operatorname{Re} \tfrac{L'}{L}(1, \chi_K)\bigr),$$
with $\gamma$ Euler's constant. The number in the brackets is the constant of the formula of Chowla and Selberg for the periods of elliptic curves with complex multiplication by $K$. The source calls it the Chowla-Selberg constant.

### The main theorem in brief

For a Dirichlet character $\chi$ let $\tilde L(s, \chi)$ be $L(s, \chi)$ if $\chi$ is not principal, and the entire function $(s - 1) L(s, \chi)$ if $\chi$ is principal. For $\rho \in \mathbb{C}$ put
$$n(\rho) = \sum_{\psi \bmod q} \operatorname{ord}_\rho \tilde L(\cdot, \psi), \qquad n_K(\rho) = \sum_{\psi \bmod q} \operatorname{ord}_\rho \tilde L(\cdot, \psi\chi_K),$$
where $\psi$ runs over the $\varphi(q)$ characters modulo $q$, and $\psi\chi_K$ is the product character modulo $qd$. Section 5 proves the following theorem.

*Let $d \equiv 7 \bmod 8$ be a prime with $\gcd(q, d) = 1$. The integral $\int_1^\infty R_q(y) y^{-s}\, dy$, which converges for $\operatorname{Re} s > 2$, continues to a meromorphic function on $\mathbb{C}$. In $\operatorname{Re} s > 0$ its poles are at most simple. It has no pole at $s = 1$. At $\rho \neq 1$ with $\operatorname{Re} \rho > 0$ its residue is*
$$\frac{n(\rho) - n_K(\rho)}{\varphi(q)\, \rho(1 - \rho)}.$$

The zeros of the L-functions of the characters $\psi$ enter with a plus sign. The zeros of the twists $\psi\chi_K$ enter with a minus sign. On the real segment $0 < x < 1$ the factor $x(1 - x)$ is positive. So at a real point where no twist vanishes, the residue is at least $0$.

### Where the chapter sits in the argument

The plan of the proof is in [the theorem and the plan](/chapter/theorem-and-plan/). The argument uses $R_q$ for $q = q_0$, a fixed multiple of $18480$, and for $q = 1$. The prime $d$ runs over a class $d \equiv d_0 \bmod q_0$, with $d \equiv 7 \bmod 8$ ([fields, places and twists](/chapter/fields-places-twists/)). The results of this chapter are used in four places.

1. [Landau's criterion](/chapter/landau-criterion/) uses the main theorem. It turns a one-sided bound $R_{q_0}(y) \leq y^{\beta - 1}$ for all large $y$, for every prime $d$ of the class, into the absence of zeros of $L(s, \psi)$, $\psi \bmod q_0$, in $\operatorname{Re} s > \beta$.
2. [Prime sums and the total remainder](/chapter/prime-sums/) uses the form of $R_q$ with positive parts (Section 3). The lattice argument produces sums of exactly this kind.
3. [The main inequality and the end of the proof](/chapter/main-inequality/) proves the one-sided bound, and it needs the two-sided bound $|R_q(x_1)| \leq (\log x_1)^{-B}$ at the second cut-off $x_1$. This is the prime number theorem for $R_q$ (Section 5).
4. The constant $c_1$ enters the period $\Omega$ of the data and the main prime sum. It cancels between them (Section 4).

### Why these weights

The weight $1 - \chi_K(p)$ of a prime $p \neq d$ is $0$ when $p$ splits in $K$ and $2$ when $p$ is inert. So for $q = 1$ the weighted sum counts the primes that do not split. Section 4 shows that for $q = 1$ and $d \equiv 3 \bmod 4$, $\sum \lambda(n) n^{-s} = -2\zeta'/\zeta(s) + \zeta_K'/\zeta_K(s)$ for $\operatorname{Re} s > 1$, where $\zeta_K$ is the Dedekind zeta function of $K$. The lattice method of the source produces prime sums with these weights. It does not produce the classical sum with weights $\Lambda(n)$.

Two properties of the weights matter. First, $\lambda(n) \geq 0$, so Landau's lemma applies, and a one-sided bound on $R_q$ is enough. Second, the zeros of the twists enter with the wrong sign. The criterion avoids them by the choice of a prime $d$ of the class for which no twist vanishes near the point under study. So the construction runs for every prime $d$ of a class.

The chapter uses no zero-free region, no functional equation, and no bound for $L$ in the critical strip.

### The plan of the chapter

Section 2 is the model case: the explicit formula for $\psi(x)$, and the Mellin transform of a sum with weights $1/n - 1/x$. Section 3 defines the weights, the functions $\tilde L$ and $G_q$ and the remainder $R_q$, and proves the elementary bounds. Section 4 computes the Dirichlet series of $\lambda$ and the constant $c_1$. Section 5 computes the transform and its residues, proves the main theorem, and explains the sign. Section 6 has the exercises and the notes. The proof of the main theorem has four steps.

1. Orthogonality of characters writes $\lambda$ as a mean of $\psi\Lambda - \psi\chi_K\Lambda$ over the characters $\psi$ modulo $q$. So the Dirichlet series of $\lambda$ is $s/(\varphi(q)(s - 1)) + G_q(s)$, where $G_q$ is a mean of logarithmic derivatives of the functions $\tilde L$.
2. Partial summation turns the Dirichlet series into the Mellin transform of the weighted sum. The weight $1/n - 1/x$ gives the factor $1/(s(s - 1))$.
3. The terms $\log x/\varphi(q)$ and $c_q$ remove the double pole and the simple pole at $s = 1$. The transform of $R_q$ is $(G_q(s)/s - c_q)/(s - 1)$, with no pole at $1$ because $c_q = G_q(1)$.
4. The logarithmic derivative of $\tilde L$ has a simple pole at each zero, with residue the order of the zero. This gives the residues.

Lean accepts these results, if the checks that the source reports hold. This book did not rerun the checks (Volume 0, Chapter 2).
