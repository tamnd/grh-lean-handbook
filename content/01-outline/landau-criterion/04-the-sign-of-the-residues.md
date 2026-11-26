---
title: The sign of the residues
lean:
  - Lib/General/NumberTheory/ImaginaryQuadraticField.lean
  - Lib/Analytic/EntireLFunction.lean
  - New/Reduction/Zeros/PrimeError.lean
decls:
  - New.entireL
  - New.isPolar_primeRemainder
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The sign of the residues

This section recalls the polar pair of the remainder $R_q$ from [the weighted prime remainder](/chapter/weighted-prime-remainder/), and explains the sign of its residues. The zeros of the L-functions modulo $q$ give residues of the right sign for [Theorem](/decl/New.IsPolar.landau/). The zeros of their twists by $\chi_K$ give residues of the wrong sign. This sign is the reason for the choice of $d$ in Section 5, and so for the form of the hypothesis of the criterion.

### The objects

Fix a prime $d$ and let $\chi_K = (\cdot / d)$ be the Legendre symbol, a character modulo $d$. For $d \equiv 3 \bmod 4$ it is the character of $K = \mathbb{Q}(\sqrt{-d})$. Fix $q \geq 1$ prime to $d$. For a Dirichlet character $\psi$ modulo $q$, the *twist* $\psi\chi_K$ is the character modulo $qd$ with $(\psi\chi_K)(n) = \psi(n)(n/d)$. For $d$ odd it is not principal.

Lean: `New.quadTwist` (Lib/General/NumberTheory/ImaginaryQuadraticField.lean), with `New.quadTwist_ne_one` (Lib/Analytic/EntireLFunction.lean) for the last sentence.

**Definition (The entire L-function).** For a Dirichlet character $\chi$ modulo $N \geq 1$, let $\tilde L(s, \chi) = L(s, \chi)$ if $\chi$ is not principal, and let $\tilde L(\cdot, \chi)$ be the entire continuation of $(s - 1)L(s, \chi)$ if $\chi$ is principal.

Lean: `New.entireL` (Lib/General/NumberTheory/ImaginaryQuadraticField.lean).

The function $\tilde L(\cdot, \chi)$ is entire, and $\tilde L(s, \chi) \neq 0$ for $\operatorname{Re} s \geq 1$, by the classical non-vanishing on the line $\operatorname{Re} s = 1$ and the value of the residue of $L(s, \chi_0)$ at $1$ (Lean: `New.entireL_ne_zero` (Lib/Analytic/EntireLFunction.lean)). So $\tilde L(\cdot, \chi)$ is not identically zero, and its order $\operatorname{ord}_s \tilde L(\cdot, \chi)$ at each point is a natural number, which is $0$ exactly when $\tilde L(s, \chi) \neq 0$ (Lean: `New.analyticOrderNatAt_entireL_eq_zero_iff` (Lib/Analytic/EntireLFunction.lean)). For $s \neq 1$ the orders of $\tilde L(\cdot, \chi)$ and $L(s, \chi)$ agree. The comments of the source write $E_\chi$ for $\tilde L(\cdot, \chi)$; this book writes $\tilde L$, since $E$ is the CM field.

Write, for $s \in \mathbb{C}$,
$$n(s) = \sum_{\psi \bmod q} \operatorname{ord}_s \tilde L(\cdot, \psi), \qquad n'(s) = \sum_{\psi \bmod q} \operatorname{ord}_s \tilde L(\cdot, \psi\chi_K).$$
So $n(s)$ counts the zeros of the $L(s, \psi)$ at $s$ with multiplicity, and $n'(s)$ counts the zeros of the twists. Both are natural numbers, and both are $0$ for $\operatorname{Re} s \geq 1$.

The remainder is
$$R_q(x) = \sum_{n \leq x} \lambda(n)\Bigl(\frac{1}{n} - \frac{1}{x}\Bigr) - \frac{\log x}{\varphi(q)} - c_q, \qquad \lambda(n) = \mathbf{1}_{n \equiv 1 \bmod q}\, \Lambda(n)\bigl(1 - \chi_K(n)\bigr),$$
with $c_q = \operatorname{Re} G_q(1)$, where
$$G_q(s) = \frac{1}{\varphi(q)}\Bigl(\sum_{\psi \bmod q}\Bigl(\frac{\tilde L'}{\tilde L}(s, \psi\chi_K) - \frac{\tilde L'}{\tilde L}(s, \psi)\Bigr) - 1\Bigr).$$
Lean: `New.lambdaKResidueClass`, `New.logDerivMean` and `New.primeRemainder` (New/Reduction/Zeros/PrimeError.lean). [The weighted prime remainder](/chapter/weighted-prime-remainder/) explains these definitions and the value of $c_1$ through the Chowla-Selberg constant.

### The polar pair

**Theorem (The polar pair of the remainder).** Let $d$ be a prime with $d \equiv 7 \bmod 8$, let $q \geq 1$ be prime to $d$, and let $R_q$ be the remainder of $d$ and $q$. Then the pair $(E, r)$ with $E(v) = R_q(e^v)$ and
$$r(s) = \frac{n(s) - n'(s)}{\varphi(q)\; s\,(1 - s)}$$
is polar.

Lean: `New.isPolar_primeRemainder` (New/Reduction/Zeros/PrimeError.lean).

At $s = 1$ the formula divides by $0$, and Lean gives it the value $0$. This is the right value: the transform has no pole at $1$. At $s = 0$ the formula is also a division by zero, but the definition of a polar pair says nothing about $r$ at points with $\operatorname{Re} s \leq 0$.

*Proof.* [The weighted prime remainder](/chapter/weighted-prime-remainder/) gives the proof. Here are its steps. By orthogonality, for $(n, q) = 1$,
$$\mathbf{1}_{n \equiv 1 \bmod q}\bigl(1 - \chi_K(n)\bigr) = \frac{1}{\varphi(q)} \sum_{\psi \bmod q} \bigl(\psi(n) - (\psi\chi_K)(n)\bigr).$$
With $\sum \chi(n)\Lambda(n) n^{-s} = -L'/L(s, \chi)$ this gives, for $\operatorname{Re} s > 1$,
$$\sum_{n \geq 1} \lambda(n) n^{-s} = \frac{s}{\varphi(q)(s - 1)} + G_q(s).$$
(Lean: `New.LSeries_lambdaKResidueClass_eq_add_logDerivMean`.) The term $s/(\varphi(q)(s - 1))$ comes from the principal character, whose $E$ has the extra factor $s - 1$. The same computation as in Step 1 of the model criterion of Section 2 then gives, for $\operatorname{Re} s > 2$,
$$\int_0^\infty R_q(e^v)\, e^{(1 - s)v}\, dv = \frac{1}{s - 1}\Bigl(\frac{G_q(s)}{s} - c_q\Bigr).$$
(Lean: `New.integral_primeRemainder`.) The right side is meromorphic on $\mathbb{C}$. The bound $|R_q(e^v)| \leq (|c_q| + 5)e^v$ for $v \geq 0$ is elementary (Lean: `New.abs_primeRemainder_exp_le`).

At $s = 1$: the function $G_q$ is analytic on $\operatorname{Re} s \geq 1$, since no $\tilde L(\cdot, \chi)$ vanishes there, and $G_q(1)$ is real (Lean: `New.ofReal_re_logDerivMean_one`). So $G_q(1)/1 - c_q = 0$, and the transform has no pole at $1$. At $\rho \neq 0, 1$: the logarithmic derivative $f'/f$ of an entire function $f$ has residue $\operatorname{ord}_\rho f$ at $\rho$. So $G_q$ has residue $(n'(\rho) - n(\rho))/\varphi(q)$, and the transform has residue
$$\frac{n'(\rho) - n(\rho)}{\varphi(q)\, \rho\, (\rho - 1)} = \frac{n(\rho) - n'(\rho)}{\varphi(q)\, \rho\, (1 - \rho)}.$$
(Lean: `New.tendsto_logDerivMean_residue`.) $\square$

**Remark (Formalization).** The hypothesis $d \equiv 7 \bmod 8$ of the theorem is used in its proof only to get $d \neq 2$. The congruence matters in the zero density theorem of Section 5 and in the arithmetic of $K$ in later chapters.

### Where the sign comes from

The weight $\lambda$ is $\Lambda$ times $1 - \chi_K$, restricted to a class. In the Dirichlet series the term $1$ gives $-L'/L(s, \psi)$, and the term $-\chi_K$ gives $+L'/L(s, \psi\chi_K)$. The two families of L-functions enter with opposite signs. The weight $1/n - 1/x$ then divides the transform by $s(s - 1)$, which is negative on $(0, 1)$, as in Section 2.

The explicit formula shows the effect on $R_q$ itself. Heuristically,
$$R_q(x) \approx \sum_{\rho} r(\rho)\, x^{\rho - 1} = \frac{1}{\varphi(q)} \sum_\rho \frac{n(\rho) - n'(\rho)}{\rho(1 - \rho)}\, x^{\rho - 1},$$
the sum over the zeros $\rho$ of all the functions $\tilde L(\cdot, \psi)$ and $\tilde L(\cdot, \psi\chi_K)$ in the strip. Look at a real zero $\sigma \in (0, 1)$.

- A real zero of some $L(s, \psi)$ contributes $+x^{\sigma - 1}/(\varphi(q)\sigma(1 - \sigma))$. It makes $R_q$ larger. An upper bound $R_q(x) \leq x^{\beta - 1}$ with $\beta < \sigma$ excludes it.
- A real zero of some twist $L(s, \psi\chi_K)$ contributes $-x^{\sigma - 1}/(\varphi(q)\sigma(1 - \sigma))$. It makes $R_q$ smaller. An upper bound for $R_q$ cannot see it.

In the language of polar pairs: [Theorem](/decl/New.IsPolar.landau/) needs $\operatorname{Re} r(x) \geq 0$ for real $x > \beta$. At a real $x \in (\beta, 1)$ we have $x(1 - x) > 0$, so this holds if $n'(x) = 0$, and it can fail if $n'(x) > 0$. At real $x \geq 1$ both orders are $0$.

There is a second problem, at the point $\rho$ itself. Landau's lemma gives $r(\rho) = 0$, which is $n(\rho) = n'(\rho)$. If $n'(\rho) > 0$, this does not give $n(\rho) = 0$. A zero of some $L(s, \psi)$ at $\rho$ can be hidden by a zero of a twist at the same point. Then the residues cancel, the transform has no pole at $\rho$, and no bound on $R_q$ can see the zero.

So the criterion needs a prime $d$ with $n'(x) = 0$ for real $x \in (\beta, 1)$ and $n'(\rho) = 0$. Real zeros of the twists are the hard case. The twist $\psi\chi_K$ of a real character $\psi$ is a real character, and for real characters no one can exclude a real zero near $1$. This is the problem of Siegel zeros. The source does not exclude such zeros for a given $d$. It chooses $d$.

**Example (The modulus 1).** Let $q = 1$. There is one character, the principal one, and its twist is $\chi_K$. Then $\tilde L(s, \chi_0) = (s - 1)\zeta(s)$, $\tilde L(s, \chi_K) = L(s, \chi_K)$, and the Dedekind zeta function of $K$ is $\zeta_K(s) = \zeta(s)L(s, \chi_K)$. The residue of the transform of $R_1$ at $\rho \neq 0, 1$ is
$$r(\rho) = \frac{\operatorname{ord}_\rho \zeta - \operatorname{ord}_\rho L(s, \chi_K)}{\rho(1 - \rho)}.$$
Suppose that $L(s, \chi_K)$ had a real zero $\sigma \in (1/2, 1)$, for example a Siegel zero. Then $\zeta(\sigma) \neq 0$ (Section 2), so $r(\sigma) = -1/(\sigma(1 - \sigma)) < 0$ if the zero is simple. The transform of $R_1$ has a pole with a negative residue at $\sigma$, and $R_1(x)$ has a term $-x^{\sigma - 1}/(\sigma(1 - \sigma))$. An upper bound $R_1(x) \leq x^{\beta - 1}$ with $\beta < \sigma$ is consistent with this term. So an upper bound for $R_1$ for this one $d$ says nothing about the zero $\sigma$. The sign hypothesis of Landau's lemma fails at $\sigma$, so the lemma gives nothing about the zeros of $\zeta$ to the right of $\beta$ either.

The weight $1 - \chi_K$ comes from the lattice method of the later chapters, which bounds sums over the primes that are inert in $K$ ([the weighted prime remainder](/chapter/weighted-prime-remainder/)). So the twists come with the method, and the criterion must remove them.
