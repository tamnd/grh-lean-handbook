---
title: The explicit formula of the source
lean:
  - New/Reduction/Zeros/PrimeError.lean
  - New/Reduction/Zeros/Criterion.lean
decls:
  - New.isPolar_primeRemainder
  - New.integral_primeRemainder
  - New.ofReal_re_logDerivMean_one
  - New.tendsto_sub_mul_logDerivMean
  - New.tendsto_logDerivMean_residue
  - New.abs_primeRemainder_exp_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The explicit formula of the source

This section gives the form of the explicit formula that the source proves, compares it with the classical form of Section 3, and checks one point of the notes. The full proof is in [the weighted prime remainder](/chapter/weighted-prime-remainder/), and this section does not repeat it. It gives the structure of the proof, and it looks at the residue formula point by point, with its junk values.

### The objects

Let $d$ be a prime, let $q \geq 1$, and let $\chi_K = (\cdot/d)$. For $n \geq 1$ put $\lambda(n) = \Lambda(n)(1 - \chi_K(n))$ if $n \equiv 1 \bmod q$, and $\lambda(n) = 0$ otherwise. The source defines
$$G_q(s) = \frac{1}{\varphi(q)}\Big(\sum_{\psi \bmod q}\Big(\frac{\tilde L'}{\tilde L}(s, \psi\chi_K) - \frac{\tilde L'}{\tilde L}(s, \psi)\Big) - 1\Big),$$
with the logarithmic derivative of Mathlib, which is $0$ at a zero (Section 2). Then $c_q = \operatorname{Re} G_q(1)$ and
$$R_q(y) = \sum_{n \leq y}\lambda(n)\Big(\frac1n - \frac1y\Big) - \frac{\log y}{\varphi(q)} - c_q.$$
These are `New.logDerivMean` and `New.primeRemainder` in the source. For $\operatorname{Re} s > 1$ and odd $d$ prime to $q$, the orthogonality of characters gives $G_q(s) = \sum_n \lambda(n)n^{-s} - s/(\varphi(q)(s - 1))$. So $G_q$ is the Dirichlet series of the weights with its pole at $s = 1$ removed.

### The theorem

**Theorem (The explicit formula of the source).** Let $d$ be a prime with $d \equiv 7 \bmod 8$, and let $q \geq 1$ with $\gcd(q, d) = 1$. Then the function $v \mapsto R_q(e^v)$ is polar with the residues
$$r(s) = \frac{1}{\varphi(q)\, s(1 - s)}\sum_{\psi \bmod q}\Big(\operatorname{ord}_s \tilde L(\cdot, \psi) - \operatorname{ord}_s \tilde L(\cdot, \psi\chi_K)\Big) = \frac{n(s) - n_K(s)}{\varphi(q)\, s(1 - s)}.$$
Lean: `New.isPolar_primeRemainder` (New/Reduction/Zeros/PrimeError.lean).

In Lean the orders are `analyticOrderNatAt`, cast to $\mathbb{C}$, and the divisions are the divisions of $\mathbb{C}$, with $x/0 = 0$.

*Proof.* This is a summary of the proof in the source. Put $C = |c_q| + 5$, $F(s) = G_q(s)/s - c_q$ and $\Phi(s) = F(s)/(s - 1)$. The four properties of a polar function come from five lemmas.

1. Measurability is proved by the tactic `fun_prop` from the definitions.
2. $\Phi$ is meromorphic on $\mathbb{C}$, since $G_q$ is a finite combination of logarithmic derivatives of entire functions and of a constant.
3. $|R_q(e^v)| \leq (|c_q| + 5)e^v$ for $v \geq 0$ ([Lemma](/decl/New.abs_primeRemainder_exp_le/)).
4. For $\operatorname{Re} s > 2$, $\int_0^\infty R_q(e^v)e^{(1 - s)v}\, dv = \Phi(s)$ ([Lemma](/decl/New.integral_primeRemainder/)). The proof transforms the four terms of $R_q(e^v)$ one by one. The term $\log y/\varphi(q)$, that is $v/\varphi(q)$, gives $1/(\varphi(q)(s - 1)^2)$ by the lemma on the transform of a power of Section 4.
5. The residues. Let $\operatorname{Re}\rho > 0$. If $\rho \neq 1$, then also $\rho \neq 0$, and [Lemma](/decl/New.tendsto_logDerivMean_residue/) gives $(z - \rho)\Phi(z) \to r(\rho)$. It rests on [Lemma](/decl/New.tendsto_sub_mul_logDerivMean/): $(z - \rho)G_q(z) \to (n_K(\rho) - n(\rho))/\varphi(q)$ for every $\rho \in \mathbb{C}$, which is the residue lemma of Section 2 summed over $\psi$. If $\rho = 1$, then $F$ is analytic at $1$, and $F(1) = 0$, since $G_q(1)$ is real ([Lemma](/decl/New.ofReal_re_logDerivMean_one/)). So $(z - 1)\Phi(z) = F(z) \to 0$, and the formula for $r(1)$ is $0/0$, which is $0$ in Lean. $\square$

The proof that $G_q(1)$ is real is worth a note, as it uses no information about $L(1, \psi)$. On $(2, \infty)$, $(s - 1)\Phi(s)$ is the transform of a real function at a real point, times a real number, so $F$ is real there. $F$ is analytic on $[1, \infty)$, so $\operatorname{Im} F$ is a real analytic function on $[1, \infty)$ that is $0$ on $(2, \infty)$. By the identity theorem it is $0$ at $1$. So $G_q(1) = F(1) + c_q$ is real, and $F(1) = G_q(1) - \operatorname{Re} G_q(1) = 0$. The constant $c_q$ was chosen to make this true.

### The hypothesis d ≡ 7 mod 8

**Remark (Formalization).** The brief of this chapter asks for a check of a claim of the notes: the theorem uses $d \equiv 7 \bmod 8$ only to get $d \neq 2$. The check confirms the claim. The first line of the proof is `have hd_ne : d ≠ 2 := by lia`, which derives $d \neq 2$ from `hd : d % 8 = 7` by linear arithmetic. After this line the proof does not use `hd`. The lemmas that it calls, `New.integral_primeRemainder` and `New.ofReal_re_logDerivMean_one`, take `hd : d ≠ 2` and `h_cop : q.Coprime d` as their hypotheses. The other lemmas need neither. So the conclusion holds for every odd prime $d$ prime to $q$, but the source states it only for $d \equiv 7 \bmod 8$.

The condition $d \equiv 7 \bmod 8$ is not idle in the argument. The criterion `New.LFunction_ne_zero_of_primeRemainder_le` uses it through `New.exists_entireL_quadTwist_ne_zero`, which chooses the prime $d$ ([Landau's criterion](/chapter/landau-criterion/)). There the class $d \equiv 7 \bmod 8$ is part of the hypothesis on the residue class of the primes.

### The residue formula point by point

The formula for $r(s)$ is a single expression, but its meaning changes from one region of $\mathbb{C}$ to another. Let $\Phi$ be the continuation of the proof.

| Region | Value of the formula | Relation to $\Phi$ |
|---|---|---|
| $\operatorname{Re} s \geq 1$, $s \neq 1$ | $0$, since no $\tilde L$ vanishes there | the residue, which is $0$ |
| $s = 1$ | $0/0$, so $0$ in Lean | the residue, which is $0$ (finding F-039) |
| $0 < \operatorname{Re} s < 1$ | $(n(s) - n_K(s))/(\varphi(q)s(1 - s))$ | the residue |
| $\operatorname{Re} s \leq 0$, $s \neq 0$ | the same expression | the residue, but the definition does not ask for it |
| $s = 0$ | $x/0$, so $0$ in Lean | not the residue in general |

At $s \neq 0, 1$ the formula is the true residue, since [Lemma](/decl/New.tendsto_logDerivMean_residue/) has no condition on $\operatorname{Re}\rho$. A polar function asks for the residue only in $\operatorname{Re} s > 0$, so the source uses only the first three rows. The last row shows that the formula must not be read as the residue at every point.

**Example (The point s = 0).** Let $q = 1$ and $d = 7$, so $\chi_K = \chi_{-7}$, the character of $\mathbb{Q}(\sqrt{-7})$. There is one character $\psi$, the principal one, with $\tilde L(s, \psi) = (s - 1)\zeta(s)$, and $\psi\chi_K = \chi_{-7}$. At $s = 0$: $\tilde L(0, \psi) = -\zeta(0) = 1/2$, and $L(0, \chi_{-7}) = 1$, from the class number $1$ of $\mathbb{Q}(\sqrt{-7})$ (Davenport, *Multiplicative Number Theory*, Chapter 6). So $n(0) = n_K(0) = 0$, $G_1$ is analytic at $0$, and the formula gives $r(0) = 0/0 = 0$. A computation gives
$$G_1(0) = \frac{L'}{L}(0, \chi_{-7}) - \frac{\tilde L'}{\tilde L}(0, \psi) - 1 \approx 0.453547 - 0.837877 - 1 = -1.384330,$$
with $\tilde L'/\tilde L(0, \psi) = -1 + \log 2\pi$. Near $0$, $\Phi(s) = (G_1(s)/s - c_1)/(s - 1)$ has a simple pole with residue $-G_1(0) \approx 1.384330 \neq 0$. So the formula is wrong at $0$. This does not affect the theorem, since $\operatorname{Re} 0 = 0$.

For $q > 1$ the principal $\psi$ gives $\tilde L(s, \psi) = (s - 1)\zeta(s)\prod_{p \mid q}(1 - p^{-s})$, and the factor $1 - p^{-s}$ vanishes at $s = 2\pi i k/\log p$ for every integer $k$, so also at $s = 0$ (Section 2). Then $G_q(s)/s$ can have a double pole at $0$, and $\Phi$ too. The definition of a polar function allows this, since it says nothing about $\operatorname{Re} s \leq 0$.

**Remark (Formalization).** The notes describe the residue formula only in $\operatorname{Re} s > 0$, and this is all that the theorem states. They do not say that the same formula is the residue at every $s \neq 0$, and they do not say that it fails at $0$. Neither point changes the argument.

### Comparison with the classical form

Write the explicit formula of Section 3 in the variable $v = \log y$. Formally, a simple pole of $\Phi$ at $\rho$ with residue $r(\rho)$ comes from a term $r(\rho)e^{(\rho - 1)v}$ of $E(v)$, that is, a term $r(\rho)y^{\rho - 1}$ of $R_q(y)$. So the theorem corresponds to the formal expansion
$$R_q(y) \;\text{``=''}\; \sum_{0 < \operatorname{Re}\rho < 1}\frac{n(\rho) - n_K(\rho)}{\varphi(q)\,\rho(1 - \rho)}\, y^{\rho - 1} + (\text{terms from } \operatorname{Re} s \leq 0).$$
The source proves no such expansion, and this book does not claim one. The theorem gives only the poles and the residues of the transform in $\operatorname{Re} s > 0$. The differences from the classical theorem are these.

1. The classical theorem is an identity for $\psi(x)$, with an error term or a limit over $T$ (Davenport, Chapters 17 and 19). The theorem of the source is a statement about a Laplace transform. It has no sum over zeros and no question of convergence.
2. The classical proof uses the functional equation, the Hadamard product and a count of zeros. The proof of the source uses only the Dirichlet series for $\operatorname{Re} s > 2$ and the local form of an analytic function at each point (Section 1).
3. The main terms. The classical formula keeps the main term $x$ and the trivial zeros. The source removes the main terms $\log y/\varphi(q) + c_q$ before it takes the transform, so that $\Phi$ has no pole at $s = 1$ and the remainder is polar (Section 4, the example of a double pole).
4. The combination. The source works with a combination of $2\varphi(q)$ $L$-functions, with signs, not with one. The residues are differences $n(\rho) - n_K(\rho)$, and they can cancel.

### What the argument uses

The argument uses the theorem once, in the criterion `New.LFunction_ne_zero_of_primeRemainder_le` ([Landau's criterion](/chapter/landau-criterion/)). There $d$ is chosen so that $n_K(s) = 0$ in a box around $\rho$, and Landau's lemma for polar functions (Section 4) is applied. So the argument uses these parts of the theorem.

1. The growth bound, so that the transform converges for $\operatorname{Re} s > 2$.
2. The continuation to $\operatorname{Re} s > \beta$ with $\beta > 1/2$, with at most simple poles.
3. The value of $r$ at real points $x > \beta$: it is $0$ for $x \geq 1$, by the first two rows of the table, and it is $n(x)/(\varphi(q)x(1 - x)) \geq 0$ for $\beta < x < 1$ when $n_K(x) = 0$.
4. The value of $r$ at $\rho$ with $\operatorname{Re}\rho > \beta$: it is $n(\rho)/(\varphi(q)\rho(1 - \rho))$ when $n_K(\rho) = 0$, and it is $0$ exactly when $n(\rho) = 0$, since $\rho(1 - \rho) \neq 0$ for $\rho \neq 1$.

Point 3 uses the junk value at $s = 1$. If Lean gave a different value to $0/0$, the sign hypothesis of Landau's lemma could fail at $x = 1$. The value $0$ is the correct residue, so this use is sound (finding F-039). The sign of the residues in point 3 is the point that the notes mark for a check by a person (finding F-077). This book has not done that check. The argument does not use the formula in $\operatorname{Re} s \leq 0$, and so it does not meet the failure at $s = 0$.
