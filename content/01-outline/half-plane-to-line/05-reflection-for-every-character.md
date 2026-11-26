---
title: Zero reflection for every character
lean:
  - Lib/Analytic/ZeroSymmetry.lean
decls:
  - New.prod_euler_factor_ne_zero
  - New.exists_isPrimitive_changeLevel_eq
  - New.gammaFactor_changeLevel
  - New.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Zero reflection for every character

This section proves that a zero $s$ of $L(s, \chi)$ with $\operatorname{Re} s \neq 0$ and $s \neq 1$ gives a zero $1 - s$ of $L(s, \bar\chi)$, unless $s$ is a pole of the gamma factor. The character $\chi$ need not be primitive. Mathlib has the functional equation only for primitive characters, and its L-function of an imprimitive character is the imprimitive L-function. So the proof passes to the primitive character $\chi^*$ that induces $\chi$, uses the functional equation of $\chi^*$, and comes back. Three lemmas carry the passage.

### The finite Euler factors

**Lemma (The finite Euler factors).** Let $\chi$ be a Dirichlet character modulo $q$, let $q'$ be a natural number, and let $s \in \mathbb{C}$ with $\operatorname{Re} s \neq 0$. Then
$$\prod_{p \mid q'} \left(1 - \chi(p) p^{-s}\right) \neq 0,$$
where the product is over the primes that divide $q'$.

Lean: `New.prod_euler_factor_ne_zero` (Lib/Analytic/ZeroSymmetry.lean).

For $q' = 0$ and $q' = 1$ the product is empty and equal to $1$.

*Proof.* It is enough to show that each factor is not zero. Suppose $1 - \chi(p) p^{-s} = 0$ for a prime $p$. Then $\chi(p) = p^s$, so $\chi(p) \neq 0$, and $p$ is a unit modulo $q$. Then $\chi(p)$ is a root of unity, and $|\chi(p)| = 1$. But $|p^s| = p^{\operatorname{Re} s}$. So $p^{\operatorname{Re} s} = 1$, and $\operatorname{Re} s = 0$, against the hypothesis. $\square$

The zeros of one factor are explicit. Let $p \nmid q$ and write $\chi(p) = e^{i\vartheta}$. Then $1 - \chi(p)p^{-s} = 0$ exactly when
$$s = \frac{i(\vartheta + 2\pi k)}{\log p}, \qquad k \in \mathbb{Z}.$$
These zeros form a vertical arithmetic progression on the line $\operatorname{Re} s = 0$, with step $2\pi / \log p$. Each zero is simple.

**Remark (Formalization).** The Lean proof does not use that $\chi(p)$ is a root of unity. It uses that $\overline{\chi(p)} = \chi(p)^{-1}$, with Lean's convention $0^{-1} = 0$, so that the identity holds also when $\chi(p) = 0$. From $\chi(p) = p^s$ it gets $p^{\operatorname{Re} s} = |\chi(p)| = |\chi(p)^{-1}| = p^{-\operatorname{Re} s}$, and so $\operatorname{Re} s = -\operatorname{Re} s$.

### The primitive character and its gamma factor

**Lemma (A primitive character induces $\chi$).** Let $q \geq 1$ and let $\chi$ be a Dirichlet character modulo $q$. Then there are a divisor $q^* \geq 1$ of $q$ and a primitive character $\chi^*$ modulo $q^*$ such that $\chi^*$ induces $\chi$.

Lean: `New.exists_isPrimitive_changeLevel_eq` (Lib/Analytic/ZeroSymmetry.lean).

*Proof.* Take for $q^*$ the conductor of $\chi$, and for $\chi^*$ Mathlib's primitive character of $\chi$ (Section 2). Mathlib proves that the conductor divides $q$ and is not $0$, that $\chi^*$ is primitive, and that $\chi^*$ induces $\chi$. $\square$

**Lemma (The gamma factor of an induced character).** Let $q^* \mid q$, let $\psi$ be a character modulo $q^*$, and let $\chi$ be the character that $\psi$ induces modulo $q$. Then $G_\chi(s) = G_\psi(s)$ for every $s \in \mathbb{C}$.

Lean: `New.gammaFactor_changeLevel` (Lib/Analytic/ZeroSymmetry.lean).

*Proof.* The class of $-1$ is a unit modulo $q$, so $\chi(-1) = \psi(-1)$. So $\chi$ and $\psi$ have the same parity, and the same gamma factor. $\square$

### The reflection theorem

**Theorem (Zero reflection).** Let $q \geq 1$, let $\chi$ be a Dirichlet character modulo $q$, and let $s \in \mathbb{C}$ with $\operatorname{Re} s \neq 0$, $s \neq 1$ and $L(s, \chi) = 0$. Then $G_\chi(s) = 0$ or $L(1 - s, \bar\chi) = 0$.

Lean: `New.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero` (Lib/Analytic/ZeroSymmetry.lean).

By the convention for $\Gamma_{\mathbb{R}}$, the first alternative says that $s$ is a pole of the gamma factor of $\chi$: $s \in \{-2, -4, \dots\}$ if $\chi$ is even, and $s \in \{-1, -3, \dots\}$ if $\chi$ is odd. (The pole $0$ of an even character is excluded by $\operatorname{Re} s \neq 0$.)

*Proof.* By [Lemma](/decl/New.exists_isPrimitive_changeLevel_eq/), let $\chi^*$ be a primitive character modulo $q^* \mid q$, $q^* \geq 1$, that induces $\chi$. Write
$$E(s) = \prod_{p \mid q}\left(1 - \chi^*(p) p^{-s}\right), \qquad \bar E(s) = \prod_{p \mid q}\left(1 - \bar\chi^*(p) p^{-s}\right).$$

Step 1: $L(s, \chi^*) = 0$. Since $s \neq 1$, the change of level formula of Section 2 gives $L(s, \chi) = L(s, \chi^*) E(s)$. By [Lemma](/decl/New.prod_euler_factor_ne_zero/), $E(s) \neq 0$, since $\operatorname{Re} s \neq 0$. So $L(s, \chi^*) = 0$.

Step 2: $\Lambda(s, \chi^*) = 0$, if $G_\chi(s) \neq 0$. Suppose $G_\chi(s) \neq 0$; we prove the second alternative. By [Lemma](/decl/New.gammaFactor_changeLevel/), $G_{\chi^*}(s) = G_\chi(s) \neq 0$. Since $\operatorname{Re} s \neq 0$, we have $s \neq 0$. So Mathlib's formula gives $0 = L(s, \chi^*) = \Lambda(s, \chi^*) / G_{\chi^*}(s)$, and $\Lambda(s, \chi^*) = 0$.

Step 3: $\Lambda(1 - s, \bar\chi^*) = 0$. The conductor of $\bar\chi^*$ is the conductor of $\chi^*$, so $\bar\chi^*$ is primitive modulo $q^*$. The functional equation for $\bar\chi^*$ gives
$$\Lambda(1 - s, \bar\chi^*) = (q^*)^{s - 1/2}\, w(\bar\chi^*)\, \Lambda(s, \chi^*) = 0.$$

Step 4: $L(1 - s, \bar\chi^*) = 0$. Since $s \neq 1$, we have $1 - s \neq 0$. So Mathlib's formula gives $L(1 - s, \bar\chi^*) = \Lambda(1 - s, \bar\chi^*) / G_{\bar\chi^*}(1 - s) = 0$.

Step 5: $L(1 - s, \bar\chi) = 0$. Induction commutes with conjugation, so $\bar\chi^*$ induces $\bar\chi$. Since $1 - s \neq 1$, the change of level formula gives $L(1 - s, \bar\chi) = L(1 - s, \bar\chi^*)\, \bar E(1 - s) = 0$. $\square$

Each hypothesis of the theorem is used once. The hypothesis $\operatorname{Re} s \neq 0$ makes $E(s) \neq 0$ in step 1 and gives $s \neq 0$ in step 2. The hypothesis $s \neq 1$ allows the change of level formula in step 1 when $\chi^*$ is principal, and gives $1 - s \neq 0$ in step 4 and $1 - s \neq 1$ in step 5. Step 4 needs no condition on $G_{\bar\chi^*}(1 - s)$, since a quotient with numerator $0$ is $0$ in Lean.

**Remark (Formalization).** The theorem keeps only the reflection of zeros. It does not compare the orders of the zeros at $s$ and $1 - s$, and it does not keep the root number $w(\chi^*)$ or the identity between the completed functions. The source cites Montgomery and Vaughan, *Multiplicative Number Theory I*, Corollaries 10.3 and 10.8. The list of citations of the source puts this file among those whose citations were not compared with their sources, and this book has not compared them.

### Examples

**Example (An imprimitive character modulo 12).** The units modulo $12$ are $1, 5, 7, 11$. Let $\chi$ be the character modulo $12$ induced by $\chi_4$: $\chi(1) = \chi(5) = 1$ and $\chi(7) = \chi(11) = -1$. It is odd and real, and its conductor is $4$. The primes that divide $12$ are $2$ and $3$. The factor at $2$ is $1$, since $\chi_4(2) = 0$. The factor at $3$ is $1 - \chi_4(3)3^{-s} = 1 + 3^{-s}$. So
$$L(s, \chi) = (1 + 3^{-s})\, L(s, \chi_4).$$
The factor $1 + 3^{-s}$ vanishes exactly at $s_k = i\pi(2k + 1)/\log 3$, $k \in \mathbb{Z}$. These are zeros of $L(s, \chi)$ on $\operatorname{Re} s = 0$. At $s_k$ neither alternative of the theorem holds. First, $G_\chi(s_k) = \Gamma_{\mathbb{R}}(s_k + 1) \neq 0$, since $\operatorname{Re}(s_k + 1) = 1 > 0$. Second, $L(1 - s_k, \bar\chi) = L(1 - s_k, \chi) = (1 + 3^{s_k - 1}) L(1 - s_k, \chi_4)$. Here $3^{s_k} = e^{i\pi(2k+1)} = -1$, so $1 + 3^{s_k - 1} = 2/3$. And $L(1 - s_k, \chi_4) \neq 0$, since $\operatorname{Re}(1 - s_k) = 1$. So $L(1 - s_k, \bar\chi) \neq 0$. The hypothesis $\operatorname{Re} s \neq 0$ cannot be removed.

**Example (A trivial zero).** For $\chi_4$ and $s = -1$, the hypotheses of the theorem hold, and $L(-1, \chi_4) = 0$ (Section 2). The second alternative fails: $L(2, \chi_4) \neq 0$. The first alternative holds: $G_{\chi_4}(-1) = \Gamma_{\mathbb{R}}(0) = 0$ by the convention. So the theorem needs its first alternative.

### The classical form

The textbook states the symmetry for one character, as a symmetry about the critical line. It follows from the theorem and the conjugate symmetry of Section 2. The source does not state it.

**Corollary (Symmetry about the critical line).** Let $q \geq 1$, let $\chi$ be a Dirichlet character modulo $q$, and let $\rho \in \mathbb{C}$ with $0 < \operatorname{Re} \rho < 1$ and $L(\rho, \chi) = 0$. Then $L(1 - \bar\rho, \chi) = 0$.

*Proof.* We have $\operatorname{Re} \rho \neq 0$ and $\rho \neq 1$. Also $G_\chi(\rho) = \Gamma_{\mathbb{R}}(\rho + a(\chi)) \neq 0$, since $\operatorname{Re}(\rho + a(\chi)) > 0$. So [Theorem](/decl/New.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero/) gives $L(1 - \rho, \bar\chi) = 0$. Since $1 - \rho \neq 1$, the conjugate symmetry gives $L(1 - \bar\rho, \chi) = \overline{L(1 - \rho, \bar\chi)} = 0$. $\square$

So the zeros of $L(s, \chi)$ in the open strip are symmetric under the reflection $s \mapsto 1 - \bar s$ in the critical line, for every Dirichlet character, primitive or not.
