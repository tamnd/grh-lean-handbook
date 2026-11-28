---
title: Symmetry of the zeros
lean:
  - Lib/Analytic/ZeroSymmetry.lean
  - Lib/Cyclotomic/Voronoi.lean
decls:
  - New.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero
  - New.OddPart.LFunction_neg_nat_eq_zero_iff
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Symmetry of the zeros

This section states the classical symmetry of the zeros of $L(s, \chi)$, then the reflection theorem of the source, which holds for every character, and then the trivial zeros of every character. The last part shows how Volume 1 uses the reflection.

### The classical statement

Let $\chi$ be a primitive character modulo $q$ with parity $a$. The zeros of $L(s, \chi)$ fall into two kinds (Davenport, *Multiplicative Number Theory*, Chapter 9).

1. The *trivial zeros* are the poles of $G_\chi$, except $s = 0$ when $\chi = \chi_0$ and $q = 1$. They are the points $s = -a - 2n$ with $n \in \mathbb{N}$, and they are simple. For $\chi \neq \chi_0$ even, the point $s = 0$ is a trivial zero. For $q = 1$, $\zeta(0) = -1/2$, and the trivial zeros are $-2, -4, \ldots$.
2. The *nontrivial zeros* lie in the strip $0 \leq \operatorname{Re} s \leq 1$. By the non-vanishing of Section 2 they lie in $0 \leq \operatorname{Re} s < 1$, and so, by the functional equation, in $0 < \operatorname{Re} s < 1$.

For $\operatorname{Re} s > 1$ the Euler product shows that $L(s, \chi) \neq 0$. For $\operatorname{Re} s < 0$ the functional equation of Section 3 shows that the only zeros are the trivial ones. In the strip, the gamma factors $G_\chi(s)$ and $G_{\bar\chi}(1 - s)$ have no zero and no pole. So the functional equation $\Lambda(1 - s, \chi) = q^{s - 1/2}w(\chi)\Lambda(s, \bar\chi)$ gives the first symmetry: for $0 < \operatorname{Re}\rho < 1$,
$$\operatorname{ord}_{s = \rho} L(s, \chi) = \operatorname{ord}_{s = 1 - \rho} L(s, \bar\chi).$$
The second symmetry is conjugation. The series $\sum_n \chi(n)n^{-s}$ gives $L(\bar s, \bar\chi) = \overline{L(s, \chi)}$ for $\operatorname{Re} s > 1$. Both sides are holomorphic in $s$ on $\mathbb{C} \setminus \{1\}$, so the identity theorem extends the identity. So $\operatorname{ord}_{s = \rho} L(s, \chi) = \operatorname{ord}_{s = \bar\rho} L(s, \bar\chi)$.

Together, the two maps $s \mapsto 1 - s$ and $s \mapsto \bar s$ act on the set of pairs $(\rho, \chi)$. The composite $s \mapsto 1 - \bar s$ keeps the character. It is the reflection in the critical line $\operatorname{Re} s = 1/2$. So the nontrivial zeros of one $L(s, \chi)$ are symmetric about the critical line, with multiplicities. They are symmetric about the real axis when $\chi$ is real, that is, when $\chi = \bar\chi$.

For an imprimitive $\chi$, the zeros of $L(s, \chi)$ are those of $L(s, \chi^*)$ together with the zeros of $E(s)$ on $\operatorname{Re} s = 0$ (Section 3). The zeros of $E$ break the symmetry: a zero $s$ of $E$ with $\operatorname{Re} s = 0$ has $1 - s$ on the line $\operatorname{Re} s = 1$, where $L(\cdot, \bar\chi)$ has no zero.

### The reflection theorem

**Theorem (Reflection of zeros).** Let $q \geq 1$, let $\chi$ be a character modulo $q$, and let $s \in \mathbb{C}$ with $\operatorname{Re} s \neq 0$, $s \neq 1$ and $L(s, \chi) = 0$. Then $G_\chi(s) = 0$ or $L(1 - s, \bar\chi) = 0$.

Lean: `New.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero` (Lib/Analytic/ZeroSymmetry.lean).

Here $L$ is Mathlib's L-function, and $G_\chi(s) = 0$ is Mathlib's value at a pole of the gamma factor (Section 3). So the first alternative says that $s$ is a pole of $G_\chi$. The character need not be primitive.

*Proof.* Let $\chi^*$ be the primitive character modulo $q^*$ that induces $\chi$ (Section 2).

Step 1: $L(s, \chi^*) = 0$. Since $s \neq 1$, the change of level gives $L(s, \chi) = L(s, \chi^*)E(s)$. Since $\operatorname{Re} s \neq 0$, the lemma on the finite Euler factors gives $E(s) \neq 0$.

Assume now that $G_\chi(s) \neq 0$. We show that $L(1 - s, \bar\chi) = 0$.

Step 2: $\Lambda(s, \chi^*) = 0$. By the lemma on gamma factors, $G_{\chi^*}(s) = G_\chi(s) \neq 0$. Also $s \neq 0$, since $\operatorname{Re} s \neq 0$. So Mathlib's formula $L(s, \chi^*) = \Lambda(s, \chi^*)/G_{\chi^*}(s)$ applies, and gives $\Lambda(s, \chi^*) = 0$.

Step 3: $\Lambda(1 - s, \bar\chi^*) = 0$. The character $\bar\chi^*$ is primitive, since it has the conductor of $\chi^*$. Its functional equation reads $\Lambda(1 - s, \bar\chi^*) = (q^*)^{s - 1/2}w(\bar\chi^*)\Lambda(s, \chi^*)$, and the right side is $0$ by Step 2.

Step 4: $L(1 - s, \bar\chi^*) = 0$. Since $1 - s \neq 0$, Mathlib's formula gives $L(1 - s, \bar\chi^*) = \Lambda(1 - s, \bar\chi^*)/G_{\bar\chi^*}(1 - s) = 0/G_{\bar\chi^*}(1 - s) = 0$.

Step 5: $L(1 - s, \bar\chi) = 0$. The character $\bar\chi^*$ induces $\bar\chi$. Since $1 - s \neq 1$, the change of level gives $L(1 - s, \bar\chi) = L(1 - s, \bar\chi^*)\bar E(1 - s) = 0$. $\square$

Step 4 needs no hypothesis on $G_{\bar\chi^*}(1 - s)$. If it is a pole, then Lean's value of the quotient is still $0$, and classically $L(1 - s, \bar\chi^*)$ is $0$ there too, as a trivial zero.

**Example (The hypothesis $\operatorname{Re} s \neq 0$).** Let $\chi$ be the character modulo $12$ induced by $\chi_4$ (Section 2). Then $E(s) = (1 - \chi_4(2)2^{-s})(1 - \chi_4(3)3^{-s}) = 1 + 3^{-s}$. It vanishes at $s_k = (2k + 1)\pi i/\log 3$, $k \in \mathbb{Z}$. So $L(s_k, \chi) = 0$. The character is odd, so $G_\chi(s_k) = \Gamma_{\mathbb{R}}(s_k + 1) \neq 0$. And $\operatorname{Re}(1 - s_k) = 1$, so $L(1 - s_k, \bar\chi) \neq 0$ by the non-vanishing of Section 2. Both alternatives fail. The theorem does not apply, because $\operatorname{Re} s_k = 0$.

**Example (The first alternative).** The character $\chi_4$ is odd and primitive. Its gamma factor $G_{\chi_4}(s) = \Gamma_{\mathbb{R}}(s + 1)$ has a pole at $s = -1$. In Mathlib $L(-1, \chi_4) = \Lambda(-1, \chi_4)/G_{\chi_4}(-1) = 0$. The theorem gives $G_{\chi_4}(-1) = 0$, the first alternative. The second fails: $L(2, \chi_4) = 1 - 3^{-2} + 5^{-2} - \cdots$ is Catalan's constant, which is positive.

### Symmetry about the critical line

The source states the reflection from $\chi$ to $\bar\chi$. The symmetry for one character follows with the conjugate symmetry.

**Corollary (Symmetry about the critical line).** Let $q \geq 1$, let $\chi$ be a character modulo $q$, and let $\rho \in \mathbb{C}$ with $0 < \operatorname{Re}\rho < 1$ and $L(\rho, \chi) = 0$. Then $L(1 - \bar\rho, \chi) = 0$.

*Proof.* We have $\operatorname{Re}\rho \neq 0$ and $\rho \neq 1$. Also $G_\chi(\rho) \neq 0$, since $\operatorname{Re}(\rho + a(\chi)) > 0$. So the theorem gives $L(1 - \rho, \bar\chi) = 0$. Since $1 - \rho \neq 1$, the conjugate symmetry gives $L(1 - \bar\rho, \chi) = \overline{L(1 - \rho, \bar\chi)} = 0$. $\square$

Not in the source. Mathlib does not have the conjugate symmetry $L(\bar s, \bar\chi) = \overline{L(s, \chi)}$ for Dirichlet L-functions, and the source does not need it: the reflection from $\chi$ to $\bar\chi$ is enough, since the statements of the source quantify over all characters.

### Trivial zeros of every character

The reflection theorem also gives the trivial zeros of every character, primitive or not. The source proves this in its file on the Voronoi congruences, where the values $L(-e, \chi)$ are Bernoulli sums.

**Lemma (Trivial zeros).** Let $q \geq 1$, let $\chi$ be a character modulo $q$, and let $e \geq 1$ be an integer. Then $L(-e, \chi) = 0$ if and only if $\chi(-1) = (-1)^{e}$.

Lean: `New.OddPart.LFunction_neg_nat_eq_zero_iff` (Lib/Cyclotomic/Voronoi.lean).

*Proof.* The condition $\chi(-1) = (-1)^{e}$ says that $e \equiv a(\chi) \bmod 2$. Since $e \geq 1$, this holds exactly when $-e$ is a pole of $G_\chi$, that is, when $G_\chi(-e) = 0$ in Mathlib.

Suppose that $G_\chi(-e) = 0$. Mathlib's formula, which applies since $-e \neq 0$, gives $L(-e, \chi) = \Lambda(-e, \chi)/0 = 0$.

Suppose that $L(-e, \chi) = 0$. Then $\operatorname{Re}(-e) \neq 0$ and $-e \neq 1$, so the theorem gives $G_\chi(-e) = 0$ or $L(1 + e, \bar\chi) = 0$. The second is false, since $\operatorname{Re}(1 + e) \geq 1$ and $1 + e \neq 1$. So $G_\chi(-e) = 0$. $\square$

In the first half of the proof the value $L(-e, \chi) = 0$ comes from the convention $x/0 = 0$. It agrees with the classical value. The classical $\Lambda(s, \chi)$ is finite at $-e$, since its only poles are at $1$ and, for $q = 1$, at $0$. So the pole of $G_\chi$ forces a zero of $L(s, \chi) = \Lambda(s, \chi)/G_\chi(s)$.

**Example.** For $q = 1$ the lemma says that $\zeta(-e) = 0$ exactly when $e$ is even: the trivial zeros $-2, -4, \ldots$ of $\zeta$, and $\zeta(-1), \zeta(-3), \ldots \neq 0$. For $\chi_4$ it says that $L(-e, \chi_4) = 0$ exactly when $e$ is odd.

### The use in Volume 1

Volume 1, [From the half-plane to the line](/chapter/half-plane-to-line/), uses the theorem in `New.zeros_on_line` (New/Main.lean). That lemma assumes that no Dirichlet L-function has a zero with $\operatorname{Re} s > 1/2$, except at the pole. Its conclusion is that every zero $s$ of a Dirichlet L-function with $0 < \operatorname{Re} s < 1$ has $\operatorname{Re} s = 1/2$. The proof applies the theorem to $s$ and to $\chi$. The gamma factor has no pole at $s$, since $\operatorname{Re} s > 0$. So $L(1 - s, \bar\chi) = 0$. The assumption, for $\chi$ at $s$ and for $\bar\chi$ at $1 - s$, gives $\operatorname{Re} s \leq 1/2$ and $\operatorname{Re}(1 - s) \leq 1/2$. Hence $\operatorname{Re} s = 1/2$. The assumption is the content of the argument. This chapter supplies only the reflection.

**Remark (Formalization).** The classical statement and the Lean theorem differ in four ways.

1. Every character. Mathlib's $L(s, \chi)$ for an imprimitive $\chi$ is the imprimitive L-function. The Lean theorem holds for it, at the cost of the hypothesis $\operatorname{Re} s \neq 0$. The example modulo $12$ shows that this hypothesis cannot be dropped.
2. Multiplicities. The classical symmetry keeps the order of a zero. The Lean theorem says only that $1 - s$ is a zero. The proof could compare orders, since the functional equation is an identity of functions, but the source has no need for it.
3. The root number. The proof uses the functional equation only to move a zero. The root number $w(\bar\chi^*)$ and the factor $(q^*)^{s - 1/2}$ are not $0$, but the proof does not use this: it multiplies $0$ by them.
4. Junk values. The alternative $G_\chi(s) = 0$ refers to Mathlib's value at a pole of $\Gamma_{\mathbb{R}}$. The trivial zeros lemma uses the convention $x/0 = 0$ in one direction. In both places the Lean value agrees with the classical meaning.

The source cites Montgomery and Vaughan, *Multiplicative Number Theory I*, Corollaries 10.3 and 10.8, for this file. Its list of references puts these citations among those not compared with the book. This chapter did not check them.
