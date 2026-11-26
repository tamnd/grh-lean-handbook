---
title: Characters and L-functions
lean:
  - Lib/Analytic/ZeroSymmetry.lean
  - Lib/Analytic/PolyaVinogradov.lean
  - Lib/Analytic/EntireLFunction.lean
  - Lib/General/NumberTheory/ImaginaryQuadraticField.lean
decls:
  - New.exists_isPrimitive_changeLevel_eq
  - New.norm_gaussSum_of_isPrimitive
  - New.prod_euler_factor_ne_zero
  - New.entireL
  - New.entireL_ne_zero
  - New.quadTwist_ne_one
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Characters and L-functions

This section collects the classical facts about characters and their L-functions that the later sections use, each with its source and with its name in Mathlib or in the source. The facts are: the reduction of a character to a primitive one, the Gauss sum of a primitive character, the continuation of $L(s, \chi)$, the formula for an induced character, the zeros of the finite Euler factors, and the non-vanishing on $\operatorname{Re} s \geq 1$. The section ends with the entire L-function $\tilde L(s, \chi)$ of the source.

### Characters

**Definition (Dirichlet character).** Let $q \geq 1$. A *Dirichlet character modulo $q$* is a map $\chi : \mathbb{Z}/q\mathbb{Z} \to \mathbb{C}$ with $\chi(1) = 1$ and $\chi(ab) = \chi(a)\chi(b)$, and with $\chi(a) = 0$ exactly when $a$ is not a unit. We write $\chi(n)$ for $\chi(n \bmod q)$. The *principal character* $\chi_0$ modulo $q$ is $1$ on the units and $0$ on the other classes. The character is *even* if $\chi(-1) = 1$ and *odd* if $\chi(-1) = -1$. Put $a(\chi) = 0$ if $\chi$ is even and $a(\chi) = 1$ if $\chi$ is odd.

Mathlib: `DirichletCharacter`, `DirichletCharacter.Even`, `DirichletCharacter.Odd`.

The characters modulo $q$ form a group of order $\varphi(q)$, isomorphic to $(\mathbb{Z}/q\mathbb{Z})^\times$. The values on units are roots of unity, so the inverse of $\chi$ is its conjugate $\bar\chi$. Mathlib writes `χ⁻¹`. The orthogonality relations hold: $\sum_{\chi} \chi(n) = \varphi(q)$ if $n \equiv 1 \bmod q$ and $0$ otherwise (Davenport, *Multiplicative Number Theory*, Chapter 4). In Mathlib the principal character modulo $q$ is the identity `1` of the group. It is not only the character modulo $1$.

**Definition (Induced character, conductor, primitive character).** Let $q^* \mid q$ and let $\psi$ be a character modulo $q^*$. The character *induced* by $\psi$ modulo $q$ is $\chi(n) = \psi(n)$ for $\gcd(n, q) = 1$ and $\chi(n) = 0$ otherwise. The *conductor* of $\chi$ is the least $q^* \mid q$ such that a character modulo $q^*$ induces $\chi$. The character $\chi$ is *primitive* if its conductor is $q$.

Mathlib: `DirichletCharacter.changeLevel`, `DirichletCharacter.conductor`, `DirichletCharacter.IsPrimitive`.

A primitive character modulo the conductor induces $\chi$, and it is unique (Davenport, Chapter 5). The source needs only the existence.

**Lemma (A primitive character induces $\chi$).** Let $q \geq 1$ and let $\chi$ be a character modulo $q$. There are a divisor $q^* \geq 1$ of $q$ and a primitive character $\chi^*$ modulo $q^*$ that induces $\chi$.

Lean: `New.exists_isPrimitive_changeLevel_eq` (Lib/Analytic/ZeroSymmetry.lean).

*Proof.* Take for $q^*$ the conductor of $\chi$ and for $\chi^*$ Mathlib's `DirichletCharacter.primitiveCharacter`. Mathlib proves that the conductor divides $q$ and is not $0$, that $\chi^*$ is primitive, and that it induces $\chi$. $\square$

Two facts on induced characters are used later. First, $\chi$ and the character that induces it have the same parity, since $-1$ is a unit modulo every $q$. Second, induction commutes with conjugation: if $\psi$ induces $\chi$, then $\bar\psi$ induces $\bar\chi$. Also $\bar\chi^*$ is primitive, with the conductor of $\chi^*$ (Mathlib: `DirichletCharacter.conductor_inv`).

**Example (Characters modulo 4 and 12).** Modulo $4$ there are two characters, $\chi_0$ and $\chi_4$, with $\chi_4(1) = 1$ and $\chi_4(3) = -1$. The character $\chi_4$ is odd and primitive. Modulo $12$ the units are $1, 5, 7, 11$, and the group of characters has order $4$. The character $\chi$ with $\chi(1) = \chi(5) = 1$ and $\chi(7) = \chi(11) = -1$ is induced by $\chi_4$: $5 \equiv 1$ and $7 \equiv 11 \equiv 3 \bmod 4$. Its conductor is $4$.

### Gauss sums

For a character $\chi$ modulo $q$ and $n \in \mathbb{Z}$, put $e(x) = e^{2\pi i x}$ and
$$\tau(\chi, n) = \sum_{a \bmod q} \chi(a)\, e(an/q), \qquad \tau(\chi) = \tau(\chi, 1).$$
The number $\tau(\chi)$ is the *Gauss sum* of $\chi$.

**Proposition (Gauss sums of a primitive character).** Let $\chi$ be a primitive character modulo $q$. Then $\tau(\chi, n) = \bar\chi(n)\tau(\chi)$ for every $n \in \mathbb{Z}$, and $|\tau(\chi)| = q^{1/2}$.

Lean: `New.norm_gaussSum_of_isPrimitive` (Lib/Analytic/PolyaVinogradov.lean), with `DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum` (Mathlib).

*Proof.* This is in Davenport, Chapter 9. If $\gcd(n, q) = 1$, substitute $a \mapsto a n^{-1}$: then $\tau(\chi, n) = \sum_a \chi(a n^{-1}) e(a/q) = \bar\chi(n)\tau(\chi)$. Let $\gcd(n, q) = g > 1$, and write $q = g q_1$ and $n = g n_1$. Then $e(an/q) = e(an_1/q_1)$ depends only on $a \bmod q_1$. Since $\chi$ is primitive and $q_1 < q$, the character $\chi$ is not induced from modulus $q_1$. So there is a unit $c \equiv 1 \bmod q_1$ with $\chi(c) \neq 1$. The substitution $a \mapsto ca$ gives $\tau(\chi, n) = \chi(c)\tau(\chi, n)$, so $\tau(\chi, n) = 0 = \bar\chi(n)\tau(\chi)$. For the absolute value, sum $|\tau(\chi, n)|^2$ over $n \bmod q$. By the first part the sum is $\varphi(q)|\tau(\chi)|^2$. By Parseval for $\mathbb{Z}/q\mathbb{Z}$ it is $q\sum_a |\chi(a)|^2 = q\varphi(q)$. $\square$

The source proves the absolute value by Fourier inversion on $\mathbb{Z}/q\mathbb{Z}$ at $-1$, which gives $\overline{\tau(\chi)}\tau(\chi) = q$. Mathlib writes the first identity with the discrete Fourier transform, as $\sum_a \chi(a) e(-ak/q) = \bar\chi(-k)\tau(\chi)$.

**Example.** For $\chi_4$ we get $\tau(\chi_4) = e(1/4) - e(3/4) = i - (-i) = 2i$, and $|\tau(\chi_4)| = 2 = 4^{1/2}$. For the imprimitive $\chi$ modulo $12$ of the last example the identity fails at $n = 3$ (Exercise 2).

### The L-function

**Definition (Dirichlet L-function).** For $\operatorname{Re} s > 1$ let $L(s, \chi) = \sum_{n \geq 1} \chi(n) n^{-s} = \prod_p (1 - \chi(p)p^{-s})^{-1}$. The function continues to a meromorphic function on $\mathbb{C}$. The continuation is entire if $\chi \neq \chi_0$. If $\chi = \chi_0$ it has one pole, a simple pole at $s = 1$ with residue $\varphi(q)/q$.

Mathlib: `DirichletCharacter.LFunction`, `DirichletCharacter.LFunction_eq_LSeries`, `DirichletCharacter.differentiable_LFunction`, `DirichletCharacter.LFunctionTrivChar_residue_one`.

Mathlib defines $L(s, \chi)$ at every $s \in \mathbb{C}$ as a finite linear combination of Hurwitz zeta functions. For $\chi = \chi_0$ the value at $s = 1$ is a junk value. For $q = 1$ the function is $\zeta$ (Mathlib: `DirichletCharacter.LFunction_modOne_eq`). For an imprimitive $\chi$ it is the L-function of $\chi$ itself, with the Euler factors at the primes $p \mid q$ removed, and not the L-function of $\chi^*$.

**Proposition (Change of level).** Let $q^* \mid q$, let $\psi$ be a character modulo $q^*$, and let $\chi$ be the character that $\psi$ induces modulo $q$. If $\psi \neq \chi_0$ or $s \neq 1$, then
$$L(s, \chi) = L(s, \psi) \prod_{p \mid q} \left(1 - \psi(p)p^{-s}\right).$$

Mathlib: `DirichletCharacter.LFunction_changeLevel`.

*Proof.* For $\operatorname{Re} s > 1$ compare the Euler products: $\chi(p) = \psi(p)$ for $p \nmid q$ and $\chi(p) = 0$ for $p \mid q$. Both sides are holomorphic on $\mathbb{C} \setminus \{1\}$, so the identity theorem extends the formula. If $\psi \neq \chi_0$, both sides are entire, and the formula holds at $s = 1$ by continuity. $\square$

A factor with $p \mid q^*$ is $1$. So only primes that divide $q$ and not $q^*$ contribute.

**Lemma (The finite Euler factors).** Let $\chi$ be a character modulo $q$, let $m \in \mathbb{N}$, and let $\operatorname{Re} s \neq 0$. Then $\prod_{p \mid m}(1 - \chi(p)p^{-s}) \neq 0$, where the product is over the primes that divide $m$.

Lean: `New.prod_euler_factor_ne_zero` (Lib/Analytic/ZeroSymmetry.lean).

*Proof.* Suppose that $1 - \chi(p)p^{-s} = 0$. Then $\chi(p) = p^s$, so $|\chi(p)| = p^{\operatorname{Re} s}$. Also $\overline{\chi(p)} = \chi(p)^{-1}$, so $|\chi(p)| = |\chi(p)|^{-1} = p^{-\operatorname{Re} s}$. Hence $p^{\operatorname{Re} s} = p^{-\operatorname{Re} s}$, and $\operatorname{Re} s = 0$ since $p > 1$. $\square$

The zeros of one factor are explicit. If $p \nmid q$ and $\chi(p) = e^{i\alpha}$, the factor $1 - \chi(p)p^{-s}$ vanishes exactly at $s = i(\alpha + 2\pi k)/\log p$, $k \in \mathbb{Z}$. These zeros lie on $\operatorname{Re} s = 0$. They are zeros of the imprimitive $L(s, \chi)$, and Section 5 shows that they do not reflect.

**Remark (Formalization).** The identity $\overline{\chi(p)} = \chi(p)^{-1}$ holds also when $\chi(p) = 0$, with Lean's convention $0^{-1} = 0$. So the proof needs no case distinction between $p \mid q$ and $p \nmid q$. The lemma allows $m = 0$, where the product is empty. The source applies it with $m = q$.

### The line $\operatorname{Re} s = 1$

**Theorem (Non-vanishing on $\operatorname{Re} s \geq 1$).** Let $\chi$ be a character modulo $q \geq 1$, and let $\operatorname{Re} s \geq 1$. If $\chi \neq \chi_0$ or $s \neq 1$, then $L(s, \chi) \neq 0$.

Mathlib: `DirichletCharacter.LFunction_ne_zero_of_one_le_re`.

For $\operatorname{Re} s > 1$ this follows from the Euler product. The point $s = 1$ with $\chi \neq \chi_0$ is Dirichlet's theorem $L(1, \chi) \neq 0$ (Davenport, Chapter 4). For $s = 1 + it$ with $t \neq 0$, the classical proof is that of Hadamard and de la Vallée Poussin. For $\sigma > 1$, the inequality $3 + 4\cos\alpha + \cos 2\alpha \geq 0$ gives $|L(\sigma, \chi_0)^3 L(\sigma + it, \chi)^4 L(\sigma + 2it, \chi^2)| \geq 1$, and a zero at $1 + it$ would make the left side tend to $0$ as $\sigma \to 1^+$. When $\chi^2 = \chi_0$ and $t = 0$ the inequality gives nothing, which is why $L(1, \chi) \neq 0$ for a real $\chi$ needs a separate argument. The source uses the theorem from Mathlib and does not prove it.

### The entire L-function

The logarithmic derivative $L'/L(s, \chi)$ has a pole at each zero of $L(s, \chi)$ and, for $\chi = \chi_0$, a pole at $s = 1$. The source removes the second kind by a factor $s - 1$, so that every pole is a zero of an entire function.

**Definition (The entire L-function).** Let $\chi$ be a character modulo $q \geq 1$. If $\chi \neq \chi_0$, put $\tilde L(s, \chi) = L(s, \chi)$. If $\chi = \chi_0$, put $\tilde L(s, \chi_0) = (s - 1)L(s, \chi_0)$ for $s \neq 1$ and $\tilde L(1, \chi_0) = \prod_{p \mid q}(1 - p^{-1}) = \varphi(q)/q$.

Lean: `New.entireL` (Lib/General/NumberTheory/ImaginaryQuadraticField.lean), with `DirichletCharacter.LFunctionTrivChar₁` (Mathlib) and `New.analyticAt_entireL` (Lib/Analytic/EntireLFunction.lean).

The value at $1$ is the residue of $L(s, \chi_0)$, so $\tilde L(\cdot, \chi)$ is entire in both cases. It has the same zeros as $L(\cdot, \chi)$ in $\mathbb{C} \setminus \{1\}$, with the same orders.

**Lemma (No zero on $\operatorname{Re} s \geq 1$).** Let $\chi$ be a character modulo $q \geq 1$ and let $\operatorname{Re} s \geq 1$. Then $\tilde L(s, \chi) \neq 0$.

Lean: `New.entireL_ne_zero` (Lib/Analytic/EntireLFunction.lean).

*Proof.* If $\chi \neq \chi_0$, this is the theorem above. If $\chi = \chi_0$ and $s = 1$, the value $\prod_{p \mid q}(1 - p^{-1})$ is not $0$. If $\chi = \chi_0$ and $s \neq 1$, then $s - 1 \neq 0$ and $L(s, \chi_0) \neq 0$ by the theorem above. $\square$

The twist of a character by a Legendre symbol is the main source of characters in the argument. One fact about it belongs here, since it decides whether $\tilde L$ of the twist is $L$ or $(s - 1)L$.

**Lemma (The quadratic twist is not principal).** Let $\chi$ be a character modulo $N$, let $d$ be an odd prime with $\gcd(N, d) = 1$, and let $\chi'$ be the character modulo $Nd$ with $\chi'(n) = \chi(n)\left(\frac{n}{d}\right)$. Then $\chi'$ is not principal.

Lean: `New.quadTwist_ne_one` (Lib/Analytic/EntireLFunction.lean), with `New.quadTwist` (Lib/General/NumberTheory/ImaginaryQuadraticField.lean) and `New.quadTwist_apply`.

*Proof.* Since $d$ is odd, there is a non-residue $b$ modulo $d$. By the Chinese remainder theorem there is $n$ with $n \equiv 1 \bmod N$ and $n \equiv b \bmod d$. Then $\chi'(n) = \chi(1)\left(\frac{b}{d}\right) = -1$. A value $x$ of a principal character satisfies $x^2 = x$, and $(-1)^2 \neq -1$. $\square$

**Remark (Formalization).** The source writes the twist as the product of the characters that $\chi$ and $(\cdot/d)$ induce modulo $Nd$. The lemma `New.quadTwist_apply` gives its value $\chi(n)(n/d)$ at every $n \in \mathbb{Z}$. The source uses $\tilde L$ only through its zeros and the residues of $\tilde L'/\tilde L$. Chapter 2 of this volume, [polar functions and the explicit formula](/chapter/polar-functions/), treats these residues.
