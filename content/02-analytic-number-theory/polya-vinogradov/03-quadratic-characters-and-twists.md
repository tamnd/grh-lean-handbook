---
title: Quadratic characters and twists
lean:
  - Lib/Analytic/QuadraticTwist.lean
  - Lib/Analytic/EntireLFunction.lean
decls:
  - New.exists_dirichletCharacter_eq_jacobiSym
  - New.dirichletCharacter_jacobiSym_ne_one
  - New.norm_sum_jacobiSym_le
  - New.norm_sum_jacobiSym_ordCompl_le
  - New.legendreSym_eq_jacobiSym_ordCompl
  - New.isPrimitive_quadTwist
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Quadratic characters and twists

The twists of the criterion are the characters $\xi\chi_K$, with $\chi_K = (\cdot/d)$ the Legendre symbol of a prime $d$. As a function of $n$ for fixed $d$, the symbol $(n/d)$ is a character modulo $d$. The count of bad primes needs it as a function of $d$ for fixed $n$. Quadratic reciprocity makes the exchange. This section proves the exchange for $d \equiv 7 \bmod 8$, the bound of Pólya-Vinogradov for sums of Jacobi symbols, and the primitivity of the twists.

### The classical facts

Let $m$ be an odd positive integer with prime factorization $m = p_1 \cdots p_r$ (with repetition). The *Jacobi symbol* is $(v/m) = \prod_i (v/p_i)$, a product of Legendre symbols. It is completely multiplicative in $v$ and in $m$, it depends only on $v \bmod m$, and it is $0$ exactly when $\gcd(v, m) > 1$. For odd positive $m$ and $n$ the reciprocity law holds:
$$\Bigl(\frac nm\Bigr)\Bigl(\frac mn\Bigr) = (-1)^{\frac{m - 1}2\cdot\frac{n - 1}2} \quad (\gcd(m, n) = 1), \qquad \Bigl(\frac{-1}m\Bigr) = (-1)^{\frac{m - 1}2}, \qquad \Bigl(\frac2m\Bigr) = (-1)^{\frac{m^2 - 1}8}.$$
See Ireland and Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 5, and Davenport, *Multiplicative Number Theory*, Chapter 5, where the real primitive characters are described by Kronecker symbols. Mathlib has the Jacobi symbol, `jacobiSym` (Mathlib), and its reciprocity law, `jacobiSym.quadratic_reciprocity'` (Mathlib).

The symbol $(\cdot/m)$ is principal exactly when $m$ is a square. If $m$ is a square, every value at a unit is $(\pm1)^2 = 1$. If $m$ is not a square, write $m = c^2 a$ with $a > 1$ squarefree, and take a prime $p \mid a$; the Chinese remainder theorem gives $v$ with $(v/p) = -1$ and $(v/p') = 1$ for the other primes $p' \mid m$.

The *odd part* $n^\circ$ of $n \neq 0$ is $n/2^{k}$, where $2^k$ is the largest power of $2$ that divides $n$. Lean writes `ordCompl[2] n`.

### Jacobi symbols as characters

**Lemma (The Jacobi symbol is a character).** For every $b \in \mathbb{N}$ there is a Dirichlet character $\psi$ modulo $b$ such that, if $b \neq 0$, then $\psi(v) = (v/b)$ for every $v \in \mathbb{Z}$.

Lean: `New.exists_dirichletCharacter_eq_jacobiSym` (Lib/Analytic/QuadraticTwist.lean).

*Proof.* Induction on the prime factorization of $b$. For $b = 1$ take the trivial character. If $\psi$ works for $b$ and $p$ is a prime, the twist $\psi(\cdot/p)$ modulo $bp$ works for $bp$: its value at $v$ is $(v/b)(v/p) = (v/bp)$, by [the formula for the values of the twist](/decl/New.quadTwist_apply/) and the multiplicativity of the Jacobi symbol in the lower argument. $\square$

The Jacobi symbol $(v/b)$ in Mathlib is defined for every $b \in \mathbb{N}$, also for even $b$, by the same product over the prime factors. So the lemma has no parity condition. For $b = 0$ the statement is empty.

**Lemma (Not principal).** Let $m$ be odd and not a square, and let $\psi$ be a character modulo $m$ with $\psi(v) = (v/m)$ for all $v \in \mathbb{Z}$. Then $\psi \neq \chi_0$.

Lean: `New.dirichletCharacter_jacobiSym_ne_one` (Lib/Analytic/QuadraticTwist.lean).

*Proof.* Write $m = c^2 a$ with $a$ squarefree. Since $m$ is not a square, $a \neq 1$. Let $p$ be a prime factor of $a$, and write $a = pb$. Then $p$ is odd and $\gcd(b, p) = 1$. Suppose $\psi = \chi_0$. For a unit $v$ modulo $m$, $(v/c)^2 = 1$, so $(v/p)(v/b) = 1$. Let $\psi_b$ be the character $(\cdot/b)$ of the last lemma. Then the twist $\psi_b(\cdot/p)$ modulo $bp$ is $1$ at every unit, so it is principal. This contradicts [Lemma](/decl/New.quadTwist_ne_one/), since $p \neq 2$ and $\gcd(b, p) = 1$. $\square$

### Pólya-Vinogradov for Jacobi symbols

**Lemma (Sums of Jacobi symbols).** Let $m$ be odd and not a square, and let $X \in \mathbb{N}$. Then
$$\Bigl|\sum_{v = 1}^{X}\Bigl(\frac{-v}m\Bigr)\Bigr| \leq 2\sqrt m\,(1 + \log m).$$

Lean: `New.norm_sum_jacobiSym_le` (Lib/Analytic/QuadraticTwist.lean).

*Proof.* Let $\psi$ be the character $(\cdot/m)$. Then $(-v/m) = \psi(-1)\psi(v)$, and $|\psi(-1)| \leq 1$. The character is not principal, by the last lemma. Apply [Theorem](/decl/New.polya_vinogradov/). $\square$

The mean square of Section 5 needs the bound as a power of the size of $n$, for every $n \neq 0$ with a non-square odd part.

**Lemma (Sums of Jacobi symbols of an odd part).** Let $\delta > 0$, let $n \geq 1$, and suppose that $n^\circ$ is not a square. Then for every $X \in \mathbb{N}$,
$$\Bigl|\sum_{v = 1}^{X}\Bigl(\frac{-v}{n^\circ}\Bigr)\Bigr| \leq 2\Bigl(1 + \frac2\delta\Bigr)\,n^{1/2 + \delta/2}.$$

Lean: `New.norm_sum_jacobiSym_ordCompl_le` (Lib/Analytic/QuadraticTwist.lean).

*Proof.* The odd part $n^\circ$ is odd and $n^\circ \leq n$. The last lemma gives the bound $2\sqrt n(1 + \log n)$. For $t \geq 1$ and $\varepsilon > 0$ we have $\log t \leq t^{\varepsilon}/\varepsilon$ and $1 \leq t^{\varepsilon}$. With $\varepsilon = \delta/2$ this gives $1 + \log n \leq (1 + 2/\delta)n^{\delta/2}$. $\square$

### Reciprocity for $d \equiv 7 \bmod 8$

**Lemma (Reciprocity).** Let $d$ be a prime with $d \equiv 7 \bmod 8$, and let $n \geq 1$. Then
$$\Bigl(\frac nd\Bigr) = \Bigl(\frac{-d}{n^\circ}\Bigr).$$

Lean: `New.legendreSym_eq_jacobiSym_ordCompl` (Lib/Analytic/QuadraticTwist.lean).

*Proof.* Write $n = 2^k m$ with $m = n^\circ$ odd. Since $d \equiv 7 \bmod 8$, $(2/d) = (-1)^{(d^2 - 1)/8} = 1$, so $(n/d) = (m/d)$. Since $d \equiv 3 \bmod 4$, reciprocity gives $(m/d) = (-1)^{(m - 1)/2}(d/m) = (-1/m)(d/m) = (-d/m)$. If $d \mid m$, both sides are $0$, and the formula still holds. $\square$

So, for fixed $n$, the value $(n/d)$ at a prime $d \equiv 7 \bmod 8$ is the value at $v = d$ of the function $v \mapsto (-v/n^\circ)$, which is periodic in $v$ with period $n^\circ$. This function is defined for every $v \geq 1$, prime or not. The mean square of Section 5 sums it over all $v \leq T^2$.

Both congruences matter. The condition $d \equiv 3 \bmod 4$ gives the sign $(-1)^{(m - 1)/2}$ that reciprocity needs, absorbed into $-d$. The condition $d \equiv 7 \bmod 8$ removes the power of $2$. For $d \equiv 3 \bmod 8$ one would get $(n/d) = (-1)^k(-d/n^\circ)$, and the coefficient would depend on $k$ as well.

**Example.** Let $d = 7$ and $n = 12 = 2^2\cdot 3$. Then $n^\circ = 3$, and $(12/7) = (5/7) = -1$, since the squares modulo $7$ are $1, 2, 4$. On the other side, $(-7/3) = (2/3) = -1$. The two values agree.

### Parity and primitivity of the twists

For a character $\psi$ modulo $M$ and a prime $d$, the twist $\psi\chi_K$ is the character modulo $Md$ with the value $\psi(n)(n/d)$ at $n$ ([the formula for its values](/decl/New.quadTwist_apply/)). If $d \equiv 3 \bmod 4$, then $(-1/d) = -1$, so $\psi\chi_K(-1) = -\psi(-1)$: the twist has the parity opposite to that of $\psi$, for every such $d$.

**Lemma (The twist of a primitive character).** Let $\psi$ be a primitive character modulo $M$, and let $d$ be an odd prime with $\gcd(M, d) = 1$. Then $\psi\chi_K$ is primitive modulo $Md$.

Lean: `New.isPrimitive_quadTwist` (Lib/Analytic/QuadraticTwist.lean).

*Proof.* Let $f$ be the conductor of $\psi\chi_K$, and let $\varepsilon = (\cdot/d)$ as a character modulo $d$. It is not principal, so its conductor is $d$. The conductor of a product divides the least common multiple, hence the product, of the conductors. Divide $\psi\chi_K$ by $\varepsilon$ (lifted to $Md$): the quotient is $\psi$ lifted to $Md$, with conductor $M$. So $M \mid fd$, and since $\gcd(M, d) = 1$, $M \mid f$. Divide by $\psi$ instead: $d \mid fM$, so $d \mid f$. Hence $Md \mid f$, and $f \mid Md$. $\square$

Primitivity matters in Section 4. The symmetry of the theta series, [Theorem](/decl/New.norm_thetaSeries_inv/), and the folding of the integral, [Corollary](/decl/New.integral_norm_thetaSeries_div/), hold only for primitive characters. For an imprimitive character the dual theta series has the coefficients $\tau(\chi, n)$, and these are not a multiple of $\bar\chi(n)$.

**Remark (Formalization).** The source writes the twist as the product of the characters that $\psi$ and $\varepsilon$ induce modulo $Md$. Here $\varepsilon$ is the quadratic character `chiK d` of $(\mathbb{Z}/d\mathbb{Z})^\times$ with values in $\mathbb{Z}$, mapped to $\mathbb{C}$. The lemma on primitivity asks for a prime $d$ (an instance `Fact d.Prime`) with $d \neq 2$ and $\gcd(M, d) = 1$, and for $M \neq 0$ (an instance `NeZero M`). The reciprocity lemma asks for $n \neq 0$, which for $n \in \mathbb{N}$ is $n \geq 1$. The first lemma of this section is an existence statement: the character is not named, and the later lemmas take any character with the values $(v/m)$ as a hypothesis.
