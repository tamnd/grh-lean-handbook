---
title: The Pólya-Vinogradov inequality
lean:
  - Lib/Analytic/PolyaVinogradov.lean
decls:
  - New.four_mul_le_norm_stdAddChar_sub_one
  - New.norm_sum_stdAddChar_pow_le
  - New.norm_sum_le_of_isPrimitive
  - New.card_divisors_le_two_mul_sqrt
  - New.sum_eq_sum_divisors_of_changeLevel_eq
  - New.polya_vinogradov
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The Pólya-Vinogradov inequality

A sum $\sum_{n \leq X} \chi(n)$ of a non-principal character modulo $q$ is periodic in $X$ with period $q$, and a full period sums to $0$. So the trivial bound is $q$. Pólya and Vinogradov proved, independently in 1918, that the true size is at most about $\sqrt q \log q$. This section states the classical theorem and proves the form of the source, which has the explicit constant $2\sqrt q(1 + \log q)$ for every non-principal character.

### The classical theorem

Write $e(x) = e^{2\pi i x}$. For a character $\chi$ modulo $q$, the Gauss sums $\tau(\chi, k) = \sum_{a \bmod q} \chi(a) e(ak/q)$ and $\tau(\chi) = \tau(\chi, 1)$ are those of [Proposition](/decl/New.norm_gaussSum_of_isPrimitive/): if $\chi$ is primitive, then $\tau(\chi, k) = \bar\chi(k)\tau(\chi)$ and $|\tau(\chi)| = \sqrt q$.

**Theorem (Pólya-Vinogradov, classical form).** Let $\chi$ be a non-principal character modulo $q$. Then for all integers $M$ and $N \geq 0$,
$$\Bigl|\sum_{M < n \leq M + N} \chi(n)\Bigr| \ll \sqrt q \log q,$$
with an absolute implied constant.

This is Davenport, *Multiplicative Number Theory*, Chapter 23, and Montgomery and Vaughan, *Multiplicative Number Theory I*, Theorem 9.18. Iwaniec and Kowalski, *Analytic Number Theory*, Chapter 12, treat it with the other bounds for character sums.

The proof for a primitive $\chi$ is a finite Fourier expansion. By the proposition on Gauss sums, $\chi(n) = \tau(\bar\chi)^{-1}\sum_{k \bmod q} \bar\chi(k) e(kn/q)$, up to a sign convention. Sum over the interval: each $k \neq 0$ gives a geometric series of size at most $\|k/q\|^{-1}/2$, where $\|x\|$ is the distance to the nearest integer, and the term $k = 0$ vanishes. With $|\tau(\bar\chi)| = \sqrt q$ the total is at most $q^{-1/2}\sum_{0 < k < q}\|k/q\|^{-1}/2 \ll \sqrt q \log q$. An imprimitive $\chi$ is reduced to the primitive character that induces it by a Möbius sum over the divisors of $q/q^*$.

### The geometric sums

For $k \in \mathbb{Z}/q\mathbb{Z}$ let $k_0 \in \{0, \dots, q - 1\}$ be its representative. Mathlib's standard additive character of $\mathbb{Z}/q\mathbb{Z}$ is $\mathbf{e}(k) = e(k_0/q)$.

**Lemma (The chord).** Let $k \in \mathbb{Z}/q\mathbb{Z}$ and $x \in [0, 1]$ with $k_0 = qx$. Then $|\mathbf{e}(k) - 1| \geq 4x(1 - x)$.

Lean: `New.four_mul_le_norm_stdAddChar_sub_one` (Lib/Analytic/PolyaVinogradov.lean).

*Proof.* Put $y = \pi x/2 \in [0, \pi/2]$. Then $|e(x) - 1| = 2\sin(\pi x) = 4\sin y\cos y$. By concavity of $\sin$ on $[0, \pi/2]$, $\sin y \geq x$, and by concavity of $\cos$ there, $\cos y \geq 1 - x$. Multiply. $\square$

The classical proofs use $|e(x) - 1| = 2\sin(\pi\|x\|) \geq 4\|x\|$. The product $x(1 - x)$ is a little weaker near $x = 1/2$, but it splits into partial fractions, and this gives the harmonic sum below.

**Lemma (The geometric sums).** Let $k \in \mathbb{Z}/q\mathbb{Z}$ with $k \neq 0$, and let $X \in \mathbb{N}$. Then
$$\Bigl|\sum_{v = 1}^{X} \mathbf{e}(k)^v\Bigr| \leq \frac q2\Bigl(\frac1{k_0} + \frac1{q - k_0}\Bigr).$$

Lean: `New.norm_sum_stdAddChar_pow_le` (Lib/Analytic/PolyaVinogradov.lean).

*Proof.* Since $k \neq 0$, $\mathbf{e}(k) \neq 1$. The geometric sum is $(\mathbf{e}(k)^{X + 1} - \mathbf{e}(k))/(\mathbf{e}(k) - 1)$. The numerator has absolute value at most $2$. By the lemma on the chord, with $x = k_0/q \in (0, 1)$, the denominator has absolute value at least $4x(1 - x)$. Finally $2/(4x(1 - x)) = \frac q2(1/k_0 + 1/(q - k_0))$. $\square$

### Primitive characters

**Proposition (Pólya-Vinogradov for a primitive character).** Let $q \neq 1$, let $\chi$ be a primitive character modulo $q$, and let $X \in \mathbb{N}$. Then
$$\Bigl|\sum_{v = 1}^{X}\chi(v)\Bigr| \leq \sqrt q\,(1 + \log q).$$

Lean: `New.norm_sum_le_of_isPrimitive` (Lib/Analytic/PolyaVinogradov.lean).

*Proof.* Step 1: the expansion. Fourier inversion on $\mathbb{Z}/q\mathbb{Z}$ and the proposition on Gauss sums give
$$\chi(v) = \frac1q\sum_{k \bmod q}\mathbf{e}(k)^v\,\bar\chi(-k)\,\tau(\chi).$$
Sum over $1 \leq v \leq X$ and exchange the sums.

Step 2: the term $k = 0$. Since $q \neq 1$, the class $0$ is not a unit, so $\bar\chi(0) = 0$, and the term $k = 0$ vanishes.

Step 3: the other terms. For $k \neq 0$, $|\bar\chi(-k)| \leq 1$, $|\tau(\chi)| = \sqrt q$, and the lemma on geometric sums applies. So
$$\Bigl|\sum_{v = 1}^X\chi(v)\Bigr| \leq \frac{\sqrt q}{q}\sum_{k_0 = 1}^{q - 1}\frac q2\Bigl(\frac1{k_0} + \frac1{q - k_0}\Bigr) = \sqrt q\,H_{q - 1} \leq \sqrt q\,H_q,$$
where $H_q = \sum_{n = 1}^q 1/n$ is the harmonic number. The two halves of the sum are equal after $k_0 \mapsto q - k_0$.

Step 4: the harmonic number. $H_q \leq 1 + \log q$, by comparison with $\int_1^q dt/t$ (`harmonic_le_one_add_log` (Mathlib)). $\square$

**Remark (Formalization).** In Step 3 the source sums the bound over $n = 0, \dots, q$, not over $k_0 = 1, \dots, q - 1$. The two extra terms contain $1/0$ and $1/(q - q)$, which Lean evaluates to $0$. So the sum over the larger range is exactly $2H_q$, and the inequality is still true. The junk value does no harm here, and the source says so in a comment.

**Example.** Let $q = 5$ and let $\chi = (\cdot/5)$, the Legendre symbol. The values at $1, 2, 3, 4$ are $1, -1, -1, 1$, so the partial sums are $1, 0, -1, 0$, and then they repeat. The maximum is $1$. The bound is $\sqrt 5(1 + \log 5) \approx 5.84$. For small $q$ the inequality is far from sharp. Its point is the uniformity in the length $X$.

### Imprimitive characters

Let $\chi$ be a character modulo $q$, and let $\psi$ be a character modulo $M$ that induces $\chi$, with $q = Mr$. Then $\chi(v) = \psi(v)$ if $\gcd(v, r) = 1$, and $\chi(v) = 0$ otherwise (since $\gcd(v, q) = 1$ exactly when $\gcd(v, M) = 1$ and $\gcd(v, r) = 1$). Möbius inversion gives $\chi(v) = \sum_{e \mid \gcd(v, r)}\mu(e)\psi(v)$ (Lean: `New.apply_eq_sum_moebius_smul_of_changeLevel_eq`).

**Lemma (The Möbius sieve).** Let $q = Mr$, and let $\psi$ modulo $M$ induce $\chi$ modulo $q$. Then for every $X \in \mathbb{N}$,
$$\sum_{v = 1}^X\chi(v) = \sum_{e \mid r}\mu(e)\,\psi(e)\sum_{w = 1}^{\lfloor X/e\rfloor}\psi(w).$$

Lean: `New.sum_eq_sum_divisors_of_changeLevel_eq` (Lib/Analytic/PolyaVinogradov.lean), with `New.apply_eq_sum_moebius_smul_of_changeLevel_eq` and `New.filter_dvd_Ioc_eq_image_mul`.

*Proof.* Insert the formula for $\chi(v)$, exchange the sums over $v$ and $e$, and write the multiples of $e$ in $[1, X]$ as $v = ew$ with $1 \leq w \leq \lfloor X/e\rfloor$. Then $\psi(ew) = \psi(e)\psi(w)$. $\square$

**Lemma (Divisors).** Every $r \in \mathbb{N}$ has at most $2\sqrt r$ divisors.

Lean: `New.card_divisors_le_two_mul_sqrt` (Lib/Analytic/PolyaVinogradov.lean).

*Proof.* Of two complementary divisors $e$ and $r/e$, one is at most $\sqrt r$. So the map $e \mapsto \min(e, r/e)$ sends the divisors into $\{1, \dots, \lfloor\sqrt r\rfloor\}$, and each fibre has at most two elements. For $r = 0$ the set of divisors is empty in Mathlib, and the bound holds. $\square$

The bound is weak: the number of divisors is $r^{o(1)}$. But it is exactly what is needed to turn $\sqrt M$ into $\sqrt q$.

### The theorem of the source

**Theorem (Pólya-Vinogradov).** Let $q \geq 1$, let $\chi$ be a character modulo $q$ with $\chi \neq \chi_0$, and let $X \in \mathbb{N}$. Then
$$\Bigl|\sum_{v = 1}^X\chi(v)\Bigr| \leq 2\sqrt q\,(1 + \log q).$$

Lean: `New.polya_vinogradov` (Lib/Analytic/PolyaVinogradov.lean).

*Proof.* By [Lemma](/decl/New.exists_isPrimitive_changeLevel_eq/), a primitive character $\psi$ modulo some $M \mid q$ induces $\chi$. Write $q = Mr$. If $M = 1$, then $\psi$ is the trivial character, and it induces $\chi_0$; so $M \neq 1$. By the lemma on the Möbius sieve, the sum is a sum over the divisors $e$ of $r$ of terms $\mu(e)\psi(e)\sum_{w \leq X/e}\psi(w)$. Each term is at most $\sqrt M(1 + \log M) \leq \sqrt M(1 + \log q)$ in absolute value, by the proposition for primitive characters and $|\mu(e)\psi(e)| \leq 1$. There are at most $2\sqrt r$ terms, by the lemma on divisors. So the sum is at most $2\sqrt r\sqrt M(1 + \log q) = 2\sqrt q(1 + \log q)$. $\square$

**Remark (Formalization).** The theorem of the source is the classical theorem for initial intervals $[1, X]$ only, with $X$ a natural number, and with the explicit constant $2$. Two points are worth a check.

1. Arbitrary intervals. A sum over $(Y, X]$ is a difference of two initial sums, so it is at most $4\sqrt q(1 + \log q)$. The source does not state this, and it does not need it: the only use, in Section 3, is a sum over $1 \leq v \leq \lfloor T^2\rfloor$.
2. The constant. The classical reduction loses the factor $2^{\omega(r)}$, the number of squarefree divisors of $r$. The source sums over all divisors and bounds their number by $2\sqrt r$. This is cruder, but it gives a clean bound in terms of $q$ alone. The argument never needs a constant better than $O_\varepsilon(q^{1/2 + \varepsilon})$: Section 3 replaces $\log q$ at once by $q^{\delta/2}$.

The hypothesis $\chi \neq \chi_0$ is necessary: for $\chi_0$ the sum is about $X\varphi(q)/q$. For $q = 1$ every character is $\chi_0$, so the hypothesis excludes $q = 1$.
