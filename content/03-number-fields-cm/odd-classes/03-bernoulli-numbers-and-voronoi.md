---
title: Bernoulli numbers and Voronoi's congruence
lean:
  - Lib/Cyclotomic/Voronoi.lean
decls:
  - New.OddPart.sum_mul_bernoulli_eq_neg_mul_LFunction
  - New.OddPart.exists_sq_dvd_factorial_mul_sum_pow_sub
  - New.OddPart.voronoi_congruence
  - New.OddPart.voronoi_congruence_bernoulli
  - New.OddPart.IsStickelbergerBound
  - New.OddPart.exists_isStickelbergerBound
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Bernoulli numbers and Voronoi's congruence

This section gives the analytic input of the bound. For $N \ge 1$ and $e \ge 1$ it produces one nonzero integer $X$, with $X \le 2^{(N+e+3)^6}$, that is a multiple of every twisted Stickelberger sum of level $Nm$, up to an explicit factor, modulo $m$. Section 5 uses $X$ to kill the odd components of the Galois cocycles, and Section 6 uses its size. The tools are classical: the values of Dirichlet L-functions at negative integers, Voronoi's congruence, and one determinant.

Throughout, $N \ge 1$ and $e \ge 0$ are integers, and $B_k(X)$ is the Bernoulli polynomial. A Dirichlet character mod $N$ need not be primitive. For an integer $c$ and a positive integer $f$, $\lfloor ca/f \rfloor$ is the integer part of $ca/f$.

### Twisted Bernoulli sums and L-values

Let $\chi$ be a Dirichlet character mod $N$ with values in $\mathbb{C}$. For a primitive character, the textbook formulas are $B_{k,\chi} = N^{k-1}\sum_{a=1}^{N} \chi(a) B_k(a/N)$ and $L(1-k, \chi) = -B_{k,\chi}/k$ (Washington, *Introduction to Cyclotomic Fields*, Proposition 4.1 and Theorem 4.2). With $k = e + 1$, they give $\sum_{a} \chi(a) N^{e+1} B_{e+1}(a/N) = -(e+1) N L(\chi, -e)$. The source scales this sum by $(e+2)!$ so that every term is an integer, and it proves the formula for every character.

**Proposition (Hurwitz's formula for twisted Bernoulli sums).** Let $\chi$ be a complex Dirichlet character mod $N$, and let $e \ne 0$. Let $\beta : \mathbb{N} \to \mathbb{Z}$ satisfy $\beta(a) = (e+2)!\, N^{e+1} B_{e+1}(a/N)$ in $\mathbb{Q}$ for every $a$. Then
$$\sum_{a \in \mathbb{Z}/N} \chi(a)\, \beta(a) = -(e+2)!\,(e+1)\, N\, L(\chi, -e),$$
where $a$ is read as its representative in $[0, N)$.

Lean: `New.OddPart.sum_mul_bernoulli_eq_neg_mul_LFunction` (Lib/Cyclotomic/Voronoi.lean).

*Proof.* By definition $L(\chi, s) = N^{-s}\sum_{a \in \mathbb{Z}/N} \chi(a)\, \zeta(s, a/N)$, where $\zeta(s, x)$ is the Hurwitz zeta function, so $L(\chi, -e) = N^{e}\sum_a \chi(a)\, \zeta(-e, a/N)$. For $e \ge 1$ and $0 \le x \le 1$, $\zeta(-e, x) = -B_{e+1}(x)/(e+1)$. So $\beta(a) = -(e+2)!\,(e+1)\, N^{e+1}\, \zeta(-e, a/N)$, and the sum is $-(e+2)!\,(e+1)\,N\,L(\chi, -e)$. $\square$

The values $L(\chi, -e)$ vanish exactly when $\chi(-1) = (-1)^e$. This is [Lemma](/decl/New.OddPart.LFunction_neg_nat_eq_zero_iff/) of Volume 2, proved there from the reflection of zeros. With the proposition, it gives the following: if $e \ne 0$ and $\chi(-1) = -(-1)^e$, then $\sum_a \chi(a)\beta(a) \ne 0$ (Lean: `New.OddPart.sum_mul_bernoulli_ne_zero`). This is the only place where the analytic theory enters the chapter.

### Power sums along a progression

**Lemma.** Let $a \ge 0$. There is an integer $\beta$ with $\beta = (e+2)!\, N^{e+1} B_{e+1}(a/N)$ in $\mathbb{Q}$ such that for every $u \ge 0$,
$$u^2 \;\Big|\; (e+2)! \sum_{i < u} (a + iN)^{e+1} - \beta u \quad \text{in } \mathbb{Z}.$$

Lean: `New.OddPart.exists_sq_dvd_factorial_mul_sum_pow_sub` (Lib/Cyclotomic/Voronoi.lean).

*Proof.* The number $(i+1)!\, B_i$ is an integer for every $i$, by induction on the recursion $\sum_{k \le i} \binom{i+1}{k} B_k = 0$ (Lean: `New.OddPart.exists_intCast_eq_factorial_mul_bernoulli`). So the polynomial
$$p(X) = (e+1)!\, N^{e+2} \big( B_{e+2}(X/N) - B_{e+2}(0) \big)$$
has integer coefficients (Lean: `New.OddPart.exists_map_eq_bernoulli_sub_comp`). From $B_k(x+1) - B_k(x) = k x^{k-1}$ one gets $p(a + uN) - p(a) = N (e+2)! \sum_{i<u} (a+iN)^{e+1}$. By Taylor's formula for a polynomial with integer coefficients, $p(a + uN) - p(a) \equiv p'(a)\, uN \bmod (uN)^2$, and $p'(a) = (e+2)!\, N^{e+1} B_{e+1}(a/N)$, since $B_k' = k B_{k-1}$. Put $\beta = p'(a)$ and divide by $N$. $\square$

### Voronoi's congruence

The classical congruence of Voronoi relates the Bernoulli numbers to the integer parts $\lfloor ca/f \rfloor$ (Ireland and Rosen, *A Classical Introduction to Modern Number Theory*, Ch. 15). The source proves a twisted form, first for power sums, then for Bernoulli numbers.

**Lemma (Voronoi's congruence, twisted).** Let $O$ be a commutative ring and $\chi$ a Dirichlet character mod $N$ with values in $O$. Let $f = Nm$ with $f \ne 0$, and let $c \equiv 1 \bmod N$ be prime to $m$. Then in $O$
$$f^2 \;\Big|\; (c^{e+1} - 1) \sum_{t \in \mathbb{Z}/f} \chi(t)\, t^{e+1} \;-\; (e+1)\, c^e f \sum_{t \in \mathbb{Z}/f} \Big\lfloor \frac{ct}{f} \Big\rfloor \chi(t)\, t^e,$$
where $t$ is read as its representative in $[0, f)$.

Lean: `New.OddPart.voronoi_congruence` (Lib/Cyclotomic/Voronoi.lean).

*Proof.* As $c$ is prime to $N$ and to $m$, multiplication by $c$ permutes $\mathbb{Z}/f$. So $\sum_t \chi(t) t^{e+1} = \sum_t \chi(r_t) r_t^{e+1}$, where $r_t = ct - f k_t$ is the representative of $ct$ and $k_t = \lfloor ct/f \rfloor$. As $N \mid f$ and $c \equiv 1 \bmod N$, $\chi(r_t) = \chi(t)$. The binomial theorem gives $(ct - fk_t)^{e+1} \equiv (ct)^{e+1} - (e+1)(ct)^e f k_t \bmod f^2$. Sum over $t$ and rearrange. $\square$

**Theorem (Voronoi's congruence for Bernoulli numbers).** Let $O$ be a commutative ring without additive torsion, and $\chi$ a Dirichlet character mod $N$ with values in $O$. Let $m \ge 1$, and let $c \equiv 1 \bmod N$ be prime to $m$. Let $\beta : \mathbb{N} \to \mathbb{Z}$ satisfy $\beta(a) = (e+2)!\, N^{e+1} B_{e+1}(a/N)$ for every $a$. Then in $O$
$$m \;\Big|\; (e+2)!\,(e+1)\, N\, c^e \sum_{0 \le a < Nm} \Big\lfloor \frac{ca}{Nm} \Big\rfloor a^e \chi(a) \;-\; (c^{e+1} - 1) \sum_{a \in \mathbb{Z}/N} \chi(a)\, \beta(a).$$

Lean: `New.OddPart.voronoi_congruence_bernoulli` (Lib/Cyclotomic/Voronoi.lean).

*Proof.* Write $t = a + iN$ with $0 \le a < N$ and $0 \le i < m$. Then $\chi(t) = \chi(a)$, and the lemma on power sums gives
$$(e+2)! \sum_{0 \le t < Nm} \chi(t)\, t^{e+1} \equiv m \sum_{a} \chi(a)\, \beta(a) \bmod m^2.$$
Multiply the twisted Voronoi congruence, which holds modulo $f^2$ and so modulo $m^2$, by $(e+2)!$, and replace the power sum. Both sides are then $m$ times an element of $O$, modulo $m^2$. As $O$ has no additive torsion, divide by $m$. $\square$

**Example.** Let $N = 3$, $e = 2$ and $\chi$ the nontrivial character mod $3$, so $\chi(-1) = -1 = -(-1)^e$. Here $B_3(x) = x^3 - \tfrac{3}{2}x^2 + \tfrac{1}{2}x$, and $\beta(a) = 4! \cdot 27 \cdot B_3(a/3)$ is $0, 24, -24$ for $a = 0, 1, 2$. So $\sum_a \chi(a)\beta(a) = 48$, and Hurwitz's formula gives $L(\chi, -2) = -48/(24 \cdot 3 \cdot 3) = -2/9$, the classical value $-B_{3,\chi}/3$ with $B_{3,\chi} = 2/3$. Take $c = 4$ and $m = 5$. The Stickelberger sum $\sum_{0 \le a < 15} \lfloor 4a/15 \rfloor a^2 \chi(a)$ is $-211$. The left term of the theorem is $4! \cdot 3 \cdot 3 \cdot 16 \cdot (-211) = -729216$, the right term is $(4^3 - 1) \cdot 48 = 3024$, and their difference $-732240$ is divisible by $5$.

### The Stickelberger property

The source collects what Section 5 needs in one definition.

**Definition.** Let $N \ge 1$ and $e \ge 0$. A natural number $X$ has the *Stickelberger property* for $N$ and $e$ if:

1. for every prime $\ell$, some $c \equiv 1 \bmod N$ prime to $\ell$ has $(c^e - 1)(c^{e+1} - 1) \mid X$;
2. for every $c \equiv 1 \bmod N$, every domain $O$ of characteristic $0$, and every Dirichlet character $\psi$ mod $N$ with values in $O$ and $\psi(-1) = -(-1)^e$, there is $w \in O$ such that for every $m \ge 1$ prime to $c$,
$$m \;\Big|\; (c^{e+1} - 1)\, X - 2 w \sum_{0 \le a < Nm} \Big\lfloor \frac{ca}{Nm} \Big\rfloor a^e \psi(a) \quad \text{in } O.$$

Lean: `New.OddPart.IsStickelbergerBound` (Lib/Cyclotomic/Voronoi.lean).

The element $w$ depends on $c$ and $\psi$, but not on $m$. This is the point of the definition: one $w$ serves at all levels $m$, so the Stickelberger sums at the levels $N\ell^n$ for all $n$ are controlled by one integer. In Iwasawa theory, the compatibility of the Stickelberger elements at the levels $N\ell^n$ gives the Kubota-Leopoldt $\ell$-adic L-function (Washington, Ch. 7). The definition is a finite form of that compatibility, with the value at $-e$ in place of the $\ell$-adic L-function.

### One integer for all characters

**Theorem.** Let $N \ge 1$ and $e \ne 0$. There is a natural number $X \ne 0$ with $X \le 2^{(N+e+3)^6}$ that has the Stickelberger property for $N$ and $e$.

Lean: `New.OddPart.exists_isStickelbergerBound` (Lib/Cyclotomic/Voronoi.lean).

The idea is that one integer must be a multiple of a nonzero Bernoulli sum for every character $\psi$ of the right parity, and for every ring of values. The product of these sums over all characters is a norm, an integer. The source realizes it as the determinant of an integer matrix whose eigenvectors are the characters. The characters of the wrong parity have Bernoulli sum $0$, so the matrix is corrected there to keep the determinant nonzero.

*Proof.* Let $\beta(t) = (e+2)!\, N^{e+1} B_{e+1}(t/N)$, an integer by the lemma on power sums. For $t \in \mathbb{Z}/N$ put
$$g(t) = 2\beta(t) + [t = 1]\,(-1)^e + [t = -1],$$
where $[\cdot]$ is $1$ or $0$, and let $T$ be the matrix indexed by $(\mathbb{Z}/N)^\times$ with entries $T_{s,t} = g(t/s)$.

*Eigenvalues.* For a character $\chi$ with values in any commutative ring, the vector $(\chi(t))_t$ is an eigenvector of $T$ with eigenvalue $\lambda_\chi = \sum_{t} \chi(t)\, g(t) = 2\sum_t \chi(t)\beta(t) + (-1)^e + \chi(-1)$ (Lean: `New.OddPart.mulVec_mulChar_eq_sum_smul`). For complex $\chi$ with $\chi(-1) = -(-1)^e$, $\lambda_\chi = 2\sum_t \chi(t)\beta(t)$, and this is not $0$ by Hurwitz's formula and the trivial zeros. For $\chi(-1) = (-1)^e$, $\sum_t \chi(t)\beta(t) = 0$ by the same two results, so $\lambda_\chi = 2(-1)^e \ne 0$. The complex characters form a basis of the functions on $(\mathbb{Z}/N)^\times$, so $\det T \ne 0$ (Lean: `New.OddPart.det_ne_zero_of_forall_sum_mul_ne_zero`).

*The integer.* Put
$$X = \big((1+N)^e - 1\big)\big((1+N)^{e+1} - 1\big)\big((1+2N)^e - 1\big)\big((1+2N)^{e+1} - 1\big)\, |\det T|.$$
Each factor is nonzero, as $N \ge 1$ and $e \ge 1$, so $X \ne 0$.

*Size.* The Fourier series of the Bernoulli function gives $|B_{e+1}(x)| < 17\,(e+1)!$ for $0 \le x \le 1$ (Lean: `New.OddPart.abs_bernoulliFun_lt`). So $|\beta(t)| < 17 M$ with $M = (e+2)!\, N^{e+1} (e+1)!$, and every entry of $T$ is at most $64 M$ in absolute value. The expansion of the determinant gives $|\det T| \le \varphi(N)!\, (64M)^{\varphi(N)}$. Bound each base $a$ by $2^a$ and $a!$ by $a^a$, and compare exponents: $X \le 2^{(N+e+3)^6}$ (Lean: `New.OddPart.mul_sub_one_mul_le_two_pow_of_le`).

*Property 1.* A prime $\ell$ does not divide both $1 + N$ and $1 + 2N$, since it would divide their difference $N$ and then $1$. Take $c$ to be one of them that is prime to $\ell$. Then $c \equiv 1 \bmod N$, and $(c^e - 1)(c^{e+1} - 1)$ is a factor of $X$ (Lean: `New.OddPart.exists_modEq_one_coprime_dvd_of_prime`).

*Property 2.* Let $c$, $O$ and $\psi$ be as in the definition. Multiply the eigenvector equation by the adjugate of $T$ and read the coordinate at $1$: $\lambda_\psi$ divides $\det T$ in $O$, so $X = \lambda_\psi u$ for some $u \in O$. By the parity of $\psi$, $\lambda_\psi = 2\sum_a \psi(a)\beta(a)$. Voronoi's congruence for Bernoulli numbers, multiplied by $2u$, gives the property with $w = u\,(e+2)!\,(e+1)\,N\,c^e$. $\square$

**Remark (Formalization).** The integer $X$ of the theorem is an existence statement. The proof of [Theorem](/decl/New.exists_length_shaOdd_le/) takes one such $X$ for each $e$ with `choose`, so the reader should treat it as some integer with the two properties and the bound, not as the explicit product of the proof. Nothing later uses the formula for $X$. The factor $2$ in property 2 comes from the correction of the matrix at the characters of the wrong parity. The characters in property 2 are characters mod $N$ with values in any domain of characteristic $0$, primitive or not. This is what Section 6 needs, because there the values lie in a ring of $\ell$-adic integers. The classical sources state Voronoi's congruence for $\chi = 1$; the twist by $\chi$ and the form for Bernoulli sums are the source's own. The docstring of the theorem calls it a finite-level analogue of the interpolation property of the Kubota-Leopoldt $\ell$-adic L-functions. No $\ell$-adic L-function is defined, and the interpolation formula is not stated.

**Remark (Formalization).** The bound $2^{(N+e+3)^6}$ is crude. Only its shape matters for the argument: $\log X$ is at most a polynomial in $N + e$. Section 6 shows that $\log X$ enters the argument only through a sum that the source bounds by a power of the size parameter $x$.
